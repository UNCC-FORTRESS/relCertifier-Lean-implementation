#!/usr/bin/env python3
"""Transcription-fidelity audit: Lean instance data terms vs benchmark R sides.

Each `def <name>{M,T,A}` in {Settling,Terrain,Affine}Instances.lean is a hand
transcription of a benchmark's [Rsys] under documented conventions (values scaled
per coordinate, time scaled by lambda/epsilon_R so dtQ = 1). A mistranscription
would attach a kernel certificate to the wrong model, so this checks, per mode:

  1. mode count and successor lists (succs == next minus the self-loop, as indices);
  2. shape KIND vs ode form per coordinate (frozen <-> 0; driven j <-> the plain
     driver var; chase j k <-> (- x_j (* k x)); self-affine shapes <-> odes that
     reference only the coordinate itself; drivenDamp <-> the damped-product form);
  3. guard band vs [glo, ghi] under the gcoord scale (x1000);
  4. envelope vs evolve: for each coordinate with both bounds finite on both sides,
     a SINGLE positive linear factor must map the evolve interval to the env
     interval (the per-coordinate value scale); one-sided bounds must agree in
     which sides are present.

Kind- and reference-level checks catch slot mix-ups; the linear-factor check
catches envelope typos without hard-coding each benchmark's scale table.
"""
import re, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
BENCH = os.path.join(ROOT, "benchmarks", "suite_uniform")

# ---------- benchmark parsing ----------
def parse_bench(path):
    txt = open(path).read()
    out = {"modes": [], "vars": None}
    cur = None
    in_r = False
    for line in txt.splitlines():
        ls = line.strip()
        if ls.startswith("#") or not ls:
            continue
        if re.match(r"\[Rsys\]", ls):
            in_r = True; cur = None; continue
        m = re.match(r"\[Rsys\.mode\.(\w+)\]", ls)
        if m:
            in_r = True
            cur = {"name": m.group(1)}
            out["modes"].append(cur)
            continue
        if re.match(r"\[.*\]", ls):
            in_r = False; cur = None; continue
        if not in_r:
            continue
        if cur is None and ls.startswith("state_vars"):
            out["vars"] = [v.strip() for v in ls.split("=",1)[1].strip().strip("[]").split(",")]
        if cur is not None:
            for key in ("ode", "guard", "evolve", "next"):
                if ls.startswith(key):
                    cur[key] = ls.split("=",1)[1].strip()
    return out

def ode_map(ode):
    d = {}
    for part in ode.split(";"):
        m = re.match(r"([\w]+)' = (.*)", part.strip())
        if m:
            rhs = m.group(2).strip()
            rhs = re.sub(r"^smt2:", "", rhs)
            d[m.group(1)] = rhs
    return d

def bounds(ev):
    d = {}
    for a in ev.split(" and "):
        m = re.match(r"([\w]+)\s*(>=|>|<=|<)\s*(-?[\d.]+)", a.strip())
        if not m: continue
        v, op, val = m.group(1), m.group(2), float(m.group(3))
        lo, hi = d.setdefault(v, [None, None])
        if op in (">=", ">"): d[v][0] = val if lo is None else max(lo, val)
        else: d[v][1] = val if hi is None else min(hi, val)
    return d

def refs(expr, allvars, self_var):
    toks = set(re.findall(r"[A-Za-z_]\w*", expr))
    return {v for v in allvars if v in toks}, (self_var in toks)

# ---------- Lean instance parsing ----------
def parse_instances(path, suffix):
    txt = open(path).read()
    out = {}
    for m in re.finditer(r"def (\w+)" + suffix + r"\b.*?(?=\nexample|\ndef |\Z)", txt, re.S):
        name, body = m.group(1), m.group(0)
        modes = []
        for sm in re.finditer(r"shapes := !\[(.*?)\], gcoord := (\d+),\s*"
                              r"glo := (-?\d+), ghi := (-?\d+), succs := \[([\d, ]*)\]", body, re.S):
            shapes_raw = sm.group(1)
            shapes = []
            depth = 0; tok = ""
            for ch in shapes_raw:
                if ch == "," and depth == 0:
                    shapes.append(tok.strip()); tok = ""
                else:
                    if ch in "([": depth += 1
                    if ch in ")]": depth -= 1
                    tok += ch
            if tok.strip(): shapes.append(tok.strip())
            modes.append({
                "shapes": shapes,
                "gcoord": int(sm.group(2)),
                "glo": int(sm.group(3)), "ghi": int(sm.group(4)),
                "succs": [int(x) for x in sm.group(5).replace(",", " ").split()],
            })
        env = []
        em = re.search(r"env := !\[(.*?)\]\s*\n?\s*dtQ", body, re.S) or \
             re.search(r"env := !\[(.*?)\]", body, re.S) or \
             re.search(r"env := fun _ => ({.*?})", body)
        if em:
            for b in re.finditer(r"{ lo := ([^,]+), hi := ([^}]+) }", em.group(1)):
                def val(s):
                    s = s.strip()
                    if s == "none": return None
                    mm = re.search(r"some \(?(-?\d+)", s)
                    return int(mm.group(1)) if mm else None
                env.append((val(b.group(1)), val(b.group(2))))
        if modes:
            out[name] = {"modes": modes, "env": env}
        else:
            out[name] = None  # unparsed style (e.g. `shapes := fun _ =>`)
    return out

def shape_kind(s):
    s = s.replace("CoordShape.", "")
    for k in ("drivenDamp", "driven", "contractQ", "contract", "constRate",
              "frozen", "riccati", "pairSym", "chase"):
        if s.startswith(k):
            args = re.findall(r"-?\d+", s[len(k):])
            return k, [int(a) for a in args]
    return s, []

NAME_MAP = {
    "watertankSuite": "watertank",
}

def bench_dir(name):
    if name in NAME_MAP: return NAME_MAP[name]
    for cand in (name, re.sub(r"_\d+dof$", "", name), re.sub(r"_12dof$", "", name),
                 re.sub(r"_6to8$", "_6to8", name)):
        if os.path.isdir(os.path.join(BENCH, cand)): return cand
    return None

def main():
    fails = notes = checked = 0
    inst = {}
    inst.update(parse_instances(os.path.join(ROOT, "RelCertifier/SettlingInstances.lean"), "M"))
    inst.update(parse_instances(os.path.join(ROOT, "RelCertifier/TerrainInstances.lean"), "T"))
    inst.update(parse_instances(os.path.join(ROOT, "RelCertifier/AffineInstances.lean"), "A"))
    for name, I in sorted(inst.items()):
        if I is None:
            print(f"NOTE  {name}: non-literal style, checked by eye"); notes += 1; continue
        bd = bench_dir(name)
        if bd is None:
            print(f"NOTE  {name}: no benchmark dir matched"); notes += 1; continue
        B = parse_bench(os.path.join(BENCH, bd, "input.txt"))
        vs = B["vars"]; msgs = []
        if len(I["modes"]) != len(B["modes"]):
            msgs.append(f"mode count {len(I['modes'])} vs {len(B['modes'])}")
        idx_of = {m["name"]: i for i, m in enumerate(B["modes"])}
        for qi, (im, bm) in enumerate(zip(I["modes"], B["modes"])):
            nxt = [idx_of[n.strip()] for n in bm.get("next", "").strip("[]").split(",")
                   if n.strip() in idx_of]
            want = sorted(set(nxt) - {qi})
            if sorted(set(im["succs"])) != want:
                msgs.append(f"{bm['name']}: succs {im['succs']} vs next-minus-self {want}")
            om = ode_map(bm.get("ode", ""))
            n = len(im["shapes"])
            if n != len(vs):
                # inert padding is allowed: extra trailing coords must be frozen
                # with an unconstrained envelope (a frozen, env-free coordinate
                # cannot affect H for the real coordinates)
                extra = im["shapes"][len(vs):]
                extra_env = I["env"][len(vs):n] if I["env"] else []
                if n > len(vs) and all(sh.endswith("frozen") for sh in extra) \
                        and all(e == (None, None) for e in extra_env):
                    pass
                else:
                    msgs.append(f"{bm['name']}: {n} shapes vs {len(vs)} vars")
                    continue
            for ci, sh in enumerate(im["shapes"][:len(vs)]):
                kind, args = shape_kind(sh)
                v = vs[ci]; expr = om.get(v, "")
                rf, selfref = refs(expr, vs, v)
                rf_other = rf - {v}
                ok = True
                if kind == "frozen":
                    ok = expr in ("0", "0.0") or re.fullmatch(r"\(?0\)?", expr)
                elif kind == "driven":
                    ok = (len(rf_other) <= 1) and not selfref and rf_other == {vs[args[0]]} \
                         if args and not expr.startswith("(*") and "(" not in expr or True else True
                    ok = rf == {vs[args[0]]} if args else False
                elif kind == "drivenDamp":
                    ok = vs[args[0]] in rf if args else False
                elif kind in ("contract", "contractQ", "constRate", "riccati"):
                    ok = rf_other == set()
                elif kind == "chase":
                    ok = selfref and rf_other == {vs[args[0]]}
                elif kind == "pairSym":
                    ok = selfref and rf_other == {vs[args[0]]}
                if not ok:
                    msgs.append(f"{bm['name']}.{v}: shape {kind}{args} vs ode refs {sorted(rf)} '{expr[:40]}'")
            gb = bounds(bm.get("guard", ""))
            # gcoord guard band (settling family: guard on the gcoord var)
            gv = vs[im["gcoord"]]
            if gv in gb and gb[gv][0] is not None:
                if abs(gb[gv][0] * 1000 - im["glo"]) > 0.5:
                    msgs.append(f"{bm['name']}: glo {im['glo']} vs guard lo {gb[gv][0]}")
                if gb[gv][1] is not None and abs(gb[gv][1] * 1000 - im["ghi"]) > 0.5:
                    msgs.append(f"{bm['name']}: ghi {im['ghi']} vs guard hi {gb[gv][1]}")
        # envelope linear-consistency (mode 0's evolve == all modes')
        eb = bounds(B["modes"][0].get("evolve", ""))
        for ci, (elo, ehi) in enumerate(I["env"][:min(len(vs), len(I["env"]))]):
            v = vs[ci]
            blo, bhi = eb.get(v, (None, None))
            if (blo is None) != (elo is None) or (bhi is None) != (ehi is None):
                msgs.append(f"env[{v}]: sidedness {elo},{ehi} vs {blo},{bhi}")
                continue
            cands = []
            if bhi not in (None, 0) and ehi is not None: cands.append(ehi / bhi)
            if blo not in (None, 0) and elo is not None: cands.append(elo / blo)
            if len(cands) == 2 and abs(cands[0] - cands[1]) > 1e-6 * max(1, abs(cands[0])):
                msgs.append(f"env[{v}]: inconsistent scale {cands[0]:.4g} vs {cands[1]:.4g} "
                            f"(env [{elo},{ehi}] vs evolve [{blo},{bhi}])")
            if cands and cands[0] <= 0:
                msgs.append(f"env[{v}]: nonpositive scale {cands[0]}")
        checked += 1
        if msgs:
            fails += 1
            print(f"VIOL {name} -> {bd}")
            for x in msgs[:10]: print("     ", x)
    # the documented transcription lambda must lie in the benchmark's declared range
    for f in ("SettlingInstances", "TerrainInstances", "AffineInstances"):
        txt = open(os.path.join(ROOT, "RelCertifier", f + ".lean")).read()
        for m in re.finditer(r"/-- `(\w+?)`.*?at\s*\n?#?\s*λ = (\d+)", txt, re.S):
            bench, lam = m.group(1), int(m.group(2))
            p2 = os.path.join(BENCH, bench, "input.txt")
            if not os.path.exists(p2): continue
            b = open(p2).read()
            lo = float(re.search(r"lambda_min = ([\d.]+)", b).group(1))
            hi = float(re.search(r"lambda_max = ([\d.]+)", b).group(1))
            if not (lo <= lam <= hi):
                print(f"VIOL {bench}: transcription λ={lam} outside declared [{lo},{hi}]")
                fails += 1
    print(f"instances checked: {checked}, violations: {fails}, notes: {notes}")
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
