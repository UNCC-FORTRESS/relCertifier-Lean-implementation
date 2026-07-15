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

# ---------- polynomial extraction from ode RHS (exact Fractions) ----------
from fractions import Fraction

def tokenize_s(s):
    s = s.replace("(", " ( ").replace(")", " ) ")
    return s.split()

def parse_sexpr(toks):
    t = toks.pop(0)
    if t == "(":
        op = toks.pop(0)
        args = []
        while toks[0] != ")":
            args.append(parse_sexpr(toks))
        toks.pop(0)
        return (op, args)
    return t

class Poly:
    """Multivariate polynomial: dict monomial(frozenset of (var,exp))->Fraction."""
    def __init__(self, d=None): self.d = dict(d or {})
    @staticmethod
    def const(c):
        c = Fraction(c)
        return Poly({frozenset(): c} if c != 0 else {})
    @staticmethod
    def var(v): return Poly({frozenset({(v, 1)}): Fraction(1)})
    def __add__(a, b):
        d = dict(a.d)
        for m, c in b.d.items(): d[m] = d.get(m, Fraction(0)) + c
        return Poly({m: c for m, c in d.items() if c != 0})
    def __neg__(a): return Poly({m: -c for m, c in a.d.items()})
    def __sub__(a, b): return a + (-b)
    def __mul__(a, b):
        d = {}
        for m1, c1 in a.d.items():
            for m2, c2 in b.d.items():
                e = {}
                for v, k in list(m1) + list(m2): e[v] = e.get(v, 0) + k
                m = frozenset(e.items())
                d[m] = d.get(m, Fraction(0)) + c1 * c2
        return Poly({m: c for m, c in d.items() if c != 0})
    def coeff(self, *vars_exp):
        return self.d.get(frozenset(vars_exp), Fraction(0))

def sexpr_to_poly(e):
    if isinstance(e, str):
        try: return Poly.const(Fraction(e))
        except ValueError: return Poly.var(e)
    op, args = e
    ps = [sexpr_to_poly(a) for a in args]
    if op == "-":
        if len(ps) == 1: return -ps[0]
        r = ps[0]
        for q in ps[1:]: r = r - q
        return r
    if op == "+":
        r = ps[0]
        for q in ps[1:]: r = r + q
        return r
    if op == "*":
        r = ps[0]
        for q in ps[1:]: r = r * q
        return r
    if op == "/":
        num, den = ps
        assert list(den.d) == [frozenset()], "nonconstant divisor"
        return num * Poly.const(Fraction(1) / den.coeff())
    raise ValueError(f"op {op}")

def ode_poly(expr):
    """expr: benchmark ode RHS (smt2:... or plain). -> Poly or None."""
    expr = expr.strip()
    if expr.startswith("smt2:"): expr = expr[5:].strip()
    try:
        if expr.startswith("("):
            return sexpr_to_poly(parse_sexpr(tokenize_s(expr)))
        # plain: a bare var or number (e.g. "v", "0.2")
        return sexpr_to_poly(expr)
    except Exception:
        return None

# ---------- Lean instance parsing ----------
def parse_instances(path, suffix):
    txt = open(path).read()
    out = {}
    for m in re.finditer(r"(/--(?:[^-]|-(?!/))*?-/\s*)?def (\w+)" + suffix +
                         r"\b.*?(?=\n/--|\nexample|\ndef |\Z)", txt, re.S):
        name, body = m.group(2), m.group(0)
        modes = []
        for sm in re.finditer(r"shapes := !\[(.*?)\],\s*gcoord := (\d+),\s*"
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
        dtq = 1
        dm = re.search(r"dtQ := (\d+)", body)
        if dm: dtq = int(dm.group(1))
        lam = None
        lm = re.search(r"at\s*\n?\s*λ = (\d+)", body) or re.search(r"λ = (\d+)\b[^.]*\)?\.", body)
        if lm: lam = int(lm.group(1))
        sbands = []
        for sb in re.finditer(r"{ sc := (\d+), slo := (-?\d+), shi := (some \(?-?\d+\)?|none) }", body):
            shi = None if sb.group(3) == "none" else int(re.search(r"-?\d+", sb.group(3)).group(0))
            sbands.append((int(sb.group(1)), int(sb.group(2)), shi))
        # damper triples per mode/coord: shapes like drivenDamp 0 [(2, 1, 2000000), ...]
        for md in modes:
            dampers = {}
            for ci, sh in enumerate(md["shapes"]):
                if "drivenDamp" in sh:
                    trips = re.findall(r"\((\d+),\s*(\d+),\s*(\d+)\)", sh)
                    dampers[ci] = [(int(a), int(b), int(c)) for a, b, c in trips]
            md["dampers"] = dampers
        vtops = None
        vm = re.search(r"vtops := \[(.*?)\]", body, re.S)
        if vm:
            vtops = [None if t.strip() == "none" else int(re.search(r"-?\d+", t).group(0))
                     for t in vm.group(1).split(",")]
        if modes:
            out[name] = {"modes": modes, "env": env, "dtq": dtq, "lam": lam,
                         "sbands": sbands, "vtops": vtops}
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
        # time unit u: real seconds per stored time unit = (eps_R/lambda)/dtQ
        btxt = open(os.path.join(BENCH, bd, "input.txt")).read()
        rsec = btxt.split("[Rsys]", 1)[1]
        em2 = re.search(r"^epsilon = ([\d.]+)", rsec, re.M)
        epsR = Fraction(str(em2.group(1))) if em2 else Fraction(1)
        lam = I.get("lam") or 1
        u = (epsR / lam) / I.get("dtq", 1)
        # per-coordinate value scale from envelope/evolve ratios (exact); gcoord from guard
        eb0 = bounds(B["modes"][0].get("evolve", ""))
        scale = {}
        for ci, v in enumerate(vs):
            if ci < len(I["env"]):
                elo, ehi = I["env"][ci]
                blo, bhi = eb0.get(v, (None, None))
                for ev, bv in ((ehi, bhi), (elo, blo)):
                    if ev is not None and bv not in (None, 0):
                        scale[v] = Fraction(ev) / Fraction(str(bv))
                        break
        gv0 = vs[I["modes"][0]["gcoord"]]
        scale.setdefault(gv0, Fraction(1000))
        # derive missing scales through the coupling relations (cj*scale[v]*u = scale[j])
        om0 = ode_map(B["modes"][0].get("ode", ""))
        for _ in range(3):
            for ci, sh in enumerate(I["modes"][0]["shapes"][:len(vs)]):
                kind, args = shape_kind(sh)
                if kind not in ("driven", "chase", "drivenDamp") or not args:
                    continue
                v, j = vs[ci], vs[args[0]]
                P0 = ode_poly(om0.get(v, ""))
                if P0 is None: continue
                cj = P0.d.get(frozenset({(j, 1)}), Fraction(0))
                if cj == 0: continue
                if v in scale and j not in scale:
                    scale[j] = cj * scale[v] * u
                elif j in scale and v not in scale:
                    scale[v] = scale[j] / (cj * u)
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
                P = ode_poly(expr)
                if P is None:
                    msgs.append(f"{bm['name']}.{v}: cannot poly-ize ode '{expr[:40]}'")
                    continue
                X = lambda w: frozenset({(w, 1)})
                X2 = lambda w: frozenset({(w, 2)})
                A0 = P.coeff()                       # constant term
                Bi = P.d.get(X(v), Fraction(0))      # self coefficient
                sc = lambda w: scale.get(w)          # per-coordinate value scale (Fraction|None)
                def chk(cond, what):
                    if not cond: msgs.append(f"{bm['name']}.{v}: {what}")
                if kind == "frozen":
                    chk(not P.d, f"frozen but ode = '{expr[:40]}'")
                elif kind == "constRate":
                    chk(set(P.d) <= {frozenset()}, "constRate but nonconstant ode")
                    if sc(v) is not None:
                        chk(Fraction(args[0]) == A0 * sc(v) * u,
                            f"constRate stored {args[0]} != {A0}*scale*u")
                elif kind in ("contract", "contractQ"):
                    kk = Fraction(args[0]) if kind == "contract" else Fraction(args[0], args[1])
                    cc = Fraction(args[-1])
                    chk(set(P.d) <= {frozenset(), X(v)} and Bi < 0,
                        f"{kind} but ode not affine-decaying in self")
                    if Bi < 0:
                        chk(kk == -Bi * u, f"{kind} rate stored {kk} != {-Bi}*u={-Bi*u}")
                        if sc(v) is not None:
                            chk(cc == (A0 / -Bi) * sc(v),
                                f"{kind} equilibrium stored {cc} != {(A0 / -Bi)}*scale")
                elif kind == "driven":
                    j = vs[args[0]]
                    chk(set(P.d) == {X(j)}, f"driven({j}) but ode '{expr[:40]}'")
                    cj = P.d.get(X(j), Fraction(0))
                    if sc(v) is not None and sc(j) is not None:
                        chk(cj * sc(v) * u == sc(j),
                            f"driven coupling: {cj}*scale[{v}]*u != scale[{j}] "
                            f"({cj}*{sc(v)}*{u} != {sc(j)})")
                elif kind == "chase":
                    j = vs[args[0]]; kk = Fraction(args[1])
                    chk(set(P.d) <= {X(j), X(v)}, f"chase but ode '{expr[:40]}'")
                    cj = P.d.get(X(j), Fraction(0))
                    chk(kk == -P.d.get(X(v), Fraction(0)) * u, "chase rate mismatch")
                    if sc(v) is not None and sc(j) is not None:
                        chk(cj * sc(v) * u == sc(j),
                            f"chase driver coupling: {cj}*{sc(v)}*{u} != {sc(j)}")
                elif kind == "riccati":
                    bs, as_ = Fraction(args[0]), Fraction(args[1])
                    chk(set(P.d) <= {frozenset(), X2(v)}, "riccati shape mismatch")
                    a2 = -P.d.get(X2(v), Fraction(0))
                    if sc(v) is not None:
                        chk(bs == A0 * sc(v) * u, f"riccati b stored {bs} != {A0}*scale*u")
                        chk(Fraction(as_, 10**6) == a2 * u / sc(v),
                            f"riccati a stored {as_} != {a2}*u*10^6/scale")
                elif kind == "pairSym":
                    j = vs[args[0]]; cc, hh = Fraction(args[1]), Fraction(args[2])
                    chk(set(P.d) <= {frozenset(), X(v), X(j)}, "pairSym shape mismatch")
                    chk(-Bi * u == 1, f"pairSym implicit unit rate: {-Bi}*u != 1")
                    if sc(v) is not None and sc(j) is not None:
                        chk(Fraction(hh, 1000) == P.d.get(X(j), Fraction(0)) * u * sc(v) / sc(j),
                            "pairSym coupling mismatch")
                        chk(cc == (A0 / -Bi) * sc(v), "pairSym equilibrium mismatch")
                elif kind == "drivenDamp":
                    j = vs[args[0]]
                    chk(P.d.get(X(j), Fraction(0)) != 0, f"drivenDamp: no {j} term")
                    cj = P.d.get(X(j), Fraction(0))
                    if sc(v) is not None and sc(j) is not None:
                        chk(cj * sc(v) * u == sc(j), "drivenDamp linear coupling mismatch")
                    # damper coefficients: stored an/ad * scale_d^2 == real coefficient of x_j*x_d^2 / cj
                    for (di, an, ad) in (im.get("dampers") or {}).get(ci, []):
                        d = vs[di]
                        m = frozenset({(j, 1), (d, 2)})
                        areal = -P.d.get(m, Fraction(0)) / cj
                        if sc(d) is not None:
                            chk(Fraction(an, ad) * sc(d) ** 2 == areal,
                                f"damper[{d}]: stored {an}/{ad}*scale^2 != {areal}")
            gb = bounds(bm.get("guard", ""))
            # gcoord guard band (settling family: guard on the gcoord var)
            gv = vs[im["gcoord"]]
            if gv in gb and gb[gv][0] is not None:
                if abs(gb[gv][0] * 1000 - im["glo"]) > 0.5:
                    msgs.append(f"{bm['name']}: glo {im['glo']} vs guard lo {gb[gv][0]}")
                ghi_stored = im["ghi"]
                if I.get("vtops") is not None:
                    # affine: ghi is a dummy; the guard top lives in vtops
                    ghi_stored = I["vtops"][qi] if qi < len(I["vtops"]) else None
                if gb[gv][1] is not None:
                    if ghi_stored is None or abs(gb[gv][1] * 1000 - ghi_stored) > 0.5:
                        msgs.append(f"{bm['name']}: top {ghi_stored} vs guard hi {gb[gv][1]}")
                elif I.get("vtops") is not None and ghi_stored is not None:
                    msgs.append(f"{bm['name']}: vtop {ghi_stored} but guard is topless")
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
        # terrain sbands vs the benchmark's s-guard bands (scaled)
        if I.get("sbands"):
            for qi, (bm, (sc_i, slo, shi)) in enumerate(zip(B["modes"], I["sbands"])):
                sv = vs[sc_i] if sc_i < len(vs) else None
                gb = bounds(bm.get("guard", ""))
                if sv is None or sv not in gb:
                    msgs.append(f"{bm['name']}: sband coord '{sv}' not guarded"); continue
                ssc = scale.get(sv, Fraction(1000))
                blo, bhi = gb[sv]
                if blo is None or Fraction(str(blo)) * ssc != slo:
                    msgs.append(f"{bm['name']}: sband slo {slo} vs guard lo {blo}")
                if (bhi is None) != (shi is None):
                    msgs.append(f"{bm['name']}: sband shi {shi} vs guard hi {bhi}")
                elif bhi is not None and Fraction(str(bhi)) * ssc != shi:
                    msgs.append(f"{bm['name']}: sband shi {shi} vs guard hi {bhi}")
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
