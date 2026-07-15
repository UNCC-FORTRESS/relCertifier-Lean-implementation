#!/usr/bin/env python3
"""Suite guideline audit for benchmarks/suite_uniform.

Checks, per benchmark:
  (U) mode-uniform evolve within each side (the UniformEvol design: one physical
      envelope per side across all modes);
  (G) per-side guard disjointness (pairwise, on the parsed guard box);
and, per declared ladder pair (rung_i.L == rung_{i+1}.R), shared-coordinate model
equality: per-variable ode, per-variable evolve atoms, guard text, next list.
R-side padding coordinates (off-H slack lifts) are excluded by construction: the
comparison basis is the LOWER rung's state_vars.

Certification (1) and provable-H (2) are dynamic: `lake exe relcert .../input.txt`
and `scripts/h_audit.py`. shield_unreachable is the documented negative control
(overlapping Cruise/Continue guards, certifier-inconclusive by design).
"""
import re, os, sys

ROOT = os.path.join(os.path.dirname(__file__), "..", "benchmarks", "suite_uniform")

LADDER_PAIRS = [
    ("refinement_ladder_rover_rung1_2to3", "refinement_ladder_rover_rung2_3to6"),
    ("refinement_ladder_rover_rung2_3to6", "refinement_ladder_rover_rung3_6to8"),
    ("refinement_ladder_rover_rung3_6to8", "refinement_ladder_rover_rung4_8to12"),
    ("endurance_orderlift_1to2", "endurance_orderlift_2to3"),
    ("story1_attdist_rung_a_6to8", "story1_attdist_rung_b_12dof"),
    ("story2_lateral_rung_a_8dof", "story2_lateral_rung_b_12dof"),
    ("story3_rollover_ladder_rung_a", "story3_rollover_ladder_rung_b"),
]
NEGATIVE_CONTROLS = {"shield_unreachable"}

def section(path, side):
    out, cur = {}, None
    for line in open(path):
        ls = line.strip()
        if ls.startswith("#") or not ls:
            continue
        m = re.match(rf"\[{side}\.mode\.(\w+)\]", ls)
        if m:
            cur = m.group(1); out[cur] = {}; continue
        if re.match(r"\[.*\]", ls):
            cur = "_hdr" if re.match(rf"\[{side}\]", ls) else None
            if cur: out[cur] = {}
            continue
        if cur:
            for key in ("state_vars", "ode", "guard", "evolve", "next"):
                if ls.startswith(key):
                    out[cur][key] = re.sub(r"\s+", " ", ls.split("=", 1)[1].strip())
    return out

def ode_map(ode):
    d = {}
    for part in ode.split(";"):
        m = re.match(r"([\w]+)' = (.*)", part.strip())
        if m: d[m.group(1)] = m.group(2).strip()
    return d

def ev_map(ev):
    d = {}
    for a in ev.split(" and "):
        d.setdefault(a.split()[0], []).append(a.strip())
    return {k: tuple(sorted(v)) for k, v in d.items()}

def guard_box(g):
    iv = {}
    for c in g.split(" and "):
        m = re.match(r"([\w\[\]]+)\s*(>=|>|<=|<)\s*(-?[\d.]+)", c.strip())
        if not m: return None
        v, op, val = m.group(1), m.group(2), float(m.group(3))
        d = iv.setdefault(v, [-1e18, 1e18])
        if op in (">=", ">"): d[0] = max(d[0], val)
        else: d[1] = min(d[1], val)
    return iv

def main():
    fail = 0
    for bench in sorted(os.listdir(ROOT)):
        p = os.path.join(ROOT, bench, "input.txt")
        if not os.path.exists(p): continue
        for side in ("Lsys", "Rsys"):
            S = section(p, side)
            evs = {frozenset(d.get("evolve", "").split(" and "))
                   for m, d in S.items() if m != "_hdr"}
            if len(evs) > 1:
                print(f"VIOL uniform-evol {bench}.{side}"); fail += 1
            boxes = {m: guard_box(d.get("guard", ""))
                     for m, d in S.items() if m != "_hdr"}
            ms = [m for m in boxes if boxes[m] is not None]
            for i in range(len(ms)):
                for j in range(i + 1, len(ms)):
                    g1, g2 = boxes[ms[i]], boxes[ms[j]]
                    shared = set(g1) & set(g2)
                    if shared and all(min(g1[v][1], g2[v][1]) > max(g1[v][0], g2[v][0]) + 1e-12
                                      for v in shared):
                        tag = "note(negative-control)" if bench in NEGATIVE_CONTROLS else "VIOL"
                        print(f"{tag} guard-overlap {bench}.{side}: {ms[i]}/{ms[j]}")
                        if bench not in NEGATIVE_CONTROLS: fail += 1
    for a, b in LADDER_PAIRS:
        A = section(os.path.join(ROOT, a, "input.txt"), "Lsys")
        B = section(os.path.join(ROOT, b, "input.txt"), "Rsys")
        shared = [v.strip() for v in A["_hdr"]["state_vars"].strip("[]").split(",")]
        diffs = []
        if not set(shared) <= set(v.strip() for v in B["_hdr"]["state_vars"].strip("[]").split(",")):
            diffs.append("vars")
        for m in sorted((set(A) & set(B)) - {"_hdr"}):
            oa, ob = ode_map(A[m]["ode"]), ode_map(B[m]["ode"])
            ea, eb = ev_map(A[m]["evolve"]), ev_map(B[m]["evolve"])
            for v in shared:
                if oa.get(v) != ob.get(v): diffs.append(f"{m}.ode[{v}]")
                if ea.get(v) != eb.get(v): diffs.append(f"{m}.evolve[{v}]")
            if A[m]["guard"] != B[m]["guard"]: diffs.append(f"{m}.guard")
            if A[m]["next"] != B[m]["next"]: diffs.append(f"{m}.next")
        if diffs:
            print(f"VIOL ladder {a}.L != {b}.R: {', '.join(diffs[:6])}"); fail += 1
        else:
            print(f"ok   ladder {a}.L == {b}.R (shared {len(shared)})")
    print("FAILURES:", fail)
    sys.exit(1 if fail else 0)

if __name__ == "__main__":
    main()
