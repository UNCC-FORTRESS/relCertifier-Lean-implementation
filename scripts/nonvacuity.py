#!/usr/bin/env python3
"""Non-vacuity check (branch `mutation`): every left mode of every benchmark has a
satisfiable start, i.e. Z3 returns `sat` for

    guard_L(mL) and evolve_L(mL) and row(mL) and OR_{mR} (guard_R(mR) and evolve_R(mR)).

If this were unsat for some mL, its obligation would hold vacuously.
Usage: scripts/nonvacuity.py [--z3 BIN] [--json OUT]
"""
import argparse, glob, json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import inv_smt as I

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))


def conj(atoms):
    return atoms[0] if len(atoms) == 1 else ["and"] + atoms


def vars_in(e, acc):
    if isinstance(e, list):
        for x in e[1:]: vars_in(x, acc)
    elif re.match(r"^[LR]_", e):
        acc.add(e)
    return acc


def check(path, z3):
    b = I.parse_bench(open(path).read())
    rows = {k: v for _, k, v in b["rows"]}
    rside = []
    for m, d in b["R"]["modes"].items():
        rside.append(conj(I.atoms_of(d["guard"], "R", b["R"]["vars"]) + I.atoms_of(d["evolve"], "R", b["R"]["vars"])))
    anyR = ["or"] + rside if len(rside) > 1 else rside[0]
    res = {}
    for m, d in b["L"]["modes"].items():
        if m not in rows:
            res[m] = "norow"; continue
        f = conj(I.atoms_of(d["guard"], "L", b["L"]["vars"]) + I.atoms_of(d["evolve"], "L", b["L"]["vars"])
                 + I.atoms_of(rows[m], "", []) + [anyR])
        vs = sorted(vars_in(f, set()))
        q = "".join(f"(declare-const {v} Real)\n" for v in vs) + f"(assert {I.show(f)})\n(check-sat)\n"
        r = subprocess.run([z3, "-in", "-T:30"], input=q, capture_output=True, text=True)
        res[m] = (r.stdout.strip().splitlines() or ["error"])[0]
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--z3", default="/opt/homebrew/bin/z3")
    ap.add_argument("--json")
    a = ap.parse_args()
    allres, bad = {}, []
    for p in sorted(glob.glob(os.path.join(ROOT, "benchmarks/suite_v2/*/input.txt"))):
        name = os.path.basename(os.path.dirname(p))
        try:
            r = check(p, a.z3)
        except Exception as e:
            r = {"__error__": repr(e)}
        allres[name] = r
        nonsat = {m: v for m, v in r.items() if v != "sat"}
        print(f"{name}: {len(r)} left modes, " + ("all sat" if not nonsat else f"NOT SAT {nonsat}"))
        if nonsat: bad.append(name)
    print(f"benchmarks={len(allres)} left-modes={sum(len(r) for r in allres.values())} with-non-sat={len(bad)}")
    if a.json:
        json.dump(allres, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
