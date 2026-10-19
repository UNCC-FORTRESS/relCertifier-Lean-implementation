#!/usr/bin/env python3
"""Invariant mutation study (branch `mutation`): how tight are the hand-written invariants?

For every benchmark, every distinct inequality atom of the relational invariant that has a
nonzero constant slack c is tightened by FRAC * |c| (`a <= b` -> `a <= b - d`, `a >= b` ->
`a >= b + d`) in every row it occurs in, one atom at a time, and relcert is rerun.
A first run rewrites all rows to `smt2:` form unmutated and must stay CERTIFIED (sanity:
the rewrite changes nothing). Atoms with zero constant slack (e.g. v_l <= v_r) are skipped.

A DECLINED mutant means the tightened invariant is false or beyond the certifier; a
CERTIFIED one means the original had slack. The study profiles tightness, it does not
prove falsity.

Usage: scripts/mutation.py [--frac 0.1] [--jobs 8] [--timeout 120] [--json OUT]
"""
import argparse, glob, json, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import inv_smt as I

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
RELCERT = os.path.join(ROOT, ".lake", "build", "bin", "relcert")
VERDICT = re.compile(r"^(\S+): (CERTIFIED|DECLINED|ERROR)", re.M)


def run(text, timeout):
    d = tempfile.mkdtemp()
    p = os.path.join(d, "input.txt")
    open(p, "w").write(text)
    env = dict(os.environ, RELCERT_IMPLIED_CUT="1")
    try:
        r = subprocess.run([RELCERT, p], capture_output=True, text=True, env=env, timeout=timeout, cwd=ROOT)
        m = VERDICT.search(r.stdout + r.stderr)
        return m.group(2) if m else "ERROR"
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


def rewrite(text, rows, repl):
    lines = text.split("\n")
    for ln, name, atoms in rows:
        atoms = [repl.get(I.show(a), a) for a in atoms]
        body = atoms[0] if len(atoms) == 1 else ["and"] + atoms
        lines[ln] = f"{name} = smt2:{I.show(body)}"
    return "\n".join(lines)


def study(path, frac, timeout, pool):
    name = os.path.basename(os.path.dirname(path))
    text = open(path).read()
    b = I.parse_bench(text)
    rows = [(ln, k, I.atoms_of(v, "", [])) for ln, k, v in b["rows"]]
    distinct = {}
    for _, _, atoms in rows:
        for a in atoms:
            distinct.setdefault(I.show(a), a)
    jobs = {"__sanity__": pool.submit(run, rewrite(text, rows, {}), timeout)}
    skipped = []
    for key, a in distinct.items():
        t = I.tighten(a, frac)
        if t is None:
            skipped.append(key); continue
        jobs[key] = pool.submit(run, rewrite(text, rows, {key: t}), timeout)
    res = {k: f.result() for k, f in jobs.items()}
    return name, res, skipped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--frac", default="0.1")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--only")
    ap.add_argument("--json")
    a = ap.parse_args()
    paths = sorted(glob.glob(os.path.join(ROOT, "benchmarks/suite_v2/*/input.txt")))
    if a.only:
        keep = set(a.only.split(","))
        paths = [p for p in paths if os.path.basename(os.path.dirname(p)) in keep]
    out = {}
    tot = {"mutants": 0, "declined": 0, "certified": 0, "other": 0, "skipped": 0, "sanity_fail": []}
    with ThreadPoolExecutor(a.jobs) as pool:
        for p in paths:
            name, res, skipped = study(p, a.frac, a.timeout, pool)
            out[name] = {"results": res, "skipped": skipped}
            muts = {k: v for k, v in res.items() if k != "__sanity__"}
            dec = sum(v == "DECLINED" for v in muts.values())
            cer = sum(v == "CERTIFIED" for v in muts.values())
            oth = len(muts) - dec - cer
            tot["mutants"] += len(muts); tot["declined"] += dec; tot["certified"] += cer
            tot["other"] += oth; tot["skipped"] += len(skipped)
            if res["__sanity__"] != "CERTIFIED": tot["sanity_fail"].append(name)
            print(f"{name}: sanity={res['__sanity__']} mutants={len(muts)} declined={dec} "
                  f"certified={cer} other={oth} skipped={len(skipped)}", flush=True)
    print("TOTAL", json.dumps(tot))
    if a.json:
        json.dump({"frac": a.frac, "total": tot, "per_benchmark": out}, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
