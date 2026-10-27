#!/usr/bin/env python3
"""The refutation experiment (branch `refutation`).

Per Black-Okun-Yesha mutant of the suite (the finder's records, `docs/refute/witnesses.jsonl`):

* relcert's verdict on the mutant file (this worktree's binary, `RELCERT_IMPLIED_CUT=1` as the
  suite runs; the default verdict includes the handoff check);
* KERNEL-REFUTED iff its instance `RelCertifier/InstancesV2/Refute/<Camel>.lean` builds (listed in
  the aggregator, `lake build RelCertifier.InstancesV2.Refute` green) AND the runner
  `relcert-refute-verdicts` discharges every one of its query groups (`UNSAT <id>`).

Tabulates certified / kernel-refuted / open per operator and per kind, checks that no
kernel-refuted mutant is certified, and writes `docs/refute/results.json`.

Usage: scripts/refute_experiment.py [--jobs 6] [--timeout 600] [--runner-log FILE]
"""
import argparse, json, os, re, subprocess
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
RELCERT = os.path.join(ROOT, ".lake/build/bin/relcert")
VERDICT = re.compile(r"^(\S+): (CERTIFIED|DECLINED|ERROR)", re.M)


def camel(s):
    return "".join(w.capitalize() for w in s.split("_"))


def relcert(path, timeout):
    env = dict(os.environ, RELCERT_IMPLIED_CUT="1")
    try:
        r = subprocess.run([RELCERT, path], capture_output=True, text=True, env=env,
                           timeout=timeout, cwd=ROOT)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    m = VERDICT.search(r.stdout + r.stderr)
    return m.group(2) if m else "ERROR"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--witnesses", default=os.path.join(ROOT, "docs/refute/witnesses.jsonl"))
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--timeout", type=int, default=600)  # above relcert's 300 s default budget
    ap.add_argument("--runner-log", default=os.path.join(ROOT, "docs/refute/runner.log"))
    ap.add_argument("--verdicts", default=os.path.join(ROOT, "docs/refute/relcert.json"))
    ap.add_argument("--out", default=os.path.join(ROOT, "docs/refute/results.json"))
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(a.witnesses)]
    # relcert verdicts (cached)
    cache = json.load(open(a.verdicts)) if os.path.exists(a.verdicts) else {}
    todo = [r for r in recs if f"{r['bench']}_m{r['idx']:03d}" not in cache]
    with ThreadPoolExecutor(a.jobs) as pool:
        futs = {f"{r['bench']}_m{r['idx']:03d}": pool.submit(relcert, r["file"], a.timeout)
                for r in todo}
        for k, f in futs.items():
            cache[k] = f.result()
    json.dump(cache, open(a.verdicts, "w"), indent=1, sort_keys=True)
    # instances in the aggregator, runner verdicts
    agg = open(os.path.join(ROOT, "RelCertifier/InstancesV2/Refute.lean")).read()
    built = set(re.findall(r"import RelCertifier\.InstancesV2\.Refute\.(\w+)", agg))
    runner = open(a.runner_log).read()
    unsat = set(re.findall(r"^\s*UNSAT (\S+)", runner, re.M))
    green = "[coverage] refute:" in runner and "discharged but owes" not in runner
    rows = []
    for r in recs:
        mid = f"{r['bench']}_m{r['idx']:03d}"
        w = r["witness"]
        kref = bool(w) and camel(mid) in built and mid in unsat and green
        rows.append({"id": mid, "bench": r["bench"], "op": r["op"], "mutant": r["mutant"],
                     "kind": w["kind"] if w else None, "relcert": cache[mid],
                     "kernel_refuted": kref, "witness_found": bool(w)})
    json.dump(rows, open(a.out, "w"), indent=1)
    per = defaultdict(Counter)
    for x in rows:
        st = "kernel-refuted" if x["kernel_refuted"] else ("certified" if x["relcert"] == "CERTIFIED"
                                                            else "open")
        per[x["op"]][st] += 1
        per["all"][st] += 1
    bad = [x["id"] for x in rows if x["kernel_refuted"] and x["relcert"] == "CERTIFIED"]
    kinds = Counter(x["kind"] for x in rows if x["kernel_refuted"])
    print("operator        certified  kernel-refuted  open  total")
    for op in ["RRO/SNO", "MCO", "ORO", "all"]:
        c = per[op]
        print(f"{op:14s} {c['certified']:9d} {c['kernel-refuted']:15d} {c['open']:5d} {sum(c.values()):6d}")
    print("kernel-refuted by kind:", dict(kinds))
    print("kernel-refuted AND certified:", bad or "none")
    print("relcert verdicts:", dict(Counter(cache[x["id"]] for x in rows)))
    print("witness found but not kernel-refuted:",
          [x["id"] for x in rows if x["witness_found"] and not x["kernel_refuted"]] or "none")


if __name__ == "__main__":
    main()
