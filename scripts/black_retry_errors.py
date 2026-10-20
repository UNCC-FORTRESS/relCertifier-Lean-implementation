#!/usr/bin/env python3
"""Retry the mutants whose relcert verdict was not CERTIFIED/DECLINED (load-related
errors/timeouts in the parallel run), at low parallelism; rewrites the JSONL in place."""
import json, os, sys
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import black_mutation as B
B.RUN_CWD = os.environ["RELCERT_CWD"]
RB, SUITE, PATH = os.environ["RELCERT_BIN"], os.environ["SUITE"], sys.argv[1]
recs = [json.loads(l) for l in open(PATH)]
with ThreadPoolExecutor(int(os.environ.get("JOBS", "2"))) as pool:
    for d in recs:
        bad = [i for i, m in enumerate(d.get("mutants", [])) if m["relcert"] not in ("CERTIFIED", "DECLINED")]
        if not bad:
            continue
        text, b, M, rows = B.load(os.path.join(SUITE, d["bench"], "input.txt"))
        ms = B.mutants(rows, b["L"]["vars"], b["R"]["vars"])
        futs = {i: pool.submit(B.run_relcert, RB, B.write(text, B.apply(rows, ms[i][2], ms[i][3])), 300) for i in bad}
        for i, f in futs.items():
            assert d["mutants"][i]["mutant"] == ms[i][1]
            d["mutants"][i]["relcert_first"] = d["mutants"][i]["relcert"]
            d["mutants"][i]["relcert"] = f.result()
        print(d["bench"], [d["mutants"][i]["relcert"] for i in bad], flush=True)
with open(PATH, "w") as fh:
    for d in recs:
        fh.write(json.dumps(d) + "\n")
