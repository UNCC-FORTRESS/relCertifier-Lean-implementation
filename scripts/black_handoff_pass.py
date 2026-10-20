#!/usr/bin/env python3
"""Post-hoc handoff pass: rerun `relcert --handoff` on every mutant of a black_mutation.py
run (same deterministic mutant order) and record it, so a cover-only CERTIFIED can be
combined with Theorem 3's handoff premise. Usage: black_handoff_pass.py IN.jsonl OUT.jsonl"""
import json, os, sys
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import black_mutation as B

RELCERT = os.environ.get("RELCERT_BIN")
SUITE = os.environ.get("SUITE")
src, dst = sys.argv[1], sys.argv[2]
with ThreadPoolExecutor(8) as pool, open(dst, "w") as out:
    for line in open(src):
        d = json.loads(line)
        text, b, M, rows = B.load(os.path.join(SUITE, d["bench"], "input.txt"))
        ms = B.mutants(rows, b["L"]["vars"], b["R"]["vars"])
        assert len(ms) == len(d["mutants"]), d["bench"]
        futs = [pool.submit(B.run_handoff, RELCERT, B.write(text, B.apply(rows, key, new)))
                for _, _, key, new in ms]
        hs = [f.result() for f in futs]
        for m, (op, label, _, _), h in zip(d["mutants"], ms, hs):
            assert m["mutant"] == label
            m["handoff"] = h
        d["sanity_handoff"] = B.run_handoff(RELCERT, B.write(text, rows))
        out.write(json.dumps(d) + "\n"); out.flush()
        print(d["bench"], "handoff fail:", sum(h != "PASS" for h in hs), "of", len(hs), flush=True)
