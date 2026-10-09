#!/usr/bin/env python3
"""Transparent Z3 timing proxy for relcert (RELCERT_Z3=<this file>; used by scripts/suite_v2_matrix.py --z3time). Forwards stdin to a real
`z3 -in`, and for every query (the block ending in `(check-sat)` + echo sentinel) records
the wall time from the moment the `(check-sat)` line is forwarded to the moment the
sentinel comes back, the verdict, and the query text. Appends one JSON line per query to
$Z3PROXY_LOG (if set). No change to what relcert sees."""
import sys, os, subprocess, time, json, threading
Z3 = os.environ.get("Z3PROXY_REAL", "/opt/homebrew/bin/z3")
log = os.environ.get("Z3PROXY_LOG")
p = subprocess.Popen([Z3] + sys.argv[1:], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=sys.stderr, bufsize=0)
pending = []          # queue of (t0, text)
lock = threading.Lock()
recs = []
def reader():
    verdict = None
    for line in iter(p.stdout.readline, b""):
        sys.stdout.buffer.write(line); sys.stdout.buffer.flush()
        t = line.decode().strip().replace('"', '')
        if t in ("sat", "unsat", "unknown"):
            verdict = t
        if t == "<<RCEND>>":
            t1 = time.time()
            with lock:
                t0, text = pending.pop(0) if pending else (t1, "")
            recs.append({"ms": round((t1 - t0) * 1000, 3), "verdict": verdict, "q": text})
            verdict = None
th = threading.Thread(target=reader, daemon=True); th.start()
buf = []
armed = False
for raw in iter(sys.stdin.buffer.readline, b""):
    line = raw.decode()
    if line.strip() == "(reset)":
        buf = []; armed = False
    buf.append(line)
    if line.strip() == "(check-sat)" and not armed:
        armed = True
        with lock:
            pending.append((time.time(), "".join(buf)))
    p.stdin.write(raw); p.stdin.flush()
    if line.strip() == "(exit)":
        break
try:
    p.stdin.close()
except Exception:
    pass
p.wait(); th.join(timeout=5)
if log:
    with open(log, "a") as f:
        for r in recs:
            f.write(json.dumps(r) + "\n")
