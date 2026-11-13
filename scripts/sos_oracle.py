#!/usr/bin/env python3
"""The SOS oracle as the tool calls it (`RELCERT_SOS_SECS`, `Trusted/Sos.lean`, `docs/SOS-ORACLE.md`):
prove numerically (`sos_prove.py`), then check EXACTLY (`sos_check.py`); the answer is `unsat` only
when the exact checker says VERIFIED. One line on stdout:

    SOS unsat <checker stats>              the certificate verified exactly
    SOS rejected <checker reason>          a certificate was found but the exact check failed
    SOS unknown <prover stats>             no certificate within the budget / basis cap / solver failure

Usage: sos_oracle.py QUERY.smt2 BUDGET_SECONDS [CERT.json]   (the certificate is kept when a path is given,
       or when RELCERT_SOS_CERT_DIR is set: <dir>/<basename of QUERY>.cert.json)
Exit 0 always (the tool treats any other exit as `unknown`).
"""
import os, sys, json, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def main(argv):
    if len(argv) < 3:
        sys.stderr.write(__doc__); return 2
    qpath = argv[1]; budget = float(argv[2]); cpath = argv[3] if len(argv) > 3 else None
    if cpath is None and os.environ.get("RELCERT_SOS_CERT_DIR"):
        os.makedirs(os.environ["RELCERT_SOS_CERT_DIR"], exist_ok=True)
        cpath = os.path.join(os.environ["RELCERT_SOS_CERT_DIR"], os.path.basename(qpath) + ".cert.json")
    t0 = time.time()
    from sos_prove import prove, fmt, Budget
    from sos_check import check
    def alarm(signum, frame): raise Budget()
    signal.signal(signal.SIGALRM, alarm); signal.alarm(int(budget) + 10)
    query = open(qpath).read()
    maxbasis = int(os.environ.get("RELCERT_SOS_MAXBASIS", "600")); deg = int(os.environ.get("RELCERT_SOS_DEG", "0"))
    try:
        status, cert, stats = prove(query, budget, maxbasis, deg)
    except Budget:
        print("SOS unknown note=budget"); return 0
    except Exception as ex:
        print(f"SOS unknown note=error:{type(ex).__name__}:{str(ex)[:80]}"); return 0
    if cert is None:
        print(f"SOS unknown {fmt(stats)}"); return 0
    if cpath:
        json.dump(cert, open(cpath, "w"))
    try:
        signal.alarm(max(int(budget), 30) + 10)
        line = check(query, cert)
    except Budget:
        print(f"SOS unknown note=checker budget {fmt(stats)}"); return 0
    except Exception as ex:
        print(f"SOS rejected checker error: {type(ex).__name__}: {str(ex)[:100]}"); return 0
    if line.startswith("VERIFIED"):
        print(f"SOS unsat {line[len('VERIFIED '):]} prover: {fmt(stats)} total={time.time() - t0:.1f}")
    else:
        print(f"SOS rejected {line[len('REJECTED '):]} prover: {fmt(stats)}")
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))
