#!/usr/bin/env python3
"""The stutter tests (docs/STUTTER.md): the opt-in `[problem] stutter = true` (stretch 0, the right
waits while the left runs a joint segment).

Every variant file is written to a temporary directory, never to the suite. Runs the CLI with
RELCERT_IMPLIED_CUT=1 (the suite's setting) and prints one line per case and a summary.

  positive   benchmarks/stutter_demo/salt_tank_stutter at band c in {0, 0.5, 1, 2, 2.99, 3}:
             CERTIFIED with the key; band 0 without the key DECLINED; band -0.01 DECLINED
             (the rows admit no start)
  guard      the demo without the key at lambda_min = 0: DECLINED (0 is never a candidate
             without the key; before the key this certified unbacked)
  lam00      the demo with lambda in [0, 0] (stretch 0 only): DECLINED (the attacked On moves,
             the frozen genuine tank cannot follow)
  moving     the demo with the attacked Off drifting (xp' = 0.1): DECLINED
  negatives  every benchmarks/refute_mutants/*/input.txt and benchmarks/negative/*/input.txt
             with `stutter = true` added: DECLINED

Usage: python3 scripts/stutter_tests.py [--relcert BIN] [--skip-negatives]
"""
import argparse, glob, os, re, subprocess, sys, tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
DEMO = os.path.join(ROOT, "benchmarks", "stutter_demo", "salt_tank_stutter", "input.txt")
VERD = re.compile(r": (CERTIFIED|DECLINED|ERROR)")


def verdict(relcert, path):
    env = dict(os.environ, RELCERT_IMPLIED_CUT="1")
    for k in ("RELCERT_SYNC", "RELCERT_NO_CUT", "RELCERT_NO_IMPLIED_CUT", "RELCERT_NO_PAIR_STRETCH",
              "RELCERT_NO_CHOICE", "RELCERT_NO_PRUNE", "RELCERT_NO_REPO"):
        env.pop(k, None)
    try:
        r = subprocess.run([relcert, path], capture_output=True, text=True, env=env, timeout=600)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    m = VERD.search(r.stdout)
    return m.group(1) if m else "NONE"


def with_key(text, on=True):
    text = re.sub(r"(?m)^stutter\s*=.*\n", "", text)
    return text.replace("[problem]\n", "[problem]\nstutter = true\n", 1) if on else text


def band(text, c):
    return text.replace("+ 0.0 and", f"+ {c} and")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--relcert", default=os.path.join(ROOT, ".lake", "build", "bin", "relcert"))
    ap.add_argument("--skip-negatives", action="store_true")
    a = ap.parse_args()
    demo = open(DEMO).read()
    cases = []
    for c in ["0.0", "0.5", "1.0", "2.0", "2.99", "3.0"]:
        cases.append((f"positive band {c} (key)", band(demo, c), "CERTIFIED"))
    cases.append(("positive band 0.0 (no key)", with_key(demo, False), "DECLINED"))
    cases.append(("positive band 3.0 (no key)", band(with_key(demo, False), "3.0"), "CERTIFIED"))
    cases.append(("positive band 2.99 (no key)", band(with_key(demo, False), "2.99"), "DECLINED"))
    cases.append(("positive band -0.01 (key)", band(demo, "-0.01"), "DECLINED"))
    guard = with_key(demo, False).replace("lambda_min = 1.0", "lambda_min = 0.0")
    cases.append(("guard band 0.0, lambda in [0,1] (no key)", guard, "DECLINED"))
    lam00 = demo.replace("lambda_min = 1.0", "lambda_min = 0.0").replace("lambda_max = 1.0", "lambda_max = 0.0")
    cases.append(("lam00 lambda in [0,0] (key)", lam00, "DECLINED"))
    moving = demo.replace("[Lsys.mode.Off]\node = xp' = smt2:0.0;", "[Lsys.mode.Off]\node = xp' = smt2:0.1;")
    assert moving != demo
    cases.append(("moving left Off xp' = 0.1 (key)", moving, "DECLINED"))
    if not a.skip_negatives:
        for d in ("refute_mutants", "negative"):
            for p in sorted(glob.glob(os.path.join(ROOT, "benchmarks", d, "*", "input.txt"))):
                cases.append((f"{d}/{os.path.basename(os.path.dirname(p))} (key)",
                              with_key(open(p).read()), "DECLINED"))
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        for i, (name, text, want) in enumerate(cases):
            p = os.path.join(tmp, f"case{i}.txt")
            open(p, "w").write(text)
            got = verdict(a.relcert, p)
            ok = got == want
            bad += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {name}: {got} (expected {want})", flush=True)
    print(f"stutter tests: {len(cases) - bad}/{len(cases)} as expected")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
