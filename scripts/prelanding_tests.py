#!/usr/bin/env python3
"""The pre-landing tests (docs/PRELANDING.md): the pre-landing certificate (a right-only node
needs its flow certificate only on the half-open region before the progress certificate's last
threshold; the witness right run stops at its first entry into the target), a run feature on
for every benchmark (docs/PRELANDING.md, "Status"). "Off" below is the ablation
RELCERT_NO_PRELANDING=1; "on" is the default run.

Every variant file is written to a temporary directory, never to the suite. Runs the CLI with
RELCERT_IMPLIED_CUT=1 (the suite's setting) and prints one line per case and a summary.

  engine     benchmarks/prelanding_demo/engine_cooling_prelanding (NAHS 2025 engine cooling, the
             genuine Cool guard closed to temp >= 100): band 0.3 CERTIFIED (the paper's distance),
             0.29 DECLINED; 0.3 off DECLINED; 0.3 on under RELCERT_NO_REPO
             DECLINED (the right-only node is genuine, letter R); the source's strict genuine
             Cool guard (temp > 100) DECLINED (no closed target: strict-guard targets are
             rejected)
  cause      the attack offset o in {0, 0.1, 0.5, 1} (attacked guards temp > 100 - o,
             temp <= 100 + o): band o CERTIFIED, band o - 0.01 DECLINED (o > 0); the tight band
             tracks the attack offset, and o = 0 is exact (band 0)
  adversarial synthetic (a frozen left, a right that climbs in Up and holds in Hold), with
             stretch 0 off (RELCERT_NO_STUTTER=1; with it on and the declared range widened to
             [0, 1] the right may wait and every claim below is true and CERTIFIED, listed as
             `stutter` cases; the default run on their declared [1, 1] never tries stretch 0,
             listed as `default` cases):
             fails-after: the row y_R <= 0 breaks only after the landing threshold y = 0
             (CERTIFIED on, DECLINED off);
             fails-before: the row y_R <= 0.5 against the landing threshold y = 1 breaks before
             the landing (DECLINED on; false for every right run that moves);
             strict-target: fails-after with the Hold guard opened to y > 0 (DECLINED: no
             closed target)
  strict     benchmarks/prelanding_demo/hold_reposition_strict (a row with a strict component that
             falls while the right repositions, and a non-strict one that breaks only past the
             landing): CERTIFIED on (the strict component on the CLOSED pre-landing
             region, route A), DECLINED off and under RELCERT_NO_REPO (both with stretch 0
             off; CERTIFIED by default, and off, because the right may wait);
             strict-equality: the synthetic file with the strict row y_R < 0, which reaches
             equality exactly at the landing y_R = 0: DECLINED (on the half-open region route B
             would pass vacuously, its boundary lying outside it; the closed region refuses it)
  mixed      benchmarks/progress_demo/stopline_friction_mixed (the right's braking nodes need a
             two-stage progress certificate, helper up then landing down; 2026-11-01): CERTIFIED;
             with the right's brake never applied (BRAKE b' = -b/0.3, the speed never falls)
             DECLINED
  negatives  every benchmarks/refute_mutants/*/input.txt and benchmarks/negative/*/input.txt
             (on): DECLINED
  key        a file that still carries the retired key `prelanding = true` is refused (ERROR,
             the unknown-key gate)

Every text edit is asserted to change the file (no case passes on an unedited file).

Usage: python3 scripts/prelanding_tests.py [--relcert BIN] [--skip-negatives]
"""
import argparse, glob, os, re, subprocess, sys, tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
DEMO = os.path.join(ROOT, "benchmarks", "prelanding_demo", "engine_cooling_prelanding", "input.txt")
STRICT = os.path.join(ROOT, "benchmarks", "prelanding_demo", "hold_reposition_strict", "input.txt")
MIXED = os.path.join(ROOT, "benchmarks", "progress_demo", "stopline_friction_mixed", "input.txt")
VERD = re.compile(r": (CERTIFIED|DECLINED|ERROR)")


def verdict(relcert, path, extra_env=None):
    env = dict(os.environ, RELCERT_IMPLIED_CUT="1")
    for k in ("RELCERT_SYNC", "RELCERT_NO_CUT", "RELCERT_NO_IMPLIED_CUT", "RELCERT_NO_PAIR_STRETCH",
              "RELCERT_NO_CHOICE", "RELCERT_NO_PRUNE", "RELCERT_NO_REPO", "RELCERT_NO_PROGRESS",
              "RELCERT_NO_STUTTER", "RELCERT_NO_PRELANDING"):
        env.pop(k, None)
    if extra_env:
        env.update(extra_env)
    try:
        r = subprocess.run([relcert, path], capture_output=True, text=True, env=env, timeout=600)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    m = VERD.search(r.stdout)
    return m.group(1) if m else "NONE"


def sub(text, old, new, count=-1):
    """`text.replace(old, new)`, asserting that the edit applies (no silent pass)."""
    assert old in text, f"edit does not apply: {old!r}"
    return text.replace(old, new) if count < 0 else text.replace(old, new, count)


OFF = {"RELCERT_NO_PRELANDING": "1"}
# The synthetic files and the strict demo have a HOLDING left (y' = 0): with stretch 0 a candidate
# the right may wait through every left cycle, so every one of their claims is TRUE under
# Theorem 3 (a zero-duration right cycle is a run) and CERTIFIES by stutter. They declare the range
# [1, 1], so (stretch 0 only for a declared range including 0) the default run does
# not try stretch 0; their pre-landing cases still run with RELCERT_NO_STUTTER=1 as well, which
# isolates the pre-landing certificate whatever the range; the stutter cases widen it to [0, 1].
NOSTUT = {"RELCERT_NO_STUTTER": "1"}
OFF_NOSTUT = {"RELCERT_NO_PRELANDING": "1", "RELCERT_NO_STUTTER": "1"}


def band(text, c):
    return sub(text, "+ 0.3 and temp[r] <= temp[l] + 0.3", f"+ {c} and temp[r] <= temp[l] + {c}")


def offset(text, o):
    text = sub(text, "guard = temp > 99.7", f"guard = temp > {100 - o}")
    return sub(text, "guard = temp <= 100.3", f"guard = temp <= {100 + o}")


SYN = """[problem]
name = prelanding_synthetic
max_depth = 8
lambda_min = 1.0
lambda_max = 1.0
bound_T = 40.0

[Lsys]
state_vars = [y]
epsilon = 1.0

[Lsys.mode.Hold]
ode = y' = smt2:0.0;
guard = y >= -10.0
evolve = y >= -10.0
next = [Hold]

[Rsys]
state_vars = [y]
epsilon = 1.0

[Rsys.mode.Up]
ode = y' = smt2:1.0;
guard = y <= THETA
evolve = y >= -10.0
next = [Up, Hold]

[Rsys.mode.Hold]
ode = y' = smt2:0.0;
guard = HOLDGUARD
evolve = y >= -10.0
next = [Hold]

[relational_invariant]
Hold = ROW
"""


def synthetic(theta, holdguard, row):
    t = sub(SYN, "THETA", theta)
    t = sub(t, "HOLDGUARD", holdguard)
    return sub(t, "ROW", row)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--relcert", default=os.path.join(ROOT, ".lake", "build", "bin", "relcert"))
    ap.add_argument("--skip-negatives", action="store_true")
    a = ap.parse_args()
    demo = open(DEMO).read()
    for f in (DEMO, STRICT):
        assert not re.search(r"(?m)^prelanding\s*=", open(f).read()), f"{f} carries the retired key"
    cases = []   # (name, text, expected, extra_env)
    cases.append(("engine band 0.3", demo, "CERTIFIED", None))
    cases.append(("engine band 0.29", band(demo, 0.29), "DECLINED", None))
    cases.append(("engine band 0.31", band(demo, 0.31), "CERTIFIED", None))
    cases.append(("engine band 0.3 off", demo, "DECLINED", OFF))
    cases.append(("engine band 0.3 RELCERT_NO_REPO", demo, "DECLINED", {"RELCERT_NO_REPO": "1"}))
    cases.append(("engine source strict genuine Cool (temp > 100)",
                  sub(demo, "guard = temp >= 100.0", "guard = temp > 100.0"), "DECLINED", None))
    for o in (0, 0.1, 0.5, 1):
        t = offset(demo, o) if o != 0.3 else demo
        cases.append((f"cause offset {o} band {o}", band(t, o), "CERTIFIED", None))
        if o > 0:
            cases.append((f"cause offset {o} band {round(o - 0.01, 2)}", band(t, round(o - 0.01, 2)),
                          "DECLINED", None))
    after = synthetic("0.0", "y >= 0.0", "y[r] <= 0.0 and y[l] <= y[l]")
    before = synthetic("1.0", "y >= 1.0", "y[r] <= 0.5 and y[l] <= y[l]")
    starget = synthetic("0.0", "y > 0.0", "y[r] <= 0.0 and y[l] <= y[l]")
    sequal = synthetic("0.0", "y >= 0.0", "y[r] < 0.0 and y[l] <= y[l]")
    strict = open(STRICT).read()
    cases.append(("adversarial fails-after (row breaks only past the threshold), no stutter", after,
                  "CERTIFIED", NOSTUT))
    cases.append(("adversarial fails-after off, no stutter", after, "DECLINED", OFF_NOSTUT))
    cases.append(("adversarial fails-before (row y_R <= 0.5, threshold 1), no stutter", before,
                  "DECLINED", NOSTUT))
    cases.append(("adversarial strict-target (Hold guard y > 0), no stutter", starget,
                  "DECLINED", NOSTUT))
    cases.append(("strict demo", strict, "CERTIFIED", None))
    cases.append(("strict demo, no stutter", strict, "CERTIFIED", NOSTUT))
    cases.append(("strict demo off, no stutter", strict, "DECLINED", OFF_NOSTUT))
    cases.append(("strict demo RELCERT_NO_REPO, no stutter", strict, "DECLINED",
                  {"RELCERT_NO_REPO": "1", "RELCERT_NO_STUTTER": "1"}))
    cases.append(("adversarial strict-equality (row y_R < 0 reaches 0 at the landing), no stutter",
                  sequal, "DECLINED", NOSTUT))
    # the default run on the declared range [1, 1] (stretch 0 is a candidate only when
    # the declared range includes 0): the verdicts of the runs without stretch 0
    cases.append(("default fails-after (range [1,1])", after, "CERTIFIED", None))
    cases.append(("default fails-after off (range [1,1])", after, "DECLINED", OFF))
    cases.append(("default fails-before (range [1,1])", before, "DECLINED", None))
    cases.append(("default strict-target (range [1,1])", starget, "DECLINED", None))
    cases.append(("default strict-equality (range [1,1])", sequal, "DECLINED", None))
    cases.append(("default strict demo off (range [1,1])", strict, "DECLINED", OFF))
    mixed = open(MIXED).read()
    cases.append(("mixed demo (two stages, helper up then landing down)", mixed, "CERTIFIED", None))
    cases.append(("mixed demo, the right brake never applied (BRAKE b' = -b/0.3)",
                  sub(mixed, "b' = smt2:(* (/ 1.0 0.3) (- 3.0 b));", "b' = smt2:(* (/ 1.0 0.3) (- 0.0 b));"),
                  "DECLINED", None))
    # stretch 0 on and the declared range [0, 1]: the holding left lets the right wait, every
    # claim is true
    lam0 = lambda t: sub(t, "lambda_min = 1.0", "lambda_min = 0.0")
    for nm, t in (("fails-after", after), ("fails-before", before), ("strict-target", starget),
                  ("strict-equality", sequal)):
        cases.append((f"stutter: {nm}, range [0,1] (the right waits; true claim)", lam0(t),
                      "CERTIFIED", None))
    cases.append(("stutter: strict demo off, range [0,1] (the right waits; true claim)", lam0(strict),
                  "CERTIFIED", OFF))
    cases.append(("key: the retired key prelanding = true is refused",
                  sub(demo, "[problem]\n", "[problem]\nprelanding = true\n", 1), "ERROR", None))
    if not a.skip_negatives:
        negs = sorted(glob.glob(os.path.join(ROOT, "benchmarks", "refute_mutants", "*", "input.txt")) +
                      glob.glob(os.path.join(ROOT, "benchmarks", "negative", "*", "input.txt")))
        for f in negs:
            name = os.path.basename(os.path.dirname(f))
            cases.append((f"negative {name} (on)", open(f).read(), "DECLINED", None))
    ok = 0
    with tempfile.TemporaryDirectory() as td:
        for i, (name, text, exp, env) in enumerate(cases):
            p = os.path.join(td, f"case{i}.txt")
            open(p, "w").write(text)
            v = verdict(a.relcert, p, env)
            good = v == exp
            ok += good
            print(f"{'ok  ' if good else 'FAIL'} {name}: {v} (expected {exp})", flush=True)
    print(f"prelanding tests: {ok}/{len(cases)} as expected")
    sys.exit(0 if ok == len(cases) else 1)


if __name__ == "__main__":
    main()
