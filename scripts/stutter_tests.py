#!/usr/bin/env python3
"""The stutter tests (docs/STUTTER.md): stretch 0 (the right waits while the left runs a joint
segment), on for every benchmark since 2026-10-31 (docs/BATCH12-2026-10-31.md; until then the
opt-in key `[problem] stutter = true`) whose declared stretch range includes 0 (lambda_min = 0;
batch 13, docs/BATCH13-2026-10-31.md). "Off" below is the ablation RELCERT_NO_STUTTER=1 (the
key-off cases of the opt-in era); "on" is the default run.

Every variant file is written to a temporary directory, never to the suite. Runs the CLI with
RELCERT_IMPLIED_CUT=1 (the suite's setting) and prints one line per case and a summary.

  positive   benchmarks/stutter_demo/salt_tank_stutter at band c in {0, 0.5, 1, 2, 2.99, 3}:
             CERTIFIED (on); band 0 off DECLINED; band -0.01 DECLINED
             (the rows admit no start)
  guard      the demo (lambda_min = 0) off: DECLINED (0 is never a candidate
             off; before the opt-in key this certified unbacked)
  range      (batch 13, docs/BATCH13-2026-10-31.md) stretch 0 is a candidate only when the
             declared range includes 0: the demo at lambda in [1, 1] or [0.5, 1], on, band 0:
             DECLINED; band 3 at [1, 1], on: CERTIFIED (lock step)
  lam00      the demo with lambda in [0, 0] (stretch 0 only): DECLINED (the attacked On moves,
             the frozen genuine tank cannot follow)
  moving     the demo with the attacked Off drifting (xp' = 0.1): DECLINED
  negatives  every benchmarks/refute_mutants/*/input.txt and benchmarks/negative/*/input.txt
             (on): DECLINED
  adversarial (2026-10-30, docs/STUTTER-SOUNDNESS.md) claims that are false for every choice of
             right duration, so a CERTIFIED would be unsound; all on, all DECLINED:
             the held Off creeping up (0.001), also at band 0.0005; the attacked Off sinking
             out of the relation on its own (-0.1); the attacked On rising out of reach (to 30);
             the attacked Off drifting away from the boundary (0.1 (xp - 25)); a right-only atom
             in the Off row (xp_R <= 25.5) that the On -> Off handoff breaks; a shared clock c
             (c' = 1 on both sides) with a two-sided pace row and with c_L <= c_R (the claims
             that need the reference to keep pace); lit_csf25_salt_tank_hold (every mode moves)
             on, below its tight slope (1.24)
  controls   on, CERTIFIED: the clock with the one-sided row c_R <= c_L (true while
             the right waits: the stretch-0 query keeps the left field in mixed rows);
             lit_csf25_salt_tank_hold at its own values (and its cover equal to the one off)
  key        a file that still carries the retired key `stutter = true` is refused (ERROR, the
             unknown-key gate)

Every text edit is asserted to change the file (no case passes on an unedited file).

Usage: python3 scripts/stutter_tests.py [--relcert BIN] [--skip-negatives]
"""
import argparse, glob, os, re, subprocess, sys, tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
DEMO = os.path.join(ROOT, "benchmarks", "stutter_demo", "salt_tank_stutter", "input.txt")
CSF25 = os.path.join(ROOT, "benchmarks", "suite_v2", "lit_csf25_salt_tank_hold", "input.txt")
VERD = re.compile(r": (CERTIFIED|DECLINED|ERROR)")


def clean_env(off=False):
    env = dict(os.environ, RELCERT_IMPLIED_CUT="1")
    for k in ("RELCERT_SYNC", "RELCERT_NO_CUT", "RELCERT_NO_IMPLIED_CUT", "RELCERT_NO_PAIR_STRETCH",
              "RELCERT_NO_CHOICE", "RELCERT_NO_PRUNE", "RELCERT_NO_REPO", "RELCERT_NO_STUTTER",
              "RELCERT_NO_PRELANDING"):
        env.pop(k, None)
    if off:
        env["RELCERT_NO_STUTTER"] = "1"
    return env


def verdict(relcert, path, off=False):
    env = clean_env(off)
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




def band(text, c):
    return sub(text, "+ 0.0 and", f"+ {c} and")


def clock(text, rows):
    """A shared clock `c` (c' = 1 in every mode of both sides) with `rows` appended to both rows."""
    text = sub(text, "state_vars = [xp]", "state_vars = [xp, c]")
    text = re.sub(r"(?m)^(ode = xp' = smt2:.*;)$", r"\1 c' = smt2:1.0;", text)
    assert text.count("c' = smt2:1.0;") == 4
    text, k = re.subn(r"(?m)^((On|Off) = .*)$", lambda m: m.group(1) + rows, text)
    assert k == 2
    return text


def emit_cover(relcert, path, off=False):
    env = clean_env(off)
    r = subprocess.run([relcert, "--emit-cover", path, "cov"], capture_output=True, text=True,
                       env=env, timeout=600)
    assert "CoverEmitE" in r.stdout, f"no cover emitted for {path}"
    return r.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--relcert", default=os.path.join(ROOT, ".lake", "build", "bin", "relcert"))
    ap.add_argument("--skip-negatives", action="store_true")
    a = ap.parse_args()
    demo = open(DEMO).read()
    assert not re.search(r"(?m)^stutter\s*=", demo), "the demo still carries the retired key"
    cases = []   # (name, text, expected, off)
    for c in ["0.0", "0.5", "1.0", "2.0", "2.99", "3.0"]:
        cases.append((f"positive band {c} (on)", band(demo, c), "CERTIFIED", False))
    cases.append(("positive band 0.0 (off)", demo, "DECLINED", True))
    cases.append(("positive band 3.0 (off)", band(demo, "3.0"), "CERTIFIED", True))
    cases.append(("positive band 2.99 (off)", band(demo, "2.99"), "DECLINED", True))
    cases.append(("positive band -0.01 (on)", band(demo, "-0.01"), "DECLINED", False))
    assert re.search(r"(?m)^lambda_min = 0\.0$", demo), "the demo does not declare lambda_min = 0"
    cases.append(("guard band 0.0, lambda in [0,1] (off)", demo, "DECLINED", True))
    # batch 13: stretch 0 is a candidate only when the declared range includes 0
    cases.append(("range: band 0.0, lambda in [1,1] (on; 0 outside the declared range)",
                  sub(demo, "lambda_min = 0.0", "lambda_min = 1.0"), "DECLINED", False))
    cases.append(("range: band 0.0, lambda in [0.5,1] (on; 0 outside the declared range)",
                  sub(demo, "lambda_min = 0.0", "lambda_min = 0.5"), "DECLINED", False))
    cases.append(("range: band 3.0, lambda in [1,1] (on)",
                  sub(band(demo, "3.0"), "lambda_min = 0.0", "lambda_min = 1.0"), "CERTIFIED", False))
    lam00 = sub(demo, "lambda_max = 1.0", "lambda_max = 0.0")
    cases.append(("lam00 lambda in [0,0] (on)", lam00, "DECLINED", False))
    lOff = "[Lsys.mode.Off]\node = xp' = smt2:0.0;"
    moving = sub(demo, lOff, "[Lsys.mode.Off]\node = xp' = smt2:0.1;")
    cases.append(("moving left Off xp' = 0.1 (on)", moving, "DECLINED", False))
    # adversarial (2026-10-30)
    creep = sub(demo, lOff, "[Lsys.mode.Off]\node = xp' = smt2:0.001;")
    cases.append(("adv: left Off creeping xp' = 0.001 (on)", creep, "DECLINED", False))
    cases.append(("adv: left Off creeping 0.001, band 0.0005 (on)", band(creep, "0.0005"), "DECLINED", False))
    cases.append(("adv: left Off sinking xp' = -0.1 (on)",
                  sub(demo, lOff, "[Lsys.mode.Off]\node = xp' = smt2:-0.1;"), "DECLINED", False))
    cases.append(("adv: left Off drifting away xp' = 0.1 (xp - 25) (on)",
                  sub(demo, lOff, "[Lsys.mode.Off]\node = xp' = smt2:(* 0.1 (- xp 25.0));"), "DECLINED", False))
    cases.append(("adv: left On rising to 30 (on)",
                  sub(demo, "[Lsys.mode.On]\node = xp' = smt2:(* 0.1 (- 25.0 xp));",
                      "[Lsys.mode.On]\node = xp' = smt2:(* 0.1 (- 30.0 xp));"), "DECLINED", False))
    offrow = re.search(r"(?m)^Off = .*$", demo).group(0)
    cases.append(("adv: right-only atom xp_R <= 25.5 in the Off row (on)",
                  sub(demo, offrow, offrow + " and xp[r] <= 25.5"), "DECLINED", False))
    cases.append(("adv: shared clock, two-sided pace row 0.5 (on)",
                  clock(demo, " and c[l] <= c[r] + 0.5 and c[r] <= c[l] + 0.5"), "DECLINED", False))
    cases.append(("adv: shared clock, c_L <= c_R (on)", clock(demo, " and c[l] <= c[r]"), "DECLINED", False))
    cases.append(("control: shared clock, c_R <= c_L (on)", clock(demo, " and c[r] <= c[l]"),
                  "CERTIFIED", False))
    csf25 = open(CSF25).read()
    cases.append(("control: lit_csf25_salt_tank_hold (on)", csf25, "CERTIFIED", False))
    cases.append(("adv: lit_csf25_salt_tank_hold slope 1.24 (on)",
                  sub(csf25, "t[l]*1.25 - 4.15", "t[l]*1.24 - 4.15"), "DECLINED", False))
    cases.append(("key: the retired key stutter = true is refused",
                  sub(demo, "[problem]\n", "[problem]\nstutter = true\n", 1), "ERROR", False))
    if not a.skip_negatives:
        for d in ("refute_mutants", "negative"):
            for p in sorted(glob.glob(os.path.join(ROOT, "benchmarks", d, "*", "input.txt"))):
                cases.append((f"{d}/{os.path.basename(os.path.dirname(p))} (on)",
                              open(p).read(), "DECLINED", False))
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        for i, (name, text, want, off) in enumerate(cases):
            p = os.path.join(tmp, f"case{i}.txt")
            open(p, "w").write(text)
            got = verdict(a.relcert, p, off)
            ok = got == want
            bad += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {name}: {got} (expected {want})", flush=True)
        # a file that closes without stretch 0 keeps its cover with stretch 0 on
        p0 = os.path.join(tmp, "csf25.txt")
        open(p0, "w").write(csf25)
        same = emit_cover(a.relcert, p0, off=True) == emit_cover(a.relcert, p0, off=False)
        bad += not same
        cases.append(("csf25 cover", "", "", False))
        print(f"{'ok  ' if same else 'FAIL'} control: lit_csf25_salt_tank_hold cover on "
              f"= off: {same}", flush=True)
    print(f"stutter tests: {len(cases) - bad}/{len(cases)} as expected")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
