#!/usr/bin/env python3
"""Emit the suite_v2 data layer: per-benchmark leaves under RelCertifier/InstancesV2/.

Per benchmark `<b>` of benchmarks/suite_v2 (all of them):
  BenchIR/<b>.lean       `Parse.<b>_IRv2`         (relcert --emit-ir; drift-checked by relcert-test)
  BenchCovers/<b>.lean   `<b>_coverV2`            (RELCERT_IMPLIED_CUT=1 relcert --emit-cover; progress certificates by default)
  BenchProgress/<b>.lean `<b>_coverV2_progress`   (the same run, RELCERT_PROGRESS_OUT)
  Cuts/<b>.lean          `Oracle.<b>_cutsV2` (legacy part) and `Oracle.<b>_cutsV2X` (extended),
                         both kernel-checked well-formed against the IR literal by `rfl`
  BenchPrelanding/<b>.lean `<b>_coverV2_prelanding` (the same run, RELCERT_PRELANDING_OUT: the
                         pre-landing right-only nodes, docs/PRELANDING.md; every benchmark since
                         2026-10-31, the pre-landing feature being always on; empty for a cover
                         without right-only nodes)
Aggregators: BenchIR.lean (`benchIRTableV2`), BenchCovers.lean (`coverTableV2`),
BenchChoice.lean (`choiceTableV2`), BenchProgress.lean (`progressTableV2`), Cuts.lean
(`cutTableV2`), BenchPrelanding.lean (`prelandTableV2`).

The run features (stretch 0, the pre-landing certificate) are on for every benchmark; the
ablation switches RELCERT_NO_STUTTER / RELCERT_NO_PRELANDING are removed from the environment of
every run, so the leaves are always the default configuration's.

The choice exhibits (benchmarks/choice, `--choice`): the same run's leaves under
InstancesV2/Choice/{BenchCovers,BenchProgress,BenchChoice,BenchPrelanding}/<b>.lean (their IR and
cut leaves are checked to be unchanged, not rewritten: `<b>_IRc`, `<b>_cutsC(X)`).

Usage: python3 scripts/gen_v2_data.py [bench ...]   (default: all of benchmarks/suite_v2)
       python3 scripts/gen_v2_data.py --choice      (the two choice exhibits)
Every generated file is overwritten; the aggregators always list the whole suite.
"""
import os, subprocess, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
os.chdir(ROOT)
RELCERT = "./.lake/build/bin/relcert"
SUITE = "benchmarks/suite_v2"
OUT = "RelCertifier/InstancesV2"
HDR = """/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `{b}` (suite_v2) — {what} (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py {b}`.
-/
"""

def run(args, env_extra=None):
    env = dict(os.environ)
    env.pop("RELCERT_NO_CUT", None); env.pop("RELCERT_NO_IMPLIED_CUT", None)
    env.pop("RELCERT_NO_LINEAR_CUT", None); env.pop("RELCERT_NO_PRUNE", None)
    for k in ["RELCERT_NO_STUTTER", "RELCERT_NO_PRELANDING", "RELCERT_SYNC", "RELCERT_NO_REPO",
              "RELCERT_NO_CHOICE", "RELCERT_NO_PAIR_STRETCH", "RELCERT_SINGLE_STEP",
              "RELCERT_NO_PROGRESS"]:
        env.pop(k, None)
    if env_extra:
        env.update(env_extra)
    r = subprocess.run(args, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"FAILED: {' '.join(args)}\n{r.stdout}\n{r.stderr}")
    return r.stdout

def all_benches():
    return sorted(d for d in os.listdir(SUITE) if os.path.isfile(f"{SUITE}/{d}/input.txt"))


def emit_leaves(b):
    path = f"{SUITE}/{b}/input.txt"
    ir = run([RELCERT, "--emit-ir", path, f"{b}_IRv2"])
    with open(f"{OUT}/BenchIR/{b}.lean", "w") as f:
        f.write(HDR.format(b=b, what="parser-emitted IR literal"))
        f.write("import RelCertifier.Trusted.Parse\n\nnamespace RelCertifier.Parse\n\n")
        f.write(ir.rstrip() + "\n\nend RelCertifier.Parse\n")
    # the cover is searched with the progress certificates required of every reposition node
    # (the tool's default); the certificates found are written to the BenchProgress leaf
    env = {"RELCERT_IMPLIED_CUT": "1",
           "RELCERT_PROGRESS_OUT": f"{OUT}/BenchProgress/{b}.lean",
           "RELCERT_CHOICE_OUT": f"{OUT}/BenchChoice/{b}.lean"}
    # the pre-landing record (docs/PRELANDING.md; the feature is on for every benchmark): the
    # right-only nodes certified before the landing, never in the cover's dynPre/dynPost flags
    pl_leaf = f"{OUT}/BenchPrelanding/{b}.lean"
    env["RELCERT_PRELANDING_OUT"] = pl_leaf
    if os.path.exists(pl_leaf):
        os.remove(pl_leaf)
    cov = run([RELCERT, "--emit-cover", path, f"{b}_coverV2"], env)
    pl = open(pl_leaf).read() if os.path.exists(pl_leaf) else ""
    if "PrelandEmitE" not in pl:
        sys.exit(f"{b}: no pre-landing record written")
    open(pl_leaf, "w").write(HDR.format(b=b, what="emitted pre-landing record") + pl)
    with open(f"{OUT}/BenchCovers/{b}.lean", "w") as f:
        f.write(HDR.format(b=b, what="emitted cover, `RELCERT_IMPLIED_CUT=1`, reposition certificates by default"))
        f.write("import RelCertifier.Checker.CoverEmit\n\nnamespace RelCertifier\n\n")
        f.write(f"/-- `{b}` (emitted, suite_v2, implied mode-fact candidates on). -/\n")
        f.write(cov.rstrip() + "\n\nend RelCertifier\n")
    cuts = run([RELCERT, "--emit-cuts", path, f"{b}_cutsV2"], {"RELCERT_IMPLIED_CUT": "1"})
    if f"def {b}_cutsV2X : EvolStrengtheningX" not in cuts:
        sys.exit(f"{b}: --emit-cuts printed no extended certificate")
    with open(f"{OUT}/Cuts/{b}.lean", "w") as f:
        f.write(HDR.format(b=b, what="mode-fact certificates, legacy and extended"))
        f.write("import RelCertifier.Checker.EvolStrengtheningX\n")
        f.write(f"import RelCertifier.InstancesV2.BenchIR.{b}\n\n")
        f.write("namespace RelCertifier.Oracle\n\nopen RelCertifier.Parse\n\n")
        f.write(cuts.rstrip() + "\n\n")
        f.write(f"/-- The legacy (guard-conjunct) part is well formed. -/\n")
        f.write(f"theorem {b}_cutsV2_wf : evolStrengtheningWF {b}_IRv2 {b}_cutsV2 = true := rfl\n\n")
        f.write(f"/-- The extended certificate is well formed (every kind, entry and rational route\n"
                f"re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/\n")
        f.write(f"theorem {b}_cutsV2X_wf : evolStrengtheningWFX {b}_IRv2 {b}_cutsV2X = true := rfl\n\n")
        f.write("end RelCertifier.Oracle\n")

def emit_aggregators(benches):
    with open(f"{OUT}/BenchIR.lean", "w") as f:
        f.write("""/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# suite_v2 IR aggregator + `benchIRTableV2` (GENERATED — `scripts/gen_v2_data.py`)

The parser-emitted literals of `benchmarks/suite_v2`. `relcert-test`'s drift check
(`[ir-drift-v2]`) re-parses `benchmarks/suite_v2/<name>/input.txt` for every entry and
compares it with the literal of the same name in `benchIRTableV2`.
-/
""")
        for b in benches:
            f.write(f"import RelCertifier.InstancesV2.BenchIR.{b}\n")
        f.write("\nnamespace RelCertifier.Parse\n\n")
        f.write("def benchIRTableV2 : List (String × PProblem) := [\n")
        f.write(",\n".join(f"  (\"{b}\", {b}_IRv2)" for b in benches))
        f.write(" ]\n\nend RelCertifier.Parse\n")
    with open(f"{OUT}/BenchCovers.lean", "w") as f:
        f.write("/- suite_v2 cover aggregator (GENERATED — `scripts/gen_v2_data.py`). -/\n")
        for b in benches:
            f.write(f"import RelCertifier.InstancesV2.BenchCovers.{b}\n")
        f.write("\nnamespace RelCertifier\n\n")
        f.write("def coverTableV2 : List (String × CoverEmitE) := [\n")
        f.write(",\n".join(f"  (\"{b}\", {b}_coverV2)" for b in benches))
        f.write(" ]\n\nend RelCertifier\n")
    with open(f"{OUT}/BenchChoice.lean", "w") as f:
        f.write("/- suite_v2 choice-record aggregator (GENERATED — `scripts/gen_v2_data.py`): the committed\n")
        f.write("successor subsets per benchmark (empty for a benchmark whose cover\n")
        f.write("needs none). -/\n")
        for b in benches:
            f.write(f"import RelCertifier.InstancesV2.BenchChoice.{b}\n")
        f.write("\nnamespace RelCertifier.Choice\n\n")
        f.write("def choiceTableV2 : List (String × ChoiceEmitE) := [\n")
        f.write(",\n".join(f"  (\"{b}\", {b}_coverV2_choice)" for b in benches))
        f.write(" ]\n\nend RelCertifier.Choice\n")
    # the progress table (`relcert-progress-verdicts`, and the bridge runner's `progV2`): every
    # benchmark, so the bridge runner sends every instance's progress queries, which its
    # `Verdicts` names (docs/PRELANDING.md)
    pbenches = list(benches)
    with open(f"{OUT}/BenchProgress.lean", "w") as f:
        f.write("/- suite_v2 reposition-certificate aggregator (GENERATED — `scripts/gen_v2_data.py`; "
                "the leaves by `--emit-cover` with `RELCERT_PROGRESS_OUT`). -/\n")
        for b in pbenches:
            f.write(f"import RelCertifier.InstancesV2.BenchProgress.{b}\n")
        f.write("\nnamespace RelCertifier.Progress\n\n")
        f.write("/-- Every benchmark's emitted reposition certificates (stage lists), by name. -/\n")
        f.write("def progressTableV2 : List (String × ProgressEmitE) :=\n")
        f.write("  [" + ",\n   ".join(f"(\"{b}\", {b}_coverV2_progress)" for b in pbenches))
        f.write("]\n\nend RelCertifier.Progress\n")
    # the pre-landing records (docs/PRELANDING.md) of every benchmark (the feature is always on)
    pbs = list(benches)
    with open(f"{OUT}/BenchPrelanding.lean", "w") as f:
        f.write("/- suite_v2 pre-landing-record aggregator (GENERATED — `scripts/gen_v2_data.py`): the\n")
        f.write("pre-landing records of every benchmark, its right-only nodes checked on the restricted\n")
        f.write("mode of Lemma 4 (`docs/PRELANDING.md`; a record without nodes is empty). -/\n")
        f.write("import RelCertifier.Trusted.PrelandEmit\n")
        for b in pbs:
            f.write(f"import RelCertifier.InstancesV2.BenchPrelanding.{b}\n")
        f.write("\nnamespace RelCertifier.Preland\n\n")
        f.write("def prelandTableV2 : List (String × PrelandEmitE) := [")
        f.write(",\n".join(f"\n  (\"{b}\", {b}_coverV2_prelanding)" for b in pbs))
        f.write(" ]\n\nend RelCertifier.Preland\n")
    with open(f"{OUT}/Cuts.lean", "w") as f:
        f.write("/- suite_v2 mode-fact-certificate aggregator (GENERATED — `scripts/gen_v2_data.py`). -/\n")
        for b in benches:
            f.write(f"import RelCertifier.InstancesV2.Cuts.{b}\n")
        f.write("\nnamespace RelCertifier.Oracle\n\n")
        f.write("def cutTableV2 : List (String × EvolStrengthening × EvolStrengtheningX) := [\n")
        f.write(",\n".join(f"  (\"{b}\", {b}_cutsV2, {b}_cutsV2X)" for b in benches))
        f.write(" ]\n\nend RelCertifier.Oracle\n")

def choice_entries(b):
    """Number of chosen-set entries in the emitted choice record of `b`."""
    src = open(f"{OUT}/BenchChoice/{b}.lean").read()
    return max(src.count("⟨\"") - 1, 0)   # the record header `⟨"<b>", [...]⟩` is not an entry

def nvars(b):
    """The left state variables of `b` (its IR literal's `state_vars`)."""
    for line in open(f"{SUITE}/{b}/input.txt"):
        if line.startswith("state_vars"):
            return len([v for v in line.split("[", 1)[1].split("]")[0].split(",") if v.strip()])
    return 1

CHOICE_DIR = "benchmarks/choice"
COUT = f"{OUT}/Choice"
CHDR = """/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `{b}` (choice) — {what} (GENERATED leaf)

Regenerate with `scripts/gen_v2_data.py --choice`.
-/
"""

def body_of(path, start):
    """The text of a leaf from its first line starting with `start` (the literal itself)."""
    txt = open(path).read()
    i = txt.find(start)
    return txt[i:] if i >= 0 else None

def emit_choice_leaves(b):
    """The choice exhibit `b`'s cover-run leaves (cover, progress, choice, pre-landing record);
    its IR and cut leaves must be unchanged (checked, not rewritten)."""
    path = f"{CHOICE_DIR}/{b}/input.txt"
    ir = run([RELCERT, "--emit-ir", path, f"{b}_IRc"])
    lit = ir[ir.index(f"def {b}_IRc"):].rstrip()
    old = body_of(f"{COUT}/BenchIR/{b}.lean", f"def {b}_IRc")
    if old is None or old.split("\n\nend RelCertifier.Parse")[0].rstrip() != lit:
        sys.exit(f"{b}: the choice IR leaf differs from --emit-ir (regenerate it first)")
    cuts = run([RELCERT, "--emit-cuts", path, f"{b}_cutsC"], {"RELCERT_IMPLIED_CUT": "1"})
    oldc = open(f"{COUT}/Cuts/{b}.lean").read()
    for blk in cuts.strip().split("\n\n"):
        if blk.strip() and blk.strip() not in oldc:
            sys.exit(f"{b}: the choice cut leaf differs from --emit-cuts (regenerate it first)")
    for d in ["BenchCovers", "BenchProgress", "BenchChoice", "BenchPrelanding"]:
        os.makedirs(f"{COUT}/{d}", exist_ok=True)
    pr, ch, pl = (f"{COUT}/BenchProgress/{b}.lean", f"{COUT}/BenchChoice/{b}.lean",
                  f"{COUT}/BenchPrelanding/{b}.lean")
    for x in (pr, ch, pl):
        if os.path.exists(x):
            os.remove(x)
    env = {"RELCERT_IMPLIED_CUT": "1", "RELCERT_PROGRESS_OUT": pr, "RELCERT_CHOICE_OUT": ch,
           "RELCERT_PRELANDING_OUT": pl}
    cov = run([RELCERT, "--emit-cover", path, f"{b}_coverV2"], env)
    for x, what in ((pr, "emitted reposition certificates"), (ch, "emitted choice record"),
                    (pl, "emitted pre-landing record")):
        if not os.path.exists(x):
            sys.exit(f"{b}: no {what} written")
        body = open(x).read()
        open(x, "w").write(CHDR.format(b=b, what=what) + body)
    with open(f"{COUT}/BenchCovers/{b}.lean", "w") as f:
        f.write(CHDR.format(b=b, what="emitted cover, `RELCERT_IMPLIED_CUT=1`, reposition certificates by default"))
        f.write("import RelCertifier.Checker.CoverEmit\n\nnamespace RelCertifier\n\n")
        f.write(cov.rstrip() + "\n\n\nend RelCertifier\n")

def main():
    if sys.argv[1:] == ["--choice"]:
        for b in sorted(os.listdir(CHOICE_DIR)):
            if os.path.isfile(f"{CHOICE_DIR}/{b}/input.txt"):
                emit_choice_leaves(b)
                print(f"  emitted choice {b}")
        return
    for d in ["BenchIR", "BenchCovers", "Cuts", "BenchProgress", "BenchChoice", "BenchPrelanding"]:
        os.makedirs(f"{OUT}/{d}", exist_ok=True)
    benches = all_benches()
    todo = sys.argv[1:] or benches
    for b in todo:
        emit_leaves(b)
        print(f"  emitted {b}")
    emit_aggregators(benches)
    print(f"aggregators over {len(benches)} benchmarks")

if __name__ == "__main__":
    main()
