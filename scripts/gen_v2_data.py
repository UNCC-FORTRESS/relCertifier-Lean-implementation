#!/usr/bin/env python3
"""Emit the suite_v2 data layer: per-benchmark leaves under RelCertifier/InstancesV2/.

Per benchmark `<b>` of benchmarks/suite_v2 (all 45):
  BenchIR/<b>.lean       `Parse.<b>_IRv2`         (relcert --emit-ir; drift-checked by relcert-test)
  BenchCovers/<b>.lean   `<b>_coverV2`            (RELCERT_IMPLIED_CUT=1 relcert --emit-cover)
  Cuts/<b>.lean          `Oracle.<b>_cutsV2` (legacy part) and `Oracle.<b>_cutsV2X` (extended),
                         both kernel-checked well-formed against the IR literal by `rfl`
Aggregators: BenchIR.lean (`benchIRTableV2`), BenchCovers.lean (`coverTableV2`),
Cuts.lean (`cutTableV2`), CoverReplay.lean (kernel replay of every emitted cover,
`by decide`), SameIR.lean (the 19 benchmarks copied unchanged from suite_uniform: their v2
literal IS the legacy literal, `rfl`).

Usage: python3 scripts/gen_v2_data.py [bench ...]   (default: all of benchmarks/suite_v2)
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
    if env_extra:
        env.update(env_extra)
    r = subprocess.run(args, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"FAILED: {' '.join(args)}\n{r.stdout}\n{r.stderr}")
    return r.stdout

def all_benches():
    return sorted(d for d in os.listdir(SUITE) if os.path.isfile(f"{SUITE}/{d}/input.txt"))

# the 19 benchmarks whose suite_v2 file normalizes to the suite_uniform one
SAME = ["match_multi_rate", "refinement_ladder_rover_rung1_2to3",
        "refinement_ladder_rover_rung2_3to6", "refinement_ladder_rover_rung2_6dof",
        "refinement_ladder_rover_rung2b_6dof", "refinement_ladder_rover_rung2c_6dof",
        "refinement_ladder_rover_rung3_6to8", "refinement_ladder_rover_rung4_8to12",
        "rover3tier_rung12", "rover_dof_terrain_rung1", "rover_dof_terrain_rung2",
        "rover_dof_terrain_rung3", "rover_dof_terrain_rung3_8d",
        "story1_attdist_rung_a_6to8", "story1_attdist_rung_b_12dof",
        "story2_lateral_rung_a_8dof", "story2_lateral_rung_b_12dof",
        "story3_rollover_base_12dof", "story3_rollover_ladder_rung_a"]

def emit_leaves(b):
    path = f"{SUITE}/{b}/input.txt"
    ir = run([RELCERT, "--emit-ir", path, f"{b}_IRv2"]).replace(
        "benchmarks/suite_uniform/", "benchmarks/suite_v2/")
    with open(f"{OUT}/BenchIR/{b}.lean", "w") as f:
        f.write(HDR.format(b=b, what="parser-emitted IR literal"))
        f.write("import RelCertifier.Trusted.Parse\n\nnamespace RelCertifier.Parse\n\n")
        f.write(ir.rstrip() + "\n\nend RelCertifier.Parse\n")
    cov = run([RELCERT, "--emit-cover", path, f"{b}_coverV2"], {"RELCERT_IMPLIED_CUT": "1"})
    with open(f"{OUT}/BenchCovers/{b}.lean", "w") as f:
        f.write(HDR.format(b=b, what="emitted cover, `RELCERT_IMPLIED_CUT=1`"))
        f.write("import RelCertifier.Checker.CoverEmit\n\nnamespace RelCertifier\n\n")
        f.write(f"/-- `{b}` (emitted, suite_v2, widened cut channel on). -/\n")
        f.write(cov.rstrip() + "\n\nend RelCertifier\n")
    cuts = run([RELCERT, "--emit-cuts", path, f"{b}_cutsV2"], {"RELCERT_IMPLIED_CUT": "1"})
    if f"def {b}_cutsV2X : EvolStrengtheningX" not in cuts:
        sys.exit(f"{b}: --emit-cuts printed no extended certificate")
    with open(f"{OUT}/Cuts/{b}.lean", "w") as f:
        f.write(HDR.format(b=b, what="checked-cut certificates, legacy and extended"))
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

The 45 parser-emitted literals of `benchmarks/suite_v2`. `relcert-test`'s drift check
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
    with open(f"{OUT}/Cuts.lean", "w") as f:
        f.write("/- suite_v2 cut-certificate aggregator (GENERATED — `scripts/gen_v2_data.py`). -/\n")
        for b in benches:
            f.write(f"import RelCertifier.InstancesV2.Cuts.{b}\n")
        f.write("\nnamespace RelCertifier.Oracle\n\n")
        f.write("def cutTableV2 : List (String × EvolStrengthening × EvolStrengtheningX) := [\n")
        f.write(",\n".join(f"  (\"{b}\", {b}_cutsV2, {b}_cutsV2X)" for b in benches))
        f.write(" ]\n\nend RelCertifier.Oracle\n")
    with open(f"{OUT}/CoverReplay.lean", "w") as f:
        f.write("""/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Kernel replays of the suite_v2 covers (GENERATED — `scripts/gen_v2_data.py`)

Per benchmark, for every emitted left-mode cover and every admissible start, the verified
`decideCovered` accepts on the structural graph the tool built (`coverReplays`,
`Instances/BenchCoverReplay.lean`), by kernel computation.
-/
import RelCertifier.Instances.BenchCoverReplay
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.BenchCovers

namespace RelCertifier

""")
        for b in benches:
            f.write(f"theorem {b}_coverV2_replay : coverReplays Parse.{b}_IRv2 {b}_coverV2 = true := by decide\n\n")
        f.write("end RelCertifier\n")
    with open(f"{OUT}/SameIR.lean", "w") as f:
        f.write("""/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The 19 suite_v2 benchmarks copied unchanged from suite_uniform (GENERATED)

For each, the suite_v2 file's parser-emitted literal IS the suite_uniform literal every
legacy instance quotes (`rfl`), so the legacy theorems are theorems about the suite_v2
file (the file-to-literal tie is `relcert-test`'s drift check over the suite_v2 manifest).
-/
""")
        for b in SAME:
            f.write(f"import RelCertifier.InstancesV2.BenchIR.{b}\n")
            f.write(f"import RelCertifier.Instances.BenchIR.{b}\n")
        f.write("\nnamespace RelCertifier.Parse\n\n")
        for b in SAME:
            f.write(f"theorem {b}_IRv2_eq : {b}_IRv2 = {b}_IR := rfl\n")
        f.write("\nend RelCertifier.Parse\n")

def main():
    for d in ["BenchIR", "BenchCovers", "Cuts"]:
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
