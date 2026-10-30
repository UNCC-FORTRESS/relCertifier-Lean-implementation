#!/usr/bin/env python3
"""Emit the pre-landing demo (benchmarks/prelanding_demo/engine_cooling_prelanding,
docs/PRELANDING.md) through the existing generator path, without touching the suite_v2
aggregators.

* the data leaves (IR, cover, progress, choice, cuts) by `gen_v2_data.emit_leaves`, reading
  benchmarks/prelanding_demo instead of benchmarks/suite_v2 (the leaves land beside the suite's,
  named after the demo; no aggregator is rewritten, so the suite tables are unchanged); the IR
  carries `prelanding := true`; the same `--emit-cover` run writes the pre-landing record
  (`RELCERT_PRELANDING_OUT`) to InstancesV2/BenchPrelanding/<b>.lean;
* the generic-bridge instance InstancesV2/Bridge/EngineCoolingPrelanding.lean, in the window
  form (the rows are the same in both left modes), at dimension 3 (+1, the right clock), with
  Theorem 3 from the records (`VerdictsPL`, `theorem3_window_of_records_pl`) and from a green run
  of the groups (`bridgeGroupsPL`). Assumption 1 is the demo's own Z3-free lemma
  (InstancesV2/WellFormed/EngineCoolingPrelanding.lean), lifted by one coordinate.

Usage: python3 scripts/gen_prelanding_demo.py
Kernel check: lake build RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding
Verdicts:     lake env lean scripts/prelanding_demo_verdicts.lean
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_v2_data as D

DEMO_DIR = "benchmarks/prelanding_demo"
B = "engine_cooling_prelanding"
CAMEL = "EngineCoolingPrelanding"
PL_LEAF = f"{D.OUT}/BenchPrelanding/{B}.lean"

D.SUITE = DEMO_DIR
D.HDR = D.HDR.replace("(suite_v2)", "(prelanding_demo)").replace(
    "Regenerate with `scripts/gen_v2_data.py {b}`.", "Regenerate with `scripts/gen_prelanding_demo.py`.")

_run = D.run


def run(args, env_extra=None):
    """`gen_v2_data.run`, with the pre-landing record written by the same `--emit-cover` run."""
    if "--emit-cover" in args:
        env_extra = dict(env_extra or {}, RELCERT_PRELANDING_OUT=PL_LEAF)
    return _run(args, env_extra)


D.run = run

INSTANCE = '''/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `{b}` (prelanding_demo) through the generic bridge (GENERATED —
`scripts/gen_prelanding_demo.py`)

The NAHS 2025 engine cooling system at the paper's distance 0.3, with the opt-in key
`prelanding = true` (`docs/PRELANDING.md`). Each left mode's cover has one pre-landing
right-only node (the genuine heats alone up to 100 against the attacked Cool, cools alone down
to 100 against the attacked Heat), recorded in the pre-landing record `pl`, never as the
cover's `dynPre`/`dynPost` flags; the kernel merges them (`withPL`) for the cover graph and
backs each by the pre-landing pack at the region before its progress certificate's last stage.

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel on the merged cover (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), the data
gate `pl_ok` (the key is set, the whole-domain flags are off), Assumption 1 from the demo's own
lemma at dimension 3 lifted to 4 (the right clock), the verdicts assumed (`VerdictsPL`: the groups
`scripts/prelanding_demo_verdicts.lean` discharges, `Emitted.verdictsPL_of_groups`). The claim is
over the emitted cover `cov`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Prelanding
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.{camel}
import RelCertifier.InstancesV2.Cuts.{b}
import RelCertifier.InstancesV2.BenchCovers.{b}
import RelCertifier.InstancesV2.BenchProgress.{b}
import RelCertifier.InstancesV2.BenchChoice.{b}
import RelCertifier.InstancesV2.BenchPrelanding.{b}

namespace RelCertifier.Bridge.{camel}

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.{b}_IRv2
abbrev cX := Oracle.{b}_cutsV2X
abbrev cov := {b}_coverV2
abbrev prog := Progress.{b}_coverV2_progress
abbrev ce := Choice.{b}_coverV2_choice
abbrev pl := Preland.{b}_coverV2_prelanding
/-- The cover graph's rows: the emitted cover with the pre-landing nodes merged in. -/
abbrev covM := withPL cov pl

/-- The data gate: the key is set and the emitted whole-domain flags are all off. -/
theorem pl_ok : plOK IR cov pl = true := by decide +kernel
theorem struct_ok : structOK IR 4 covM cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 covM prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 covM ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 3
(`V2{camel}.{b}_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2{camel}.{b}_wellFormedR_direct (prunedOf cov))) reg

/-- The demo opts in, and its cover really uses pre-landing nodes (decided in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel

/-- **Theorem 3 of `{b}`** (window form, over the emitted cover): every verdict group of the
benchmark `unsat`. -/
theorem {b}_bridge (hv : VerdictsPL IR 4 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 4 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records_pl pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroupsPL`,
`scripts/prelanding_demo_verdicts.lean`). -/
theorem {b}_bridge_run {{gs : List (List (IForm 4))}}
    (hrun : bridgeGroupsPL IR 4 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaim IR 4 cX cov reg 0 1 2 dt :=
  {b}_bridge (verdictsPL_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.{camel}
'''


def main():
    for d in ["BenchIR", "BenchCovers", "Cuts", "BenchProgress", "BenchChoice", "BenchPrelanding"]:
        os.makedirs(f"{D.OUT}/{d}", exist_ok=True)
    D.emit_leaves(B)
    fn = f"{D.OUT}/BenchIR/{B}.lean"
    txt = open(fn).read().replace(f"benchmarks/suite_v2/{B}/", f"{DEMO_DIR}/{B}/")
    open(fn, "w").write(txt)
    pl = open(PL_LEAF).read()
    if "PrelandEmitE" not in pl:
        sys.exit(f"{B}: no pre-landing record written")
    open(PL_LEAF, "w").write(D.HDR.format(b=B, what="emitted pre-landing record") + pl)
    print(f"  emitted leaves of {B}")
    out = f"RelCertifier/InstancesV2/Bridge/{CAMEL}.lean"
    open(out, "w").write(INSTANCE.format(b=B, camel=CAMEL))
    print(f"  emitted {out} (dim 4)")


if __name__ == "__main__":
    main()
