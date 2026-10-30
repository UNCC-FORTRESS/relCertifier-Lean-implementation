/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_cooling_prelanding` (prelanding_demo) through the generic bridge (GENERATED —
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
import RelCertifier.InstancesV2.WellFormed.EngineCoolingPrelanding
import RelCertifier.InstancesV2.Cuts.engine_cooling_prelanding
import RelCertifier.InstancesV2.BenchCovers.engine_cooling_prelanding
import RelCertifier.InstancesV2.BenchProgress.engine_cooling_prelanding
import RelCertifier.InstancesV2.BenchChoice.engine_cooling_prelanding
import RelCertifier.InstancesV2.BenchPrelanding.engine_cooling_prelanding

namespace RelCertifier.Bridge.EngineCoolingPrelanding

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.engine_cooling_prelanding_IRv2
abbrev cX := Oracle.engine_cooling_prelanding_cutsV2X
abbrev cov := engine_cooling_prelanding_coverV2
abbrev prog := Progress.engine_cooling_prelanding_coverV2_progress
abbrev ce := Choice.engine_cooling_prelanding_coverV2_choice
abbrev pl := Preland.engine_cooling_prelanding_coverV2_prelanding
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
(`V2EngineCoolingPrelanding.engine_cooling_prelanding_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2EngineCoolingPrelanding.engine_cooling_prelanding_wellFormedR_direct (prunedOf cov))) reg

/-- The demo opts in, and its cover really uses pre-landing nodes (decided in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel

/-- **Theorem 3 of `engine_cooling_prelanding`** (window form, over the emitted cover): every verdict group of the
benchmark `unsat`. -/
theorem engine_cooling_prelanding_bridge (hv : VerdictsPL IR 4 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 4 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records_pl pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroupsPL`,
`scripts/prelanding_demo_verdicts.lean`). -/
theorem engine_cooling_prelanding_bridge_run {gs : List (List (IForm 4))}
    (hrun : bridgeGroupsPL IR 4 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaim IR 4 cX cov reg 0 1 2 dt :=
  engine_cooling_prelanding_bridge (verdictsPL_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.EngineCoolingPrelanding
