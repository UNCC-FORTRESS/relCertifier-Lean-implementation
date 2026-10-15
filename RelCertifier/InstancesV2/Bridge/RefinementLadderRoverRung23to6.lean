/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2_3to6` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py refinement_ladder_rover_rung2_3to6`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.RoverLadderRung2
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung2_3to6
import RelCertifier.InstancesV2.BenchCovers.refinement_ladder_rover_rung2_3to6
import RelCertifier.InstancesV2.BenchProgress.refinement_ladder_rover_rung2_3to6
import RelCertifier.InstancesV2.BenchChoice.refinement_ladder_rover_rung2_3to6

namespace RelCertifier.Bridge.RefinementLadderRoverRung23to6

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.refinement_ladder_rover_rung2_3to6_IRv2
abbrev cX := Oracle.refinement_ladder_rover_rung2_3to6_cutsV2X
abbrev cov := refinement_ladder_rover_rung2_3to6_coverV2
abbrev prog := Progress.refinement_ladder_rover_rung2_3to6_coverV2_progress
abbrev ce := Choice.refinement_ladder_rover_rung2_3to6_coverV2_choice

theorem struct_ok : structOK IR 6 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 6 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 6 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = RoverLadderRung2Guarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR RoverLadderRung2Guarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR RoverLadderRung2Guarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 6 (prunedOf cov)).modeAt q = some m' →
    ∃ m, RoverLadderRung2Guarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, RoverLadderRung2Guarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 6) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 6 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `RoverLadderRung2Guarded.refinement_ladder_rover_rung2_3to6_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 6 (prunedOf cov)) (guardR IR 6) reg (epsR IR) :=
  wellFormedR_transport (RoverLadderRung2Guarded.refinement_ladder_rover_rung2_3to6_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `refinement_ladder_rover_rung2_3to6`** (window form): every verdict group of the benchmark `unsat`. -/
theorem refinement_ladder_rover_rung2_3to6_bridge (hv : Verdicts IR 6 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 6 cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt

end RelCertifier.Bridge.RefinementLadderRoverRung23to6
