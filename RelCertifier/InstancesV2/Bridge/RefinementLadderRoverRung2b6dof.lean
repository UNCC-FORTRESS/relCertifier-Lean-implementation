/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2b_6dof` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py refinement_ladder_rover_rung2b_6dof`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.RoverRung2b6dof
import RelCertifier.InstancesV2.BenchCovers.refinement_ladder_rover_rung2b_6dof
import RelCertifier.InstancesV2.BenchProgress.refinement_ladder_rover_rung2b_6dof

namespace RelCertifier.Bridge.RefinementLadderRoverRung2b6dof

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.refinement_ladder_rover_rung2b_6dof_IRv2
abbrev cX := Oracle.refinement_ladder_rover_rung2b_6dof_cutsV2X
abbrev cov := refinement_ladder_rover_rung2b_6dof_coverV2
abbrev prog := Progress.refinement_ladder_rover_rung2b_6dof_coverV2_progress

theorem struct_ok : structOK IR 6 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 6 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 6 cov = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = RoverRung2b6dofGuarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR RoverRung2b6dofGuarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR RoverRung2b6dofGuarded.GrG = true := by decide +kernel

/-- Assumption 1, transported from `RoverRung2b6dofGuarded.refinement_ladder_rover_rung2b_6dof_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 6 (prunedOf cov)) (guardR IR 6) (epsR IR) :=
  wellFormedR_transport RoverRung2b6dofGuarded.refinement_ladder_rover_rung2b_6dof_wellFormedR (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, RoverRung2b6dofGuarded.GrG_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `refinement_ladder_rover_rung2b_6dof`** (window form): every verdict group of the benchmark `unsat`. -/
theorem refinement_ladder_rover_rung2b_6dof_bridge (hv : Verdicts IR 6 cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 6 cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt

end RelCertifier.Bridge.RefinementLadderRoverRung2b6dof
