/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story2_lateral_rung_b_12dof` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py story2_lateral_rung_b_12dof`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.Story2LateralB
import RelCertifier.InstancesV2.BenchCovers.story2_lateral_rung_b_12dof
import RelCertifier.InstancesV2.BenchProgress.story2_lateral_rung_b_12dof

namespace RelCertifier.Bridge.Story2LateralRungB12dof

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.story2_lateral_rung_b_12dof_IRv2
abbrev cX := Oracle.story2_lateral_rung_b_12dof_cutsV2X
abbrev cov := story2_lateral_rung_b_12dof_coverV2
abbrev prog := Progress.story2_lateral_rung_b_12dof_coverV2_progress

theorem struct_ok : structOK IR 12 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 12 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 12 cov = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = Story2LateralBGuarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR Story2LateralBGuarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR Story2LateralBGuarded.GrG = true := by decide +kernel

/-- Assumption 1, transported from `Story2LateralBGuarded.story2_lateral_rung_b_12dof_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 12 (prunedOf cov)) (guardR IR 12) (epsR IR) :=
  wellFormedR_transport Story2LateralBGuarded.story2_lateral_rung_b_12dof_wellFormedR (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, Story2LateralBGuarded.GrG_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `story2_lateral_rung_b_12dof`** (window form): every verdict group of the benchmark `unsat`. -/
theorem story2_lateral_rung_b_12dof_bridge (hv : Verdicts IR 12 cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 12 cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt

end RelCertifier.Bridge.Story2LateralRungB12dof
