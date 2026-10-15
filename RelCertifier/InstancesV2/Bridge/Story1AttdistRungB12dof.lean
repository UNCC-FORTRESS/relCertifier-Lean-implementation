/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_b_12dof` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py story1_attdist_rung_b_12dof`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.Story1AttdistRungB
import RelCertifier.InstancesV2.BenchCovers.story1_attdist_rung_b_12dof
import RelCertifier.InstancesV2.BenchProgress.story1_attdist_rung_b_12dof

namespace RelCertifier.Bridge.Story1AttdistRungB12dof

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.story1_attdist_rung_b_12dof_IRv2
abbrev cX := Oracle.story1_attdist_rung_b_12dof_cutsV2X
abbrev cov := story1_attdist_rung_b_12dof_coverV2
abbrev prog := Progress.story1_attdist_rung_b_12dof_coverV2_progress

theorem struct_ok : structOK IR 12 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 12 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 12 cov = true := by decide +kernel
theorem nR_eq : nR IR = Story1AttdistRungBGuarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR Story1AttdistRungBGuarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR Story1AttdistRungBGuarded.GrG = true := by decide +kernel

/-- Assumption 1, transported from `Story1AttdistRungBGuarded.story1_attdist_rung_b_12dof_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 12 (prunedOf cov)) (guardR IR 12) (epsR IR) :=
  wellFormedR_transport Story1AttdistRungBGuarded.story1_attdist_rung_b_12dof_wellFormedR (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, Story1AttdistRungBGuarded.GrG_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `story1_attdist_rung_b_12dof`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem story1_attdist_rung_b_12dof_bridge (hv : Verdicts IR 12 cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 12 cX cov 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.Story1AttdistRungB12dof
