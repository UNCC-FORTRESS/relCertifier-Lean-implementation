/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story2_lateral_rung_a_8dof` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py story2_lateral_rung_a_8dof`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.Story2LateralA
import RelCertifier.InstancesV2.BenchCovers.story2_lateral_rung_a_8dof
import RelCertifier.InstancesV2.BenchProgress.story2_lateral_rung_a_8dof

namespace RelCertifier.Bridge.Story2LateralRungA8dof

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.story2_lateral_rung_a_8dof_IRv2
abbrev cX := Oracle.story2_lateral_rung_a_8dof_cutsV2X
abbrev cov := story2_lateral_rung_a_8dof_coverV2
abbrev prog := Progress.story2_lateral_rung_a_8dof_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "story2_lateral_rung_a_8dof"

theorem struct_ok : structOK IR 8 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 8 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 8 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = Story2LateralAGuarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR Story2LateralAGuarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR Story2LateralAGuarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 8 (prunedOf cov)).modeAt q = some m' →
    ∃ m, Story2LateralAGuarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, Story2LateralAGuarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 8) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 8 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `Story2LateralAGuarded.story2_lateral_rung_a_8dof_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 8 (prunedOf cov)) (guardR IR 8) reg (epsR IR) :=
  wellFormedR_transport (Story2LateralAGuarded.story2_lateral_rung_a_8dof_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `story2_lateral_rung_a_8dof`** (window form): every verdict group of the benchmark `unsat`. -/
theorem story2_lateral_rung_a_8dof_bridge (hv : Verdicts IR 8 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 8 cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt

end RelCertifier.Bridge.Story2LateralRungA8dof
