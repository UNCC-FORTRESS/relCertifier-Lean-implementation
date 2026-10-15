/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_choice` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py watertank_choice`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.Choice.General.WatertankChoice
import RelCertifier.InstancesV2.Choice.BenchCovers.watertank_choice
import RelCertifier.InstancesV2.Choice.BenchProgress.watertank_choice
import RelCertifier.InstancesV2.Choice.BenchChoice.watertank_choice

namespace RelCertifier.Bridge.WatertankChoice

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.watertank_choice_IRc
abbrev cX := Oracle.watertank_choice_cutsCX
abbrev cov := watertank_choice_coverV2
abbrev prog := Progress.watertank_choice_coverV2_progress
abbrev ce := Choice.watertank_choice_coverV2_choice

theorem struct_ok : structOK IR 2 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 2 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 2 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = ChoiceWatertank.GrP.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR ChoiceWatertank.GrP = true := by decide +kernel
theorem src_ok : edgesSrcOK IR ChoiceWatertank.GrP = true := by decide +kernel
theorem epsR_eq : epsR IR = 1 := by
  have h : Run.parseRat IR.R.epsilon = some (1 : ℚ) := by decide +kernel
  simp only [epsR, h, Option.getD_some, Rat.cast_one]

/-- Assumption 1, transported from `ChoiceWatertank.wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 2 (prunedOf cov)) (guardR IR 2) (epsR IR) :=
  wellFormedR_transport (by rw [epsR_eq]; exact ChoiceWatertank.wellFormedR) (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, ChoiceWatertank.GrP_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `watertank_choice`** (window form): every verdict group of the benchmark `unsat`. -/
theorem watertank_choice_bridge (hv : Verdicts IR 2 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 2 cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt

end RelCertifier.Bridge.WatertankChoice
