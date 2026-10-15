/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py charger_fast_setpoints`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.ChargerFastSetpoints
import RelCertifier.InstancesV2.BenchCovers.charger_fast_setpoints
import RelCertifier.InstancesV2.BenchProgress.charger_fast_setpoints

namespace RelCertifier.Bridge.ChargerFastSetpoints

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.charger_fast_setpoints_IRv2
abbrev cX := Oracle.charger_fast_setpoints_cutsV2X
abbrev cov := charger_fast_setpoints_coverV2
abbrev prog := Progress.charger_fast_setpoints_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "charger_fast_setpoints"

theorem struct_ok : structOK IR 2 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 2 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 2 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2ChargerFastSetpoints.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2ChargerFastSetpoints.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2ChargerFastSetpoints.Gr = true := by decide +kernel

/-- Assumption 1, transported from `V2ChargerFastSetpoints.charger_fast_setpoints_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 2 (prunedOf cov)) (guardR IR 2) (epsR IR) :=
  wellFormedR_transport (V2ChargerFastSetpoints.charger_fast_setpoints_wellFormedR) (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, V2ChargerFastSetpoints.Gr_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `charger_fast_setpoints`** (window form): every verdict group of the benchmark `unsat`. -/
theorem charger_fast_setpoints_bridge (hv : Verdicts IR 2 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 2 cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt

end RelCertifier.Bridge.ChargerFastSetpoints
