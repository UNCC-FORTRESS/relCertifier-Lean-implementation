/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_lag` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py acc_spoof_lag`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.AccSpoofLag
import RelCertifier.InstancesV2.BenchCovers.acc_spoof_lag
import RelCertifier.InstancesV2.BenchProgress.acc_spoof_lag

namespace RelCertifier.Bridge.AccSpoofLag

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.acc_spoof_lag_IRv2
abbrev cX := Oracle.acc_spoof_lag_cutsV2X
abbrev cov := acc_spoof_lag_coverV2
abbrev prog := Progress.acc_spoof_lag_coverV2_progress

theorem struct_ok : structOK IR 2 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 2 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 2 cov = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2AccSpoofLag.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2AccSpoofLag.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2AccSpoofLag.Gr = true := by decide +kernel

/-- Assumption 1, transported from `V2AccSpoofLag.acc_spoof_lag_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 2 (prunedOf cov)) (guardR IR 2) (epsR IR) :=
  wellFormedR_transport V2AccSpoofLag.acc_spoof_lag_wellFormedR (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, V2AccSpoofLag.Gr_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `acc_spoof_lag`** (window form): every verdict group of the benchmark `unsat`. -/
theorem acc_spoof_lag_bridge (hv : Verdicts IR 2 cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 2 cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt

end RelCertifier.Bridge.AccSpoofLag
