/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_profiles` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py platoon_delay_profiles`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.PlatoonDelayProfiles
import RelCertifier.InstancesV2.BenchCovers.platoon_delay_profiles
import RelCertifier.InstancesV2.BenchProgress.platoon_delay_profiles

namespace RelCertifier.Bridge.PlatoonDelayProfiles

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.platoon_delay_profiles_IRv2
abbrev cX := Oracle.platoon_delay_profiles_cutsV2X
abbrev cov := platoon_delay_profiles_coverV2
abbrev prog := Progress.platoon_delay_profiles_coverV2_progress

theorem struct_ok : structOK IR 2 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 2 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 2 cov = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2PlatoonDelayProfiles.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2PlatoonDelayProfiles.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2PlatoonDelayProfiles.Gr = true := by decide +kernel

/-- Assumption 1, transported from `V2PlatoonDelayProfiles.platoon_delay_profiles_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 2 (prunedOf cov)) (guardR IR 2) (epsR IR) :=
  wellFormedR_transport V2PlatoonDelayProfiles.platoon_delay_profiles_wellFormedR (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, V2PlatoonDelayProfiles.Gr_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `platoon_delay_profiles`** (window form): every verdict group of the benchmark `unsat`. -/
theorem platoon_delay_profiles_bridge (hv : Verdicts IR 2 cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 2 cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt

end RelCertifier.Bridge.PlatoonDelayProfiles
