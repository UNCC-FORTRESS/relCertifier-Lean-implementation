/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_profiles` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py platoon3_profiles`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.Platoon3Profiles
import RelCertifier.InstancesV2.BenchCovers.platoon3_profiles
import RelCertifier.InstancesV2.BenchProgress.platoon3_profiles

namespace RelCertifier.Bridge.Platoon3Profiles

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.platoon3_profiles_IRv2
abbrev cX := Oracle.platoon3_profiles_cutsV2X
abbrev cov := platoon3_profiles_coverV2
abbrev prog := Progress.platoon3_profiles_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "platoon3_profiles"

theorem struct_ok : structOK IR 6 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 6 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 6 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2Platoon3Profiles.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2Platoon3Profiles.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2Platoon3Profiles.Gr = true := by decide +kernel

/-- Assumption 1, transported from `V2Platoon3Profiles.platoon3_profiles_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 6 (prunedOf cov)) (guardR IR 6) (epsR IR) :=
  wellFormedR_transport (V2Platoon3Profiles.platoon3_profiles_wellFormedR) (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, V2Platoon3Profiles.Gr_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `platoon3_profiles`** (window form): every verdict group of the benchmark `unsat`. -/
theorem platoon3_profiles_bridge (hv : Verdicts IR 6 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 6 cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt

end RelCertifier.Bridge.Platoon3Profiles
