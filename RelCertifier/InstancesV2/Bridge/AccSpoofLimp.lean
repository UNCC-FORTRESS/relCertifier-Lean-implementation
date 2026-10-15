/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_limp` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py acc_spoof_limp`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.AccSpoofLimp
import RelCertifier.InstancesV2.BenchCovers.acc_spoof_limp
import RelCertifier.InstancesV2.BenchProgress.acc_spoof_limp

namespace RelCertifier.Bridge.AccSpoofLimp

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.acc_spoof_limp_IRv2
abbrev cX := Oracle.acc_spoof_limp_cutsV2X
abbrev cov := acc_spoof_limp_coverV2
abbrev prog := Progress.acc_spoof_limp_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "acc_spoof_limp"

theorem struct_ok : structOK IR 3 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 3 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 3 cov ce = true := by decide +kernel
theorem nR_eq : nR IR = V2AccSpoofLimp.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2AccSpoofLimp.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2AccSpoofLimp.Gr = true := by decide +kernel

/-- Assumption 1, transported from `V2AccSpoofLimp.acc_spoof_limp_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 3 (prunedOf cov)) (guardR IR 3) (epsR IR) :=
  wellFormedR_transport (V2AccSpoofLimp.acc_spoof_limp_wellFormedR) (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, V2AccSpoofLimp.Gr_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `acc_spoof_limp`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem acc_spoof_limp_bridge (hv : Verdicts IR 3 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 3 cX cov 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.AccSpoofLimp
