/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py rover3tier_rung12`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.Rover3tierRung12
import RelCertifier.InstancesV2.BenchCovers.rover3tier_rung12
import RelCertifier.InstancesV2.BenchProgress.rover3tier_rung12

namespace RelCertifier.Bridge.Rover3tierRung12

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.rover3tier_rung12_IRv2
abbrev cX := Oracle.rover3tier_rung12_cutsV2X
abbrev cov := rover3tier_rung12_coverV2
abbrev prog := Progress.rover3tier_rung12_coverV2_progress

theorem struct_ok : structOK IR 3 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 3 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 3 cov = true := by decide +kernel
theorem nR_eq : nR IR = Rover3tierRung12Guarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR Rover3tierRung12Guarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR Rover3tierRung12Guarded.GrG = true := by decide +kernel

/-- Assumption 1, transported from `Rover3tierRung12Guarded.rover3tier_rung12_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR 3 (prunedOf cov)) (guardR IR 3) (epsR IR) :=
  wellFormedR_transport Rover3tierRung12Guarded.rover3tier_rung12_wellFormedR (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, Rover3tierRung12Guarded.GrG_modeAt q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `rover3tier_rung12`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem rover3tier_rung12_bridge (hv : Verdicts IR 3 cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 3 cX cov 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.Rover3tierRung12
