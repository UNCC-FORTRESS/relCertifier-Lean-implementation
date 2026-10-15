/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_limp` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py acc_tune_limp`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.AccTuneLimp
import RelCertifier.InstancesV2.Cuts.acc_tune_limp
import RelCertifier.InstancesV2.BenchCovers.acc_tune_limp
import RelCertifier.InstancesV2.BenchProgress.acc_tune_limp
import RelCertifier.InstancesV2.BenchChoice.acc_tune_limp

namespace RelCertifier.Bridge.AccTuneLimp

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.acc_tune_limp_IRv2
abbrev cX := Oracle.acc_tune_limp_cutsV2X
abbrev cov := acc_tune_limp_coverV2
abbrev prog := Progress.acc_tune_limp_coverV2_progress
abbrev ce := Choice.acc_tune_limp_coverV2_choice

theorem struct_ok : structOK IR 3 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 3 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 3 cov ce = true := by decide +kernel
theorem nR_eq : nR IR = V2AccTuneLimp.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2AccTuneLimp.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2AccTuneLimp.Gr = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 3 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2AccTuneLimp.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2AccTuneLimp.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 3) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 3 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2AccTuneLimp.acc_tune_limp_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 3 (prunedOf cov)) (guardR IR 3) reg (epsR IR) :=
  wellFormedR_transport (V2AccTuneLimp.acc_tune_limp_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `acc_tune_limp`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem acc_tune_limp_bridge (hv : Verdicts IR 3 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 3 cX cov reg 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.AccTuneLimp
