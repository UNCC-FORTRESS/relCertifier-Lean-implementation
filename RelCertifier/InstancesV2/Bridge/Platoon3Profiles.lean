/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_profiles` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py platoon3_profiles`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 6 and lifted to 7 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.Platoon3Profiles
import RelCertifier.InstancesV2.Cuts.platoon3_profiles
import RelCertifier.InstancesV2.BenchCovers.platoon3_profiles
import RelCertifier.InstancesV2.BenchProgress.platoon3_profiles
import RelCertifier.InstancesV2.BenchChoice.platoon3_profiles

namespace RelCertifier.Bridge.Platoon3Profiles

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.platoon3_profiles_IRv2
abbrev cX := Oracle.platoon3_profiles_cutsV2X
abbrev cov := platoon3_profiles_coverV2
abbrev prog := Progress.platoon3_profiles_coverV2_progress
abbrev ce := Choice.platoon3_profiles_coverV2_choice

theorem struct_ok : structOK IR 7 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 7 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 7 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 6 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2Platoon3Profiles.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2Platoon3Profiles.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2Platoon3Profiles.Gr = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 6 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2Platoon3Profiles.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2Platoon3Profiles.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 7) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 7 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2Platoon3Profiles.platoon3_profiles_wellFormedR` at dimension 6 and lifted to 7. -/
theorem wellFormedR : WellFormedRIn (grOf IR 7 (prunedOf cov)) (guardR IR 7) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 6) pad_ok
    (wellFormedR_transport (V2Platoon3Profiles.platoon3_profiles_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `platoon3_profiles`** (window form): every verdict group of the benchmark `unsat`. -/
theorem platoon3_profiles_bridge (hv : Verdicts IR 7 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 7 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.Platoon3Profiles
