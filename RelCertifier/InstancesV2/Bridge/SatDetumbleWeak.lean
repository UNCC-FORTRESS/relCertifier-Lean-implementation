/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_weak` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py sat_detumble_weak`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 4 and lifted to 5 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.SatDetumbleWeak
import RelCertifier.InstancesV2.Cuts.sat_detumble_weak
import RelCertifier.InstancesV2.BenchCovers.sat_detumble_weak
import RelCertifier.InstancesV2.BenchProgress.sat_detumble_weak
import RelCertifier.InstancesV2.BenchChoice.sat_detumble_weak

namespace RelCertifier.Bridge.SatDetumbleWeak

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.sat_detumble_weak_IRv2
abbrev cX := Oracle.sat_detumble_weak_cutsV2X
abbrev cov := sat_detumble_weak_coverV2
abbrev prog := Progress.sat_detumble_weak_coverV2_progress
abbrev ce := Choice.sat_detumble_weak_coverV2_choice

theorem struct_ok : structOK IR 5 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 5 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 5 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 4 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2SatDetumbleWeak.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2SatDetumbleWeak.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2SatDetumbleWeak.Gr = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 4 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2SatDetumbleWeak.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2SatDetumbleWeak.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 5) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 5 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2SatDetumbleWeak.sat_detumble_weak_wellFormedR` at dimension 4 and lifted to 5. -/
theorem wellFormedR : WellFormedRIn (grOf IR 5 (prunedOf cov)) (guardR IR 5) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 4) pad_ok
    (wellFormedR_transport (V2SatDetumbleWeak.sat_detumble_weak_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `sat_detumble_weak`** (window form): every verdict group of the benchmark `unsat`. -/
theorem sat_detumble_weak_bridge (hv : Verdicts IR 5 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 5 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.SatDetumbleWeak
