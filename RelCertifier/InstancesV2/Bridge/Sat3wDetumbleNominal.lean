/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_nominal` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py sat3w_detumble_nominal`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.Sat3wDetumbleNominal
import RelCertifier.InstancesV2.BenchCovers.sat3w_detumble_nominal
import RelCertifier.InstancesV2.BenchProgress.sat3w_detumble_nominal

namespace RelCertifier.Bridge.Sat3wDetumbleNominal

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.sat3w_detumble_nominal_IRv2
abbrev cX := Oracle.sat3w_detumble_nominal_cutsV2X
abbrev cov := sat3w_detumble_nominal_coverV2
abbrev prog := Progress.sat3w_detumble_nominal_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "sat3w_detumble_nominal"

theorem struct_ok : structOK IR 6 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 6 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 6 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2Sat3wDetumbleNominal.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2Sat3wDetumbleNominal.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2Sat3wDetumbleNominal.Gr = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 6 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2Sat3wDetumbleNominal.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2Sat3wDetumbleNominal.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds on the momentum band `V2Sat3wDetumbleNominal.nbF` (the unconditional form is false:
`V2Sat3wDetumbleNominal.sat3w_detumble_nominal_wellFormedR_false`); the band is kept by every right flow. -/
noncomputable abbrev reg : Formula (Var 6) := V2Sat3wDetumbleNominal.nbF
theorem reg_fv : reg.fv ⊆ range Rv := by
  intro x hx
  simp only [reg, V2Sat3wDetumbleNominal.nbF, V2Sat3wDetumbleNominal.bandF, V2Sat3wDetumbleNominal.c1T, V2Sat3wDetumbleNominal.c2T, V2Sat3wDetumbleNominal.c3T, Formula.fv, Term.fv, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false, false_or] at hx
  repeat' rcases hx with hx | hx
  all_goals first | (subst hx; exact ⟨_, rfl⟩) | exact ⟨_, rfl⟩ | simp_all
theorem reg_inv : RegionInvariant (grOf IR 6 (prunedOf cov)) reg :=
  regionInvariant_transport V2Sat3wDetumbleNominal.sat3w_detumble_nominal_band_invariant modes_eq

/-- Assumption 1 on the band, transported from `V2Sat3wDetumbleNominal.sat3w_detumble_nominal_wellFormedR_onBand`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 6 (prunedOf cov)) (guardR IR 6) reg (epsR IR) :=
  wellFormedRIn_transport V2Sat3wDetumbleNominal.sat3w_detumble_nominal_wellFormedR_onBand (by rw [grOf_len, nR_eq]) modes_eq
    (fun q => rfl) (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `sat3w_detumble_nominal`** (window form): every verdict group of the benchmark `unsat`. -/
theorem sat3w_detumble_nominal_bridge (hv : Verdicts IR 6 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 6 cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt

end RelCertifier.Bridge.Sat3wDetumbleNominal
