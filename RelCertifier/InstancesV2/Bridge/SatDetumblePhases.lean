/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_phases` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py sat_detumble_phases`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.SatDetumblePhases
import RelCertifier.InstancesV2.BenchCovers.sat_detumble_phases
import RelCertifier.InstancesV2.BenchProgress.sat_detumble_phases

namespace RelCertifier.Bridge.SatDetumblePhases

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.sat_detumble_phases_IRv2
abbrev cX := Oracle.sat_detumble_phases_cutsV2X
abbrev cov := sat_detumble_phases_coverV2
abbrev prog := Progress.sat_detumble_phases_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "sat_detumble_phases"

theorem struct_ok : structOK IR 4 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 cov ce = true := by decide +kernel
theorem nR_eq : nR IR = V2SatDetumblePhases.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2SatDetumblePhases.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2SatDetumblePhases.Gr = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 4 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2SatDetumblePhases.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2SatDetumblePhases.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2SatDetumblePhases.sat_detumble_phases_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  wellFormedR_transport (V2SatDetumblePhases.sat_detumble_phases_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `sat_detumble_phases`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem sat_detumble_phases_bridge (hv : Verdicts IR 4 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 4 cX cov reg 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.SatDetumblePhases
