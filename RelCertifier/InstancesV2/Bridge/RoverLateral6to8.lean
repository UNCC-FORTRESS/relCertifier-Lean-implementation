/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_lateral_6to8` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py rover_lateral_6to8`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 8 and lifted to 9 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.RoverLateral6to8
import RelCertifier.InstancesV2.Cuts.rover_lateral_6to8
import RelCertifier.InstancesV2.BenchCovers.rover_lateral_6to8
import RelCertifier.InstancesV2.BenchProgress.rover_lateral_6to8
import RelCertifier.InstancesV2.BenchChoice.rover_lateral_6to8

namespace RelCertifier.Bridge.RoverLateral6to8

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.rover_lateral_6to8_IRv2
abbrev cX := Oracle.rover_lateral_6to8_cutsV2X
abbrev cov := rover_lateral_6to8_coverV2
abbrev prog := Progress.rover_lateral_6to8_coverV2_progress
abbrev ce := Choice.rover_lateral_6to8_coverV2_choice

theorem struct_ok : structOK IR 9 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 9 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 9 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 8 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = RoverLateral6to8Guarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR RoverLateral6to8Guarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR RoverLateral6to8Guarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 8 (prunedOf cov)).modeAt q = some m' →
    ∃ m, RoverLateral6to8Guarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, RoverLateral6to8Guarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 9) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 9 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `RoverLateral6to8Guarded.rover_lateral_6to8_wellFormedR` at dimension 8 and lifted to 9. -/
theorem wellFormedR : WellFormedRIn (grOf IR 9 (prunedOf cov)) (guardR IR 9) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 8) pad_ok
    (wellFormedR_transport (RoverLateral6to8Guarded.rover_lateral_6to8_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `rover_lateral_6to8`** (window form): every verdict group of the benchmark `unsat`. -/
theorem rover_lateral_6to8_bridge (hv : Verdicts IR 9 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 9 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.RoverLateral6to8
