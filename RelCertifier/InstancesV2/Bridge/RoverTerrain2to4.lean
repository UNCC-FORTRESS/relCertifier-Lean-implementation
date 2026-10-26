/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_2to4` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py rover_terrain_2to4`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 4 and lifted to 5 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.RoverTerrain2to4
import RelCertifier.InstancesV2.Cuts.rover_terrain_2to4
import RelCertifier.InstancesV2.BenchCovers.rover_terrain_2to4
import RelCertifier.InstancesV2.BenchProgress.rover_terrain_2to4
import RelCertifier.InstancesV2.BenchChoice.rover_terrain_2to4

namespace RelCertifier.Bridge.RoverTerrain2to4

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.rover_terrain_2to4_IRv2
abbrev cX := Oracle.rover_terrain_2to4_cutsV2X
abbrev cov := rover_terrain_2to4_coverV2
abbrev prog := Progress.rover_terrain_2to4_coverV2_progress
abbrev ce := Choice.rover_terrain_2to4_coverV2_choice

theorem struct_ok : structOK IR 5 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 5 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 5 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 4 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = RoverTerrain2to4Guarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR RoverTerrain2to4Guarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR RoverTerrain2to4Guarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 4 (prunedOf cov)).modeAt q = some m' →
    ∃ m, RoverTerrain2to4Guarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, RoverTerrain2to4Guarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 5) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 5 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `RoverTerrain2to4Guarded.rover_terrain_2to4_wellFormedR` at dimension 4 and lifted to 5. -/
theorem wellFormedR : WellFormedRIn (grOf IR 5 (prunedOf cov)) (guardR IR 5) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 4) pad_ok
    (wellFormedR_transport (RoverTerrain2to4Guarded.rover_terrain_2to4_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `rover_terrain_2to4`** (window form): every verdict group of the benchmark `unsat`. -/
theorem rover_terrain_2to4_bridge (hv : Verdicts IR 5 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 5 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.RoverTerrain2to4
