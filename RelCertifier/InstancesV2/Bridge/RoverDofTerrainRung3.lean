/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung3` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py rover_dof_terrain_rung3`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.RoverDofTerrainRung3
import RelCertifier.InstancesV2.Cuts.rover_dof_terrain_rung3
import RelCertifier.InstancesV2.BenchCovers.rover_dof_terrain_rung3
import RelCertifier.InstancesV2.BenchProgress.rover_dof_terrain_rung3
import RelCertifier.InstancesV2.BenchChoice.rover_dof_terrain_rung3

namespace RelCertifier.Bridge.RoverDofTerrainRung3

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.rover_dof_terrain_rung3_IRv2
abbrev cX := Oracle.rover_dof_terrain_rung3_cutsV2X
abbrev cov := rover_dof_terrain_rung3_coverV2
abbrev prog := Progress.rover_dof_terrain_rung3_coverV2_progress
abbrev ce := Choice.rover_dof_terrain_rung3_coverV2_choice

theorem struct_ok : structOK IR 12 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 12 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 12 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = RoverDofTerrainRung3Guarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR RoverDofTerrainRung3Guarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR RoverDofTerrainRung3Guarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 12 (prunedOf cov)).modeAt q = some m' →
    ∃ m, RoverDofTerrainRung3Guarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, RoverDofTerrainRung3Guarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 12) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 12 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `RoverDofTerrainRung3Guarded.rover_dof_terrain_rung3_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 12 (prunedOf cov)) (guardR IR 12) reg (epsR IR) :=
  wellFormedR_transport (RoverDofTerrainRung3Guarded.rover_dof_terrain_rung3_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `rover_dof_terrain_rung3`** (window form): every verdict group of the benchmark `unsat`. -/
theorem rover_dof_terrain_rung3_bridge (hv : Verdicts IR 12 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 12 cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt

end RelCertifier.Bridge.RoverDofTerrainRung3
