/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung1` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py rover_dof_terrain_rung1`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.RoverDofTerrainRung1
import RelCertifier.InstancesV2.BenchCovers.rover_dof_terrain_rung1
import RelCertifier.InstancesV2.BenchProgress.rover_dof_terrain_rung1

namespace RelCertifier.Bridge.RoverDofTerrainRung1

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.rover_dof_terrain_rung1_IRv2
abbrev cX := Oracle.rover_dof_terrain_rung1_cutsV2X
abbrev cov := rover_dof_terrain_rung1_coverV2
abbrev prog := Progress.rover_dof_terrain_rung1_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "rover_dof_terrain_rung1"

theorem struct_ok : structOK IR 3 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 3 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 3 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = RoverDofTerrainRung1Guarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR RoverDofTerrainRung1Guarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR RoverDofTerrainRung1Guarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 3 (prunedOf cov)).modeAt q = some m' →
    ∃ m, RoverDofTerrainRung1Guarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, RoverDofTerrainRung1Guarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 3) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 3 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `RoverDofTerrainRung1Guarded.rover_dof_terrain_rung1_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 3 (prunedOf cov)) (guardR IR 3) reg (epsR IR) :=
  wellFormedR_transport (RoverDofTerrainRung1Guarded.rover_dof_terrain_rung1_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `rover_dof_terrain_rung1`** (window form): every verdict group of the benchmark `unsat`. -/
theorem rover_dof_terrain_rung1_bridge (hv : Verdicts IR 3 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 3 cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt

end RelCertifier.Bridge.RoverDofTerrainRung1
