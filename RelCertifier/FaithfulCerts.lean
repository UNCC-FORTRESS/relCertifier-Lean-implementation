/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `Faithful` certificates — kernel-checked instance ↔ benchmark identity (GENERATED metas)

Each `example : faithful… <IR> <meta> <instance> = true := rfl` is a kernel computation:
the parser-emitted IR literal (BenchIR.lean), the transcription metadata (λ and the
per-coordinate value scales, as data), and the certified instance agree under the
conventions documented in Faithful.lean. Together with the runtime drift check
(relcert-test re-parses each file and compares to the IR literal), the chain
file → parser → IR → (Faithful, kernel) → instance → (wellformed, kernel) → GuardSettlingH
is machine-checked end to end; the residual trust is the parser (already in the base).
-/
import RelCertifier.BenchIR
import RelCertifier.Faithful
import RelCertifier.SettlingInstances
import RelCertifier.TerrainInstances
import RelCertifier.AffineInstances

namespace RelCertifier
open RelCertifier.Parse


def arm_chain_rung1_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling arm_chain_rung1_IR arm_chain_rung1_meta arm_chain_rung1M = true := rfl

def arm_chain_rung2_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling arm_chain_rung2_IR arm_chain_rung2_meta arm_chain_rung2M = true := rfl

def arm_chain_rung3_meta : TransMeta :=
  { lam := (qMk 5 1), scales := [(qMk 1000 1)] }

example : faithfulSettling arm_chain_rung3_IR arm_chain_rung3_meta arm_chain_rung3M = true := rfl

def arm_fidelity_high_meta : TransMeta :=
  { lam := (qMk 5 1), scales := [(qMk 1000 1)] }

example : faithfulSettling arm_fidelity_high_IR arm_fidelity_high_meta arm_fidelity_highM = true := rfl

def arm_fidelity_low_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling arm_fidelity_low_IR arm_fidelity_low_meta arm_fidelity_lowM = true := rfl

def arm_fidelity_mid_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling arm_fidelity_mid_IR arm_fidelity_mid_meta arm_fidelity_midM = true := rfl

def arm_refinement_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling arm_refinement_IR arm_refinement_meta arm_refinementM = true := rfl

def attitude_rate_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulSettling attitude_rate_IR attitude_rate_meta attitude_rateM = true := rfl

def endurance_gain_M1_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 2000 1)] }

example : faithfulSettling endurance_gain_M1_IR endurance_gain_M1_meta endurance_gain_M1M = true := rfl

def endurance_orderlift_1to2_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 2000 1), (qMk 1000 1)] }

example : faithfulSettling endurance_orderlift_1to2_IR endurance_orderlift_1to2_meta endurance_orderlift_1to2M = true := rfl

def endurance_orderlift_2to3_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 2000 1), (qMk 500 1), (qMk 1000 1)] }

example : faithfulSettling endurance_orderlift_2to3_IR endurance_orderlift_2to3_meta endurance_orderlift_2to3M = true := rfl

def match_multi_eps_meta : TransMeta :=
  { lam := (qMk 5 1), scales := [(qMk 1000 1), (qMk 50000 1)] }

example : faithfulSettling match_multi_eps_IR match_multi_eps_meta match_multi_epsM = true := rfl

def match_multi_rate_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 10000 1)] }

example : faithfulSettling match_multi_rate_IR match_multi_rate_meta match_multi_rateM = true := rfl

def plant_fan_high_meta : TransMeta :=
  { lam := (qMk 5 1), scales := [(qMk 1000 1)] }

example : faithfulSettling plant_fan_high_IR plant_fan_high_meta plant_fan_highM = true := rfl

def plant_fan_low_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling plant_fan_low_IR plant_fan_low_meta plant_fan_lowM = true := rfl

def plant_fan_mid_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling plant_fan_mid_IR plant_fan_mid_meta plant_fan_midM = true := rfl

def refinement_ladder_rover_rung1_2to3_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain refinement_ladder_rover_rung1_2to3_IR refinement_ladder_rover_rung1_2to3_meta refinement_ladder_rover_rung1_2to3T = true := rfl

def refinement_ladder_rover_rung2_3to6_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain refinement_ladder_rover_rung2_3to6_IR refinement_ladder_rover_rung2_3to6_meta refinement_ladder_rover_rung2_3to6T = true := rfl

def refinement_ladder_rover_rung2_6dof_meta : TransMeta :=
  { lam := (qMk 3 1), scales := [(qMk 1000 1), (qMk 3000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain refinement_ladder_rover_rung2_6dof_IR refinement_ladder_rover_rung2_6dof_meta refinement_ladder_rover_rung2_6dofT = true := rfl

def refinement_ladder_rover_rung2b_6dof_meta : TransMeta :=
  { lam := (qMk 3 1), scales := [(qMk 1000 1), (qMk 3000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain refinement_ladder_rover_rung2b_6dof_IR refinement_ladder_rover_rung2b_6dof_meta refinement_ladder_rover_rung2b_6dofT = true := rfl

def refinement_ladder_rover_rung2c_6dof_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain refinement_ladder_rover_rung2c_6dof_IR refinement_ladder_rover_rung2c_6dof_meta refinement_ladder_rover_rung2c_6dofT = true := rfl

def refinement_ladder_rover_rung3_6to8_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain refinement_ladder_rover_rung3_6to8_IR refinement_ladder_rover_rung3_6to8_meta refinement_ladder_rover_rung3_6to8T = true := rfl

def refinement_ladder_rover_rung4_8to12_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain refinement_ladder_rover_rung4_8to12_IR refinement_ladder_rover_rung4_8to12_meta refinement_ladder_rover_rung4_8to12T = true := rfl

def robot_braking_meta : TransMeta :=
  { lam := (qMk 2 1), scales := [(qMk 1000 1)] }

example : faithfulSettling robot_braking_IR robot_braking_meta robot_brakingM = true := rfl

def rover3_M1_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1)] }

example : faithfulSettling rover3_M1_IR rover3_M1_meta rover3_M1M = true := rfl

def rover3tier_M1_meta : TransMeta :=
  { lam := (qMk 5 1), scales := [(qMk 1000 1), (qMk 50000 1)] }

example : faithfulSettling rover3tier_M1_IR rover3tier_M1_meta rover3tier_M1M = true := rfl

def rover3tier_rung12_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 10000 1), (qMk 100 1)] }

example : faithfulAffine rover3tier_rung12_IR rover3tier_rung12_meta rover3tier_rung12A = true := rfl

def rover_4d_box_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulSettling rover_4d_box_IR rover_4d_box_meta rover_4d_boxM = true := rfl

def rover_attitude_cone_12dof_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain rover_attitude_cone_12dof_IR rover_attitude_cone_12dof_meta rover_attitude_cone_12dofT = true := rfl

def rover_coupled_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulSettling rover_coupled_IR rover_coupled_meta rover_coupledM = true := rfl

def rover_dof_terrain_rung1_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain rover_dof_terrain_rung1_IR rover_dof_terrain_rung1_meta rover_dof_terrain_rung1T = true := rfl

def rover_dof_terrain_rung2_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain rover_dof_terrain_rung2_IR rover_dof_terrain_rung2_meta rover_dof_terrain_rung2T = true := rfl

def rover_dof_terrain_rung3_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain rover_dof_terrain_rung3_IR rover_dof_terrain_rung3_meta rover_dof_terrain_rung3T = true := rfl

def rover_dof_terrain_rung3_8d_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain rover_dof_terrain_rung3_8d_IR rover_dof_terrain_rung3_8d_meta rover_dof_terrain_rung3_8dT = true := rfl

def rover_drag_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1)] }

example : faithfulSettling rover_drag_IR rover_drag_meta rover_dragM = true := rfl

def rover_position_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulSettling rover_position_IR rover_position_meta rover_positionM = true := rfl

def rover_terrain_M1_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 2000 1)] }

example : faithfulSettling rover_terrain_M1_IR rover_terrain_M1_meta rover_terrain_M1M = true := rfl

def rover_tier_r1_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulAffine rover_tier_r1_IR rover_tier_r1_meta rover_tier_r1A = true := rfl

def story1_attdist_rung_a_6to8_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain story1_attdist_rung_a_6to8_IR story1_attdist_rung_a_6to8_meta story1_attdist_rung_a_6to8T = true := rfl

def story1_attdist_rung_b_12dof_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain story1_attdist_rung_b_12dof_IR story1_attdist_rung_b_12dof_meta story1_attdist_rung_b_12dofT = true := rfl

def story2_lateral_rung_a_8dof_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain story2_lateral_rung_a_8dof_IR story2_lateral_rung_a_8dof_meta story2_lateral_rung_a_8dofT = true := rfl

def story2_lateral_rung_b_12dof_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain story2_lateral_rung_b_12dof_IR story2_lateral_rung_b_12dof_meta story2_lateral_rung_b_12dofT = true := rfl

def story3_rollover_base_12dof_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain story3_rollover_base_12dof_IR story3_rollover_base_12dof_meta story3_rollover_base_12dofT = true := rfl

def story3_rollover_ladder_rung_a_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain story3_rollover_ladder_rung_a_IR story3_rollover_ladder_rung_a_meta story3_rollover_ladder_rung_aT = true := rfl

def story3_rollover_ladder_rung_b_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1), (qMk 1000 1)] }

example : faithfulTerrain story3_rollover_ladder_rung_b_IR story3_rollover_ladder_rung_b_meta story3_rollover_ladder_rung_bT = true := rfl

def watertankSuite_meta : TransMeta :=
  { lam := (qMk 1 1), scales := [(qMk 1000 1)] }

example : faithfulSettling watertank_IR watertankSuite_meta watertankSuiteM = true := rfl

end RelCertifier
