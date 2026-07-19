/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Benchmark IR aggregator + `benchIRTable`

X0 modularization: the per-benchmark IR literals live in `BenchIR/<name>.lean`
leaf modules; per-benchmark instances import their own leaf, so editing one
benchmark re-elaborates only its own column. This aggregator re-exports all
leaves and carries the whole-suite `benchIRTable` for the runtime doors
(runners, drift checks, verdicts). Import it ONLY from whole-suite consumers.
-/
import RelCertifier.Instances.BenchIR.arm_chain_rung1
import RelCertifier.Instances.BenchIR.arm_chain_rung2
import RelCertifier.Instances.BenchIR.arm_chain_rung3
import RelCertifier.Instances.BenchIR.arm_fidelity_high
import RelCertifier.Instances.BenchIR.arm_fidelity_low
import RelCertifier.Instances.BenchIR.arm_fidelity_mid
import RelCertifier.Instances.BenchIR.arm_refinement
import RelCertifier.Instances.BenchIR.attitude_rate
import RelCertifier.Instances.BenchIR.endurance_gain_M1
import RelCertifier.Instances.BenchIR.endurance_orderlift_1to2
import RelCertifier.Instances.BenchIR.endurance_orderlift_2to3
import RelCertifier.Instances.BenchIR.match_multi_eps
import RelCertifier.Instances.BenchIR.match_multi_rate
import RelCertifier.Instances.BenchIR.plant_fan_high
import RelCertifier.Instances.BenchIR.plant_fan_low
import RelCertifier.Instances.BenchIR.plant_fan_mid
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung1_2to3
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2_3to6
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2b_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2c_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung3_6to8
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung4_8to12
import RelCertifier.Instances.BenchIR.robot_braking
import RelCertifier.Instances.BenchIR.rover3_M1
import RelCertifier.Instances.BenchIR.rover3tier_M1
import RelCertifier.Instances.BenchIR.rover3tier_rung12
import RelCertifier.Instances.BenchIR.rover_4d_box
import RelCertifier.Instances.BenchIR.rover_attitude_cone_12dof
import RelCertifier.Instances.BenchIR.rover_coupled
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung1
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung2
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3_8d
import RelCertifier.Instances.BenchIR.rover_drag
import RelCertifier.Instances.BenchIR.rover_position
import RelCertifier.Instances.BenchIR.rover_terrain_M1
import RelCertifier.Instances.BenchIR.rover_tier_r1
import RelCertifier.Instances.BenchIR.story1_attdist_rung_a_6to8
import RelCertifier.Instances.BenchIR.story1_attdist_rung_b_12dof
import RelCertifier.Instances.BenchIR.story2_lateral_rung_a_8dof
import RelCertifier.Instances.BenchIR.story2_lateral_rung_b_12dof
import RelCertifier.Instances.BenchIR.story3_rollover_base_12dof
import RelCertifier.Instances.BenchIR.story3_rollover_ladder_rung_a
import RelCertifier.Instances.BenchIR.story3_rollover_ladder_rung_b
import RelCertifier.Instances.BenchIR.watertank

namespace RelCertifier.Parse

def benchIRTable : List (String × PProblem) := [
  ("arm_chain_rung1", arm_chain_rung1_IR),
  ("arm_chain_rung2", arm_chain_rung2_IR),
  ("arm_chain_rung3", arm_chain_rung3_IR),
  ("arm_fidelity_high", arm_fidelity_high_IR),
  ("arm_fidelity_low", arm_fidelity_low_IR),
  ("arm_fidelity_mid", arm_fidelity_mid_IR),
  ("arm_refinement", arm_refinement_IR),
  ("attitude_rate", attitude_rate_IR),
  ("endurance_gain_M1", endurance_gain_M1_IR),
  ("endurance_orderlift_1to2", endurance_orderlift_1to2_IR),
  ("endurance_orderlift_2to3", endurance_orderlift_2to3_IR),
  ("match_multi_eps", match_multi_eps_IR),
  ("match_multi_rate", match_multi_rate_IR),
  ("plant_fan_high", plant_fan_high_IR),
  ("plant_fan_low", plant_fan_low_IR),
  ("plant_fan_mid", plant_fan_mid_IR),
  ("refinement_ladder_rover_rung1_2to3", refinement_ladder_rover_rung1_2to3_IR),
  ("refinement_ladder_rover_rung2_3to6", refinement_ladder_rover_rung2_3to6_IR),
  ("refinement_ladder_rover_rung2_6dof", refinement_ladder_rover_rung2_6dof_IR),
  ("refinement_ladder_rover_rung2b_6dof", refinement_ladder_rover_rung2b_6dof_IR),
  ("refinement_ladder_rover_rung2c_6dof", refinement_ladder_rover_rung2c_6dof_IR),
  ("refinement_ladder_rover_rung3_6to8", refinement_ladder_rover_rung3_6to8_IR),
  ("refinement_ladder_rover_rung4_8to12", refinement_ladder_rover_rung4_8to12_IR),
  ("robot_braking", robot_braking_IR),
  ("rover3_M1", rover3_M1_IR),
  ("rover3tier_M1", rover3tier_M1_IR),
  ("rover3tier_rung12", rover3tier_rung12_IR),
  ("rover_4d_box", rover_4d_box_IR),
  ("rover_attitude_cone_12dof", rover_attitude_cone_12dof_IR),
  ("rover_coupled", rover_coupled_IR),
  ("rover_dof_terrain_rung1", rover_dof_terrain_rung1_IR),
  ("rover_dof_terrain_rung2", rover_dof_terrain_rung2_IR),
  ("rover_dof_terrain_rung3_8d", rover_dof_terrain_rung3_8d_IR),
  ("rover_dof_terrain_rung3", rover_dof_terrain_rung3_IR),
  ("rover_drag", rover_drag_IR),
  ("rover_position", rover_position_IR),
  ("rover_terrain_M1", rover_terrain_M1_IR),
  ("rover_tier_r1", rover_tier_r1_IR),
  ("story1_attdist_rung_a_6to8", story1_attdist_rung_a_6to8_IR),
  ("story1_attdist_rung_b_12dof", story1_attdist_rung_b_12dof_IR),
  ("story2_lateral_rung_a_8dof", story2_lateral_rung_a_8dof_IR),
  ("story2_lateral_rung_b_12dof", story2_lateral_rung_b_12dof_IR),
  ("story3_rollover_base_12dof", story3_rollover_base_12dof_IR),
  ("story3_rollover_ladder_rung_a", story3_rollover_ladder_rung_a_IR),
  ("story3_rollover_ladder_rung_b", story3_rollover_ladder_rung_b_IR),
  ("watertank", watertank_IR) ]

end RelCertifier.Parse
