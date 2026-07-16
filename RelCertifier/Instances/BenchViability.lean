/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Tool-emitted viability verdicts (do not edit — `relcert --emit-viability`)

Per benchmark, per right mode: `true` iff EVERY evolve-box face passes the strict
inward query (`flowQueryStrict`, left frozen, over the mode's own box) — the
certificate `box_viability` consumes. `false` modes (equilibrium-on-face and similar)
take per-shape closed-form lemmas or a named per-mode single-system hypothesis.
-/

namespace RelCertifier

/-- `arm_chain_rung1`. -/
def arm_chain_rung1_viability : List (String × Bool) := [("Approach", false), ("Return", false)]

/-- `arm_chain_rung2`. -/
def arm_chain_rung2_viability : List (String × Bool) := [("ApproachFast", false), ("ApproachSlow", false), ("Return", false)]

/-- `arm_chain_rung3`. -/
def arm_chain_rung3_viability : List (String × Bool) := [("ApproachA", false), ("ApproachB", false), ("ApproachC", false), ("Hold", false)]

/-- `arm_fidelity_high`. -/
def arm_fidelity_high_viability : List (String × Bool) := [("ApproachA", false), ("ApproachB", false), ("ApproachC", false), ("Hold", false)]

/-- `arm_fidelity_low`. -/
def arm_fidelity_low_viability : List (String × Bool) := [("Approach", false), ("Return", false)]

/-- `arm_fidelity_mid`. -/
def arm_fidelity_mid_viability : List (String × Bool) := [("ApproachFast", false), ("ApproachSlow", false), ("Hold", true)]

/-- `arm_refinement`. -/
def arm_refinement_viability : List (String × Bool) := [("Approach", false), ("Return", false)]

/-- `attitude_rate`. -/
def attitude_rate_viability : List (String × Bool) := [("RECOVER", true), ("TRACK", true)]

/-- `endurance_gain_M1`. -/
def endurance_gain_M1_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `endurance_orderlift_1to2`. -/
def endurance_orderlift_1to2_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `endurance_orderlift_2to3`. -/
def endurance_orderlift_2to3_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `match_multi_eps`. -/
def match_multi_eps_viability : List (String × Bool) := [("ACCEL", false), ("COAST", false)]

/-- `match_multi_rate`. -/
def match_multi_rate_viability : List (String × Bool) := [("DRIVE", false)]

/-- `plant_fan_high`. -/
def plant_fan_high_viability : List (String × Bool) := [("ApproachA", false), ("ApproachB", false), ("ApproachC", false), ("Hold", false)]

/-- `plant_fan_low`. -/
def plant_fan_low_viability : List (String × Bool) := [("Approach", false), ("Return", false)]

/-- `plant_fan_mid`. -/
def plant_fan_mid_viability : List (String × Bool) := [("ApproachFast", false), ("ApproachSlow", false), ("Hold", true)]

/-- `refinement_ladder_rover_rung1_2to3`. -/
def refinement_ladder_rover_rung1_2to3_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `refinement_ladder_rover_rung2_3to6`. -/
def refinement_ladder_rover_rung2_3to6_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `refinement_ladder_rover_rung2_6dof`. -/
def refinement_ladder_rover_rung2_6dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `refinement_ladder_rover_rung2b_6dof`. -/
def refinement_ladder_rover_rung2b_6dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `refinement_ladder_rover_rung2c_6dof`. -/
def refinement_ladder_rover_rung2c_6dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `refinement_ladder_rover_rung3_6to8`. -/
def refinement_ladder_rover_rung3_6to8_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `refinement_ladder_rover_rung4_8to12`. -/
def refinement_ladder_rover_rung4_8to12_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `robot_braking`. -/
def robot_braking_viability : List (String × Bool) := [("FAST", false), ("MID", false), ("SLOW", true)]

/-- `rover3_M1`. -/
def rover3_M1_viability : List (String × Bool) := [("Recover", false), ("Drive", false), ("Safe", false)]

/-- `rover3tier_M1`. -/
def rover3tier_M1_viability : List (String × Bool) := [("ACCEL", false), ("COAST", false)]

/-- `rover3tier_rung12`. -/
def rover3tier_rung12_viability : List (String × Bool) := [("ACCEL", false), ("COAST", false)]

/-- `rover_4d_box`. -/
def rover_4d_box_viability : List (String × Bool) := [("APPROACH", true), ("SETTLE", false)]

/-- `rover_attitude_cone_12dof`. -/
def rover_attitude_cone_12dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `rover_coupled`. -/
def rover_coupled_viability : List (String × Bool) := [("Recover", false), ("Drive", false), ("Safe", false)]

/-- `rover_dof_terrain_rung1`. -/
def rover_dof_terrain_rung1_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `rover_dof_terrain_rung2`. -/
def rover_dof_terrain_rung2_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `rover_dof_terrain_rung3`. -/
def rover_dof_terrain_rung3_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `rover_dof_terrain_rung3_8d`. -/
def rover_dof_terrain_rung3_8d_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `rover_drag`. -/
def rover_drag_viability : List (String × Bool) := [("Track", true)]

/-- `rover_position`. -/
def rover_position_viability : List (String × Bool) := [("Recover", false), ("Drive", false), ("Safe", false)]

/-- `rover_terrain_M1`. -/
def rover_terrain_M1_viability : List (String × Bool) := [("ROUGH", false), ("FLAT", false), ("SMOOTH", false)]

/-- `rover_tier_r1`. -/
def rover_tier_r1_viability : List (String × Bool) := [("Cruise", false)]

/-- `story1_attdist_rung_a_6to8`. -/
def story1_attdist_rung_a_6to8_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `story1_attdist_rung_b_12dof`. -/
def story1_attdist_rung_b_12dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `story2_lateral_rung_a_8dof`. -/
def story2_lateral_rung_a_8dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `story2_lateral_rung_b_12dof`. -/
def story2_lateral_rung_b_12dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `story3_rollover_base_12dof`. -/
def story3_rollover_base_12dof_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `story3_rollover_ladder_rung_a`. -/
def story3_rollover_ladder_rung_a_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `story3_rollover_ladder_rung_b`. -/
def story3_rollover_ladder_rung_b_viability : List (String × Bool) := [("STEEP", false), ("MODER", false), ("FLAT", false)]

/-- `watertank`. -/
def watertank_viability : List (String × Bool) := [("Low", true), ("Mid", false), ("High", true)]

end RelCertifier
