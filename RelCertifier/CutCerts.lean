/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# GENERATED cut certificates (relcert --emit-cuts; do not edit)

Per benchmark: the checked-cut channel's kept atoms with their O2 routes, plus the
kernel well-formedness certificate (cutCertWF, rfl) against the parser-emitted IR.
-/
import RelCertifier.CutCertDefs
import RelCertifier.BenchIR

namespace RelCertifier.Oracle

open RelCertifier.Parse

def arm_chain_rung1_cuts : CutCert :=
  { L := [
      ("ApproachFast", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachSlow", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("Return", [])
    ]
    R := [
      ("Approach", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : cutCertWF arm_chain_rung1_IR arm_chain_rung1_cuts = true := rfl

def arm_chain_rung2_cuts : CutCert :=
  { L := [
      ("ApproachA", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachB", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("ApproachC", [((.cmp ">=" (.var "theta") (.num "0.5")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.frozen)])
    ]
    R := [
      ("ApproachFast", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachSlow", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : cutCertWF arm_chain_rung2_IR arm_chain_rung2_cuts = true := rfl

def arm_chain_rung3_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachA", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachB", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("ApproachC", [((.cmp ">=" (.var "theta") (.num "0.5")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.frozen)])
    ] }

example : cutCertWF arm_chain_rung3_IR arm_chain_rung3_cuts = true := rfl

def arm_fidelity_high_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachA", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachB", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("ApproachC", [((.cmp ">=" (.var "theta") (.num "0.5")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.frozen)])
    ] }

example : cutCertWF arm_fidelity_high_IR arm_fidelity_high_cuts = true := rfl

def arm_fidelity_low_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("Approach", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : cutCertWF arm_fidelity_low_IR arm_fidelity_low_cuts = true := rfl

def arm_fidelity_mid_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachFast", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachSlow", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.shape)])
    ] }

example : cutCertWF arm_fidelity_mid_IR arm_fidelity_mid_cuts = true := rfl

def arm_refinement_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("Approach", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : cutCertWF arm_refinement_IR arm_refinement_cuts = true := rfl

def attitude_rate_cuts : CutCert :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.var "p") (.num "0.0")), CutRoute.diStrict)])
    ]
    R := [
      ("RECOVER", [((.cmp ">=" (.var "p") (.num "0.0")), CutRoute.diStrict)]),
      ("TRACK", [((.cmp ">=" (.var "p") (.num "0.5")), CutRoute.diStrict), ((.cmp "<=" (.var "p") (.num "1.15")), CutRoute.diStrict)])
    ] }

example : cutCertWF attitude_rate_IR attitude_rate_cuts = true := rfl

def endurance_gain_M1_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "v") (.num "0.40")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.575")), CutRoute.shape)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "v") (.num "0.40")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.575")), CutRoute.shape)])
    ] }

example : cutCertWF endurance_gain_M1_IR endurance_gain_M1_cuts = true := rfl

def endurance_orderlift_1to2_cuts : CutCert :=
  { L := [
      ("STEEP", []),
      ("MODER", []),
      ("FLAT", [])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "v") (.num "0.40")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.575")), CutRoute.shape)])
    ] }

example : cutCertWF endurance_orderlift_1to2_IR endurance_orderlift_1to2_cuts = true := rfl

def endurance_orderlift_2to3_cuts : CutCert :=
  { L := [
      ("STEEP", []),
      ("MODER", []),
      ("FLAT", [])
    ]
    R := [
      ("STEEP", []),
      ("MODER", []),
      ("FLAT", [])
    ] }

example : cutCertWF endurance_orderlift_2to3_IR endurance_orderlift_2to3_cuts = true := rfl

def match_multi_eps_cuts : CutCert :=
  { L := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("COAST", [])
    ]
    R := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("COAST", [])
    ] }

example : cutCertWF match_multi_eps_IR match_multi_eps_cuts = true := rfl

def match_multi_rate_cuts : CutCert :=
  { L := [
      ("FAST", [((.cmp ">=" (.var "v") (.num "0.2")), CutRoute.shape)]),
      ("MEDIUM", [((.cmp ">=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("SLOW", [((.cmp ">=" (.var "v") (.num "0.7")), CutRoute.shape)]),
      ("RESET", [])
    ]
    R := [
      ("DRIVE", [((.cmp ">=" (.var "v") (.num "0.2")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.0")), CutRoute.shape)])
    ] }

example : cutCertWF match_multi_rate_IR match_multi_rate_cuts = true := rfl

def plant_fan_high_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachA", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachB", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("ApproachC", [((.cmp ">=" (.var "theta") (.num "0.5")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.frozen)])
    ] }

example : cutCertWF plant_fan_high_IR plant_fan_high_cuts = true := rfl

def plant_fan_low_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("Approach", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : cutCertWF plant_fan_low_IR plant_fan_low_cuts = true := rfl

def plant_fan_mid_cuts : CutCert :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachFast", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachSlow", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.shape)])
    ] }

example : cutCertWF plant_fan_mid_IR plant_fan_mid_cuts = true := rfl

def refinement_ladder_rover_rung1_2to3_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF refinement_ladder_rover_rung1_2to3_IR refinement_ladder_rover_rung1_2to3_cuts = true := rfl

def refinement_ladder_rover_rung2_3to6_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF refinement_ladder_rover_rung2_3to6_IR refinement_ladder_rover_rung2_3to6_cuts = true := rfl

def refinement_ladder_rover_rung2_6dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF refinement_ladder_rover_rung2_6dof_IR refinement_ladder_rover_rung2_6dof_cuts = true := rfl

def refinement_ladder_rover_rung2b_6dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF refinement_ladder_rover_rung2b_6dof_IR refinement_ladder_rover_rung2b_6dof_cuts = true := rfl

def refinement_ladder_rover_rung2c_6dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF refinement_ladder_rover_rung2c_6dof_IR refinement_ladder_rover_rung2c_6dof_cuts = true := rfl

def refinement_ladder_rover_rung3_6to8_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF refinement_ladder_rover_rung3_6to8_IR refinement_ladder_rover_rung3_6to8_cuts = true := rfl

def refinement_ladder_rover_rung4_8to12_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF refinement_ladder_rover_rung4_8to12_IR refinement_ladder_rover_rung4_8to12_cuts = true := rfl

def robot_braking_cuts : CutCert :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "0.8")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.2")), CutRoute.shape)])
    ]
    R := [
      ("FAST", []),
      ("MID", [((.cmp "<=" (.var "v") (.num "3.5")), CutRoute.shape)]),
      ("SLOW", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.5")), CutRoute.shape)])
    ] }

example : cutCertWF robot_braking_IR robot_braking_cuts = true := rfl

def rover3_M1_cuts : CutCert :=
  { L := [
      ("Drive", []),
      ("Drift", []),
      ("Stop", [])
    ]
    R := [
      ("Recover", [((.cmp ">=" (.var "vx") (.num "0.25")), CutRoute.diStrict)]),
      ("Drive", [((.cmp ">=" (.var "vx") (.num "0.3")), CutRoute.diStrict)]),
      ("Safe", [((.cmp ">=" (.var "vx") (.num "0.75")), CutRoute.frozen), ((.cmp "<=" (.var "vx") (.num "1.0")), CutRoute.frozen)])
    ] }

example : cutCertWF rover3_M1_IR rover3_M1_cuts = true := rfl

def rover3tier_M1_cuts : CutCert :=
  { L := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("COAST", [])
    ]
    R := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("COAST", [])
    ] }

example : cutCertWF rover3tier_M1_IR rover3tier_M1_cuts = true := rfl

def rover3tier_rung12_cuts : CutCert :=
  { L := [
      ("ACCEL", []),
      ("COAST", [])
    ]
    R := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.diStrict)]),
      ("COAST", [((.cmp ">=" (.var "v") (.num "0.6")), CutRoute.diStrict)])
    ] }

example : cutCertWF rover3tier_rung12_IR rover3tier_rung12_cuts = true := rfl

def rover_4d_box_cuts : CutCert :=
  { L := [
      ("HOLD", [((.cmp ">=" (.var "px") (.num "9.0")), CutRoute.frozen), ((.cmp "<=" (.var "px") (.num "11.0")), CutRoute.frozen)])
    ]
    R := [
      ("APPROACH", [((.cmp "<=" (.var "vx") (.num "1.5")), CutRoute.shape)]),
      ("SETTLE", [((.cmp ">=" (.var "vx") (.num "0.5")), CutRoute.frozen), ((.cmp "<=" (.var "vx") (.num "0.7")), CutRoute.frozen)])
    ] }

example : cutCertWF rover_4d_box_IR rover_4d_box_cuts = true := rfl

def rover_attitude_cone_12dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF rover_attitude_cone_12dof_IR rover_attitude_cone_12dof_cuts = true := rfl

def rover_coupled_cuts : CutCert :=
  { L := [
      ("Drive", []),
      ("Drift", []),
      ("Stop", [])
    ]
    R := [
      ("Recover", [((.cmp ">=" (.var "vx") (.num "0.25")), CutRoute.diStrict)]),
      ("Drive", [((.cmp ">=" (.var "vx") (.num "0.3")), CutRoute.diStrict)]),
      ("Safe", [((.cmp ">=" (.var "vx") (.num "0.75")), CutRoute.frozen), ((.cmp "<=" (.var "vx") (.num "1.0")), CutRoute.frozen)])
    ] }

example : cutCertWF rover_coupled_IR rover_coupled_cuts = true := rfl

def rover_dof_terrain_rung1_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF rover_dof_terrain_rung1_IR rover_dof_terrain_rung1_cuts = true := rfl

def rover_dof_terrain_rung2_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF rover_dof_terrain_rung2_IR rover_dof_terrain_rung2_cuts = true := rfl

def rover_dof_terrain_rung3_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF rover_dof_terrain_rung3_IR rover_dof_terrain_rung3_cuts = true := rfl

def rover_dof_terrain_rung3_8d_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF rover_dof_terrain_rung3_8d_IR rover_dof_terrain_rung3_8d_cuts = true := rfl

def rover_drag_cuts : CutCert :=
  { L := [
      ("Cruise", [((.cmp ">=" (.var "vx") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vx") (.num "1.21")), CutRoute.diStrict)])
    ]
    R := [
      ("Track", [((.cmp ">=" (.var "vx") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vx") (.num "1.21")), CutRoute.diStrict)])
    ] }

example : cutCertWF rover_drag_IR rover_drag_cuts = true := rfl

def rover_position_cuts : CutCert :=
  { L := [
      ("Drive", []),
      ("Drift", []),
      ("Stop", [])
    ]
    R := [
      ("Recover", [((.cmp ">=" (.var "vx") (.num "0.25")), CutRoute.diStrict)]),
      ("Drive", [((.cmp ">=" (.var "vx") (.num "0.3")), CutRoute.diStrict)]),
      ("Safe", [((.cmp ">=" (.var "vx") (.num "0.75")), CutRoute.frozen), ((.cmp "<=" (.var "vx") (.num "1.0")), CutRoute.frozen)])
    ] }

example : cutCertWF rover_position_IR rover_position_cuts = true := rfl

def rover_terrain_M1_cuts : CutCert :=
  { L := [
      ("ROUGH", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.6")), CutRoute.shape)]),
      ("SMOOTH", [((.cmp ">=" (.var "v") (.num "1.0")), CutRoute.shape)])
    ]
    R := [
      ("ROUGH", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.6")), CutRoute.shape)]),
      ("SMOOTH", [((.cmp ">=" (.var "v") (.num "1.0")), CutRoute.shape)])
    ] }

example : cutCertWF rover_terrain_M1_IR rover_terrain_M1_cuts = true := rfl

def rover_tier_r1_cuts : CutCert :=
  { L := [
      ("Cruise", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.diNonstrict)])
    ]
    R := [
      ("Cruise", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.diStrict)])
    ] }

example : cutCertWF rover_tier_r1_IR rover_tier_r1_cuts = true := rfl

def story1_attdist_rung_a_6to8_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF story1_attdist_rung_a_6to8_IR story1_attdist_rung_a_6to8_cuts = true := rfl

def story1_attdist_rung_b_12dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF story1_attdist_rung_b_12dof_IR story1_attdist_rung_b_12dof_cuts = true := rfl

def story2_lateral_rung_a_8dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF story2_lateral_rung_a_8dof_IR story2_lateral_rung_a_8dof_cuts = true := rfl

def story2_lateral_rung_b_12dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF story2_lateral_rung_b_12dof_IR story2_lateral_rung_b_12dof_cuts = true := rfl

def story3_rollover_base_12dof_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF story3_rollover_base_12dof_IR story3_rollover_base_12dof_cuts = true := rfl

def story3_rollover_ladder_rung_a_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : cutCertWF story3_rollover_ladder_rung_a_IR story3_rollover_ladder_rung_a_cuts = true := rfl

def story3_rollover_ladder_rung_b_cuts : CutCert :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

example : cutCertWF story3_rollover_ladder_rung_b_IR story3_rollover_ladder_rung_b_cuts = true := rfl

def watertank_cuts : CutCert :=
  { L := [
      ("Low", [((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.diStrict)]),
      ("Mid", [((.cmp ">=" (.var "x") (.num "13.0")), CutRoute.diStrict)]),
      ("High", [])
    ]
    R := [
      ("Low", [((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.diStrict)]),
      ("Mid", [((.cmp ">=" (.var "x") (.num "10.0")), CutRoute.diStrict)]),
      ("High", [])
    ] }

example : cutCertWF watertank_IR watertank_cuts = true := rfl

end RelCertifier.Oracle
