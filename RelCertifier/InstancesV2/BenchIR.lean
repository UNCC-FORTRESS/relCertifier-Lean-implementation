/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# suite_v2 IR aggregator + `benchIRTableV2` (GENERATED — `scripts/gen_v2_data.py`)

The 45 parser-emitted literals of `benchmarks/suite_v2`. `relcert-test`'s drift check
(`[ir-drift-v2]`) re-parses `benchmarks/suite_v2/<name>/input.txt` for every entry and
compares it with the literal of the same name in `benchIRTableV2`.
-/
import RelCertifier.InstancesV2.BenchIR.acc_spoof_lag
import RelCertifier.InstancesV2.BenchIR.acc_spoof_limp
import RelCertifier.InstancesV2.BenchIR.acc_tune_lag
import RelCertifier.InstancesV2.BenchIR.acc_tune_limp
import RelCertifier.InstancesV2.BenchIR.arm_plateau_crit
import RelCertifier.InstancesV2.BenchIR.arm_plateau_profiles
import RelCertifier.InstancesV2.BenchIR.arm_plateau_slow
import RelCertifier.InstancesV2.BenchIR.charger_fast_setpoints
import RelCertifier.InstancesV2.BenchIR.charger_fast_tapers
import RelCertifier.InstancesV2.BenchIR.match_multi_rate
import RelCertifier.InstancesV2.BenchIR.platoon3_linkloss
import RelCertifier.InstancesV2.BenchIR.platoon3_profiles
import RelCertifier.InstancesV2.BenchIR.platoon_delay_linkloss
import RelCertifier.InstancesV2.BenchIR.platoon_delay_profiles
import RelCertifier.InstancesV2.BenchIR.quad_light_airframe_20
import RelCertifier.InstancesV2.BenchIR.quad_light_lag
import RelCertifier.InstancesV2.BenchIR.quad_light_profiles
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung1_2to3
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2_3to6
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2_6dof
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2b_6dof
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2c_6dof
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung3_6to8
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung4_8to12
import RelCertifier.InstancesV2.BenchIR.rover3tier_rung12
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung1
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung2
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung3
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung3_8d
import RelCertifier.InstancesV2.BenchIR.rover_patrol_refine
import RelCertifier.InstancesV2.BenchIR.rover_patrol_zones
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_nominal
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_weak
import RelCertifier.InstancesV2.BenchIR.sat_detumble_nominal
import RelCertifier.InstancesV2.BenchIR.sat_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat_detumble_weak
import RelCertifier.InstancesV2.BenchIR.story1_attdist_rung_a_6to8
import RelCertifier.InstancesV2.BenchIR.story1_attdist_rung_b_12dof
import RelCertifier.InstancesV2.BenchIR.story2_lateral_rung_a_8dof
import RelCertifier.InstancesV2.BenchIR.story2_lateral_rung_b_12dof
import RelCertifier.InstancesV2.BenchIR.story3_rollover_base_12dof
import RelCertifier.InstancesV2.BenchIR.story3_rollover_ladder_rung_a
import RelCertifier.InstancesV2.BenchIR.story3_rollover_ladder_rung_b
import RelCertifier.InstancesV2.BenchIR.watertank

namespace RelCertifier.Parse

def benchIRTableV2 : List (String × PProblem) := [
  ("acc_spoof_lag", acc_spoof_lag_IRv2),
  ("acc_spoof_limp", acc_spoof_limp_IRv2),
  ("acc_tune_lag", acc_tune_lag_IRv2),
  ("acc_tune_limp", acc_tune_limp_IRv2),
  ("arm_plateau_crit", arm_plateau_crit_IRv2),
  ("arm_plateau_profiles", arm_plateau_profiles_IRv2),
  ("arm_plateau_slow", arm_plateau_slow_IRv2),
  ("charger_fast_setpoints", charger_fast_setpoints_IRv2),
  ("charger_fast_tapers", charger_fast_tapers_IRv2),
  ("match_multi_rate", match_multi_rate_IRv2),
  ("platoon3_linkloss", platoon3_linkloss_IRv2),
  ("platoon3_profiles", platoon3_profiles_IRv2),
  ("platoon_delay_linkloss", platoon_delay_linkloss_IRv2),
  ("platoon_delay_profiles", platoon_delay_profiles_IRv2),
  ("quad_light_airframe_20", quad_light_airframe_20_IRv2),
  ("quad_light_lag", quad_light_lag_IRv2),
  ("quad_light_profiles", quad_light_profiles_IRv2),
  ("refinement_ladder_rover_rung1_2to3", refinement_ladder_rover_rung1_2to3_IRv2),
  ("refinement_ladder_rover_rung2_3to6", refinement_ladder_rover_rung2_3to6_IRv2),
  ("refinement_ladder_rover_rung2_6dof", refinement_ladder_rover_rung2_6dof_IRv2),
  ("refinement_ladder_rover_rung2b_6dof", refinement_ladder_rover_rung2b_6dof_IRv2),
  ("refinement_ladder_rover_rung2c_6dof", refinement_ladder_rover_rung2c_6dof_IRv2),
  ("refinement_ladder_rover_rung3_6to8", refinement_ladder_rover_rung3_6to8_IRv2),
  ("refinement_ladder_rover_rung4_8to12", refinement_ladder_rover_rung4_8to12_IRv2),
  ("rover3tier_rung12", rover3tier_rung12_IRv2),
  ("rover_dof_terrain_rung1", rover_dof_terrain_rung1_IRv2),
  ("rover_dof_terrain_rung2", rover_dof_terrain_rung2_IRv2),
  ("rover_dof_terrain_rung3", rover_dof_terrain_rung3_IRv2),
  ("rover_dof_terrain_rung3_8d", rover_dof_terrain_rung3_8d_IRv2),
  ("rover_patrol_refine", rover_patrol_refine_IRv2),
  ("rover_patrol_zones", rover_patrol_zones_IRv2),
  ("sat3w_detumble_nominal", sat3w_detumble_nominal_IRv2),
  ("sat3w_detumble_phases", sat3w_detumble_phases_IRv2),
  ("sat3w_detumble_weak", sat3w_detumble_weak_IRv2),
  ("sat_detumble_nominal", sat_detumble_nominal_IRv2),
  ("sat_detumble_phases", sat_detumble_phases_IRv2),
  ("sat_detumble_weak", sat_detumble_weak_IRv2),
  ("story1_attdist_rung_a_6to8", story1_attdist_rung_a_6to8_IRv2),
  ("story1_attdist_rung_b_12dof", story1_attdist_rung_b_12dof_IRv2),
  ("story2_lateral_rung_a_8dof", story2_lateral_rung_a_8dof_IRv2),
  ("story2_lateral_rung_b_12dof", story2_lateral_rung_b_12dof_IRv2),
  ("story3_rollover_base_12dof", story3_rollover_base_12dof_IRv2),
  ("story3_rollover_ladder_rung_a", story3_rollover_ladder_rung_a_IRv2),
  ("story3_rollover_ladder_rung_b", story3_rollover_ladder_rung_b_IRv2),
  ("watertank", watertank_IRv2) ]

end RelCertifier.Parse
