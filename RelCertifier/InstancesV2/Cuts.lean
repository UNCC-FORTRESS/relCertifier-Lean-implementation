/- suite_v2 cut-certificate aggregator (GENERATED — `scripts/gen_v2_data.py`). -/
import RelCertifier.InstancesV2.Cuts.acc_spoof_lag
import RelCertifier.InstancesV2.Cuts.acc_spoof_limp
import RelCertifier.InstancesV2.Cuts.acc_tune_lag
import RelCertifier.InstancesV2.Cuts.acc_tune_limp
import RelCertifier.InstancesV2.Cuts.arm_plateau_crit
import RelCertifier.InstancesV2.Cuts.arm_plateau_profiles
import RelCertifier.InstancesV2.Cuts.arm_plateau_slow
import RelCertifier.InstancesV2.Cuts.charger_fast_setpoints
import RelCertifier.InstancesV2.Cuts.charger_fast_tapers
import RelCertifier.InstancesV2.Cuts.match_multi_rate
import RelCertifier.InstancesV2.Cuts.platoon3_linkloss
import RelCertifier.InstancesV2.Cuts.platoon3_profiles
import RelCertifier.InstancesV2.Cuts.platoon_delay_linkloss
import RelCertifier.InstancesV2.Cuts.platoon_delay_profiles
import RelCertifier.InstancesV2.Cuts.quad_light_airframe_20
import RelCertifier.InstancesV2.Cuts.quad_light_lag
import RelCertifier.InstancesV2.Cuts.quad_light_profiles
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung1_2to3
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung2_3to6
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung2_6dof
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung2b_6dof
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung2c_6dof
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung3_6to8
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung4_8to12
import RelCertifier.InstancesV2.Cuts.rover3tier_rung12
import RelCertifier.InstancesV2.Cuts.rover_dof_terrain_rung1
import RelCertifier.InstancesV2.Cuts.rover_dof_terrain_rung2
import RelCertifier.InstancesV2.Cuts.rover_dof_terrain_rung3
import RelCertifier.InstancesV2.Cuts.rover_dof_terrain_rung3_8d
import RelCertifier.InstancesV2.Cuts.rover_patrol_refine
import RelCertifier.InstancesV2.Cuts.rover_patrol_zones
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_nominal
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_weak
import RelCertifier.InstancesV2.Cuts.sat_detumble_nominal
import RelCertifier.InstancesV2.Cuts.sat_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat_detumble_weak
import RelCertifier.InstancesV2.Cuts.story1_attdist_rung_a_6to8
import RelCertifier.InstancesV2.Cuts.story1_attdist_rung_b_12dof
import RelCertifier.InstancesV2.Cuts.story2_lateral_rung_a_8dof
import RelCertifier.InstancesV2.Cuts.story2_lateral_rung_b_12dof
import RelCertifier.InstancesV2.Cuts.story3_rollover_base_12dof
import RelCertifier.InstancesV2.Cuts.story3_rollover_ladder_rung_a
import RelCertifier.InstancesV2.Cuts.story3_rollover_ladder_rung_b
import RelCertifier.InstancesV2.Cuts.watertank

namespace RelCertifier.Oracle

def cutTableV2 : List (String × EvolStrengthening × EvolStrengtheningX) := [
  ("acc_spoof_lag", acc_spoof_lag_cutsV2, acc_spoof_lag_cutsV2X),
  ("acc_spoof_limp", acc_spoof_limp_cutsV2, acc_spoof_limp_cutsV2X),
  ("acc_tune_lag", acc_tune_lag_cutsV2, acc_tune_lag_cutsV2X),
  ("acc_tune_limp", acc_tune_limp_cutsV2, acc_tune_limp_cutsV2X),
  ("arm_plateau_crit", arm_plateau_crit_cutsV2, arm_plateau_crit_cutsV2X),
  ("arm_plateau_profiles", arm_plateau_profiles_cutsV2, arm_plateau_profiles_cutsV2X),
  ("arm_plateau_slow", arm_plateau_slow_cutsV2, arm_plateau_slow_cutsV2X),
  ("charger_fast_setpoints", charger_fast_setpoints_cutsV2, charger_fast_setpoints_cutsV2X),
  ("charger_fast_tapers", charger_fast_tapers_cutsV2, charger_fast_tapers_cutsV2X),
  ("match_multi_rate", match_multi_rate_cutsV2, match_multi_rate_cutsV2X),
  ("platoon3_linkloss", platoon3_linkloss_cutsV2, platoon3_linkloss_cutsV2X),
  ("platoon3_profiles", platoon3_profiles_cutsV2, platoon3_profiles_cutsV2X),
  ("platoon_delay_linkloss", platoon_delay_linkloss_cutsV2, platoon_delay_linkloss_cutsV2X),
  ("platoon_delay_profiles", platoon_delay_profiles_cutsV2, platoon_delay_profiles_cutsV2X),
  ("quad_light_airframe_20", quad_light_airframe_20_cutsV2, quad_light_airframe_20_cutsV2X),
  ("quad_light_lag", quad_light_lag_cutsV2, quad_light_lag_cutsV2X),
  ("quad_light_profiles", quad_light_profiles_cutsV2, quad_light_profiles_cutsV2X),
  ("refinement_ladder_rover_rung1_2to3", refinement_ladder_rover_rung1_2to3_cutsV2, refinement_ladder_rover_rung1_2to3_cutsV2X),
  ("refinement_ladder_rover_rung2_3to6", refinement_ladder_rover_rung2_3to6_cutsV2, refinement_ladder_rover_rung2_3to6_cutsV2X),
  ("refinement_ladder_rover_rung2_6dof", refinement_ladder_rover_rung2_6dof_cutsV2, refinement_ladder_rover_rung2_6dof_cutsV2X),
  ("refinement_ladder_rover_rung2b_6dof", refinement_ladder_rover_rung2b_6dof_cutsV2, refinement_ladder_rover_rung2b_6dof_cutsV2X),
  ("refinement_ladder_rover_rung2c_6dof", refinement_ladder_rover_rung2c_6dof_cutsV2, refinement_ladder_rover_rung2c_6dof_cutsV2X),
  ("refinement_ladder_rover_rung3_6to8", refinement_ladder_rover_rung3_6to8_cutsV2, refinement_ladder_rover_rung3_6to8_cutsV2X),
  ("refinement_ladder_rover_rung4_8to12", refinement_ladder_rover_rung4_8to12_cutsV2, refinement_ladder_rover_rung4_8to12_cutsV2X),
  ("rover3tier_rung12", rover3tier_rung12_cutsV2, rover3tier_rung12_cutsV2X),
  ("rover_dof_terrain_rung1", rover_dof_terrain_rung1_cutsV2, rover_dof_terrain_rung1_cutsV2X),
  ("rover_dof_terrain_rung2", rover_dof_terrain_rung2_cutsV2, rover_dof_terrain_rung2_cutsV2X),
  ("rover_dof_terrain_rung3", rover_dof_terrain_rung3_cutsV2, rover_dof_terrain_rung3_cutsV2X),
  ("rover_dof_terrain_rung3_8d", rover_dof_terrain_rung3_8d_cutsV2, rover_dof_terrain_rung3_8d_cutsV2X),
  ("rover_patrol_refine", rover_patrol_refine_cutsV2, rover_patrol_refine_cutsV2X),
  ("rover_patrol_zones", rover_patrol_zones_cutsV2, rover_patrol_zones_cutsV2X),
  ("sat3w_detumble_nominal", sat3w_detumble_nominal_cutsV2, sat3w_detumble_nominal_cutsV2X),
  ("sat3w_detumble_phases", sat3w_detumble_phases_cutsV2, sat3w_detumble_phases_cutsV2X),
  ("sat3w_detumble_weak", sat3w_detumble_weak_cutsV2, sat3w_detumble_weak_cutsV2X),
  ("sat_detumble_nominal", sat_detumble_nominal_cutsV2, sat_detumble_nominal_cutsV2X),
  ("sat_detumble_phases", sat_detumble_phases_cutsV2, sat_detumble_phases_cutsV2X),
  ("sat_detumble_weak", sat_detumble_weak_cutsV2, sat_detumble_weak_cutsV2X),
  ("story1_attdist_rung_a_6to8", story1_attdist_rung_a_6to8_cutsV2, story1_attdist_rung_a_6to8_cutsV2X),
  ("story1_attdist_rung_b_12dof", story1_attdist_rung_b_12dof_cutsV2, story1_attdist_rung_b_12dof_cutsV2X),
  ("story2_lateral_rung_a_8dof", story2_lateral_rung_a_8dof_cutsV2, story2_lateral_rung_a_8dof_cutsV2X),
  ("story2_lateral_rung_b_12dof", story2_lateral_rung_b_12dof_cutsV2, story2_lateral_rung_b_12dof_cutsV2X),
  ("story3_rollover_base_12dof", story3_rollover_base_12dof_cutsV2, story3_rollover_base_12dof_cutsV2X),
  ("story3_rollover_ladder_rung_a", story3_rollover_ladder_rung_a_cutsV2, story3_rollover_ladder_rung_a_cutsV2X),
  ("story3_rollover_ladder_rung_b", story3_rollover_ladder_rung_b_cutsV2, story3_rollover_ladder_rung_b_cutsV2X),
  ("watertank", watertank_cutsV2, watertank_cutsV2X) ]

end RelCertifier.Oracle
