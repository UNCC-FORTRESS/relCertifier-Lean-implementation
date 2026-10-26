/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# suite_v2 IR aggregator + `benchIRTableV2` (GENERATED — `scripts/gen_v2_data.py`)

The 46 parser-emitted literals of `benchmarks/suite_v2`. `relcert-test`'s drift check
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
import RelCertifier.InstancesV2.BenchIR.drl_car_stop
import RelCertifier.InstancesV2.BenchIR.drl_lane_control
import RelCertifier.InstancesV2.BenchIR.freedm_meter
import RelCertifier.InstancesV2.BenchIR.match_multi_rate
import RelCertifier.InstancesV2.BenchIR.platoon3_linkloss
import RelCertifier.InstancesV2.BenchIR.platoon3_profiles
import RelCertifier.InstancesV2.BenchIR.platoon_delay_linkloss
import RelCertifier.InstancesV2.BenchIR.platoon_delay_profiles
import RelCertifier.InstancesV2.BenchIR.quad_light_airframe_20
import RelCertifier.InstancesV2.BenchIR.quad_light_lag
import RelCertifier.InstancesV2.BenchIR.quad_light_profiles
import RelCertifier.InstancesV2.BenchIR.rover3tier_rung12
import RelCertifier.InstancesV2.BenchIR.rover_attitude_6to8
import RelCertifier.InstancesV2.BenchIR.rover_attitude_8to12
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to3
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to4
import RelCertifier.InstancesV2.BenchIR.rover_ladder_3to6
import RelCertifier.InstancesV2.BenchIR.rover_ladder_4to6
import RelCertifier.InstancesV2.BenchIR.rover_ladder_4to6_kin
import RelCertifier.InstancesV2.BenchIR.rover_ladder_6to8
import RelCertifier.InstancesV2.BenchIR.rover_ladder_8to12
import RelCertifier.InstancesV2.BenchIR.rover_lateral_6to8
import RelCertifier.InstancesV2.BenchIR.rover_lateral_8to12
import RelCertifier.InstancesV2.BenchIR.rover_patrol_refine
import RelCertifier.InstancesV2.BenchIR.rover_patrol_zones
import RelCertifier.InstancesV2.BenchIR.rover_rollover_6to12
import RelCertifier.InstancesV2.BenchIR.rover_rollover_split_a
import RelCertifier.InstancesV2.BenchIR.rover_rollover_split_b
import RelCertifier.InstancesV2.BenchIR.rover_terrain_2to3
import RelCertifier.InstancesV2.BenchIR.rover_terrain_3to6
import RelCertifier.InstancesV2.BenchIR.rover_terrain_6to12
import RelCertifier.InstancesV2.BenchIR.rover_terrain_6to8
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_nominal
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_weak
import RelCertifier.InstancesV2.BenchIR.sat_detumble_nominal
import RelCertifier.InstancesV2.BenchIR.sat_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat_detumble_weak
import RelCertifier.InstancesV2.BenchIR.vehicle_hypercert
import RelCertifier.InstancesV2.BenchIR.watertank
import RelCertifier.InstancesV2.BenchIR.watertank_twospeed

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
  ("drl_car_stop", drl_car_stop_IRv2),
  ("drl_lane_control", drl_lane_control_IRv2),
  ("freedm_meter", freedm_meter_IRv2),
  ("match_multi_rate", match_multi_rate_IRv2),
  ("platoon3_linkloss", platoon3_linkloss_IRv2),
  ("platoon3_profiles", platoon3_profiles_IRv2),
  ("platoon_delay_linkloss", platoon_delay_linkloss_IRv2),
  ("platoon_delay_profiles", platoon_delay_profiles_IRv2),
  ("quad_light_airframe_20", quad_light_airframe_20_IRv2),
  ("quad_light_lag", quad_light_lag_IRv2),
  ("quad_light_profiles", quad_light_profiles_IRv2),
  ("rover3tier_rung12", rover3tier_rung12_IRv2),
  ("rover_attitude_6to8", rover_attitude_6to8_IRv2),
  ("rover_attitude_8to12", rover_attitude_8to12_IRv2),
  ("rover_ladder_2to3", rover_ladder_2to3_IRv2),
  ("rover_ladder_2to4", rover_ladder_2to4_IRv2),
  ("rover_ladder_3to6", rover_ladder_3to6_IRv2),
  ("rover_ladder_4to6", rover_ladder_4to6_IRv2),
  ("rover_ladder_4to6_kin", rover_ladder_4to6_kin_IRv2),
  ("rover_ladder_6to8", rover_ladder_6to8_IRv2),
  ("rover_ladder_8to12", rover_ladder_8to12_IRv2),
  ("rover_lateral_6to8", rover_lateral_6to8_IRv2),
  ("rover_lateral_8to12", rover_lateral_8to12_IRv2),
  ("rover_patrol_refine", rover_patrol_refine_IRv2),
  ("rover_patrol_zones", rover_patrol_zones_IRv2),
  ("rover_rollover_6to12", rover_rollover_6to12_IRv2),
  ("rover_rollover_split_a", rover_rollover_split_a_IRv2),
  ("rover_rollover_split_b", rover_rollover_split_b_IRv2),
  ("rover_terrain_2to3", rover_terrain_2to3_IRv2),
  ("rover_terrain_3to6", rover_terrain_3to6_IRv2),
  ("rover_terrain_6to12", rover_terrain_6to12_IRv2),
  ("rover_terrain_6to8", rover_terrain_6to8_IRv2),
  ("sat3w_detumble_nominal", sat3w_detumble_nominal_IRv2),
  ("sat3w_detumble_phases", sat3w_detumble_phases_IRv2),
  ("sat3w_detumble_weak", sat3w_detumble_weak_IRv2),
  ("sat_detumble_nominal", sat_detumble_nominal_IRv2),
  ("sat_detumble_phases", sat_detumble_phases_IRv2),
  ("sat_detumble_weak", sat_detumble_weak_IRv2),
  ("vehicle_hypercert", vehicle_hypercert_IRv2),
  ("watertank", watertank_IRv2),
  ("watertank_twospeed", watertank_twospeed_IRv2) ]

end RelCertifier.Parse
