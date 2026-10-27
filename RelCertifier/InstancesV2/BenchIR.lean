/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# suite_v2 IR aggregator + `benchIRTableV2` (GENERATED — `scripts/gen_v2_data.py`)

The parser-emitted literals of `benchmarks/suite_v2`. `relcert-test`'s drift check
(`[ir-drift-v2]`) re-parses `benchmarks/suite_v2/<name>/input.txt` for every entry and
compares it with the literal of the same name in `benchIRTableV2`.
-/
import RelCertifier.InstancesV2.BenchIR.acc_spoof_lag
import RelCertifier.InstancesV2.BenchIR.acc_spoof_limp
import RelCertifier.InstancesV2.BenchIR.acc_tune_lag
import RelCertifier.InstancesV2.BenchIR.acc_tune_limp
import RelCertifier.InstancesV2.BenchIR.arm_plateau_crit
import RelCertifier.InstancesV2.BenchIR.arm_plateau_slow
import RelCertifier.InstancesV2.BenchIR.charger_fast_setpoints
import RelCertifier.InstancesV2.BenchIR.charger_fast_tapers
import RelCertifier.InstancesV2.BenchIR.drl_car_stop
import RelCertifier.InstancesV2.BenchIR.drl_lane_control
import RelCertifier.InstancesV2.BenchIR.engine_start_highidle
import RelCertifier.InstancesV2.BenchIR.freedm_meter
import RelCertifier.InstancesV2.BenchIR.hvac_fan_staging
import RelCertifier.InstancesV2.BenchIR.match_multi_rate
import RelCertifier.InstancesV2.BenchIR.platoon_delay_profiles
import RelCertifier.InstancesV2.BenchIR.platoon_latency
import RelCertifier.InstancesV2.BenchIR.platoon_linkloss
import RelCertifier.InstancesV2.BenchIR.quad_light_airframe_20
import RelCertifier.InstancesV2.BenchIR.quad_light_lag
import RelCertifier.InstancesV2.BenchIR.quad_light_profiles
import RelCertifier.InstancesV2.BenchIR.rover_attitude_6to8
import RelCertifier.InstancesV2.BenchIR.rover_attitude_8to12
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to3
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to4
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to6
import RelCertifier.InstancesV2.BenchIR.rover_ladder_3to6
import RelCertifier.InstancesV2.BenchIR.rover_ladder_6to8
import RelCertifier.InstancesV2.BenchIR.rover_ladder_8to12
import RelCertifier.InstancesV2.BenchIR.rover_lateral_6to8
import RelCertifier.InstancesV2.BenchIR.rover_lateral_8to12
import RelCertifier.InstancesV2.BenchIR.rover_patrol_lag
import RelCertifier.InstancesV2.BenchIR.rover_patrol_zones
import RelCertifier.InstancesV2.BenchIR.rover_rollover_6to12
import RelCertifier.InstancesV2.BenchIR.rover_rollover_6to7
import RelCertifier.InstancesV2.BenchIR.rover_rollover_7to12
import RelCertifier.InstancesV2.BenchIR.rover_terrain_2to4
import RelCertifier.InstancesV2.BenchIR.rover_terrain_4to6
import RelCertifier.InstancesV2.BenchIR.rover_terrain_6to12
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_nominal
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_weak
import RelCertifier.InstancesV2.BenchIR.sat_detumble_nominal
import RelCertifier.InstancesV2.BenchIR.sat_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat_detumble_weak
import RelCertifier.InstancesV2.BenchIR.tank_dos_3to1
import RelCertifier.InstancesV2.BenchIR.train_ato_odometry
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
  ("arm_plateau_slow", arm_plateau_slow_IRv2),
  ("charger_fast_setpoints", charger_fast_setpoints_IRv2),
  ("charger_fast_tapers", charger_fast_tapers_IRv2),
  ("drl_car_stop", drl_car_stop_IRv2),
  ("drl_lane_control", drl_lane_control_IRv2),
  ("engine_start_highidle", engine_start_highidle_IRv2),
  ("freedm_meter", freedm_meter_IRv2),
  ("hvac_fan_staging", hvac_fan_staging_IRv2),
  ("match_multi_rate", match_multi_rate_IRv2),
  ("platoon_delay_profiles", platoon_delay_profiles_IRv2),
  ("platoon_latency", platoon_latency_IRv2),
  ("platoon_linkloss", platoon_linkloss_IRv2),
  ("quad_light_airframe_20", quad_light_airframe_20_IRv2),
  ("quad_light_lag", quad_light_lag_IRv2),
  ("quad_light_profiles", quad_light_profiles_IRv2),
  ("rover_attitude_6to8", rover_attitude_6to8_IRv2),
  ("rover_attitude_8to12", rover_attitude_8to12_IRv2),
  ("rover_ladder_2to3", rover_ladder_2to3_IRv2),
  ("rover_ladder_2to4", rover_ladder_2to4_IRv2),
  ("rover_ladder_2to6", rover_ladder_2to6_IRv2),
  ("rover_ladder_3to6", rover_ladder_3to6_IRv2),
  ("rover_ladder_6to8", rover_ladder_6to8_IRv2),
  ("rover_ladder_8to12", rover_ladder_8to12_IRv2),
  ("rover_lateral_6to8", rover_lateral_6to8_IRv2),
  ("rover_lateral_8to12", rover_lateral_8to12_IRv2),
  ("rover_patrol_lag", rover_patrol_lag_IRv2),
  ("rover_patrol_zones", rover_patrol_zones_IRv2),
  ("rover_rollover_6to12", rover_rollover_6to12_IRv2),
  ("rover_rollover_6to7", rover_rollover_6to7_IRv2),
  ("rover_rollover_7to12", rover_rollover_7to12_IRv2),
  ("rover_terrain_2to4", rover_terrain_2to4_IRv2),
  ("rover_terrain_4to6", rover_terrain_4to6_IRv2),
  ("rover_terrain_6to12", rover_terrain_6to12_IRv2),
  ("sat3w_detumble_nominal", sat3w_detumble_nominal_IRv2),
  ("sat3w_detumble_phases", sat3w_detumble_phases_IRv2),
  ("sat3w_detumble_weak", sat3w_detumble_weak_IRv2),
  ("sat_detumble_nominal", sat_detumble_nominal_IRv2),
  ("sat_detumble_phases", sat_detumble_phases_IRv2),
  ("sat_detumble_weak", sat_detumble_weak_IRv2),
  ("tank_dos_3to1", tank_dos_3to1_IRv2),
  ("train_ato_odometry", train_ato_odometry_IRv2),
  ("vehicle_hypercert", vehicle_hypercert_IRv2),
  ("watertank", watertank_IRv2),
  ("watertank_twospeed", watertank_twospeed_IRv2) ]

end RelCertifier.Parse
