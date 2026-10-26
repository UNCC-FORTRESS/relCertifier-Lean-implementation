/- suite_v2 cut-certificate aggregator (GENERATED — `scripts/gen_v2_data.py`). -/
import RelCertifier.InstancesV2.Cuts.acc_spoof_lag
import RelCertifier.InstancesV2.Cuts.acc_spoof_limp
import RelCertifier.InstancesV2.Cuts.acc_tune_lag
import RelCertifier.InstancesV2.Cuts.acc_tune_limp
import RelCertifier.InstancesV2.Cuts.airheader_dos_3to1
import RelCertifier.InstancesV2.Cuts.arm_plateau_crit
import RelCertifier.InstancesV2.Cuts.arm_plateau_profiles
import RelCertifier.InstancesV2.Cuts.arm_plateau_slow
import RelCertifier.InstancesV2.Cuts.charger_fast_setpoints
import RelCertifier.InstancesV2.Cuts.charger_fast_tapers
import RelCertifier.InstancesV2.Cuts.drl_car_stop
import RelCertifier.InstancesV2.Cuts.drl_lane_control
import RelCertifier.InstancesV2.Cuts.freedm_meter
import RelCertifier.InstancesV2.Cuts.hvac_fan_staging
import RelCertifier.InstancesV2.Cuts.match_multi_rate
import RelCertifier.InstancesV2.Cuts.platoon3_linkloss
import RelCertifier.InstancesV2.Cuts.platoon3_profiles
import RelCertifier.InstancesV2.Cuts.platoon_delay_linkloss
import RelCertifier.InstancesV2.Cuts.platoon_delay_profiles
import RelCertifier.InstancesV2.Cuts.quad_light_airframe_20
import RelCertifier.InstancesV2.Cuts.quad_light_lag
import RelCertifier.InstancesV2.Cuts.quad_light_profiles
import RelCertifier.InstancesV2.Cuts.rover_attitude_6to8
import RelCertifier.InstancesV2.Cuts.rover_attitude_8to12
import RelCertifier.InstancesV2.Cuts.rover_ladder_2to3
import RelCertifier.InstancesV2.Cuts.rover_ladder_2to4
import RelCertifier.InstancesV2.Cuts.rover_ladder_2to6
import RelCertifier.InstancesV2.Cuts.rover_ladder_3to6
import RelCertifier.InstancesV2.Cuts.rover_ladder_6to8
import RelCertifier.InstancesV2.Cuts.rover_ladder_8to12
import RelCertifier.InstancesV2.Cuts.rover_lateral_6to8
import RelCertifier.InstancesV2.Cuts.rover_lateral_8to12
import RelCertifier.InstancesV2.Cuts.rover_patrol_lag
import RelCertifier.InstancesV2.Cuts.rover_patrol_zones
import RelCertifier.InstancesV2.Cuts.rover_rollover_6to12
import RelCertifier.InstancesV2.Cuts.rover_rollover_6to7
import RelCertifier.InstancesV2.Cuts.rover_rollover_7to12
import RelCertifier.InstancesV2.Cuts.rover_terrain_2to4
import RelCertifier.InstancesV2.Cuts.rover_terrain_4to6
import RelCertifier.InstancesV2.Cuts.rover_terrain_6to12
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_nominal
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_weak
import RelCertifier.InstancesV2.Cuts.sat_detumble_nominal
import RelCertifier.InstancesV2.Cuts.sat_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat_detumble_weak
import RelCertifier.InstancesV2.Cuts.tank_dos_3to1
import RelCertifier.InstancesV2.Cuts.vehicle_hypercert
import RelCertifier.InstancesV2.Cuts.watertank
import RelCertifier.InstancesV2.Cuts.watertank_twospeed

namespace RelCertifier.Oracle

def cutTableV2 : List (String × EvolStrengthening × EvolStrengtheningX) := [
  ("acc_spoof_lag", acc_spoof_lag_cutsV2, acc_spoof_lag_cutsV2X),
  ("acc_spoof_limp", acc_spoof_limp_cutsV2, acc_spoof_limp_cutsV2X),
  ("acc_tune_lag", acc_tune_lag_cutsV2, acc_tune_lag_cutsV2X),
  ("acc_tune_limp", acc_tune_limp_cutsV2, acc_tune_limp_cutsV2X),
  ("airheader_dos_3to1", airheader_dos_3to1_cutsV2, airheader_dos_3to1_cutsV2X),
  ("arm_plateau_crit", arm_plateau_crit_cutsV2, arm_plateau_crit_cutsV2X),
  ("arm_plateau_profiles", arm_plateau_profiles_cutsV2, arm_plateau_profiles_cutsV2X),
  ("arm_plateau_slow", arm_plateau_slow_cutsV2, arm_plateau_slow_cutsV2X),
  ("charger_fast_setpoints", charger_fast_setpoints_cutsV2, charger_fast_setpoints_cutsV2X),
  ("charger_fast_tapers", charger_fast_tapers_cutsV2, charger_fast_tapers_cutsV2X),
  ("drl_car_stop", drl_car_stop_cutsV2, drl_car_stop_cutsV2X),
  ("drl_lane_control", drl_lane_control_cutsV2, drl_lane_control_cutsV2X),
  ("freedm_meter", freedm_meter_cutsV2, freedm_meter_cutsV2X),
  ("hvac_fan_staging", hvac_fan_staging_cutsV2, hvac_fan_staging_cutsV2X),
  ("match_multi_rate", match_multi_rate_cutsV2, match_multi_rate_cutsV2X),
  ("platoon3_linkloss", platoon3_linkloss_cutsV2, platoon3_linkloss_cutsV2X),
  ("platoon3_profiles", platoon3_profiles_cutsV2, platoon3_profiles_cutsV2X),
  ("platoon_delay_linkloss", platoon_delay_linkloss_cutsV2, platoon_delay_linkloss_cutsV2X),
  ("platoon_delay_profiles", platoon_delay_profiles_cutsV2, platoon_delay_profiles_cutsV2X),
  ("quad_light_airframe_20", quad_light_airframe_20_cutsV2, quad_light_airframe_20_cutsV2X),
  ("quad_light_lag", quad_light_lag_cutsV2, quad_light_lag_cutsV2X),
  ("quad_light_profiles", quad_light_profiles_cutsV2, quad_light_profiles_cutsV2X),
  ("rover_attitude_6to8", rover_attitude_6to8_cutsV2, rover_attitude_6to8_cutsV2X),
  ("rover_attitude_8to12", rover_attitude_8to12_cutsV2, rover_attitude_8to12_cutsV2X),
  ("rover_ladder_2to3", rover_ladder_2to3_cutsV2, rover_ladder_2to3_cutsV2X),
  ("rover_ladder_2to4", rover_ladder_2to4_cutsV2, rover_ladder_2to4_cutsV2X),
  ("rover_ladder_2to6", rover_ladder_2to6_cutsV2, rover_ladder_2to6_cutsV2X),
  ("rover_ladder_3to6", rover_ladder_3to6_cutsV2, rover_ladder_3to6_cutsV2X),
  ("rover_ladder_6to8", rover_ladder_6to8_cutsV2, rover_ladder_6to8_cutsV2X),
  ("rover_ladder_8to12", rover_ladder_8to12_cutsV2, rover_ladder_8to12_cutsV2X),
  ("rover_lateral_6to8", rover_lateral_6to8_cutsV2, rover_lateral_6to8_cutsV2X),
  ("rover_lateral_8to12", rover_lateral_8to12_cutsV2, rover_lateral_8to12_cutsV2X),
  ("rover_patrol_lag", rover_patrol_lag_cutsV2, rover_patrol_lag_cutsV2X),
  ("rover_patrol_zones", rover_patrol_zones_cutsV2, rover_patrol_zones_cutsV2X),
  ("rover_rollover_6to12", rover_rollover_6to12_cutsV2, rover_rollover_6to12_cutsV2X),
  ("rover_rollover_6to7", rover_rollover_6to7_cutsV2, rover_rollover_6to7_cutsV2X),
  ("rover_rollover_7to12", rover_rollover_7to12_cutsV2, rover_rollover_7to12_cutsV2X),
  ("rover_terrain_2to4", rover_terrain_2to4_cutsV2, rover_terrain_2to4_cutsV2X),
  ("rover_terrain_4to6", rover_terrain_4to6_cutsV2, rover_terrain_4to6_cutsV2X),
  ("rover_terrain_6to12", rover_terrain_6to12_cutsV2, rover_terrain_6to12_cutsV2X),
  ("sat3w_detumble_nominal", sat3w_detumble_nominal_cutsV2, sat3w_detumble_nominal_cutsV2X),
  ("sat3w_detumble_phases", sat3w_detumble_phases_cutsV2, sat3w_detumble_phases_cutsV2X),
  ("sat3w_detumble_weak", sat3w_detumble_weak_cutsV2, sat3w_detumble_weak_cutsV2X),
  ("sat_detumble_nominal", sat_detumble_nominal_cutsV2, sat_detumble_nominal_cutsV2X),
  ("sat_detumble_phases", sat_detumble_phases_cutsV2, sat_detumble_phases_cutsV2X),
  ("sat_detumble_weak", sat_detumble_weak_cutsV2, sat_detumble_weak_cutsV2X),
  ("tank_dos_3to1", tank_dos_3to1_cutsV2, tank_dos_3to1_cutsV2X),
  ("vehicle_hypercert", vehicle_hypercert_cutsV2, vehicle_hypercert_cutsV2X),
  ("watertank", watertank_cutsV2, watertank_cutsV2X),
  ("watertank_twospeed", watertank_twospeed_cutsV2, watertank_twospeed_cutsV2X) ]

end RelCertifier.Oracle
