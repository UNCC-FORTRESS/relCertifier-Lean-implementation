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
import RelCertifier.InstancesV2.BenchIR.antenna_track_kvretune
import RelCertifier.InstancesV2.BenchIR.bms_chiller_undercharge
import RelCertifier.InstancesV2.BenchIR.bottling_fill_strainer
import RelCertifier.InstancesV2.BenchIR.charger_fast_tapers
import RelCertifier.InstancesV2.BenchIR.compressor_station_recycle
import RelCertifier.InstancesV2.BenchIR.csf21_vehicle_bus
import RelCertifier.InstancesV2.BenchIR.csf21_vehicle_thermo
import RelCertifier.InstancesV2.BenchIR.drl_car_stop
import RelCertifier.InstancesV2.BenchIR.drl_lane_control
import RelCertifier.InstancesV2.BenchIR.elevator_start_discbrake
import RelCertifier.InstancesV2.BenchIR.engine_start_highidle
import RelCertifier.InstancesV2.BenchIR.flaps_slow_approach
import RelCertifier.InstancesV2.BenchIR.freedm_meter
import RelCertifier.InstancesV2.BenchIR.fuelcell_chp_dos
import RelCertifier.InstancesV2.BenchIR.furnace_program_timebase
import RelCertifier.InstancesV2.BenchIR.gantry_speed_zones
import RelCertifier.InstancesV2.BenchIR.girard_robot
import RelCertifier.InstancesV2.BenchIR.grid_ffr_dos
import RelCertifier.InstancesV2.BenchIR.hydro_rejection_gatecal
import RelCertifier.InstancesV2.BenchIR.lz_vehicle_position
import RelCertifier.InstancesV2.BenchIR.molding_pack_checkring
import RelCertifier.InstancesV2.BenchIR.platoon_linkloss
import RelCertifier.InstancesV2.BenchIR.platoon_profiles
import RelCertifier.InstancesV2.BenchIR.quad_light_lag
import RelCertifier.InstancesV2.BenchIR.quad_light_profiles
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to3
import RelCertifier.InstancesV2.BenchIR.rover_ladder_3to6
import RelCertifier.InstancesV2.BenchIR.rover_ladder_6to8
import RelCertifier.InstancesV2.BenchIR.rover_ladder_8to12
import RelCertifier.InstancesV2.BenchIR.rover_patrol_lag
import RelCertifier.InstancesV2.BenchIR.rover_terrain_2to4
import RelCertifier.InstancesV2.BenchIR.rover_terrain_4to6
import RelCertifier.InstancesV2.BenchIR.rover_terrain_6to12
import RelCertifier.InstancesV2.BenchIR.salt_tank_sensor
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat_detumble_phases
import RelCertifier.InstancesV2.BenchIR.sat_detumble_weak
import RelCertifier.InstancesV2.BenchIR.syringe_relay_prearm
import RelCertifier.InstancesV2.BenchIR.tank_dos_3to1
import RelCertifier.InstancesV2.BenchIR.train_ato_odometry
import RelCertifier.InstancesV2.BenchIR.tunnel_jetfan_pairout
import RelCertifier.InstancesV2.BenchIR.turbine_startup_gearratio
import RelCertifier.InstancesV2.BenchIR.vehicle_hypercert
import RelCertifier.InstancesV2.BenchIR.ventilator_vc_cuffleak
import RelCertifier.InstancesV2.BenchIR.watertank
import RelCertifier.InstancesV2.BenchIR.watertank_twospeed

namespace RelCertifier.Parse

def benchIRTableV2 : List (String × PProblem) := [
  ("acc_spoof_lag", acc_spoof_lag_IRv2),
  ("acc_spoof_limp", acc_spoof_limp_IRv2),
  ("acc_tune_lag", acc_tune_lag_IRv2),
  ("acc_tune_limp", acc_tune_limp_IRv2),
  ("antenna_track_kvretune", antenna_track_kvretune_IRv2),
  ("bms_chiller_undercharge", bms_chiller_undercharge_IRv2),
  ("bottling_fill_strainer", bottling_fill_strainer_IRv2),
  ("charger_fast_tapers", charger_fast_tapers_IRv2),
  ("compressor_station_recycle", compressor_station_recycle_IRv2),
  ("csf21_vehicle_bus", csf21_vehicle_bus_IRv2),
  ("csf21_vehicle_thermo", csf21_vehicle_thermo_IRv2),
  ("drl_car_stop", drl_car_stop_IRv2),
  ("drl_lane_control", drl_lane_control_IRv2),
  ("elevator_start_discbrake", elevator_start_discbrake_IRv2),
  ("engine_start_highidle", engine_start_highidle_IRv2),
  ("flaps_slow_approach", flaps_slow_approach_IRv2),
  ("freedm_meter", freedm_meter_IRv2),
  ("fuelcell_chp_dos", fuelcell_chp_dos_IRv2),
  ("furnace_program_timebase", furnace_program_timebase_IRv2),
  ("gantry_speed_zones", gantry_speed_zones_IRv2),
  ("girard_robot", girard_robot_IRv2),
  ("grid_ffr_dos", grid_ffr_dos_IRv2),
  ("hydro_rejection_gatecal", hydro_rejection_gatecal_IRv2),
  ("lz_vehicle_position", lz_vehicle_position_IRv2),
  ("molding_pack_checkring", molding_pack_checkring_IRv2),
  ("platoon_linkloss", platoon_linkloss_IRv2),
  ("platoon_profiles", platoon_profiles_IRv2),
  ("quad_light_lag", quad_light_lag_IRv2),
  ("quad_light_profiles", quad_light_profiles_IRv2),
  ("rover_ladder_2to3", rover_ladder_2to3_IRv2),
  ("rover_ladder_3to6", rover_ladder_3to6_IRv2),
  ("rover_ladder_6to8", rover_ladder_6to8_IRv2),
  ("rover_ladder_8to12", rover_ladder_8to12_IRv2),
  ("rover_patrol_lag", rover_patrol_lag_IRv2),
  ("rover_terrain_2to4", rover_terrain_2to4_IRv2),
  ("rover_terrain_4to6", rover_terrain_4to6_IRv2),
  ("rover_terrain_6to12", rover_terrain_6to12_IRv2),
  ("salt_tank_sensor", salt_tank_sensor_IRv2),
  ("sat3w_detumble_phases", sat3w_detumble_phases_IRv2),
  ("sat_detumble_phases", sat_detumble_phases_IRv2),
  ("sat_detumble_weak", sat_detumble_weak_IRv2),
  ("syringe_relay_prearm", syringe_relay_prearm_IRv2),
  ("tank_dos_3to1", tank_dos_3to1_IRv2),
  ("train_ato_odometry", train_ato_odometry_IRv2),
  ("tunnel_jetfan_pairout", tunnel_jetfan_pairout_IRv2),
  ("turbine_startup_gearratio", turbine_startup_gearratio_IRv2),
  ("vehicle_hypercert", vehicle_hypercert_IRv2),
  ("ventilator_vc_cuffleak", ventilator_vc_cuffleak_IRv2),
  ("watertank", watertank_IRv2),
  ("watertank_twospeed", watertank_twospeed_IRv2) ]

end RelCertifier.Parse
