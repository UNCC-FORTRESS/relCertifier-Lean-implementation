/- suite_v2 pre-landing-record aggregator (GENERATED — `scripts/gen_v2_data.py`): the
pre-landing records of every benchmark (`docs/PRELANDING.md`; the pre-landing
certificate is on for every benchmark; a record without nodes is empty). -/
import RelCertifier.Trusted.PrelandEmit
import RelCertifier.InstancesV2.BenchPrelanding.acc_spoof_lag
import RelCertifier.InstancesV2.BenchPrelanding.acc_spoof_limp
import RelCertifier.InstancesV2.BenchPrelanding.acc_tune_lag
import RelCertifier.InstancesV2.BenchPrelanding.acc_tune_limp
import RelCertifier.InstancesV2.BenchPrelanding.antenna_track_kvretune
import RelCertifier.InstancesV2.BenchPrelanding.autoclave_liquid_steambank
import RelCertifier.InstancesV2.BenchPrelanding.boiler_purge_vfd
import RelCertifier.InstancesV2.BenchPrelanding.bottling_fill_strainer
import RelCertifier.InstancesV2.BenchPrelanding.canal_gate_notches
import RelCertifier.InstancesV2.BenchPrelanding.elevator_start_discbrake
import RelCertifier.InstancesV2.BenchPrelanding.engine_start_highidle
import RelCertifier.InstancesV2.BenchPrelanding.extruder_pe100_manualstart
import RelCertifier.InstancesV2.BenchPrelanding.flaps_slow_approach
import RelCertifier.InstancesV2.BenchPrelanding.furnace_program_timebase
import RelCertifier.InstancesV2.BenchPrelanding.gantry_speed_zones
import RelCertifier.InstancesV2.BenchPrelanding.h2_refuel_ambientbias
import RelCertifier.InstancesV2.BenchPrelanding.hydro_rejection_gatecal
import RelCertifier.InstancesV2.BenchPrelanding.lit_csf21_vehicle_bus
import RelCertifier.InstancesV2.BenchPrelanding.lit_csf21_vehicle_thermo
import RelCertifier.InstancesV2.BenchPrelanding.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchPrelanding.lit_drl_lane_control
import RelCertifier.InstancesV2.BenchPrelanding.lit_freedm_meter
import RelCertifier.InstancesV2.BenchPrelanding.lit_girard08_robot
import RelCertifier.InstancesV2.BenchPrelanding.lit_gpt10_boost_converter
import RelCertifier.InstancesV2.BenchPrelanding.lit_lz21_vehicle_position
import RelCertifier.InstancesV2.BenchPrelanding.lit_nahs25_engine_cooling
import RelCertifier.InstancesV2.BenchPrelanding.lit_nahs25_salt_tank
import RelCertifier.InstancesV2.BenchPrelanding.molding_pack_checkring
import RelCertifier.InstancesV2.BenchPrelanding.platoon_linkloss
import RelCertifier.InstancesV2.BenchPrelanding.platoon_profiles
import RelCertifier.InstancesV2.BenchPrelanding.quad_light_lag
import RelCertifier.InstancesV2.BenchPrelanding.quad_light_profiles
import RelCertifier.InstancesV2.BenchPrelanding.rampmeter_poll_2to1
import RelCertifier.InstancesV2.BenchPrelanding.reactor_feed_wireless
import RelCertifier.InstancesV2.BenchPrelanding.rover_terrain_2to4
import RelCertifier.InstancesV2.BenchPrelanding.rover_terrain_4to6
import RelCertifier.InstancesV2.BenchPrelanding.sat3w_detumble_phases
import RelCertifier.InstancesV2.BenchPrelanding.sat_detumble_phases
import RelCertifier.InstancesV2.BenchPrelanding.sat_detumble_weak
import RelCertifier.InstancesV2.BenchPrelanding.stopline_drag
import RelCertifier.InstancesV2.BenchPrelanding.stopline_friction
import RelCertifier.InstancesV2.BenchPrelanding.stopline_lag
import RelCertifier.InstancesV2.BenchPrelanding.stopline_tyre
import RelCertifier.InstancesV2.BenchPrelanding.syringe_relay_prearm
import RelCertifier.InstancesV2.BenchPrelanding.tank_dos_3to1
import RelCertifier.InstancesV2.BenchPrelanding.train_ato_odometry
import RelCertifier.InstancesV2.BenchPrelanding.turbine_startup_gearratio
import RelCertifier.InstancesV2.BenchPrelanding.ventilator_vc_cuffleak
import RelCertifier.InstancesV2.BenchPrelanding.watertank
import RelCertifier.InstancesV2.BenchPrelanding.watertank_twospeed

namespace RelCertifier.Preland

def prelandTableV2 : List (String × PrelandEmitE) := [
  ("acc_spoof_lag", acc_spoof_lag_coverV2_prelanding),

  ("acc_spoof_limp", acc_spoof_limp_coverV2_prelanding),

  ("acc_tune_lag", acc_tune_lag_coverV2_prelanding),

  ("acc_tune_limp", acc_tune_limp_coverV2_prelanding),

  ("antenna_track_kvretune", antenna_track_kvretune_coverV2_prelanding),

  ("autoclave_liquid_steambank", autoclave_liquid_steambank_coverV2_prelanding),

  ("boiler_purge_vfd", boiler_purge_vfd_coverV2_prelanding),

  ("bottling_fill_strainer", bottling_fill_strainer_coverV2_prelanding),

  ("canal_gate_notches", canal_gate_notches_coverV2_prelanding),

  ("elevator_start_discbrake", elevator_start_discbrake_coverV2_prelanding),

  ("engine_start_highidle", engine_start_highidle_coverV2_prelanding),

  ("extruder_pe100_manualstart", extruder_pe100_manualstart_coverV2_prelanding),

  ("flaps_slow_approach", flaps_slow_approach_coverV2_prelanding),

  ("furnace_program_timebase", furnace_program_timebase_coverV2_prelanding),

  ("gantry_speed_zones", gantry_speed_zones_coverV2_prelanding),

  ("h2_refuel_ambientbias", h2_refuel_ambientbias_coverV2_prelanding),

  ("hydro_rejection_gatecal", hydro_rejection_gatecal_coverV2_prelanding),

  ("lit_csf21_vehicle_bus", lit_csf21_vehicle_bus_coverV2_prelanding),

  ("lit_csf21_vehicle_thermo", lit_csf21_vehicle_thermo_coverV2_prelanding),

  ("lit_csf25_salt_tank_hold", lit_csf25_salt_tank_hold_coverV2_prelanding),

  ("lit_drl_lane_control", lit_drl_lane_control_coverV2_prelanding),

  ("lit_freedm_meter", lit_freedm_meter_coverV2_prelanding),

  ("lit_girard08_robot", lit_girard08_robot_coverV2_prelanding),

  ("lit_gpt10_boost_converter", lit_gpt10_boost_converter_coverV2_prelanding),

  ("lit_lz21_vehicle_position", lit_lz21_vehicle_position_coverV2_prelanding),

  ("lit_nahs25_engine_cooling", lit_nahs25_engine_cooling_coverV2_prelanding),

  ("lit_nahs25_salt_tank", lit_nahs25_salt_tank_coverV2_prelanding),

  ("molding_pack_checkring", molding_pack_checkring_coverV2_prelanding),

  ("platoon_linkloss", platoon_linkloss_coverV2_prelanding),

  ("platoon_profiles", platoon_profiles_coverV2_prelanding),

  ("quad_light_lag", quad_light_lag_coverV2_prelanding),

  ("quad_light_profiles", quad_light_profiles_coverV2_prelanding),

  ("rampmeter_poll_2to1", rampmeter_poll_2to1_coverV2_prelanding),

  ("reactor_feed_wireless", reactor_feed_wireless_coverV2_prelanding),

  ("rover_terrain_2to4", rover_terrain_2to4_coverV2_prelanding),

  ("rover_terrain_4to6", rover_terrain_4to6_coverV2_prelanding),

  ("sat3w_detumble_phases", sat3w_detumble_phases_coverV2_prelanding),

  ("sat_detumble_phases", sat_detumble_phases_coverV2_prelanding),

  ("sat_detumble_weak", sat_detumble_weak_coverV2_prelanding),

  ("stopline_drag", stopline_drag_coverV2_prelanding),

  ("stopline_friction", stopline_friction_coverV2_prelanding),

  ("stopline_lag", stopline_lag_coverV2_prelanding),

  ("stopline_tyre", stopline_tyre_coverV2_prelanding),

  ("syringe_relay_prearm", syringe_relay_prearm_coverV2_prelanding),

  ("tank_dos_3to1", tank_dos_3to1_coverV2_prelanding),

  ("train_ato_odometry", train_ato_odometry_coverV2_prelanding),

  ("turbine_startup_gearratio", turbine_startup_gearratio_coverV2_prelanding),

  ("ventilator_vc_cuffleak", ventilator_vc_cuffleak_coverV2_prelanding),

  ("watertank", watertank_coverV2_prelanding),

  ("watertank_twospeed", watertank_twospeed_coverV2_prelanding) ]

end RelCertifier.Preland
