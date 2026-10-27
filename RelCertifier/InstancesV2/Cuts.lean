/- suite_v2 cut-certificate aggregator (GENERATED — `scripts/gen_v2_data.py`). -/
import RelCertifier.InstancesV2.Cuts.acc_spoof_lag
import RelCertifier.InstancesV2.Cuts.acc_spoof_limp
import RelCertifier.InstancesV2.Cuts.acc_tune_lag
import RelCertifier.InstancesV2.Cuts.acc_tune_limp
import RelCertifier.InstancesV2.Cuts.antenna_track_kvretune
import RelCertifier.InstancesV2.Cuts.bms_chiller_undercharge
import RelCertifier.InstancesV2.Cuts.bottling_fill_strainer
import RelCertifier.InstancesV2.Cuts.canal_gate_notches
import RelCertifier.InstancesV2.Cuts.charger_fast_tapers
import RelCertifier.InstancesV2.Cuts.compressor_station_recycle
import RelCertifier.InstancesV2.Cuts.drl_car_stop
import RelCertifier.InstancesV2.Cuts.drl_lane_control
import RelCertifier.InstancesV2.Cuts.elevator_start_discbrake
import RelCertifier.InstancesV2.Cuts.engine_start_highidle
import RelCertifier.InstancesV2.Cuts.flaps_slow_approach
import RelCertifier.InstancesV2.Cuts.freedm_meter
import RelCertifier.InstancesV2.Cuts.fuelcell_chp_dos
import RelCertifier.InstancesV2.Cuts.furnace_program_timebase
import RelCertifier.InstancesV2.Cuts.gantry_speed_zones
import RelCertifier.InstancesV2.Cuts.hvac_fan_staging
import RelCertifier.InstancesV2.Cuts.hydro_rejection_gatecal
import RelCertifier.InstancesV2.Cuts.insulin_basal_cgmloss
import RelCertifier.InstancesV2.Cuts.molding_pack_checkring
import RelCertifier.InstancesV2.Cuts.platoon_latency
import RelCertifier.InstancesV2.Cuts.platoon_linkloss
import RelCertifier.InstancesV2.Cuts.platoon_profiles
import RelCertifier.InstancesV2.Cuts.quad_light_lag
import RelCertifier.InstancesV2.Cuts.quad_light_profiles
import RelCertifier.InstancesV2.Cuts.rampmeter_poll_2to1
import RelCertifier.InstancesV2.Cuts.rover_ladder_2to3
import RelCertifier.InstancesV2.Cuts.rover_ladder_3to6
import RelCertifier.InstancesV2.Cuts.rover_ladder_6to8
import RelCertifier.InstancesV2.Cuts.rover_ladder_8to12
import RelCertifier.InstancesV2.Cuts.rover_patrol_lag
import RelCertifier.InstancesV2.Cuts.rover_rollover_payload
import RelCertifier.InstancesV2.Cuts.rover_terrain_2to4
import RelCertifier.InstancesV2.Cuts.rover_terrain_4to6
import RelCertifier.InstancesV2.Cuts.rover_terrain_6to12
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat_detumble_weak
import RelCertifier.InstancesV2.Cuts.syringe_relay_prearm
import RelCertifier.InstancesV2.Cuts.tank_dos_3to1
import RelCertifier.InstancesV2.Cuts.train_ato_odometry
import RelCertifier.InstancesV2.Cuts.tunnel_jetfan_pairout
import RelCertifier.InstancesV2.Cuts.turbine_startup_gearratio
import RelCertifier.InstancesV2.Cuts.vehicle_hypercert
import RelCertifier.InstancesV2.Cuts.ventilator_vc_cuffleak
import RelCertifier.InstancesV2.Cuts.watertank
import RelCertifier.InstancesV2.Cuts.watertank_twospeed

namespace RelCertifier.Oracle

def cutTableV2 : List (String × EvolStrengthening × EvolStrengtheningX) := [
  ("acc_spoof_lag", acc_spoof_lag_cutsV2, acc_spoof_lag_cutsV2X),
  ("acc_spoof_limp", acc_spoof_limp_cutsV2, acc_spoof_limp_cutsV2X),
  ("acc_tune_lag", acc_tune_lag_cutsV2, acc_tune_lag_cutsV2X),
  ("acc_tune_limp", acc_tune_limp_cutsV2, acc_tune_limp_cutsV2X),
  ("antenna_track_kvretune", antenna_track_kvretune_cutsV2, antenna_track_kvretune_cutsV2X),
  ("bms_chiller_undercharge", bms_chiller_undercharge_cutsV2, bms_chiller_undercharge_cutsV2X),
  ("bottling_fill_strainer", bottling_fill_strainer_cutsV2, bottling_fill_strainer_cutsV2X),
  ("canal_gate_notches", canal_gate_notches_cutsV2, canal_gate_notches_cutsV2X),
  ("charger_fast_tapers", charger_fast_tapers_cutsV2, charger_fast_tapers_cutsV2X),
  ("compressor_station_recycle", compressor_station_recycle_cutsV2, compressor_station_recycle_cutsV2X),
  ("drl_car_stop", drl_car_stop_cutsV2, drl_car_stop_cutsV2X),
  ("drl_lane_control", drl_lane_control_cutsV2, drl_lane_control_cutsV2X),
  ("elevator_start_discbrake", elevator_start_discbrake_cutsV2, elevator_start_discbrake_cutsV2X),
  ("engine_start_highidle", engine_start_highidle_cutsV2, engine_start_highidle_cutsV2X),
  ("flaps_slow_approach", flaps_slow_approach_cutsV2, flaps_slow_approach_cutsV2X),
  ("freedm_meter", freedm_meter_cutsV2, freedm_meter_cutsV2X),
  ("fuelcell_chp_dos", fuelcell_chp_dos_cutsV2, fuelcell_chp_dos_cutsV2X),
  ("furnace_program_timebase", furnace_program_timebase_cutsV2, furnace_program_timebase_cutsV2X),
  ("gantry_speed_zones", gantry_speed_zones_cutsV2, gantry_speed_zones_cutsV2X),
  ("hvac_fan_staging", hvac_fan_staging_cutsV2, hvac_fan_staging_cutsV2X),
  ("hydro_rejection_gatecal", hydro_rejection_gatecal_cutsV2, hydro_rejection_gatecal_cutsV2X),
  ("insulin_basal_cgmloss", insulin_basal_cgmloss_cutsV2, insulin_basal_cgmloss_cutsV2X),
  ("molding_pack_checkring", molding_pack_checkring_cutsV2, molding_pack_checkring_cutsV2X),
  ("platoon_latency", platoon_latency_cutsV2, platoon_latency_cutsV2X),
  ("platoon_linkloss", platoon_linkloss_cutsV2, platoon_linkloss_cutsV2X),
  ("platoon_profiles", platoon_profiles_cutsV2, platoon_profiles_cutsV2X),
  ("quad_light_lag", quad_light_lag_cutsV2, quad_light_lag_cutsV2X),
  ("quad_light_profiles", quad_light_profiles_cutsV2, quad_light_profiles_cutsV2X),
  ("rampmeter_poll_2to1", rampmeter_poll_2to1_cutsV2, rampmeter_poll_2to1_cutsV2X),
  ("rover_ladder_2to3", rover_ladder_2to3_cutsV2, rover_ladder_2to3_cutsV2X),
  ("rover_ladder_3to6", rover_ladder_3to6_cutsV2, rover_ladder_3to6_cutsV2X),
  ("rover_ladder_6to8", rover_ladder_6to8_cutsV2, rover_ladder_6to8_cutsV2X),
  ("rover_ladder_8to12", rover_ladder_8to12_cutsV2, rover_ladder_8to12_cutsV2X),
  ("rover_patrol_lag", rover_patrol_lag_cutsV2, rover_patrol_lag_cutsV2X),
  ("rover_rollover_payload", rover_rollover_payload_cutsV2, rover_rollover_payload_cutsV2X),
  ("rover_terrain_2to4", rover_terrain_2to4_cutsV2, rover_terrain_2to4_cutsV2X),
  ("rover_terrain_4to6", rover_terrain_4to6_cutsV2, rover_terrain_4to6_cutsV2X),
  ("rover_terrain_6to12", rover_terrain_6to12_cutsV2, rover_terrain_6to12_cutsV2X),
  ("sat3w_detumble_phases", sat3w_detumble_phases_cutsV2, sat3w_detumble_phases_cutsV2X),
  ("sat_detumble_phases", sat_detumble_phases_cutsV2, sat_detumble_phases_cutsV2X),
  ("sat_detumble_weak", sat_detumble_weak_cutsV2, sat_detumble_weak_cutsV2X),
  ("syringe_relay_prearm", syringe_relay_prearm_cutsV2, syringe_relay_prearm_cutsV2X),
  ("tank_dos_3to1", tank_dos_3to1_cutsV2, tank_dos_3to1_cutsV2X),
  ("train_ato_odometry", train_ato_odometry_cutsV2, train_ato_odometry_cutsV2X),
  ("tunnel_jetfan_pairout", tunnel_jetfan_pairout_cutsV2, tunnel_jetfan_pairout_cutsV2X),
  ("turbine_startup_gearratio", turbine_startup_gearratio_cutsV2, turbine_startup_gearratio_cutsV2X),
  ("vehicle_hypercert", vehicle_hypercert_cutsV2, vehicle_hypercert_cutsV2X),
  ("ventilator_vc_cuffleak", ventilator_vc_cuffleak_cutsV2, ventilator_vc_cuffleak_cutsV2X),
  ("watertank", watertank_cutsV2, watertank_cutsV2X),
  ("watertank_twospeed", watertank_twospeed_cutsV2, watertank_twospeed_cutsV2X) ]

end RelCertifier.Oracle
