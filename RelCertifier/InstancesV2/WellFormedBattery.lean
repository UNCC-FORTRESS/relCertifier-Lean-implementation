/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Assumption 1 battery: `WellFormedR` per benchmark, axiom-audited on every build

Assumption 1 (Well-Formedness) of the paper: *the right model is nonblocking and complete with
respect to its declared successor relation: for every mode and every state satisfying its guard,
some evolution of the mode spans the control interval `ε_r`, and every evolution of duration at
most `ε_r`, including the empty one, ends in the guard of some declared successor.*

`WellFormedR G guard ε` (`Proofs/Encoding/WellFormedR.lean`): for every mode `q` of the right
graph `G` and every state `x` in `q`'s lowered guard and `q`'s evolve domain, (i) a run of
`q`'s flow of duration `ε` exists inside the domain, and (ii) every run of duration
`t ≤ ε` ends in the lowered guard of some `e.tgt`, `e ∈ G.edgesFrom q` (self-loop
included). `G` is each benchmark's guarded right automaton (the file's modes, flows, evolve
domain and `next` lists), `guard q` the lowered right guard of mode `q`, `ε = epsR` (the file's
`epsilon`, read as the tool reads it). A model fact, independent of the relational invariant.
Each bridge instance (`InstancesV2/Bridge/<B>.lean`) transports its benchmark's proof onto the
pruned graph of the cover and lifts it by the right-clock coordinate (`wellFormedR_lift`), which
discharges the `WellFormedRIn` hypothesis of its record-level Theorem 3 (Appendix B.5).

**Results (all 50 benchmarks; declared counts `wfDeclared`, kernel-checked against the
suite's IR table by `wf_coverage`).**

* **Proved, 47** (`<bench>_wellFormedR`): every mode. The literature benchmarks are proved
  directly over the bridge's automaton (`_wellFormedR_direct`). Z3-free (no verdict leaf).
* **Refuted, 0.**
* **The detumble family, 3** (`<bench>_wellFormedR`, every mode; `<bench>_band_invariant`):
  `sat_detumble_{weak,phases}` and `sat3w_detumble_phases`, the satellite benchmarks. Their
  evolve domain is the gyro box `|w_i| ≤ 1` alone, the same on both sides; the explicit
  solution stays in it (the rates decay). The conserved momentum band `|h_i + J_i w_i| ≤ 2` is
  not in the domain and is kept by every right mode's flow (`_band_invariant`, a model fact).

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`, nothing else, for every proof of
this file (all Z3-free). The build of this module also replays the axiom lines of imported
modules, two of which, for the `CutLiftX` lift of the mode facts, add `z3_unsat_sound`
(Appendix B.5 counts 78 lines in all, 76 at the three standard axioms).
`lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"`.
-/
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.WellFormed.LitDrlLaneControl
import RelCertifier.InstancesV2.WellFormed.LitFreedmMeter
import RelCertifier.InstancesV2.WellFormed.LitLz21VehiclePosition
import RelCertifier.InstancesV2.WellFormed.LitGirard08Robot
import RelCertifier.InstancesV2.WellFormed.LitNahs25SaltTank
import RelCertifier.InstancesV2.WellFormed.LitCsf21VehicleThermo
import RelCertifier.InstancesV2.WellFormed.LitCsf21VehicleBus
import RelCertifier.InstancesV2.WellFormed.LitGpt10BoostConverter
import RelCertifier.InstancesV2.WellFormed.LitCsf25SaltTankHold
import RelCertifier.InstancesV2.WellFormed.Watertank
import RelCertifier.InstancesV2.WellFormed.AccSpoofLag
import RelCertifier.InstancesV2.WellFormed.AccSpoofLimp
import RelCertifier.InstancesV2.WellFormed.AccTuneLimp
import RelCertifier.InstancesV2.WellFormed.QuadLightLag
import RelCertifier.InstancesV2.WellFormed.GantrySpeedZones
import RelCertifier.InstancesV2.WellFormed.StoplineLag
import RelCertifier.InstancesV2.WellFormed.StoplineFriction
import RelCertifier.InstancesV2.WellFormed.StoplineTyre
import RelCertifier.InstancesV2.WellFormed.StoplineDrag
import RelCertifier.InstancesV2.WellFormed.RoverLadder2to3
import RelCertifier.InstancesV2.WellFormed.RoverLadder3to6
import RelCertifier.InstancesV2.WellFormed.RoverLadder6to8
import RelCertifier.InstancesV2.WellFormed.RoverLadder8to12
import RelCertifier.InstancesV2.WellFormed.PlatoonProfiles
import RelCertifier.InstancesV2.WellFormed.EngineStartHighidle
import RelCertifier.InstancesV2.WellFormed.TrainAtoOdometry
import RelCertifier.InstancesV2.WellFormed.RampmeterPoll2to1
import RelCertifier.InstancesV2.WellFormed.TurbineStartupGearratio
import RelCertifier.InstancesV2.WellFormed.MoldingPackCheckring
import RelCertifier.InstancesV2.WellFormed.QuadLightProfiles
import RelCertifier.InstancesV2.WellFormed.SatDetumbleWeak
import RelCertifier.InstancesV2.WellFormed.SatDetumblePhases
import RelCertifier.InstancesV2.WellFormed.Sat3wDetumblePhases
import RelCertifier.InstancesV2.WellFormed.WatertankTwospeed
import RelCertifier.InstancesV2.WellFormed.FlapsSlowApproach
import RelCertifier.InstancesV2.WellFormed.H2RefuelAmbientbias
import RelCertifier.InstancesV2.WellFormed.ElevatorStartDiscbrake
import RelCertifier.InstancesV2.WellFormed.FurnaceProgramTimebase
import RelCertifier.InstancesV2.WellFormed.ReactorFeedWireless
import RelCertifier.InstancesV2.WellFormed.SyringeRelayPrearm
import RelCertifier.InstancesV2.WellFormed.HydroRejectionGatecal
import RelCertifier.InstancesV2.WellFormed.VentilatorVcCuffleak
import RelCertifier.InstancesV2.WellFormed.TankDos3to1
import RelCertifier.InstancesV2.WellFormed.AntennaTrackKvretune
import RelCertifier.InstancesV2.WellFormed.CanalGateNotches
import RelCertifier.InstancesV2.WellFormed.BottlingFillStrainer
import RelCertifier.InstancesV2.WellFormed.BoilerPurgeVfd
import RelCertifier.InstancesV2.WellFormed.AutoclaveLiquidSteambank
import RelCertifier.InstancesV2.WellFormed.ExtruderPe100Manualstart
import RelCertifier.InstancesV2.WellFormed.LitNahs25EngineCooling

namespace RelCertifier
namespace WellFormedBattery

/-- The benchmarks whose right model satisfies Assumption 1 at every mode. -/
def wfProved : List String :=
  ["platoon_profiles", "boiler_purge_vfd",
   "molding_pack_checkring", "quad_light_profiles",
   "watertank", "acc_spoof_lag", "acc_spoof_limp", "acc_tune_limp",
   "quad_light_lag", "autoclave_liquid_steambank", "gantry_speed_zones",
   "stopline_lag",
   "stopline_friction", "stopline_tyre",
   "stopline_drag", "rover_ladder_2to3",
   "rover_ladder_3to6", "rover_ladder_6to8", "rover_ladder_8to12", "watertank_twospeed", "flaps_slow_approach", "engine_start_highidle", "train_ato_odometry",
   "turbine_startup_gearratio", "rampmeter_poll_2to1",
   "h2_refuel_ambientbias", "extruder_pe100_manualstart", "elevator_start_discbrake",
   "furnace_program_timebase", "reactor_feed_wireless", "syringe_relay_prearm",
   "hydro_rejection_gatecal", "ventilator_vc_cuffleak", "tank_dos_3to1", "antenna_track_kvretune", "canal_gate_notches",
   "bottling_fill_strainer",
   "lit_drl_lane_control",
   "lit_freedm_meter",
   "lit_lz21_vehicle_position",
   "lit_girard08_robot",
   "lit_nahs25_salt_tank",
   "lit_csf21_vehicle_thermo",
   "lit_csf21_vehicle_bus",
   "lit_gpt10_boost_converter",
   "lit_csf25_salt_tank_hold",
   "lit_nahs25_engine_cooling"]

/-- The benchmarks whose right model violates Assumption 1 (none). -/
def wfRefuted : List String := []

/-- The detumble family: Assumption 1 holds at every mode (over the gyro box `|w_i| ≤ 1`), and
the momentum band is kept by every right flow (`_band_invariant`). -/
def wfBand : List String :=
  ["sat_detumble_weak", "sat_detumble_phases",
   "sat3w_detumble_phases"]

/-- **Declared counts**: proved outside the detumble family, refuted (model defects), the
detumble family (also proved, listed apart for its band audit). -/
def wfDeclared : ℕ × ℕ × ℕ := (47, 0, 3)

/-- The suite's benchmark names, in the order of the IR table. -/
def suiteNames : List String :=
  ["acc_spoof_lag", "acc_spoof_limp", "acc_tune_limp", "antenna_track_kvretune",
   "autoclave_liquid_steambank", "boiler_purge_vfd", "bottling_fill_strainer",
   "canal_gate_notches", "elevator_start_discbrake", "engine_start_highidle",
   "extruder_pe100_manualstart", "flaps_slow_approach", "furnace_program_timebase",
   "gantry_speed_zones", "h2_refuel_ambientbias", "hydro_rejection_gatecal",
   "lit_csf21_vehicle_bus", "lit_csf21_vehicle_thermo", "lit_csf25_salt_tank_hold",
   "lit_drl_lane_control", "lit_freedm_meter", "lit_girard08_robot", "lit_gpt10_boost_converter",
   "lit_lz21_vehicle_position", "lit_nahs25_engine_cooling", "lit_nahs25_salt_tank",
   "molding_pack_checkring", "platoon_profiles", "quad_light_lag",
   "quad_light_profiles", "rampmeter_poll_2to1", "reactor_feed_wireless", "rover_ladder_2to3",
   "rover_ladder_3to6", "rover_ladder_6to8", "rover_ladder_8to12", "sat3w_detumble_phases", "sat_detumble_phases", "sat_detumble_weak",
   "stopline_drag", "stopline_friction", "stopline_lag", "stopline_tyre", "syringe_relay_prearm", "tank_dos_3to1", "train_ato_odometry", "turbine_startup_gearratio",
   "ventilator_vc_cuffleak", "watertank", "watertank_twospeed"]

/-- `suiteNames` IS the name column of the kernel-checked IR table of the suite. -/
theorem suiteNames_eq : Parse.benchIRTableV2.map Prod.fst = suiteNames := rfl

/-- The declared counts are the lists' lengths, and the three lists together are a
permutation of the suite's benchmarks (disjoint, nothing missing). -/
theorem wf_coverage :
    (wfProved.length, wfRefuted.length, wfBand.length) = wfDeclared ∧
    (wfProved ++ wfRefuted ++ wfBand).Perm (Parse.benchIRTableV2.map Prod.fst) := by
  rw [suiteNames_eq]
  exact ⟨rfl, by decide⟩

end WellFormedBattery

/-! ## Proved (47 outside the detumble family, with the next section): Assumption 1 at every mode -/

#print axioms V2LitDrlLaneControl.lit_drl_lane_control_wellFormedR_direct
#print axioms V2LitFreedmMeter.lit_freedm_meter_wellFormedR_direct
#print axioms V2LitLz21VehiclePosition.lit_lz21_vehicle_position_wellFormedR_direct
#print axioms V2LitGirard08Robot.lit_girard08_robot_wellFormedR_direct
#print axioms V2LitNahs25SaltTank.lit_nahs25_salt_tank_wellFormedR_direct
#print axioms V2LitCsf21VehicleThermo.lit_csf21_vehicle_thermo_wellFormedR_direct
#print axioms V2LitCsf21VehicleBus.lit_csf21_vehicle_bus_wellFormedR_direct
#print axioms V2LitGpt10BoostConverter.lit_gpt10_boost_converter_wellFormedR_direct
#print axioms V2LitCsf25SaltTankHold.lit_csf25_salt_tank_hold_wellFormedR_direct
#print axioms V2LitNahs25EngineCooling.lit_nahs25_engine_cooling_wellFormedR_direct

#print axioms V2Watertank.watertank_wellFormedR
#print axioms V2WatertankTwospeed.watertank_twospeed_wellFormedR
#print axioms V2FlapsSlowApproach.flaps_slow_approach_wellFormedR
#print axioms V2AccSpoofLag.acc_spoof_lag_wellFormedR
#print axioms V2AccSpoofLimp.acc_spoof_limp_wellFormedR
#print axioms V2AccTuneLimp.acc_tune_limp_wellFormedR
#print axioms V2QuadLightLag.quad_light_lag_wellFormedR
#print axioms V2GantrySpeedZones.gantry_speed_zones_wellFormedR
#print axioms StoplineLag.stopline_lag_wellFormedR
#print axioms StoplineFriction.stopline_friction_wellFormedR
#print axioms StoplineTyre.stopline_tyre_wellFormedR
#print axioms StoplineDrag.stopline_drag_wellFormedR
#print axioms RoverLadder2to3Guarded.rover_ladder_2to3_wellFormedR
#print axioms RoverLadder3to6Guarded.rover_ladder_3to6_wellFormedR
#print axioms RoverLadder6to8Guarded.rover_ladder_6to8_wellFormedR
#print axioms RoverLadder8to12Guarded.rover_ladder_8to12_wellFormedR

/-! ## Assumption 1 at every mode (continued) -/

#print axioms V2PlatoonProfiles.platoon_profiles_wellFormedR
#print axioms V2EngineStartHighidle.engine_start_highidle_wellFormedR
#print axioms V2TrainAtoOdometry.train_ato_odometry_wellFormedR
#print axioms V2RampmeterPoll2to1.rampmeter_poll_2to1_wellFormedR
#print axioms V2TurbineStartupGearratio.turbine_startup_gearratio_wellFormedR
#print axioms V2H2RefuelAmbientbias.h2_refuel_ambientbias_wellFormedR
#print axioms V2ElevatorStartDiscbrake.elevator_start_discbrake_wellFormedR
#print axioms V2FurnaceProgramTimebase.furnace_program_timebase_wellFormedR
#print axioms V2ReactorFeedWireless.reactor_feed_wireless_wellFormedR
#print axioms V2SyringeRelayPrearm.syringe_relay_prearm_wellFormedR
#print axioms V2HydroRejectionGatecal.hydro_rejection_gatecal_wellFormedR
#print axioms V2VentilatorVcCuffleak.ventilator_vc_cuffleak_wellFormedR
#print axioms V2TankDos3to1.tank_dos_3to1_wellFormedR
#print axioms V2AntennaTrackKvretune.antenna_track_kvretune_wellFormedR
#print axioms V2BottlingFillStrainer.bottling_fill_strainer_wellFormedR
#print axioms V2BoilerPurgeVfd.boiler_purge_vfd_wellFormedR
#print axioms V2AutoclaveLiquidSteambank.autoclave_liquid_steambank_wellFormedR
#print axioms V2ExtruderPe100Manualstart.extruder_pe100_manualstart_wellFormedR
#print axioms V2MoldingPackCheckring.molding_pack_checkring_wellFormedR
#print axioms V2CanalGateNotches.canal_gate_notches_wellFormedR
#print axioms PlatoonCaccAeb.cacc_w_band
#print axioms PlatoonCaccAeb.aeb_w_const
#print axioms PlatoonCaccAeb.cacc_box
#print axioms V2QuadLightProfiles.quad_light_profiles_wellFormedR

/-! ## The detumble family (3): Assumption 1 unconditional (over the gyro box), and the band
invariant as a model fact -/

#print axioms V2SatDetumbleWeak.sat_detumble_weak_wellFormedR
#print axioms V2SatDetumbleWeak.sat_detumble_weak_band_invariant
#print axioms V2SatDetumblePhases.sat_detumble_phases_wellFormedR
#print axioms V2SatDetumblePhases.sat_detumble_phases_band_invariant
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_wellFormedR
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_band_invariant

/-! ## The generic layer -/

#print axioms wellFormedR_terrain
#print axioms wellFormedR_stopline
#print axioms not_wellFormedR_of_run
#print axioms not_wellFormedR_of_noRun
#print axioms wellFormedR_switchLegal
#print axioms exists_contract_run
#print axioms exists_rate_run
#print axioms exists_of_HExistSegB_zero
#print axioms DLCalTiming.ODESol.coord_le_barrier
#print axioms DLCalTiming.ODESol.affine_const
#print axioms WellFormedBattery.wf_coverage

end RelCertifier
