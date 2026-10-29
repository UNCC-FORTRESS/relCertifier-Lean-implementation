/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Assumption 1 battery: `WellFormedR` per benchmark, axiom-audited on every build

The paper's Assumption 1 (Well-Formedness), restated 2026-10-10: *the right model is
nonblocking and complete with respect to its declared successor relation: from every state
satisfying a source-mode guard, an evolution spanning the control interval `ε_r` exists, and
every evolution of duration at most `ε_r`, including the empty one, ends in a state
satisfying the guard of at least one declared successor mode.*

`WellFormedR G guard ε` (`Proofs/Encoding/WellFormedR.lean`): for every mode `q` of the right
graph `G` and every state `x` in `q`'s lowered guard and `q`'s evolve domain, (i) a run of
`q`'s flow of duration `ε` exists inside the domain, and (ii) every run of duration
`t ≤ ε` ends in the lowered guard of some `e.tgt`, `e ∈ G.edgesFrom q` (self-loop
included). `G` is each benchmark's guarded right automaton (the graph of its Theorem 3:
the file's modes, flows, evolve domain, `next` lists), `guard q` the lowered right guard of
mode `q`, `ε = epsR` (the file's `epsilon`, read as the tool reads it). A model fact,
independent of the relational invariant and of every Theorem 3 (none takes it as a
hypothesis); this battery is a separate audit.

**Results (all 50 benchmarks; declared counts `wfDeclared`, kernel-checked against the
suite's IR table by `wf_coverage`).**

* **Proved, 46** (`<bench>_wellFormedR`): every mode (`watertank_twospeed` added 2026-10-11;
  the literature benchmarks `lit_drl_car_stop`, `lit_drl_lane_control` and
  `lit_freedm_meter` added 2026-10-15, proved directly over the bridge's automaton,
  `_wellFormedR_direct`; `lit_hypercert_vehicle`, added with them, left the suite on 2026-10-28,
  `benchmarks/skipped/`; the literature case studies of batch I8, 2026-10-27, `lit_csf21_vehicle_thermo`,
  `lit_csf21_vehicle_bus`, `lit_lz21_vehicle_position`, `lit_girard08_robot` and `lit_nahs25_salt_tank`, also direct). Z3-free (no verdict leaf). None of the nine models repaired on
  2026-10-10 (`docs/SUITE-REDESIGN.md` §21; until then refuted here with exhibited blocking
  states, declared counts `(30, 9, 6)`) is in the suite in its repaired form any more:
  `arm_plateau_{crit,profiles,slow}` and `platoon3_{linkloss,profiles}` moved to
  `benchmarks/reserve/` on 2026-10-27 with their proofs (history) and the shared `Platoon3Link`
  lemmas, `platoon_delay_linkloss` was replaced by `platoon_linkloss`, whose CACC/AEB follower it
  shares with `platoon_latency` (and shared with `platoon_profiles`, in the reserve since batch I8)
  through `PlatoonCaccAeb`,
  `platoon_delay_profiles` by `platoon_profiles`, and `quad_light_{airframe_20,profiles}` were
  redesigned on 2026-10-27 with the altitude coordinate and no limiter mode (`quad_light_airframe_20`
  moved to `benchmarks/reserve/` in batch I7 the same day, its proof in history, as did
  `rampmeter_poll_2to1` of batch I6, and `hvac_fan_staging`, `platoon_profiles`, `rover_rollover_payload`, `flaps_slow_approach`
  and `canal_gate_notches` in batch I8).
* **Refuted, 0.**
* **The detumble family, 3** (`<bench>_wellFormedR`, every mode; `<bench>_band_invariant`):
  `sat_detumble_{weak,phases}`, `sat3w_detumble_phases` (`sat_detumble_nominal` and
  `sat3w_detumble_{nominal,weak}` moved to `benchmarks/reserve/` on 2026-10-27). From 2026-10-15
  to 2026-10-29 their right evolve domains carried the conserved momentum band
  `|h_i + J_i w_i| ≤ 2` (without it clause (i) failed at the edge of the wheel-momentum box,
  `h = 2`, `w3 = 0.4`). Since 2026-10-29 (one physical domain per benchmark, the same on both
  sides) the domain is the gyro box `|w_i| ≤ 1` alone: the band is not a first integral of the
  left and the wheel box is crossed by the design model's own flow, so both left the domain; the
  explicit solution stays in the gyro box (the rates decay), and the band is still kept by every
  right mode's flow (`_band_invariant`, a model fact).

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`, nothing else (every proof is
Z3-free). `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on
axioms"`.
-/
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.WellFormed.LitDrlCarStop
import RelCertifier.InstancesV2.WellFormed.LitDrlLaneControl
import RelCertifier.InstancesV2.WellFormed.LitFreedmMeter
import RelCertifier.InstancesV2.WellFormed.LitLz21VehiclePosition
import RelCertifier.InstancesV2.WellFormed.LitGirard08Robot
import RelCertifier.InstancesV2.WellFormed.LitNahs25SaltTank
import RelCertifier.InstancesV2.WellFormed.LitCsf21VehicleThermo
import RelCertifier.InstancesV2.WellFormed.LitCsf21VehicleBus
import RelCertifier.InstancesV2.WellFormed.Watertank
import RelCertifier.InstancesV2.WellFormed.AccSpoofLag
import RelCertifier.InstancesV2.WellFormed.AccSpoofLimp
import RelCertifier.InstancesV2.WellFormed.AccTuneLag
import RelCertifier.InstancesV2.WellFormed.AccTuneLimp
import RelCertifier.InstancesV2.WellFormed.QuadLightLag
import RelCertifier.InstancesV2.WellFormed.RoverPatrolLag
import RelCertifier.InstancesV2.WellFormed.GantrySpeedZones
import RelCertifier.InstancesV2.WellFormed.RoverLadder2to3
import RelCertifier.InstancesV2.WellFormed.RoverLadder3to6
import RelCertifier.InstancesV2.WellFormed.RoverLadder6to8
import RelCertifier.InstancesV2.WellFormed.RoverLadder8to12
import RelCertifier.InstancesV2.WellFormed.RoverTerrain2to4
import RelCertifier.InstancesV2.WellFormed.RoverTerrain6to12
import RelCertifier.InstancesV2.WellFormed.RoverTerrain4to6
import RelCertifier.InstancesV2.WellFormed.PlatoonLinkloss
import RelCertifier.InstancesV2.WellFormed.PlatoonProfiles
import RelCertifier.InstancesV2.WellFormed.EngineStartHighidle
import RelCertifier.InstancesV2.WellFormed.TrainAtoOdometry
import RelCertifier.InstancesV2.WellFormed.ZoneLightmassSchedule
import RelCertifier.InstancesV2.WellFormed.InsulinBasalCgmloss
import RelCertifier.InstancesV2.WellFormed.TurbineStartupGearratio
import RelCertifier.InstancesV2.WellFormed.ChargerFastTapers
import RelCertifier.InstancesV2.WellFormed.QuadLightProfiles
import RelCertifier.InstancesV2.WellFormed.SatDetumbleWeak
import RelCertifier.InstancesV2.WellFormed.SatDetumblePhases
import RelCertifier.InstancesV2.WellFormed.Sat3wDetumblePhases
import RelCertifier.InstancesV2.WellFormed.WatertankTwospeed
import RelCertifier.InstancesV2.WellFormed.FlapsSlowApproach
import RelCertifier.InstancesV2.WellFormed.H2RefuelAmbientbias
import RelCertifier.InstancesV2.WellFormed.FuelcellChpDos
import RelCertifier.InstancesV2.WellFormed.ElevatorStartDiscbrake
import RelCertifier.InstancesV2.WellFormed.FurnaceProgramTimebase
import RelCertifier.InstancesV2.WellFormed.ReactorFeedWireless
import RelCertifier.InstancesV2.WellFormed.SyringeRelayPrearm
import RelCertifier.InstancesV2.WellFormed.HydroRejectionGatecal
import RelCertifier.InstancesV2.WellFormed.VentilatorVcCuffleak
import RelCertifier.InstancesV2.WellFormed.TankDos3to1
import RelCertifier.InstancesV2.WellFormed.AntennaTrackKvretune
import RelCertifier.InstancesV2.WellFormed.GridFfrDos
import RelCertifier.InstancesV2.WellFormed.BottlingFillStrainer
import RelCertifier.InstancesV2.WellFormed.PlatoonLatency

namespace RelCertifier
namespace WellFormedBattery

/-- The benchmarks whose right model satisfies Assumption 1 at every mode. -/
def wfProved : List String :=
  ["platoon_linkloss", "platoon_profiles", "platoon_latency",
   "charger_fast_tapers", "quad_light_profiles",
   "watertank", "acc_spoof_lag", "acc_spoof_limp", "acc_tune_lag", "acc_tune_limp",
   "quad_light_lag", "rover_patrol_lag", "gantry_speed_zones",
   "rover_ladder_2to3",
   "rover_ladder_3to6", "rover_ladder_6to8",
   "rover_ladder_8to12", "rover_terrain_2to4", "rover_terrain_6to12",
   "rover_terrain_4to6", "watertank_twospeed", "flaps_slow_approach", "engine_start_highidle", "train_ato_odometry",
   "zone_lightmass_schedule", "turbine_startup_gearratio", "insulin_basal_cgmloss",
   "h2_refuel_ambientbias", "fuelcell_chp_dos", "elevator_start_discbrake",
   "furnace_program_timebase", "reactor_feed_wireless", "syringe_relay_prearm",
   "hydro_rejection_gatecal", "ventilator_vc_cuffleak", "tank_dos_3to1", "antenna_track_kvretune", "grid_ffr_dos",
   "bottling_fill_strainer",
   "lit_drl_car_stop", "lit_drl_lane_control",
   "lit_freedm_meter",
   "lit_lz21_vehicle_position",
   "lit_girard08_robot",
   "lit_nahs25_salt_tank",
   "lit_csf21_vehicle_thermo",
   "lit_csf21_vehicle_bus"]

/-- The benchmarks whose right model violates Assumption 1 (none since the 2026-10-10
repairs; the nine refuted until then are in `wfProved`). -/
def wfRefuted : List String := []

/-- The detumble family: Assumption 1 holds at every mode (over the gyro box `|w_i| ≤ 1` since
2026-10-29; with the momentum band in the right evolve domain from 2026-10-15; before, only on the
band), and the band is kept by every right flow (`_band_invariant`). -/
def wfBand : List String :=
  ["sat_detumble_weak", "sat_detumble_phases",
   "sat3w_detumble_phases"]

/-- **Declared counts**: proved outside the detumble family, refuted (model defects), the
detumble family (also proved, listed apart for its band audit). `(30, 9, 6)` until the
2026-10-10 repairs of the nine refuted models; `(39, 0, 6)` then, `(40, 0, 6)` with
`watertank_twospeed` (2026-10-11); `(44, 0, 6)` with the 2026-10-26 additions; `(40, 0, 6)`
after the 2026-10-27 reserve moves (`airheader_dos_3to1`, `arm_plateau_profiles`,
`platoon3_{linkloss,profiles}`); `(41, 0, 6)` with `platoon_linkloss` (replacing
`platoon_delay_linkloss`) and `platoon_latency`; `(43, 0, 6)` with `engine_start_highidle` and
`train_ato_odometry`; unchanged by `gantry_speed_zones` (replacing `match_multi_rate`) and
`platoon_profiles` (replacing `platoon_delay_profiles`), and by the redesigned
`quad_light_{airframe_20,profiles}` and `watertank_twospeed`; `(46, 0, 6)` with
`bms_chiller_undercharge`, `canal_gate_notches` and `turbine_startup_gearratio`; `(36, 0, 6)`
after the rover hierarchy of 2026-10-27 (ten rover files left the suite: `rover_rollover_6to7`,
`_7to12`, `_6to12`, `rover_lateral_6to8`, `_8to12`, `rover_attitude_6to8`, `_8to12`,
`rover_ladder_2to4`, `_2to6`, `rover_patrol_zones`; the four ladder rungs and
`rover_patrol_lag` were reinstalled on new right models, `L2`, `L3`, `L6`, `L8` with pinned
coordinates and the planning model); `(32, 0, 3)` after the reserve moves of batch I4
(2026-10-27: `charger_fast_{setpoints,tapers}`, `arm_plateau_{crit,slow}`,
`sat_detumble_nominal`, `sat3w_detumble_{nominal,weak}`), unchanged by the batch I4 installs (the
`acc_*` files at the 0.1 s period, the satellite phases' three-mode right models); `(41, 0, 3)`
with the nine new benchmarks of batch I5 (`molding_pack_checkring`, `fuelcell_chp_dos`,
`elevator_start_discbrake`, `furnace_program_timebase`, `compressor_station_recycle`,
`syringe_relay_prearm`, `hydro_rejection_gatecal`, `ventilator_vc_cuffleak`,
`insulin_basal_cgmloss`); `(42, 0, 3)` with `rover_rollover_payload` (the first right model with a
coupled block, proved by Picard on an enlarged strictly inflowing box); `(47, 0, 3)` with the five
new benchmarks of batch I6 (`flaps_slow_approach`, `tunnel_jetfan_pairout`, whose right model has
the polynomial terms `u^2` and `u c` and is proved with an explicit Riccati run,
`rampmeter_poll_2to1`, `bottling_fill_strainer`, `antenna_track_kvretune`); unchanged by the swaps
of batch I7 (`charger_fast_tapers`, reinstalled at the minute time scale with its round-2 proof
at the new interval, for `quad_light_airframe_20`; `grid_ffr_dos`, a new proof with an explicit
run and a non-strict barrier for the FFR release line, for `rampmeter_poll_2to1`); unchanged by the
swaps of batch I8 (the literature case studies `lit_csf21_vehicle_thermo` and `lit_csf21_vehicle_bus`,
direct proofs with explicit polynomial runs and an exit into a coast mode, for `hvac_fan_staging`
and `platoon_profiles`; then `lit_lz21_vehicle_position`, `lit_girard08_robot`, whose right evolve domain is
the constant atom `0.0 <= 1.0`, and `lit_nahs25_salt_tank`, a contraction toward 25 kept by every run,
for `rover_rollover_payload`, `flaps_slow_approach` and `canal_gate_notches`); unchanged by the
swaps of batches I9 to I11 (2026-10-28; batch I11: `platoon_latency`, its round-2 proof over the
shared CACC/AEB run lemmas, `h2_refuel_ambientbias`, six 1-D contractions as `engine_start_highidle`,
and `reactor_feed_wireless`, four exponential runs at dimension 2 as `fuelcell_chp_dos`, for
`antenna_track_kvretune`, `molding_pack_checkring` and `compressor_station_recycle`). -/
def wfDeclared : ℕ × ℕ × ℕ := (47, 0, 3)

/-- The suite's benchmark names, in the order of the IR table. -/
def suiteNames : List String :=
  ["acc_spoof_lag", "acc_spoof_limp", "acc_tune_lag", "acc_tune_limp",
   "antenna_track_kvretune", "bottling_fill_strainer", "charger_fast_tapers",
   "elevator_start_discbrake", "engine_start_highidle", "flaps_slow_approach",
   "fuelcell_chp_dos", "furnace_program_timebase", "gantry_speed_zones", "grid_ffr_dos",
   "h2_refuel_ambientbias", "hydro_rejection_gatecal", "insulin_basal_cgmloss",
   "lit_csf21_vehicle_bus", "lit_csf21_vehicle_thermo", "lit_drl_car_stop",
   "lit_drl_lane_control", "lit_freedm_meter", "lit_girard08_robot",
   "lit_lz21_vehicle_position", "lit_nahs25_salt_tank", "platoon_latency", "platoon_linkloss",
   "platoon_profiles", "quad_light_lag", "quad_light_profiles", "reactor_feed_wireless",
   "rover_ladder_2to3", "rover_ladder_3to6", "rover_ladder_6to8", "rover_ladder_8to12",
   "rover_patrol_lag", "rover_terrain_2to4", "rover_terrain_4to6", "rover_terrain_6to12",
   "sat3w_detumble_phases", "sat_detumble_phases", "sat_detumble_weak", "syringe_relay_prearm",
   "tank_dos_3to1", "train_ato_odometry", "turbine_startup_gearratio",
   "ventilator_vc_cuffleak", "watertank", "watertank_twospeed", "zone_lightmass_schedule"]

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

/-! ## Proved (46 outside the detumble family, with the next section): Assumption 1 at every mode -/

#print axioms V2LitDrlCarStop.lit_drl_car_stop_wellFormedR_direct
#print axioms V2LitDrlLaneControl.lit_drl_lane_control_wellFormedR_direct
#print axioms V2LitFreedmMeter.lit_freedm_meter_wellFormedR_direct
#print axioms V2LitLz21VehiclePosition.lit_lz21_vehicle_position_wellFormedR_direct
#print axioms V2LitGirard08Robot.lit_girard08_robot_wellFormedR_direct
#print axioms V2LitNahs25SaltTank.lit_nahs25_salt_tank_wellFormedR_direct
#print axioms V2LitCsf21VehicleThermo.lit_csf21_vehicle_thermo_wellFormedR_direct
#print axioms V2LitCsf21VehicleBus.lit_csf21_vehicle_bus_wellFormedR_direct

#print axioms V2Watertank.watertank_wellFormedR
#print axioms V2WatertankTwospeed.watertank_twospeed_wellFormedR
#print axioms V2FlapsSlowApproach.flaps_slow_approach_wellFormedR
#print axioms V2AccSpoofLag.acc_spoof_lag_wellFormedR
#print axioms V2AccSpoofLimp.acc_spoof_limp_wellFormedR
#print axioms V2AccTuneLag.acc_tune_lag_wellFormedR
#print axioms V2AccTuneLimp.acc_tune_limp_wellFormedR
#print axioms V2QuadLightLag.quad_light_lag_wellFormedR
#print axioms V2RoverPatrolLagGuarded.rover_patrol_lag_wellFormedR
#print axioms V2GantrySpeedZones.gantry_speed_zones_wellFormedR
#print axioms RoverLadder2to3Guarded.rover_ladder_2to3_wellFormedR
#print axioms RoverLadder3to6Guarded.rover_ladder_3to6_wellFormedR
#print axioms RoverLadder6to8Guarded.rover_ladder_6to8_wellFormedR
#print axioms RoverLadder8to12Guarded.rover_ladder_8to12_wellFormedR
#print axioms RoverTerrain2to4Guarded.rover_terrain_2to4_wellFormedR
#print axioms RoverTerrain6to12Guarded.rover_terrain_6to12_wellFormedR
#print axioms RoverTerrain4to6Guarded.rover_terrain_4to6_wellFormedR

/-! ## The later additions: Assumption 1 at every mode -/

#print axioms V2PlatoonLinkloss.platoon_linkloss_wellFormedR
#print axioms V2PlatoonProfiles.platoon_profiles_wellFormedR
#print axioms V2EngineStartHighidle.engine_start_highidle_wellFormedR
#print axioms V2TrainAtoOdometry.train_ato_odometry_wellFormedR
#print axioms V2ZoneLightmassSchedule.zone_lightmass_schedule_wellFormedR
#print axioms V2InsulinBasalCgmloss.insulin_basal_cgmloss_wellFormedR
#print axioms V2TurbineStartupGearratio.turbine_startup_gearratio_wellFormedR
#print axioms V2H2RefuelAmbientbias.h2_refuel_ambientbias_wellFormedR
#print axioms V2FuelcellChpDos.fuelcell_chp_dos_wellFormedR
#print axioms V2ElevatorStartDiscbrake.elevator_start_discbrake_wellFormedR
#print axioms V2FurnaceProgramTimebase.furnace_program_timebase_wellFormedR
#print axioms V2ReactorFeedWireless.reactor_feed_wireless_wellFormedR
#print axioms V2SyringeRelayPrearm.syringe_relay_prearm_wellFormedR
#print axioms V2HydroRejectionGatecal.hydro_rejection_gatecal_wellFormedR
#print axioms V2VentilatorVcCuffleak.ventilator_vc_cuffleak_wellFormedR
#print axioms V2TankDos3to1.tank_dos_3to1_wellFormedR
#print axioms V2AntennaTrackKvretune.antenna_track_kvretune_wellFormedR
#print axioms V2BottlingFillStrainer.bottling_fill_strainer_wellFormedR
#print axioms V2PlatoonLatency.platoon_latency_wellFormedR
#print axioms V2ChargerFastTapers.charger_fast_tapers_wellFormedR
#print axioms V2GridFfrDos.grid_ffr_dos_wellFormedR
#print axioms PlatoonCaccAeb.cacc_w_band
#print axioms PlatoonCaccAeb.aeb_w_const
#print axioms PlatoonCaccAeb.cacc_box
#print axioms V2QuadLightProfiles.quad_light_profiles_wellFormedR

/-! ## The detumble family (3): Assumption 1 unconditional (over the gyro box since 2026-10-29;
the momentum band was part of the right evolve domain from 2026-10-15 to 2026-10-29), and the band
invariant as a model fact -/

#print axioms V2SatDetumbleWeak.sat_detumble_weak_wellFormedR
#print axioms V2SatDetumbleWeak.sat_detumble_weak_band_invariant
#print axioms V2SatDetumblePhases.sat_detumble_phases_wellFormedR
#print axioms V2SatDetumblePhases.sat_detumble_phases_band_invariant
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_wellFormedR
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_band_invariant

/-! ## The generic layer -/

#print axioms wellFormedR_terrain
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
