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

* **Proved, 44** (`<bench>_wellFormedR`): every mode (`watertank_twospeed` added 2026-10-11;
  the literature benchmarks `drl_car_stop`, `drl_lane_control`, `vehicle_hypercert` and
  `freedm_meter` added 2026-10-15, three of them proved directly over the bridge's automaton,
  `_wellFormedR_direct`). Z3-free (no verdict leaf). Nine of them
  are the models repaired on 2026-10-10 (`docs/SUITE-REDESIGN.md` §21; until then refuted
  here with exhibited blocking states, declared counts `(30, 9, 6)`):
  - `arm_plateau_{crit,profiles,slow}`: the planner is a sampled controller whose successor
    sets name every band one interval can reach (`ApproachA → …, ApproachC*, Hold`,
    `ApproachB → …, Hold`);
  - `platoon_delay_{linkloss,profiles}`: the AEB sink `BRAKE` re-engages `FOLLOW` at 20 m;
  - `platoon3_{linkloss,profiles}`: the AEB sinks `BRAKE1`–`BRAKE3` are latched
    (speed-matching flow `r_k' = −r_k/2`, guard `g_k < 20`, `0 ≤ g_k + 2 r_k < 20`, the other
    links in their operating range), and keep their guard;
  - `quad_light_{airframe_20,profiles}`: the limiter `LIMIT` hands back to the climb
    controller, whose operating range now reaches the limiter threshold.
* **Refuted, 0.**
* **The detumble family, 6** (`<bench>_wellFormedR`, every mode; `<bench>_band_invariant`):
  `sat_detumble_{nominal,weak,phases}`, `sat3w_detumble_{nominal,weak,phases}`. Their right
  evolve domains carry the conserved momentum band `|h_i + J_i w_i| ≤ 2` (the body's momentum
  within the wheels' capacity; since 2026-10-15). Without it clause (i) failed at the edge of
  the wheel-momentum box (`h = 2`, `w3 = 0.4`: `h + 5 w3` is conserved and would leave
  `|h| ≤ 2`); with it the explicit solution stays in the domain, and the band is kept by every
  mode's flow.

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`, nothing else (every proof is
Z3-free). `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on
axioms"`.
-/
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.WellFormed.DrlCarStop
import RelCertifier.InstancesV2.WellFormed.DrlLaneControl
import RelCertifier.InstancesV2.WellFormed.FreedmMeter
import RelCertifier.InstancesV2.Choice.General.VehicleHypercert
import RelCertifier.InstancesV2.WellFormed.Watertank
import RelCertifier.InstancesV2.WellFormed.AccSpoofLag
import RelCertifier.InstancesV2.WellFormed.AccSpoofLimp
import RelCertifier.InstancesV2.WellFormed.AccTuneLag
import RelCertifier.InstancesV2.WellFormed.AccTuneLimp
import RelCertifier.InstancesV2.WellFormed.ChargerFastSetpoints
import RelCertifier.InstancesV2.WellFormed.ChargerFastTapers
import RelCertifier.InstancesV2.WellFormed.QuadLightLag
import RelCertifier.InstancesV2.WellFormed.RoverPatrolZones
import RelCertifier.InstancesV2.WellFormed.RoverPatrolLag
import RelCertifier.InstancesV2.WellFormed.RoverRollover7to12
import RelCertifier.InstancesV2.WellFormed.MatchMultiRate
import RelCertifier.InstancesV2.WellFormed.RoverLadder2to3
import RelCertifier.InstancesV2.WellFormed.RoverLadder3to6
import RelCertifier.InstancesV2.WellFormed.RoverLadder6to8
import RelCertifier.InstancesV2.WellFormed.RoverLadder8to12
import RelCertifier.InstancesV2.WellFormed.RoverLadder2to4
import RelCertifier.InstancesV2.WellFormed.RoverLadder2to6
import RelCertifier.InstancesV2.WellFormed.RoverTerrain2to4
import RelCertifier.InstancesV2.WellFormed.RoverTerrain6to12
import RelCertifier.InstancesV2.WellFormed.RoverTerrain4to6
import RelCertifier.InstancesV2.WellFormed.RoverAttitude6to8
import RelCertifier.InstancesV2.WellFormed.RoverAttitude8to12
import RelCertifier.InstancesV2.WellFormed.RoverLateral6to8
import RelCertifier.InstancesV2.WellFormed.RoverLateral8to12
import RelCertifier.InstancesV2.WellFormed.RoverRollover6to12
import RelCertifier.InstancesV2.WellFormed.RoverRollover6to7
import RelCertifier.InstancesV2.WellFormed.ArmPlateauCrit
import RelCertifier.InstancesV2.WellFormed.ArmPlateauProfiles
import RelCertifier.InstancesV2.WellFormed.ArmPlateauSlow
import RelCertifier.InstancesV2.WellFormed.PlatoonDelayLinkloss
import RelCertifier.InstancesV2.WellFormed.PlatoonDelayProfiles
import RelCertifier.InstancesV2.WellFormed.Platoon3Linkloss
import RelCertifier.InstancesV2.WellFormed.Platoon3Profiles
import RelCertifier.InstancesV2.WellFormed.QuadLightAirframe20
import RelCertifier.InstancesV2.WellFormed.QuadLightProfiles
import RelCertifier.InstancesV2.WellFormed.SatDetumbleNominal
import RelCertifier.InstancesV2.WellFormed.SatDetumbleWeak
import RelCertifier.InstancesV2.WellFormed.SatDetumblePhases
import RelCertifier.InstancesV2.WellFormed.Sat3wDetumbleNominal
import RelCertifier.InstancesV2.WellFormed.Sat3wDetumbleWeak
import RelCertifier.InstancesV2.WellFormed.Sat3wDetumblePhases
import RelCertifier.InstancesV2.WellFormed.WatertankTwospeed
import RelCertifier.InstancesV2.WellFormed.TankDos3to1
import RelCertifier.InstancesV2.WellFormed.AirheaderDos3to1
import RelCertifier.InstancesV2.WellFormed.HvacFanStaging

namespace RelCertifier
namespace WellFormedBattery

/-- The benchmarks whose right model satisfies Assumption 1 at every mode. -/
def wfProved : List String :=
  ["arm_plateau_crit", "arm_plateau_profiles", "arm_plateau_slow", "platoon_delay_linkloss",
   "platoon_delay_profiles", "platoon3_linkloss", "platoon3_profiles",
   "quad_light_airframe_20", "quad_light_profiles",
   "watertank", "acc_spoof_lag", "acc_spoof_limp", "acc_tune_lag", "acc_tune_limp",
   "charger_fast_setpoints", "charger_fast_tapers", "quad_light_lag", "rover_patrol_zones",
   "rover_patrol_lag", "rover_rollover_7to12", "match_multi_rate",
   "rover_ladder_2to3",
   "rover_ladder_3to6", "rover_ladder_6to8",
   "rover_ladder_8to12", "rover_ladder_2to4",
   "rover_ladder_2to6",
   "rover_terrain_2to4", "rover_terrain_6to12",
   "rover_terrain_4to6", "rover_attitude_6to8", "rover_attitude_8to12",
   "rover_lateral_6to8", "rover_lateral_8to12", "rover_rollover_6to12",
   "rover_rollover_6to7", "watertank_twospeed", "tank_dos_3to1", "airheader_dos_3to1", "hvac_fan_staging", "drl_car_stop", "drl_lane_control",
   "vehicle_hypercert", "freedm_meter"]

/-- The benchmarks whose right model violates Assumption 1 (none since the 2026-10-10
repairs; the nine refuted until then are in `wfProved`). -/
def wfRefuted : List String := []

/-- The detumble family: Assumption 1 holds at every mode (the conserved momentum band is in
the right evolve domain since 2026-10-15; before, only on the band), and the band is kept by
every flow (`_band_invariant`). -/
def wfBand : List String :=
  ["sat_detumble_nominal", "sat_detumble_weak", "sat_detumble_phases",
   "sat3w_detumble_nominal", "sat3w_detumble_weak", "sat3w_detumble_phases"]

/-- **Declared counts**: proved outside the detumble family, refuted (model defects), the
detumble family (also proved, listed apart for its band audit). `(30, 9, 6)` until the
2026-10-10 repairs of the nine refuted models; `(39, 0, 6)` then, `(40, 0, 6)` with
`watertank_twospeed` (2026-10-11). -/
def wfDeclared : ℕ × ℕ × ℕ := (44, 0, 6)

/-- The suite's benchmark names, in the order of the IR table. -/
def suiteNames : List String :=
  ["acc_spoof_lag", "acc_spoof_limp", "acc_tune_lag", "acc_tune_limp", "airheader_dos_3to1",
   "arm_plateau_crit",
   "arm_plateau_profiles", "arm_plateau_slow", "charger_fast_setpoints",
   "charger_fast_tapers", "drl_car_stop", "drl_lane_control", "freedm_meter",
   "hvac_fan_staging",
   "match_multi_rate", "platoon3_linkloss", "platoon3_profiles", "platoon_delay_linkloss",
   "platoon_delay_profiles", "quad_light_airframe_20", "quad_light_lag",
   "quad_light_profiles", "rover_attitude_6to8", "rover_attitude_8to12",
   "rover_ladder_2to3", "rover_ladder_2to4", "rover_ladder_2to6", "rover_ladder_3to6",
   "rover_ladder_6to8", "rover_ladder_8to12", "rover_lateral_6to8",
   "rover_lateral_8to12", "rover_patrol_lag", "rover_patrol_zones", "rover_rollover_6to12",
   "rover_rollover_6to7", "rover_rollover_7to12",
   "rover_terrain_2to4", "rover_terrain_4to6", "rover_terrain_6to12",
   "sat3w_detumble_nominal", "sat3w_detumble_phases", "sat3w_detumble_weak",
   "sat_detumble_nominal", "sat_detumble_phases", "sat_detumble_weak", "tank_dos_3to1",
   "vehicle_hypercert",
   "watertank", "watertank_twospeed"]

/-- `suiteNames` IS the name column of the kernel-checked IR table of the suite. -/
theorem suiteNames_eq : Parse.benchIRTableV2.map Prod.fst = suiteNames := rfl

/-- The declared counts are the lists' lengths, and the three lists together are a
permutation of the suite's 50 benchmarks (disjoint, nothing missing). -/
theorem wf_coverage :
    (wfProved.length, wfRefuted.length, wfBand.length) = wfDeclared ∧
    (wfProved ++ wfRefuted ++ wfBand).Perm (Parse.benchIRTableV2.map Prod.fst) := by
  rw [suiteNames_eq]
  exact ⟨rfl, by decide⟩

end WellFormedBattery

/-! ## Proved (44, outside the detumble family): Assumption 1 at every mode -/

#print axioms V2DrlCarStop.drl_car_stop_wellFormedR_direct
#print axioms V2DrlLaneControl.drl_lane_control_wellFormedR_direct
#print axioms V2FreedmMeter.freedm_meter_wellFormedR_direct
#print axioms ChoiceVehicleHypercert.wellFormedR

#print axioms V2Watertank.watertank_wellFormedR
#print axioms V2WatertankTwospeed.watertank_twospeed_wellFormedR
#print axioms V2TankDos3to1.tank_dos_3to1_wellFormedR
#print axioms V2AirheaderDos3to1.airheader_dos_3to1_wellFormedR
#print axioms V2HvacFanStaging.hvac_fan_staging_wellFormedR
#print axioms V2AccSpoofLag.acc_spoof_lag_wellFormedR
#print axioms V2AccSpoofLimp.acc_spoof_limp_wellFormedR
#print axioms V2AccTuneLag.acc_tune_lag_wellFormedR
#print axioms V2AccTuneLimp.acc_tune_limp_wellFormedR
#print axioms V2ChargerFastSetpoints.charger_fast_setpoints_wellFormedR
#print axioms V2ChargerFastTapers.charger_fast_tapers_wellFormedR
#print axioms V2QuadLightLag.quad_light_lag_wellFormedR
#print axioms V2RoverPatrolZonesGuarded.rover_patrol_zones_wellFormedR
#print axioms V2RoverPatrolLagGuarded.rover_patrol_lag_wellFormedR
#print axioms V2RoverRollover7to12Guarded.rover_rollover_7to12_wellFormedR
#print axioms MatchMultiRateGuarded.match_multi_rate_wellFormedR
#print axioms RoverLadder2to3Guarded.rover_ladder_2to3_wellFormedR
#print axioms RoverLadder3to6Guarded.rover_ladder_3to6_wellFormedR
#print axioms RoverLadder6to8Guarded.rover_ladder_6to8_wellFormedR
#print axioms RoverLadder8to12Guarded.rover_ladder_8to12_wellFormedR
#print axioms RoverLadder2to4Guarded.rover_ladder_2to4_wellFormedR
#print axioms RoverLadder2to6Guarded.rover_ladder_2to6_wellFormedR
#print axioms RoverTerrain2to4Guarded.rover_terrain_2to4_wellFormedR
#print axioms RoverTerrain6to12Guarded.rover_terrain_6to12_wellFormedR
#print axioms RoverTerrain4to6Guarded.rover_terrain_4to6_wellFormedR
#print axioms RoverAttitude6to8Guarded.rover_attitude_6to8_wellFormedR
#print axioms RoverAttitude8to12Guarded.rover_attitude_8to12_wellFormedR
#print axioms RoverLateral6to8Guarded.rover_lateral_6to8_wellFormedR
#print axioms RoverLateral8to12Guarded.rover_lateral_8to12_wellFormedR
#print axioms RoverRollover6to12Guarded.rover_rollover_6to12_wellFormedR
#print axioms RoverRollover6to7Guarded.rover_rollover_6to7_wellFormedR

/-! ## Repaired 2026-10-10 (9, among the 40): Assumption 1 at every mode, and at the repaired
modes -/

#print axioms V2ArmPlateauCrit.arm_plateau_crit_wellFormedR
#print axioms V2ArmPlateauProfiles.arm_plateau_profiles_wellFormedR
#print axioms V2ArmPlateauSlow.arm_plateau_slow_wellFormedR
#print axioms V2PlatoonDelayLinkloss.platoon_delay_linkloss_wellFormedR
#print axioms V2PlatoonDelayLinkloss.platoon_delay_linkloss_wellFormedR_brake
#print axioms V2PlatoonDelayProfiles.platoon_delay_profiles_wellFormedR
#print axioms V2PlatoonDelayProfiles.platoon_delay_profiles_wellFormedR_brake
#print axioms V2Platoon3Linkloss.platoon3_linkloss_wellFormedR
#print axioms V2Platoon3Linkloss.platoon3_linkloss_wellFormedR_brake
#print axioms V2Platoon3Profiles.platoon3_profiles_wellFormedR
#print axioms V2Platoon3Profiles.platoon3_profiles_wellFormedR_brake
#print axioms V2QuadLightAirframe20.quad_light_airframe_20_wellFormedR
#print axioms V2QuadLightAirframe20.quad_light_airframe_20_wellFormedR_limit
#print axioms V2QuadLightProfiles.quad_light_profiles_wellFormedR
#print axioms V2QuadLightProfiles.quad_light_profiles_wellFormedR_limit

/-! ## The detumble family (6): Assumption 1 unconditional (the momentum band is part of the
right evolve domain since 2026-10-15), and the band invariant as a model fact -/

#print axioms V2SatDetumbleNominal.sat_detumble_nominal_wellFormedR
#print axioms V2SatDetumbleNominal.sat_detumble_nominal_band_invariant
#print axioms V2SatDetumbleWeak.sat_detumble_weak_wellFormedR
#print axioms V2SatDetumbleWeak.sat_detumble_weak_band_invariant
#print axioms V2SatDetumblePhases.sat_detumble_phases_wellFormedR
#print axioms V2SatDetumblePhases.sat_detumble_phases_band_invariant
#print axioms V2Sat3wDetumbleNominal.sat3w_detumble_nominal_wellFormedR
#print axioms V2Sat3wDetumbleNominal.sat3w_detumble_nominal_band_invariant
#print axioms V2Sat3wDetumbleWeak.sat3w_detumble_weak_wellFormedR
#print axioms V2Sat3wDetumbleWeak.sat3w_detumble_weak_band_invariant
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_wellFormedR
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_band_invariant

/-! ## The generic layer -/

#print axioms wellFormedR_ladder
#print axioms not_wellFormedR_of_run
#print axioms not_wellFormedR_of_noRun
#print axioms wellFormedR_switchLegal
#print axioms exists_contract_run
#print axioms exists_rate_run
#print axioms exists_of_HExistSegB_zero
#print axioms DLCalTiming.ODESol.coord_le_barrier
#print axioms DLCalTiming.ODESol.affine_const
#print axioms Platoon3Link.link_guard_Ronly
#print axioms Platoon3Link.brake_guard_Ronly
#print axioms Platoon3Link.solB_sol
#print axioms WellFormedBattery.wf_coverage

end RelCertifier
