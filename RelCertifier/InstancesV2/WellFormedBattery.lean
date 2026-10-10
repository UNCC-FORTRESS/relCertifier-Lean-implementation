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

**Results (all 45 benchmarks; declared counts `wfDeclared`, kernel-checked against the
suite's IR table by `wf_coverage`).**

* **Proved, 39** (`<bench>_wellFormedR`): every mode. Z3-free (no verdict leaf). Nine of them
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
* **On the conserved momentum band, 6** (`<bench>_wellFormedR_onBand` with
  `<bench>_band_invariant`; and `<bench>_wellFormedR_false` for the literal predicate):
  `sat_detumble_{nominal,weak,phases}`, `sat3w_detumble_{nominal,weak,phases}`. Clause (i)
  fails at the edge of the wheel-momentum box (`h = 2`, `w3 = 0.4`: `h + 5 w3` is conserved
  and would leave `|h| ≤ 2`); on the band `|h + 5 w3| ≤ 2` (three bands for `sat3w`), which
  every mode's flow keeps, Assumption 1 holds.

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`, nothing else (every proof is
Z3-free). `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on
axioms"`.
-/
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.WellFormed.Watertank
import RelCertifier.InstancesV2.WellFormed.AccSpoofLag
import RelCertifier.InstancesV2.WellFormed.AccSpoofLimp
import RelCertifier.InstancesV2.WellFormed.AccTuneLag
import RelCertifier.InstancesV2.WellFormed.AccTuneLimp
import RelCertifier.InstancesV2.WellFormed.ChargerFastSetpoints
import RelCertifier.InstancesV2.WellFormed.ChargerFastTapers
import RelCertifier.InstancesV2.WellFormed.QuadLightLag
import RelCertifier.InstancesV2.WellFormed.RoverPatrolZones
import RelCertifier.InstancesV2.WellFormed.RoverPatrolRefine
import RelCertifier.InstancesV2.WellFormed.Story3RolloverRungB
import RelCertifier.Instances.WellFormed.MatchMultiRate
import RelCertifier.Instances.WellFormed.Rover3tierRung12
import RelCertifier.Instances.WellFormed.RoverLadderRung1
import RelCertifier.Instances.WellFormed.RoverLadderRung2
import RelCertifier.Instances.WellFormed.RoverLadderRung3
import RelCertifier.Instances.WellFormed.RoverLadderRung4
import RelCertifier.Instances.WellFormed.RoverRung26dof
import RelCertifier.Instances.WellFormed.RoverRung2b6dof
import RelCertifier.Instances.WellFormed.RoverRung2c
import RelCertifier.Instances.WellFormed.RoverDofTerrainRung1
import RelCertifier.Instances.WellFormed.RoverDofTerrainRung2
import RelCertifier.Instances.WellFormed.RoverDofTerrainRung3
import RelCertifier.Instances.WellFormed.RoverDofTerrainRung38d
import RelCertifier.Instances.WellFormed.Story1AttdistRungA
import RelCertifier.Instances.WellFormed.Story1AttdistRungB
import RelCertifier.Instances.WellFormed.Story2LateralA
import RelCertifier.Instances.WellFormed.Story2LateralB
import RelCertifier.Instances.WellFormed.Story3RolloverBase
import RelCertifier.Instances.WellFormed.Story3RolloverRungA
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

namespace RelCertifier
namespace WellFormedBattery

/-- The benchmarks whose right model satisfies Assumption 1 at every mode. -/
def wfProved : List String :=
  ["arm_plateau_crit", "arm_plateau_profiles", "arm_plateau_slow", "platoon_delay_linkloss",
   "platoon_delay_profiles", "platoon3_linkloss", "platoon3_profiles",
   "quad_light_airframe_20", "quad_light_profiles",
   "watertank", "acc_spoof_lag", "acc_spoof_limp", "acc_tune_lag", "acc_tune_limp",
   "charger_fast_setpoints", "charger_fast_tapers", "quad_light_lag", "rover_patrol_zones",
   "rover_patrol_refine", "story3_rollover_ladder_rung_b", "match_multi_rate",
   "rover3tier_rung12", "refinement_ladder_rover_rung1_2to3",
   "refinement_ladder_rover_rung2_3to6", "refinement_ladder_rover_rung3_6to8",
   "refinement_ladder_rover_rung4_8to12", "refinement_ladder_rover_rung2_6dof",
   "refinement_ladder_rover_rung2b_6dof", "refinement_ladder_rover_rung2c_6dof",
   "rover_dof_terrain_rung1", "rover_dof_terrain_rung2", "rover_dof_terrain_rung3",
   "rover_dof_terrain_rung3_8d", "story1_attdist_rung_a_6to8", "story1_attdist_rung_b_12dof",
   "story2_lateral_rung_a_8dof", "story2_lateral_rung_b_12dof", "story3_rollover_base_12dof",
   "story3_rollover_ladder_rung_a"]

/-- The benchmarks whose right model violates Assumption 1 (none since the 2026-10-10
repairs; the nine refuted until then are in `wfProved`). -/
def wfRefuted : List String := []

/-- The benchmarks where Assumption 1 holds on the conserved momentum band (and fails off
it). -/
def wfBand : List String :=
  ["sat_detumble_nominal", "sat_detumble_weak", "sat_detumble_phases",
   "sat3w_detumble_nominal", "sat3w_detumble_weak", "sat3w_detumble_phases"]

/-- **Declared counts**: proved, refuted (model defects), band-relative. `(30, 9, 6)` until the
2026-10-10 repairs of the nine refuted models; now `(39, 0, 6)`. -/
def wfDeclared : ℕ × ℕ × ℕ := (39, 0, 6)

/-- The suite's benchmark names, in the order of the IR table. -/
def suiteNames : List String :=
  ["acc_spoof_lag", "acc_spoof_limp", "acc_tune_lag", "acc_tune_limp", "arm_plateau_crit",
   "arm_plateau_profiles", "arm_plateau_slow", "charger_fast_setpoints",
   "charger_fast_tapers", "match_multi_rate", "platoon3_linkloss", "platoon3_profiles",
   "platoon_delay_linkloss", "platoon_delay_profiles", "quad_light_airframe_20",
   "quad_light_lag", "quad_light_profiles", "refinement_ladder_rover_rung1_2to3",
   "refinement_ladder_rover_rung2_3to6", "refinement_ladder_rover_rung2_6dof",
   "refinement_ladder_rover_rung2b_6dof", "refinement_ladder_rover_rung2c_6dof",
   "refinement_ladder_rover_rung3_6to8", "refinement_ladder_rover_rung4_8to12",
   "rover3tier_rung12", "rover_dof_terrain_rung1", "rover_dof_terrain_rung2",
   "rover_dof_terrain_rung3", "rover_dof_terrain_rung3_8d", "rover_patrol_refine",
   "rover_patrol_zones", "sat3w_detumble_nominal", "sat3w_detumble_phases",
   "sat3w_detumble_weak", "sat_detumble_nominal", "sat_detumble_phases",
   "sat_detumble_weak", "story1_attdist_rung_a_6to8", "story1_attdist_rung_b_12dof",
   "story2_lateral_rung_a_8dof", "story2_lateral_rung_b_12dof",
   "story3_rollover_base_12dof", "story3_rollover_ladder_rung_a",
   "story3_rollover_ladder_rung_b", "watertank"]

/-- `suiteNames` IS the name column of the kernel-checked IR table of the suite. -/
theorem suiteNames_eq : Parse.benchIRTableV2.map Prod.fst = suiteNames := rfl

/-- The declared counts are the lists' lengths, and the three lists together are a
permutation of the suite's 45 benchmarks (disjoint, nothing missing). -/
theorem wf_coverage :
    (wfProved.length, wfRefuted.length, wfBand.length) = wfDeclared ∧
    (wfProved ++ wfRefuted ++ wfBand).Perm (Parse.benchIRTableV2.map Prod.fst) := by
  rw [suiteNames_eq]
  exact ⟨rfl, by decide⟩

end WellFormedBattery

/-! ## Proved (39): Assumption 1 at every mode -/

#print axioms V2Watertank.watertank_wellFormedR
#print axioms V2AccSpoofLag.acc_spoof_lag_wellFormedR
#print axioms V2AccSpoofLimp.acc_spoof_limp_wellFormedR
#print axioms V2AccTuneLag.acc_tune_lag_wellFormedR
#print axioms V2AccTuneLimp.acc_tune_limp_wellFormedR
#print axioms V2ChargerFastSetpoints.charger_fast_setpoints_wellFormedR
#print axioms V2ChargerFastTapers.charger_fast_tapers_wellFormedR
#print axioms V2QuadLightLag.quad_light_lag_wellFormedR
#print axioms V2RoverPatrolZonesGuarded.rover_patrol_zones_wellFormedR
#print axioms V2RoverPatrolRefineGuarded.rover_patrol_refine_wellFormedR
#print axioms V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_wellFormedR
#print axioms MatchMultiRateGuarded.match_multi_rate_wellFormedR
#print axioms Rover3tierRung12Guarded.rover3tier_rung12_wellFormedR
#print axioms RoverLadderRung1Guarded.refinement_ladder_rover_rung1_2to3_wellFormedR
#print axioms RoverLadderRung2Guarded.refinement_ladder_rover_rung2_3to6_wellFormedR
#print axioms RoverLadderRung3Guarded.refinement_ladder_rover_rung3_6to8_wellFormedR
#print axioms RoverLadderRung4Guarded.refinement_ladder_rover_rung4_8to12_wellFormedR
#print axioms RoverRung26dofGuarded.refinement_ladder_rover_rung2_6dof_wellFormedR
#print axioms RoverRung2b6dofGuarded.refinement_ladder_rover_rung2b_6dof_wellFormedR
#print axioms RoverRung2cGuarded.refinement_ladder_rover_rung2c_6dof_wellFormedR
#print axioms RoverDofTerrainRung1Guarded.rover_dof_terrain_rung1_wellFormedR
#print axioms RoverDofTerrainRung2Guarded.rover_dof_terrain_rung2_wellFormedR
#print axioms RoverDofTerrainRung3Guarded.rover_dof_terrain_rung3_wellFormedR
#print axioms RoverDofTerrainRung38dGuarded.rover_dof_terrain_rung3_8d_wellFormedR
#print axioms Story1AttdistRungAGuarded.story1_attdist_rung_a_6to8_wellFormedR
#print axioms Story1AttdistRungBGuarded.story1_attdist_rung_b_12dof_wellFormedR
#print axioms Story2LateralAGuarded.story2_lateral_rung_a_8dof_wellFormedR
#print axioms Story2LateralBGuarded.story2_lateral_rung_b_12dof_wellFormedR
#print axioms Story3RolloverBaseGuarded.story3_rollover_base_12dof_wellFormedR
#print axioms Story3RolloverRungAGuarded.story3_rollover_ladder_rung_a_wellFormedR

/-! ## Repaired 2026-10-10 (9, among the 39): Assumption 1 at every mode, and at the repaired
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

/-! ## On the momentum band (6): Assumption 1 on the band, the band invariant, and the
literal predicate refuted -/

#print axioms V2SatDetumbleNominal.sat_detumble_nominal_wellFormedR_onBand
#print axioms V2SatDetumbleNominal.sat_detumble_nominal_band_invariant
#print axioms V2SatDetumbleNominal.sat_detumble_nominal_wellFormedR_false
#print axioms V2SatDetumbleWeak.sat_detumble_weak_wellFormedR_onBand
#print axioms V2SatDetumbleWeak.sat_detumble_weak_band_invariant
#print axioms V2SatDetumbleWeak.sat_detumble_weak_wellFormedR_false
#print axioms V2SatDetumblePhases.sat_detumble_phases_wellFormedR_onBand
#print axioms V2SatDetumblePhases.sat_detumble_phases_band_invariant
#print axioms V2SatDetumblePhases.sat_detumble_phases_wellFormedR_false
#print axioms V2Sat3wDetumbleNominal.sat3w_detumble_nominal_wellFormedR_onBand
#print axioms V2Sat3wDetumbleNominal.sat3w_detumble_nominal_band_invariant
#print axioms V2Sat3wDetumbleNominal.sat3w_detumble_nominal_wellFormedR_false
#print axioms V2Sat3wDetumbleWeak.sat3w_detumble_weak_wellFormedR_onBand
#print axioms V2Sat3wDetumbleWeak.sat3w_detumble_weak_band_invariant
#print axioms V2Sat3wDetumbleWeak.sat3w_detumble_weak_wellFormedR_false
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_wellFormedR_onBand
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_band_invariant
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_wellFormedR_false

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
