/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 battery: the paper's Theorem 3 per benchmark, axiom-audited on every build

`benchmarks/suite_v2` (45 benchmarks, all CERTIFIED with `RELCERT_IMPLIED_CUT=1`). Every
theorem is imported here and its axioms are re-emitted on every build (`lake build
RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms"`), so the audit cannot
drift from the theorems.

**The statement (all 45, one shape).** Theorem 3 with the paper's LEFT program, the
guard-gated left automaton `leftAutomatonBody A u_L` (`?(u_L = m') ; ⋃_{t ∈ next m'} ?guard_t ;
u_L := t ; window_t`, jump then flow, the declared successors and lowered guards read from the
IR), against the GUARDED right automaton (every edge tests the lowered guard of the mode it
enters, `Gr_guards`; flow then jump), with the loop invariant `psiK u_L ϕ … (mvRegionR mv
gregion …)`: the declared rows keyed by `u_L` (one row for every left mode in the
mode-independent benchmarks), both evolve envelopes, `u_L` a declared left mode, and the right
in the MODE-CONSISTENT region `regionG guard cuts q = guard q ∧ cuts q` of its current mode
(`Proofs/Encoding/GuardedSwitch.lean`). No Assumption-1 hypothesis, no new axiom. The
mode-independent benchmarks are first proved over the choice of their (guard-gated or plain)
windows and carried to the left automaton by the generic bridge
`theorem3_leftAut_of_choice` (`Proofs/Encoding/LeftAutUniform.lean`, proved once): the left
automaton only removes left runs and adds `u_L`. Window lengths: every `dt` for 44
benchmarks; `refinement_ladder_rover_rung2c` for every window up to its control interval,
`dt ≤ ε_L = 1`. The two `platoon3` benchmarks are stated on their repaired model (operating-range
guards, `docs/SUITE-REDESIGN.md` §20).

* Generic lemmas the instances rest on, and Theorem 2 of `match_multi_rate`'s pruned edge.

Expected and observed axioms: the three standard ones plus `z3_unsat_sound` where a verdict
pack enters.

* Data, kernel-checked for all 45: the IR literals (`BenchIR/`, drift-checked against the
  files by `relcert-test` `[ir-drift-v2]`), the extended cut certificates
  (`Cuts/<b>.lean`, `evolStrengtheningWFX … = true` by `rfl`), the cover replays
  (`CoverReplay.lean`, `decideCovered` by `decide`).
* Packs are rows of `VerdictsV2.RunV2.packsV2` (pinned in `VerdictsV2/PinsV2`) and, for the
  carried-over benchmarks, of `Verdicts/RunModal.modalTable` (re-run by `relcert
  --run-verdicts-v2`, phase "copied benchmarks"); `match_multi_rate_nonconn`'s hypothesis is
  pinned to the suite_v2 non-connection phase by `VerdictsV2/NonConnPinV2`.
* Declared counts: `VerdictsV2/CoveragePinsV2` derives every declared phase count from the
  tables.
-/
import RelCertifier.InstancesV2.SameIR
import RelCertifier.InstancesV2.CoverReplay
import RelCertifier.VerdictsV2.PinsV2
import RelCertifier.VerdictsV2.CoveragePinsV2
import RelCertifier.VerdictsV2.NonConnPinV2
-- Theorem 3 over the guarded right automaton: suite_v2 instances
import RelCertifier.InstancesV2.Modal.Watertank
import RelCertifier.InstancesV2.Modal.PlatoonDelayProfiles
import RelCertifier.InstancesV2.Modal.AccSpoofLimp
import RelCertifier.InstancesV2.Modal.AccTuneLimp
import RelCertifier.InstancesV2.Modal.PlatoonDelayLinkloss
import RelCertifier.InstancesV2.Modal.QuadLightAirframe20
import RelCertifier.InstancesV2.Modal.QuadLightProfiles
import RelCertifier.InstancesV2.Modal.QuadLightLag
import RelCertifier.InstancesV2.Modal.ChargerFastSetpoints
import RelCertifier.InstancesV2.Modal.AccTuneLag
import RelCertifier.InstancesV2.Modal.AccSpoofLag
import RelCertifier.InstancesV2.Modal.ChargerFastTapers
import RelCertifier.InstancesV2.Modal.ArmPlateauCrit
import RelCertifier.InstancesV2.Modal.ArmPlateauProfiles
import RelCertifier.InstancesV2.Modal.ArmPlateauSlow
import RelCertifier.InstancesV2.Modal.SatDetumbleNominal
import RelCertifier.InstancesV2.Modal.SatDetumbleWeak
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleNominal
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleWeak
import RelCertifier.InstancesV2.Modal.SatDetumblePhases
import RelCertifier.InstancesV2.Modal.Sat3wDetumblePhases
import RelCertifier.InstancesV2.Modal.RoverPatrolZonesGuarded
import RelCertifier.InstancesV2.Modal.RoverPatrolRefineGuarded
import RelCertifier.InstancesV2.Modal.Story3RolloverRungBGuarded
-- Theorem 3 over the guarded right automaton: carried-over benchmarks
import RelCertifier.Instances.MatchMultiRatePruned
import RelCertifier.Instances.MatchMultiRateGuarded
import RelCertifier.Instances.Rover3tierRung12Guarded
import RelCertifier.Instances.RoverLadderRung1Guarded
import RelCertifier.Instances.RoverLadderRung3Guarded
import RelCertifier.Instances.RoverLadderRung4Guarded
import RelCertifier.Instances.RoverDofTerrainRung1Guarded
import RelCertifier.Instances.RoverDofTerrainRung2Guarded
import RelCertifier.Instances.RoverDofTerrainRung3Guarded
import RelCertifier.Instances.RoverDofTerrainRung38dGuarded
import RelCertifier.Instances.RoverRung26dofGuarded
import RelCertifier.Instances.RoverRung2b6dofGuarded
import RelCertifier.Instances.RoverRung2cGuarded
import RelCertifier.Instances.Story1AttdistRungAGuarded
import RelCertifier.Instances.Story1AttdistRungBGuarded
import RelCertifier.Instances.Story3RolloverBaseGuarded
import RelCertifier.Instances.Story3RolloverRungAGuarded
import RelCertifier.Instances.RoverLadderRung2Guarded
import RelCertifier.Instances.Story2LateralAGuarded
import RelCertifier.Instances.Story2LateralBGuarded
import RelCertifier.InstancesV2.Modal.Platoon3Profiles
import RelCertifier.InstancesV2.Modal.Platoon3Linkloss
-- the paper's left program for the mode-independent benchmarks (the generic bridge)
import RelCertifier.InstancesV2.LeftAutV2
import RelCertifier.Instances.LeftAutLegacy

namespace RelCertifier

/-! ## Theorem 3 with the paper's left program, over the guarded automata (all 45)

Statement shape (all 45): `RFormula.rvalid (theorem3Form (leftAutomatonBody A u_L)
(rightAutomatonBody G mv) (psiK u_L ϕ A.numModes domL domR (mvRegionR mv gregion …)))` with
every edge of `G` testing `hostGuard … Side.R (m e.tgt)`, every left edge testing the entered
left mode's lowered guard, and `gregion q = regionG guard cuts q` (`guard q ∧ cuts q`). -/

-- mode-independent invariant, suite_v2 (16), by the generic bridge
#print axioms V2Watertank.watertank_leftAut
#print axioms V2PlatoonDelayProfiles.platoon_delay_profiles_leftAut
#print axioms V2QuadLightAirframe20.quad_light_airframe_20_leftAut
#print axioms V2QuadLightProfiles.quad_light_profiles_leftAut
#print axioms V2QuadLightLag.quad_light_lag_leftAut
#print axioms V2ChargerFastSetpoints.charger_fast_setpoints_leftAut
#print axioms V2AccTuneLag.acc_tune_lag_leftAut
#print axioms V2AccSpoofLag.acc_spoof_lag_leftAut
#print axioms V2ChargerFastTapers.charger_fast_tapers_leftAut
#print axioms V2ArmPlateauCrit.arm_plateau_crit_leftAut
#print axioms V2ArmPlateauProfiles.arm_plateau_profiles_leftAut
#print axioms V2ArmPlateauSlow.arm_plateau_slow_leftAut
#print axioms V2SatDetumbleNominal.sat_detumble_nominal_leftAut
#print axioms V2SatDetumbleWeak.sat_detumble_weak_leftAut
#print axioms V2Sat3wDetumbleNominal.sat3w_detumble_nominal_leftAut
#print axioms V2Sat3wDetumbleWeak.sat3w_detumble_weak_leftAut
-- mode-independent invariant, carried-over (13), by the generic bridge
#print axioms MatchMultiRateGuarded.match_multi_rate_leftAut
#print axioms RoverLadderRung1Guarded.rover_ladder_rung1_leftAut
#print axioms RoverLadderRung3Guarded.rover_ladder_rung3_6to8_leftAut
#print axioms RoverLadderRung4Guarded.rover_ladder_rung4_8to12_leftAut
#print axioms RoverDofTerrainRung1Guarded.rover_dof_terrain_rung1_leftAut
#print axioms RoverDofTerrainRung2Guarded.rover_dof_terrain_rung2_leftAut
#print axioms RoverDofTerrainRung3Guarded.rover_dof_terrain_rung3_leftAut
#print axioms RoverDofTerrainRung38dGuarded.rover_dof_terrain_rung3_8d_leftAut
#print axioms RoverRung26dofGuarded.rung2_6dof_leftAut
#print axioms RoverRung2b6dofGuarded.rung2b_6dof_leftAut
#print axioms Story3RolloverBaseGuarded.story3_rollover_base_leftAut
#print axioms Story3RolloverRungAGuarded.story3_rollover_rung_a_leftAut
-- `refinement_ladder_rover_rung2c`: every window up to the control interval, `dt ≤ ε_L = 1`
#print axioms RoverRung2cGuarded.rover_rung2c_leftAut
-- mode-independent invariant, with the guard-gated left windows newly proved (3)
#print axioms RoverLadderRung2Guarded.rover_ladder_rung2_3to6_leftAut
#print axioms Story2LateralAGuarded.story2_lateral_rung_a_leftAut
#print axioms Story2LateralBGuarded.story2_lateral_rung_b_leftAut
-- `platoon3_profiles` (repaired model, §20 of docs/SUITE-REDESIGN.md)
#print axioms V2Platoon3Profiles.platoon3_profiles_leftAut
-- mode-keyed invariant (12)
#print axioms V2AccSpoofLimp.acc_spoof_limp_modeKeyed
#print axioms V2AccTuneLimp.acc_tune_limp_modeKeyed
#print axioms V2PlatoonDelayLinkloss.platoon_delay_linkloss_modeKeyed
#print axioms V2SatDetumblePhases.sat_detumble_phases_modeKeyed
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_modeKeyed
#print axioms Rover3tierRung12Guarded.rover3tier_rung12_modeKeyed_guarded
#print axioms V2RoverPatrolZonesGuarded.rover_patrol_zones_guarded
#print axioms V2RoverPatrolRefineGuarded.rover_patrol_refine_guarded
#print axioms V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_guarded
#print axioms Story1AttdistRungAGuarded.story1_attdist_rung_a_guarded
#print axioms Story1AttdistRungBGuarded.story1_attdist_rung_b_guarded
#print axioms V2Platoon3Linkloss.platoon3_linkloss_modeKeyed

/-! ## Theorem 2 of `match_multi_rate`'s pruned edge -/

#print axioms MatchMultiRatePruned.match_multi_rate_nonconn

/-! ## The generic layer the instances rest on -/

#print axioms couple_cutX
#print axioms modalVerdX_of_queries
#print axioms check_sound_multi_cutX
#print axioms evolStrengtheningWFX_entryL
#print axioms evolStrengtheningWFX_entryR
#print axioms guarded_rights_bridge
#print axioms hstep_assembled_GR
#print axioms gresp_final_choose
#print axioms gresp_final_run
#print axioms Hmulti_regionG
#print axioms HMode_regionG
#print axioms hddF_multiR_G
#print axioms hddF_modeKeyed_G
#print axioms theorem3_leftAut_of_choice
#print axioms theorem3_leftAut_of_choiceR
#print axioms boxle_Ronly_of_super
#print axioms Platoon3Link.link_bounds
#print axioms Platoon3Link.gap_floor_Ronly
#print axioms gresp_of_rresp
#print axioms explicit_sol
#print axioms LadderRun.climb
#print axioms LadderRun.climbD
#print axioms syncClimb
#print axioms syncWindow
#print axioms joint_of_sols_lam

end RelCertifier
