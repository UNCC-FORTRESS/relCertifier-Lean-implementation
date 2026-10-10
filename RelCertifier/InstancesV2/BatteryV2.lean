/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 battery: the paper's Theorem 3 per benchmark, axiom-audited on every build

`benchmarks/suite_v2` (45 benchmarks, all CERTIFIED with `RELCERT_IMPLIED_CUT=1`). Every
theorem is imported here and its axioms are re-emitted on every build (`lake build
RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms"`), so the audit cannot
drift from the theorems.

**The statement.** Theorem 3 over the GUARDED right automaton: every right edge tests the
lowered guard of the mode it enters (the paper's `?guard_m(x)`), proved per instance
(`Gr_guards` / `GrG_guards` / `GrPG_guards`), with the loop invariant carrying the
MODE-CONSISTENT region `regionG guard cuts q = guard q ∧ cuts q` of the right's current mode
(`Proofs/Encoding/GuardedSwitch.lean`; one uniform shape for all 45; no Assumption-1
hypothesis, no new axiom, the declared rows unchanged). The groups:

* **Theorem 3, guarded, every window length: 39 benchmarks** (`#print` group 1).
* **Theorem 3, guarded, windows `dt < 1`: `refinement_ladder_rover_rung2c`** (group 2); for
  `dt ≥ 1` its guarded statement is false (`docs/GUARDED-SWITCHING.md` §4).
* **Machine-checked refutations of the guarded statement** (group 3):
  `platoon3_profiles` (every `dt ≥ 1`) and `platoon3_linkloss` (every `dt > 0`).
* **The `⊤`-guarded relaxation only** (group 4): the five benchmarks without a guarded
  theorem for every `dt` (`refinement_ladder_rover_rung2_3to6`, `story2_lateral_rung_a_8dof`,
  `story2_lateral_rung_b_12dof`, the two platoon3 benchmarks) and `rung2c`'s every-`dt`
  relaxation. For the first three the guarded statement is false for every `dt > 0` by the
  argument of `docs/GUARDED-SWITCHING.md` §4 (not kernel-checked).
* Theorem 2 of `match_multi_rate`'s pruned edge, and the generic lemmas.

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
-- machine-checked refutations of the guarded statement
import RelCertifier.InstancesV2.Platoon3ProfilesGuardedRefuted
import RelCertifier.InstancesV2.Platoon3LinklossGuardedRefuted
-- the `⊤`-guarded relaxation only
import RelCertifier.InstancesV2.Modal.Platoon3Profiles
import RelCertifier.InstancesV2.Modal.Platoon3Linkloss
import RelCertifier.Instances.RoverLadderRung2Modal
import RelCertifier.Instances.RoverRung2cModal
import RelCertifier.Instances.Story2LateralAModal
import RelCertifier.Instances.Story2LateralBModal

namespace RelCertifier

/-! ## 1. Theorem 3 over the GUARDED right automaton, every window length (39 benchmarks)

Statement shape (all 39): `RFormula.rvalid (theorem3Form L (rightAutomatonBody G mv)
(… (mvRegionR mv gregion G.modes.length)))` (mode-keyed instances: inside `psiK`) with every
edge of `G` testing `hostGuard … Side.R (m e.tgt)` and `gregion q = regionG guard cuts q`
(`guard q ∧ cuts q`). Every switch of every response is kernel-checked legal. -/

-- the 22 benchmarks whose certificate response was already legal
#print axioms V2Watertank.watertank_modal
#print axioms V2PlatoonDelayProfiles.platoon_delay_profiles_modal
#print axioms V2AccSpoofLimp.acc_spoof_limp_modeKeyed
#print axioms V2AccTuneLimp.acc_tune_limp_modeKeyed
#print axioms V2PlatoonDelayLinkloss.platoon_delay_linkloss_modeKeyed
#print axioms V2QuadLightAirframe20.quad_light_airframe_20_modal
#print axioms V2QuadLightProfiles.quad_light_profiles_modal
#print axioms V2QuadLightLag.quad_light_lag_modal
#print axioms V2ChargerFastSetpoints.charger_fast_setpoints_modal
#print axioms V2AccTuneLag.acc_tune_lag_modal
#print axioms V2AccSpoofLag.acc_spoof_lag_modal
#print axioms V2ChargerFastTapers.charger_fast_tapers_modal
#print axioms V2ArmPlateauCrit.arm_plateau_crit_modal
#print axioms V2ArmPlateauProfiles.arm_plateau_profiles_modal
#print axioms V2SatDetumbleNominal.sat_detumble_nominal_modal
#print axioms V2SatDetumbleWeak.sat_detumble_weak_modal
#print axioms V2Sat3wDetumbleNominal.sat3w_detumble_nominal_modal
#print axioms V2Sat3wDetumbleWeak.sat3w_detumble_weak_modal
#print axioms V2SatDetumblePhases.sat_detumble_phases_modeKeyed
#print axioms V2Sat3wDetumblePhases.sat3w_detumble_phases_modeKeyed
#print axioms Rover3tierRung12Guarded.rover3tier_rung12_modeKeyed_guarded
#print axioms MatchMultiRateGuarded.match_multi_rate_guarded
-- the 17 benchmarks with a new legal response (climbs, synchronized climbs, catch-ups)
#print axioms V2ArmPlateauSlow.arm_plateau_slow_modal
#print axioms V2RoverPatrolZonesGuarded.rover_patrol_zones_guarded
#print axioms V2RoverPatrolRefineGuarded.rover_patrol_refine_guarded
#print axioms V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_guarded
#print axioms RoverLadderRung1Guarded.rover_ladder_rung1_guarded
#print axioms RoverLadderRung3Guarded.rover_ladder_rung3_6to8_guarded
#print axioms RoverLadderRung4Guarded.rover_ladder_rung4_8to12_guarded
#print axioms RoverDofTerrainRung1Guarded.rover_dof_terrain_rung1_guarded
#print axioms RoverDofTerrainRung2Guarded.rover_dof_terrain_rung2_guarded
#print axioms RoverDofTerrainRung3Guarded.rover_dof_terrain_rung3_guarded
#print axioms RoverDofTerrainRung38dGuarded.rover_dof_terrain_rung3_8d_guarded
#print axioms RoverRung26dofGuarded.rung2_6dof_guarded
#print axioms RoverRung2b6dofGuarded.rung2b_6dof_guarded
#print axioms Story1AttdistRungAGuarded.story1_attdist_rung_a_guarded
#print axioms Story1AttdistRungBGuarded.story1_attdist_rung_b_guarded
#print axioms Story3RolloverBaseGuarded.story3_rollover_base_guarded
#print axioms Story3RolloverRungAGuarded.story3_rollover_rung_a_guarded

/-! ## 2. Theorem 3 over the GUARDED right automaton, windows `dt < 1` (1 benchmark)

`refinement_ladder_rover_rung2c`: the lockstep rows forbid a mid-window switch, so the
response mirrors the window in the window's band; for `dt ≥ 1` a `STEEP` window from
`s = 0.59` carries the odometer past `1.4` and the guarded statement is false. -/

#print axioms RoverRung2cGuarded.rover_rung2c_guarded

/-! ## 3. The guarded statement is false: machine-checked refutations (2 benchmarks) -/

#print axioms V2Platoon3ProfilesRefuted.platoon3_profiles_guarded_false
#print axioms V2Platoon3LinklossRefuted.platoon3_linkloss_guarded_false

/-! ## 4. Theorem 3 over the `⊤`-guarded relaxation only

About the declared-successor relaxation of `R` (edge guards `⊤`, invariant without the
guard): the five benchmarks with no guarded theorem for every `dt`, and `rung2c` for every
`dt`. -/

#print axioms RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal
#print axioms Story2LateralAModal.story2_lateral_rung_a_modal
#print axioms Story2LateralBModal.story2_lateral_rung_b_modal
#print axioms V2Platoon3Profiles.platoon3_profiles_modal
#print axioms V2Platoon3Linkloss.platoon3_linkloss_modeKeyed
#print axioms RoverRung2cModal.rover_rung2c_modal

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
#print axioms Hmulti_regionG
#print axioms HMode_regionG
#print axioms hddF_multiR_G
#print axioms hddF_modeKeyed_G
#print axioms gresp_of_rresp
#print axioms explicit_sol
#print axioms LadderRun.climb
#print axioms LadderRun.climbD
#print axioms syncClimb
#print axioms syncWindow
#print axioms joint_of_sols_lam

end RelCertifier
