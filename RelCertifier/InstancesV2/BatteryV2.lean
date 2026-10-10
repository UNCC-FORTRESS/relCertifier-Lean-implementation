/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 battery: the paper's Theorem 3 per benchmark, axiom-audited on every build

`benchmarks/suite_v2` (45 benchmarks, all CERTIFIED with `RELCERT_IMPLIED_CUT=1`). Every
theorem is imported here and its axioms are re-emitted on every build (`lake build
RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms"`), so the audit cannot
drift from the theorems. 56 `#print axioms` lines, in four groups:

* **Theorem 3 over the GUARDED right automaton: 22 benchmarks.** Every right edge tests the
  lowered guard of the mode it enters (the paper's `?guard_m(x)`), proved per instance
  (`Gr_guards`); the response's every switch is kernel-checked legal
  (`Proofs/Encoding/GuardedSwitch.lean`). 20 suite_v2 instances (`Modal/`) and two carried-over
  benchmarks restated over the guarded automaton by an explicit catch-up
  (`Instances/Rover3tierRung12Guarded`, `Instances/MatchMultiRateGuarded`, both Z3-free).
* **Machine-checked refutations**: `rover_ladder_rung1_guarded_false` and
  `rover_patrol_zones_guarded_false`, the guarded statements of
  `refinement_ladder_rover_rung1_2to3` and `rover_patrol_zones` are false for every window
  length `dt > 0`.
* **Theorem 3 over the `⊤`-guarded relaxation only: 23 benchmarks.** For 21 the guarded
  statement is false as stated (a right state inside the invariant from which the guarded
  automaton has no step, while a left window breaks the row); for `platoon3_profiles` and
  `platoon3_linkloss` it is open (`docs/GUARDED-SWITCHING.md`).
* Theorem 2 of `match_multi_rate`'s pruned edge, and 8 generic lemmas.

Expected and observed axioms: the three standard ones plus `z3_unsat_sound` where a verdict
pack enters.

* Data, kernel-checked for all 45: the IR literals (`BenchIR/`, drift-checked against the
  files by `relcert-test` `[ir-drift-v2]`), the extended cut certificates
  (`Cuts/<b>.lean`, `evolStrengtheningWFX … = true` by `rfl`), the cover replays
  (`CoverReplay.lean`, `decideCovered` by `decide`).
* Packs are rows of `VerdictsV2.RunV2.packsV2` (pinned in `VerdictsV2/PinsV2`) and, for the
  carried-over benchmarks, of `Verdicts/RunModal.modalTable` (re-run by `relcert
  --run-verdicts-v2`, phase "copied benchmarks"); `match_multi_rate_nonconn`'s hypothesis is
  pinned to the suite_v2 non-connection phase by `VerdictsV2/NonConnPinV2`. The guarded
  theorems of `rover3tier_rung12` and `match_multi_rate` take no pack.
* Declared counts: `VerdictsV2/CoveragePinsV2` derives every declared phase count from the
  tables.
-/
import RelCertifier.InstancesV2.SameIR
import RelCertifier.InstancesV2.CoverReplay
import RelCertifier.VerdictsV2.PinsV2
import RelCertifier.VerdictsV2.CoveragePinsV2
import RelCertifier.VerdictsV2.NonConnPinV2
-- new suite_v2 instances
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
import RelCertifier.InstancesV2.Modal.Story3RolloverRungB
import RelCertifier.InstancesV2.Modal.SatDetumbleNominal
import RelCertifier.InstancesV2.Modal.Platoon3Profiles
import RelCertifier.InstancesV2.Modal.Platoon3Linkloss
import RelCertifier.InstancesV2.Modal.SatDetumbleWeak
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleNominal
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleWeak
import RelCertifier.InstancesV2.Modal.SatDetumblePhases
import RelCertifier.InstancesV2.Modal.Sat3wDetumblePhases
import RelCertifier.InstancesV2.Modal.RoverPatrolZones
import RelCertifier.InstancesV2.RoverPatrolZonesCounterexample
import RelCertifier.InstancesV2.Modal.RoverPatrolRefine
-- the 19 carried-over benchmarks: legacy theorems (their literal is the suite_v2 literal)
import RelCertifier.Instances.MatchMultiRatePruned
import RelCertifier.Instances.MatchMultiRateGuarded
import RelCertifier.Instances.RoverLadderRung1Modal
import RelCertifier.Instances.RoverLadderRung1Counterexample
import RelCertifier.Instances.RoverLadderRung2Modal
import RelCertifier.Instances.RoverRung26dofModal
import RelCertifier.Instances.RoverRung2b6dofModal
import RelCertifier.Instances.RoverRung2cModal
import RelCertifier.Instances.RoverLadderRung3Modal
import RelCertifier.Instances.RoverLadderRung4Modal
import RelCertifier.Instances.Rover3tierRung12Handoff
import RelCertifier.Instances.Rover3tierRung12Guarded
import RelCertifier.Instances.RoverDofTerrainRung1Modal
import RelCertifier.Instances.RoverDofTerrainRung2Modal
import RelCertifier.Instances.RoverDofTerrainRung3Modal
import RelCertifier.Instances.RoverDofTerrainRung38dModal
import RelCertifier.Instances.Story1AttdistRungAHandoff
import RelCertifier.Instances.Story1AttdistRungBHandoff
import RelCertifier.Instances.Story2LateralAModal
import RelCertifier.Instances.Story2LateralBModal
import RelCertifier.Instances.Story3RolloverBaseModal
import RelCertifier.Instances.Story3RolloverRungAModal

namespace RelCertifier

/-! ## Theorem 3 over the GUARDED right automaton (22 benchmarks)

Every right edge tests the lowered guard of the mode it enters (each instance's `Gr_guards`
/ `GrG_guards` / `GrPG_guards`); every switch of the response is kernel-checked legal
(`Proofs/Encoding/GuardedSwitch.lean`, `docs/GUARDED-SWITCHING.md`). -/

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

/-! ## The guarded statement is false as stated (machine-checked representatives)

`refinement_ladder_rover_rung1_2to3` (carried over) and `rover_patrol_zones` (suite_v2,
mode-keyed): the statements of `rover_ladder_rung1_modal` and `rover_patrol_zones_modeKeyed`
over the guarded right automaton fail for every `dt > 0` (a right state inside the invariant
from which the guarded automaton has no step; one left window breaks the row `v_L ≤ v_R`).
The same mechanism refutes the guarded statements of the other benchmarks of the
relaxation-only group below except the two platoon3 benchmarks
(`docs/GUARDED-SWITCHING.md` §4.3). -/

#print axioms RoverLadderRung1Counterexample.rover_ladder_rung1_guarded_false
#print axioms V2RoverPatrolZonesCounterexample.rover_patrol_zones_guarded_false

/-! ## Theorem 3 over the `⊤`-guarded relaxation only (23 benchmarks)

These theorems are about the declared-successor relaxation of `R` (edge guards `⊤`). For 21
of them the guarded statement is false as stated (a stuck right state inside the invariant,
`docs/GUARDED-SWITCHING.md` §4.3); for `platoon3_profiles` and `platoon3_linkloss` no legal
witness could be built from the certificate's response, and the guarded statement is open. -/

#print axioms V2ArmPlateauSlow.arm_plateau_slow_modal
#print axioms V2Story3RolloverRungB.story3_rollover_ladder_rung_b_modeKeyed
#print axioms V2Platoon3Profiles.platoon3_profiles_modal
#print axioms V2Platoon3Linkloss.platoon3_linkloss_modeKeyed
#print axioms V2RoverPatrolZones.rover_patrol_zones_modeKeyed
#print axioms V2RoverPatrolRefine.rover_patrol_refine_modeKeyed
#print axioms RoverLadderRung1Modal.rover_ladder_rung1_modal
#print axioms RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal
#print axioms RoverRung26dofModal.rung2_6dof_modal
#print axioms RoverRung2b6dofModal.rung2b_6dof_modal
#print axioms RoverRung2cModal.rover_rung2c_modal
#print axioms RoverLadderRung3Modal.rover_ladder_rung3_6to8_modal
#print axioms RoverLadderRung4Modal.rover_ladder_rung4_8to12_modal
#print axioms RoverDofTerrainRung1Modal.rover_dof_terrain_rung1_modal
#print axioms RoverDofTerrainRung2Modal.rover_dof_terrain_rung2_modal
#print axioms RoverDofTerrainRung3Modal.rover_dof_terrain_rung3_modal
#print axioms RoverDofTerrainRung38dModal.rover_dof_terrain_rung3_8d_modal
#print axioms Story1AttdistRungAHandoff.story1_attdist_rung_a_modeKeyed
#print axioms Story1AttdistRungBHandoff.story1_attdist_rung_b_modeKeyed
#print axioms Story2LateralAModal.story2_lateral_rung_a_modal
#print axioms Story2LateralBModal.story2_lateral_rung_b_modal
#print axioms Story3RolloverBaseModal.story3_rollover_base_modal
#print axioms Story3RolloverRungAModal.story3_rollover_rung_a_modal

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

end RelCertifier
