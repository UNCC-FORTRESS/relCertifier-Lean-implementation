/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 battery — the paper's Theorem 3 per benchmark, axiom-audited on every build

`benchmarks/suite_v2` (45 benchmarks, all CERTIFIED with `RELCERT_IMPLIED_CUT=1`). For each
benchmark that carries its theorem, the theorem is imported here and its axioms are
re-emitted on every build (`lake build RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3
"depends on axioms"`), so the audit cannot drift from the theorems. Expected: the three
standard axioms, plus `z3_unsat_sound` where a verdict pack enters.

* Data, kernel-checked for all 45: the IR literals (`BenchIR/`, drift-checked against the
  files by `relcert-test` `[ir-drift-v2]`), the extended cut certificates
  (`Cuts/<b>.lean`, `evolStrengtheningWFX … = true` by `rfl`), the cover replays
  (`CoverReplay.lean`, `decideCovered` by `decide`).
* The 19 benchmarks copied unchanged from `suite_uniform`: the suite_v2 literal IS the
  legacy literal (`SameIR.lean`, `rfl`), so the legacy theorems below are theorems about
  the suite_v2 files; their packs are rows of the legacy runner table, re-run by
  `relcert --run-verdicts-v2` (phase "copied benchmarks").
* The new suite_v2 instances (`Modal/`): Theorem 3 at the declared invariant over the
  file's right automaton, the right mode's kept cut atoms as its region, pruned sinks
  excluded; packs are rows of `VerdictsV2.RunV2.packsV2`, pinned in `VerdictsV2/PinsV2`.
* Declared counts: `VerdictsV2/CoveragePinsV2` derives every declared phase count from
  the tables.
-/
import RelCertifier.InstancesV2.SameIR
import RelCertifier.InstancesV2.CoverReplay
import RelCertifier.VerdictsV2.PinsV2
import RelCertifier.VerdictsV2.CoveragePinsV2
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
-- the 19 copied benchmarks: legacy theorems (their literal is the suite_v2 literal)
import RelCertifier.Instances.MatchMultiRatePruned
import RelCertifier.Instances.RoverLadderRung1Modal
import RelCertifier.Instances.RoverLadderRung2Modal
import RelCertifier.Instances.RoverRung26dofModal
import RelCertifier.Instances.RoverRung2b6dofModal
import RelCertifier.Instances.RoverRung2cModal
import RelCertifier.Instances.RoverLadderRung3Modal
import RelCertifier.Instances.RoverLadderRung4Modal
import RelCertifier.Instances.Rover3tierRung12Handoff
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

/-! ## New suite_v2 instances -/

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

/-! ## Copied benchmarks (legacy theorems; `SameIR` ties the literals) -/

#print axioms MatchMultiRatePruned.match_multi_rate_pruned
#print axioms MatchMultiRatePruned.match_multi_rate_nonconn
#print axioms RoverLadderRung1Modal.rover_ladder_rung1_modal
#print axioms RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal
#print axioms RoverRung26dofModal.rung2_6dof_modal
#print axioms RoverRung2b6dofModal.rung2b_6dof_modal
#print axioms RoverRung2cModal.rover_rung2c_modal
#print axioms RoverLadderRung3Modal.rover_ladder_rung3_6to8_modal
#print axioms RoverLadderRung4Modal.rover_ladder_rung4_8to12_modal
#print axioms Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed
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

/-! ## The generic layer the new instances rest on -/

#print axioms couple_cutX
#print axioms modalVerdX_of_queries
#print axioms check_sound_multi_cutX
#print axioms evolStrengtheningWFX_entryL
#print axioms evolStrengtheningWFX_entryR

end RelCertifier
