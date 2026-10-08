/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The modal battery — every benchmark's Theorem 3, in one importable place

This module imports the modal (Theorem 3) instance of EVERY certified benchmark
and re-emits its axiom audit. It is the single door for the end-to-end check
described in `docs/CERTIFICATION-CHECK.md`:

* importing it forces the kernel to check all 47 modal theorems, across the 46
  instance files imported below (`lake build`);
* the `#print axioms` lines below re-emit on every build, so the audit cannot
  drift from the theorems;
* the benchmark ↔ theorem correspondence is the import list itself — each
  instance quotes its benchmark's emitted IR literal (`BenchIR/<name>.lean`),
  which `relcert-test` re-checks against `benchmarks/.../input.txt`.

Expected audit output: every theorem depends on `[propext, Classical.choice,
Quot.sound]`, plus `RelCertifier.z3_unsat_sound` exactly for those instances
whose flow certificates come from a Z3 verdict. Five benchmarks are entirely
Z3-free — the standard three alone, no verdict hypotheses at all: `rover3_M1`,
`rover_coupled`, `rover_position`, `refinement_ladder_rover_rung2_6dof`,
`refinement_ladder_rover_rung2b_6dof`. The per-benchmark inventory (theorem
name, hypotheses, verdict pack) is the table in `docs/CERTIFICATION-CHECK.md`.

No `sorry`, no `native_decide`, no benchmark-specific axiom.
-/
import RelCertifier.Instances.ArmChainRung1Modal
import RelCertifier.Instances.ArmChainRung2Modal
import RelCertifier.Instances.ArmChainRung3Modal
import RelCertifier.Instances.ArmFidelityHighModal
import RelCertifier.Instances.ArmFidelityLowModal
import RelCertifier.Instances.ArmFidelityMidModal
import RelCertifier.Instances.ArmRefinementModal
import RelCertifier.Instances.AttitudeRateModal
import RelCertifier.Instances.EnduranceGainM1Modal
import RelCertifier.Instances.EnduranceOrderlift1to2Modal
import RelCertifier.Instances.EnduranceOrderlift2to3Modal
import RelCertifier.Instances.MatchMultiEpsModal
import RelCertifier.Instances.MatchMultiRateModal
import RelCertifier.Instances.PlantFanHighModal
import RelCertifier.Instances.PlantFanLowModal
import RelCertifier.Instances.PlantFanMidModal
import RelCertifier.Instances.RobotBrakingModal
import RelCertifier.Instances.Rover3M1Modal
import RelCertifier.Instances.Rover3tierM1Modal
import RelCertifier.Instances.Rover3tierRung12Modal
import RelCertifier.Instances.Rover4dBoxModal
import RelCertifier.Instances.RoverAttitudeConeModal
import RelCertifier.Instances.RoverCoupledModal
import RelCertifier.Instances.RoverDofTerrainRung1Modal
import RelCertifier.Instances.RoverDofTerrainRung2Modal
import RelCertifier.Instances.RoverDofTerrainRung38dModal
import RelCertifier.Instances.RoverDofTerrainRung3Modal
import RelCertifier.Instances.RoverDragModal
import RelCertifier.Instances.RoverLadderRung1Modal
import RelCertifier.Instances.RoverLadderRung2Modal
import RelCertifier.Instances.RoverLadderRung3Modal
import RelCertifier.Instances.RoverLadderRung4Modal
import RelCertifier.Instances.RoverPositionModal
import RelCertifier.Instances.RoverRung26dofModal
import RelCertifier.Instances.RoverRung2b6dofModal
import RelCertifier.Instances.RoverRung2cModal
import RelCertifier.Instances.RoverTerrainM1Modal
import RelCertifier.Instances.RoverTierR1Modal
import RelCertifier.Instances.Story1AttdistRungAModal
import RelCertifier.Instances.Story1AttdistRungBModal
import RelCertifier.Instances.Story2LateralAModal
import RelCertifier.Instances.Story2LateralBModal
import RelCertifier.Instances.Story3RolloverBaseModal
import RelCertifier.Instances.Story3RolloverRungAModal
import RelCertifier.Instances.Story3RolloverRungBModal
import RelCertifier.Instances.WatertankViability
import RelCertifier.Instances.Rover3M1Handoff
import RelCertifier.Instances.RoverCoupledHandoff
import RelCertifier.Instances.RoverPositionHandoff
import RelCertifier.Instances.Story1AttdistRungAHandoff
import RelCertifier.Instances.Story1AttdistRungBHandoff
import RelCertifier.Instances.Story3RolloverRungBHandoff
import RelCertifier.Instances.Rover3tierRung12Handoff

namespace RelCertifier

-- arm_chain_rung1
#print axioms ArmChainRung1Modal.arm_chain_rung1_modal
-- arm_chain_rung2
#print axioms ArmChainRung2Modal.arm_chain_rung2_modal
-- arm_chain_rung3
#print axioms ArmChainRung3Modal.arm_chain_rung3_modal
-- arm_fidelity_high
#print axioms ArmFidelityHighModal.arm_fidelity_high_modal
-- arm_fidelity_low
#print axioms ArmFidelityLowModal.arm_fidelity_low_modal
-- arm_fidelity_mid
#print axioms ArmFidelityMidModal.arm_fidelity_mid_modal
-- arm_refinement
#print axioms ArmRefinementModal.arm_refinement_modal
-- attitude_rate
#print axioms AttitudeRateModal.attitude_rate_modal
-- endurance_gain_M1
#print axioms EnduranceGainM1Modal.endurance_gain_M1_modal
-- endurance_orderlift_1to2
#print axioms EnduranceOrderlift1to2Modal.endurance_orderlift_1to2_modal
-- endurance_orderlift_2to3
#print axioms EnduranceOrderlift2to3Modal.endurance_orderlift_2to3_modal
-- match_multi_eps
#print axioms MatchMultiEpsModal.match_multi_eps_modal
-- match_multi_rate
#print axioms MatchMultiRateModal.match_multi_rate_modal
-- plant_fan_high
#print axioms PlantFanHighModal.plant_fan_high_modal
-- plant_fan_low
#print axioms PlantFanLowModal.plant_fan_low_modal
-- plant_fan_mid
#print axioms PlantFanMidModal.plant_fan_mid_modal
-- refinement_ladder_rover_rung1_2to3
#print axioms RoverLadderRung1Modal.rover_ladder_rung1_modal
-- refinement_ladder_rover_rung2_3to6
#print axioms RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal
-- refinement_ladder_rover_rung2_6dof
#print axioms RoverRung26dofModal.rung2_6dof_modal
-- refinement_ladder_rover_rung2b_6dof
#print axioms RoverRung2b6dofModal.rung2b_6dof_modal
-- refinement_ladder_rover_rung2c_6dof
#print axioms RoverRung2cModal.rover_rung2c_modal
-- refinement_ladder_rover_rung3_6to8
#print axioms RoverLadderRung3Modal.rover_ladder_rung3_6to8_modal
-- refinement_ladder_rover_rung4_8to12
#print axioms RoverLadderRung4Modal.rover_ladder_rung4_8to12_modal
-- robot_braking
#print axioms RobotBrakingModal.robot_braking_modal
-- rover3_M1
#print axioms Rover3M1Modal.rover3_M1_modal
-- rover3tier_M1
#print axioms Rover3tierM1Modal.rover3tier_M1_modal
-- rover3tier_rung12
#print axioms Rover3tierRung12Modal.rover3tier_rung12_modal_ACCEL
#print axioms Rover3tierRung12Modal.rover3tier_rung12_modal_COAST
-- rover_4d_box
#print axioms Rover4dBoxModal.rover_4d_box_modal
-- rover_attitude_cone_12dof
#print axioms RoverAttitudeConeModal.rover_attitude_cone_modal
-- rover_coupled
#print axioms RoverCoupledModal.rover_coupled_modal
-- rover_dof_terrain_rung1
#print axioms RoverDofTerrainRung1Modal.rover_dof_terrain_rung1_modal
-- rover_dof_terrain_rung2
#print axioms RoverDofTerrainRung2Modal.rover_dof_terrain_rung2_modal
-- rover_dof_terrain_rung3
#print axioms RoverDofTerrainRung3Modal.rover_dof_terrain_rung3_modal
-- rover_dof_terrain_rung3_8d
#print axioms RoverDofTerrainRung38dModal.rover_dof_terrain_rung3_8d_modal
-- rover_drag
#print axioms RoverDragModal.rover_drag_modal
-- rover_position
#print axioms RoverPositionModal.rover_position_modal
-- rover_terrain_M1
#print axioms RoverTerrainM1Modal.rover_terrain_M1_modal
-- rover_tier_r1
#print axioms RoverTierR1Modal.rover_tier_r1_modal
-- story1_attdist_rung_a_6to8
#print axioms Story1AttdistRungAModal.story1_attdist_rung_a_modal
-- story1_attdist_rung_b_12dof
#print axioms Story1AttdistRungBModal.story1_attdist_rung_b_modal
-- story2_lateral_rung_a_8dof
#print axioms Story2LateralAModal.story2_lateral_rung_a_modal
-- story2_lateral_rung_b_12dof
#print axioms Story2LateralBModal.story2_lateral_rung_b_modal
-- story3_rollover_base_12dof
#print axioms Story3RolloverBaseModal.story3_rollover_base_modal
-- story3_rollover_ladder_rung_a
#print axioms Story3RolloverRungAModal.story3_rollover_rung_a_modal
-- story3_rollover_ladder_rung_b
#print axioms Story3RolloverRungBModal.story3_rollover_rung_b_modal
-- watertank
#print axioms WatertankModal.watertank_modal_certified

/-! ### The mode-keyed theorems — the DECLARED per-left-mode invariants, composed across
left switches (`Proofs/Encoding/ModeHandoff.lean`; `docs/HANDOFF.md`). All seven
mode-dependent benchmarks; `rover3tier_rung12`'s ACCEL row was re-stated (rows only) so
that its handoffs hold, and it keeps its two per-left-mode theorems above as well. -/
-- rover3_M1 (padded to n = 3 for the left mode variable)
#print axioms Rover3M1Handoff.rover3_M1_modeKeyed
-- rover_coupled
#print axioms RoverCoupledHandoff.rover_coupled_modeKeyed
-- rover_position
#print axioms RoverPositionHandoff.rover_position_modeKeyed
-- story1_attdist_rung_a_6to8
#print axioms Story1AttdistRungAHandoff.story1_attdist_rung_a_modeKeyed
-- story1_attdist_rung_b_12dof
#print axioms Story1AttdistRungBHandoff.story1_attdist_rung_b_modeKeyed
-- story3_rollover_ladder_rung_b
#print axioms Story3RolloverRungBHandoff.story3_rollover_rung_b_modeKeyed
-- rover3tier_rung12 (repaired rows)
#print axioms Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed

end RelCertifier
