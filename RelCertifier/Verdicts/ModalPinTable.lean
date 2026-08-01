/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The pin table — every instance's hypothesis, tied to the runner's query

`Verdicts/RunModal.lean` rebuilds each instance's verdict queries from a hand-written
`RunInfo` (dimension, invariant row, λ, component order, region/ceiling heads). Nothing
in that table was checked by the kernel: a wrong field simply made the runner test a
*different* query and report it green. Three such fields were found during development
— a wrong λ, a wrong `invRow`, and `rover_rung2c`'s mode pairing — and the first two
were caught only because the wrong query happened to come back `sat`. One that happens
to be `unsat` passes silently, which is exactly the vacuous-hypothesis failure the
2026-07-31 audit (`docs/VERDICT-EVIDENCE-AUDIT.md`) was about.

This file removes that gap. For each of the 42 verdict packs it states, and proves by
`rfl`, that the instance's own `Verd` **is** `modalVerd`/`modalVerd1` at the arguments
the runner uses. A wrong field no longer type-checks.

Composed with the two links either side, the chain is closed end to end:

* `ModalSpecs.modal_from_spec` — the argument set ties to the theorem;
* **this file** — the theorem's hypothesis is the runner's host-level query;
* `ModalPins` — the runner's IR rebuild denotes that host-level query.

## Reading an entry

`modalVerd p n invRow order pre post lam l m` is the ∀-over-components form; `pre`
prepends a component ahead of the invariant's own (ceiling head, or the repaired
`Hold` region) and `post` appends one behind them. `modalVerd1 p n invRow lam l m` is
the bare three-route disjunction over the whole invariant row, which eleven instances
use; for those a companion `comps_*` pin states as a plain `List` equality that the
runner's component list really is that single row, so the two shapes agree on what
gets sent to Z3.
-/
import RelCertifier.Verdicts.ModalVerd
import RelCertifier.Instances.ModalSpecs

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse DL

set_option autoImplicit false

/-! ## One-component instances

Their `Verd` is a bare disjunction over the whole invariant row. The `comps_*` pin
beside each one states that the runner's rebuilt component list is exactly that row,
so its single loop iteration issues these same three queries. -/

open RelCertifier.ArmChainRung1Modal in
theorem pin_ArmChainRung1 (l : ℕ) :
    VerdC l = modalVerd1 arm_chain_rung1_IR 2 0 (lamC l : ℝ) l 0 := pin1_of rfl

theorem comps_ArmChainRung1 :
    modalComps arm_chain_rung1_IR 0 2 [0] none none
      = [modalRowG arm_chain_rung1_IR 0 2] := by rfl

open RelCertifier.ArmChainRung2Modal in
theorem pin_ArmChainRung2 (l : ℕ) :
    VerdD l = modalVerd1 arm_chain_rung2_IR 2 0 (lamD l : ℝ) l 1 := pin1_of rfl

theorem comps_ArmChainRung2 :
    modalComps arm_chain_rung2_IR 0 2 [0] none none
      = [modalRowG arm_chain_rung2_IR 0 2] := by rfl

open RelCertifier.ArmFidelityLowModal in
theorem pin_ArmFidelityLow (l : ℕ) :
    VerdF l = modalVerd1 arm_fidelity_low_IR 2 0 (5 : ℝ) l 0 := pin1_of rfl

theorem comps_ArmFidelityLow :
    modalComps arm_fidelity_low_IR 0 2 [0] none none
      = [modalRowG arm_fidelity_low_IR 0 2] := by rfl

open RelCertifier.ArmRefinementModal in
theorem pin_ArmRefinement (l : ℕ) :
    VerdF l = modalVerd1 arm_refinement_IR 2 0 (5 : ℝ) l 0 := pin1_of rfl

theorem comps_ArmRefinement :
    modalComps arm_refinement_IR 0 2 [0] none none
      = [modalRowG arm_refinement_IR 0 2] := by rfl

open RelCertifier.MatchMultiEpsModal in
theorem pin_MatchMultiEps (l : ℕ) :
    Verd3 l = modalVerd1 match_multi_eps_IR 2 0 (1 : ℝ) l 0 := pin1_of rfl

theorem comps_MatchMultiEps :
    modalComps match_multi_eps_IR 0 2 [0] none none
      = [modalRowG match_multi_eps_IR 0 2] := by rfl

open RelCertifier.PlantFanLowModal in
theorem pin_PlantFanLow (l : ℕ) :
    VerdF l = modalVerd1 plant_fan_low_IR 2 0 (5 : ℝ) l 0 := pin1_of rfl

theorem comps_PlantFanLow :
    modalComps plant_fan_low_IR 0 2 [0] none none
      = [modalRowG plant_fan_low_IR 0 2] := by rfl

open RelCertifier.RobotBrakingModal in
theorem pin_RobotBraking (l : ℕ) :
    Verd3 l = modalVerd1 robot_braking_IR 2 0 (1 : ℝ) l 2 := pin1_of rfl

theorem comps_RobotBraking :
    modalComps robot_braking_IR 0 2 [0] none none
      = [modalRowG robot_braking_IR 0 2] := by rfl

open RelCertifier.Rover3tierM1Modal in
theorem pin_Rover3tierM1 (l : ℕ) :
    Verd3 l = modalVerd1 rover3tier_M1_IR 2 0 (1 : ℝ) l 0 := pin1_of rfl

theorem comps_Rover3tierM1 :
    modalComps rover3tier_M1_IR 0 2 [0] none none
      = [modalRowG rover3tier_M1_IR 0 2] := by rfl

open RelCertifier.Rover4dBoxModal in
theorem pin_Rover4dBox (l : ℕ) :
    Verd3 l = modalVerd1 rover_4d_box_IR 4 0 (1 : ℝ) l 1 := pin1_of rfl

theorem comps_Rover4dBox :
    modalComps rover_4d_box_IR 0 4 [0] none none
      = [modalRowG rover_4d_box_IR 0 4] := by rfl

open RelCertifier.RoverDragModal in
theorem pin_RoverDrag :
    VerdRD = modalVerd1 rover_drag_IR 2 0 (1 : ℝ) 0 0 := pin1_of rfl

theorem comps_RoverDrag :
    modalComps rover_drag_IR 0 2 [0] none none
      = [modalRowG rover_drag_IR 0 2] := by rfl

open RelCertifier.WatertankModal in
theorem pin_Watertank (l m : ℕ) :
    VerdW l m = modalVerd1 watertank_IR 2 0 (1 : ℝ) l m := pin1_of rfl

theorem comps_Watertank :
    modalComps watertank_IR 0 2 [0] none none
      = [modalRowG watertank_IR 0 2] := by rfl

/-! ## Multi-component instances, no extra head -/

open RelCertifier.AttitudeRateModal in
theorem pin_AttitudeRate (m : ℕ) :
    VerdW m = modalVerd attitude_rate_IR 6 0 [0] none none (2 : ℝ) 0 m := pin_of rfl

open RelCertifier.EnduranceGainM1Modal in
theorem pin_EnduranceGainM1 (l m : ℕ) :
    VerdG l m = modalVerd endurance_gain_M1_IR 2 0 [0] none none (1 : ℝ) l m := pin_of rfl

open RelCertifier.EnduranceOrderlift1to2Modal in
theorem pin_EnduranceOrderlift1to2 (l m : ℕ) :
    VerdO l m = modalVerd endurance_orderlift_1to2_IR 3 0 [0] none none (2 : ℝ) l m :=
  pin_of rfl

open RelCertifier.EnduranceOrderlift2to3Modal in
theorem pin_EnduranceOrderlift2to3 (l m : ℕ) :
    VerdJ l m = modalVerd endurance_orderlift_2to3_IR 4 0 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.MatchMultiRateModal in
theorem pin_MatchMultiRate (l : ℕ) :
    VerdM l = modalVerd match_multi_rate_IR 2 0 [0] none none (lamM l : ℝ) l 0 :=
  pin_of rfl

open RelCertifier.Rover3tierRung12Modal in
theorem pin_Rover3tierRung12Accel (m : ℕ) :
    VerdQA m = modalVerd rover3tier_rung12_IR 3 0 [0, 1] none none (2 : ℝ) 0 m :=
  pin_of rfl

open RelCertifier.Rover3tierRung12Modal in
theorem pin_Rover3tierRung12Coast (m : ℕ) :
    VerdQC m = modalVerd rover3tier_rung12_IR 3 1 [0] none none (1 : ℝ) 1 m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung1Modal in
theorem pin_RoverDofTerrainRung1 (l m : ℕ) :
    VerdE l m = modalVerd rover_dof_terrain_rung1_IR 3 0 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung2Modal in
theorem pin_RoverDofTerrainRung2 (l m : ℕ) :
    VerdT l m = modalVerd rover_dof_terrain_rung2_IR 6 0 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung38dModal in
theorem pin_RoverDofTerrainRung38d (l m : ℕ) :
    VerdU l m =
      modalVerd rover_dof_terrain_rung3_8d_IR 8 0 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung3Modal in
theorem pin_RoverDofTerrainRung3 (l m : ℕ) :
    VerdW l m = modalVerd rover_dof_terrain_rung3_IR 12 0 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung1Modal in
theorem pin_RoverLadderRung1 (l m : ℕ) :
    VerdE l m =
      modalVerd refinement_ladder_rover_rung1_2to3_IR 3 0 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung2Modal in
theorem pin_RoverLadderRung2 (l m : ℕ) :
    Verd36 l m =
      modalVerd refinement_ladder_rover_rung2_3to6_IR 6 0 [0, 2, 3, 1] none none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverTerrainM1Modal in
theorem pin_RoverTerrainM1 (l m : ℕ) :
    VerdT l m = modalVerd rover_terrain_M1_IR 2 0 [0] none none (1 : ℝ) l m := pin_of rfl

open RelCertifier.Story1AttdistRungAModal in
theorem pin_Story1AttdistRungA (l m : ℕ) :
    VerdD l m =
      modalVerd story1_attdist_rung_a_6to8_IR 8 1 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story2LateralAModal in
theorem pin_Story2LateralA (l m : ℕ) :
    VerdY l m =
      modalVerd story2_lateral_rung_a_8dof_IR 8 0 [0, 1, 3, 4, 5, 6, 2] none none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story2LateralBModal in
theorem pin_Story2LateralB (l m : ℕ) :
    VerdZ l m =
      modalVerd story2_lateral_rung_b_12dof_IR 12 0 [0, 1, 2, 4, 5, 6, 7, 3] none none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story3RolloverRungBModal in
theorem pin_Story3RolloverRungB (l m : ℕ) :
    VerdV l m =
      modalVerd story3_rollover_ladder_rung_b_IR 12 1 [0, 1] none none (1 : ℝ) l m :=
  pin_of rfl

/-! ## Ceiling-head instances

The head `R_c − k_m` is per right mode, so it is a function of the pin's own `m`
rather than a constant. -/

open RelCertifier.RoverAttitudeConeModal in
theorem pin_RoverAttitudeCone (l m : ℕ) :
    VerdC l m =
      modalVerd rover_attitude_cone_12dof_IR 12 0 [0, 1, 2, 3] (some (ceilC m)) none
        ((17 : ℝ) / 10) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung3Modal in
theorem pin_RoverLadderRung3 (l m : ℕ) :
    VerdR l m =
      modalVerd refinement_ladder_rover_rung3_6to8_IR 8 0 [0, 1, 2, 3] (some (ceilR m))
        none ((9 : ℝ) / 4) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung4Modal in
theorem pin_RoverLadderRung4 (l m : ℕ) :
    VerdF l m =
      modalVerd refinement_ladder_rover_rung4_8to12_IR 12 0 [0, 1] (some (ceilF m)) none
        ((17 : ℝ) / 10) l m :=
  pin_of rfl

open RelCertifier.RoverTierR1Modal in
theorem pin_RoverTierR1 (l m : ℕ) :
    VerdX l m =
      modalVerd rover_tier_r1_IR 3 0 [0] (some (ceilX m)) none ((19 : ℝ) / 4) l m :=
  pin_of rfl

open RelCertifier.Story1AttdistRungBModal in
theorem pin_Story1AttdistRungB (l m : ℕ) :
    VerdF l m =
      modalVerd story1_attdist_rung_b_12dof_IR 12 0 [0, 1] (some (ceilF m)) none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story3RolloverBaseModal in
theorem pin_Story3RolloverBase (l m : ℕ) :
    VerdB l m =
      modalVerd story3_rollover_base_12dof_IR 12 0 [0, 1, 2, 3, 4] (some (ceilB m)) none
        ((5 : ℝ) / 4) l m :=
  pin_of rfl

open RelCertifier.Story3RolloverRungAModal in
theorem pin_Story3RolloverRungA (l m : ℕ) :
    VerdA l m =
      modalVerd story3_rollover_ladder_rung_a_IR 12 0 [0, 1, 2] (some (ceilA m)) none
        ((27 : ℝ) / 20) l m :=
  pin_of rfl

/-! ## Region-head instances

The five whose `Hold` case the audit found vacuous. The repair added the landing
region `3/5 − θ_R` as component 0, so the invariant's own component is narrowed by it
— which is what makes the `Hold` query discharge. -/

open RelCertifier.ArmChainRung3Modal in
theorem pin_ArmChainRung3 (l : ℕ) :
    Verd3 l = modalVerd arm_chain_rung3_IR 2 0 [0] (some regA) none (1 : ℝ) l 3 :=
  pin_of rfl

open RelCertifier.ArmFidelityHighModal in
theorem pin_ArmFidelityHigh (l : ℕ) :
    Verd3 l = modalVerd arm_fidelity_high_IR 2 0 [0] (some regA) none (1 : ℝ) l 3 :=
  pin_of rfl

open RelCertifier.ArmFidelityMidModal in
theorem pin_ArmFidelityMid (l : ℕ) :
    Verd3 l = modalVerd arm_fidelity_mid_IR 2 0 [0] (some regA) none (1 : ℝ) l 2 :=
  pin_of rfl

open RelCertifier.PlantFanHighModal in
theorem pin_PlantFanHigh (l : ℕ) :
    Verd3 l = modalVerd plant_fan_high_IR 2 0 [0] (some regA) none (1 : ℝ) l 3 :=
  pin_of rfl

open RelCertifier.PlantFanMidModal in
theorem pin_PlantFanMid (l : ℕ) :
    Verd3 l = modalVerd plant_fan_mid_IR 2 0 [0] (some regA) none (1 : ℝ) l 2 :=
  pin_of rfl

/-! ## Tail-face instance

`rover_rung2c` carries its mode region as the *last* component rather than the first,
and runs left mode `l` against right mode `l`. -/

open RelCertifier.RoverRung2cModal in
theorem pin_RoverRung2c (l : ℕ) :
    VerdR6 l =
      modalVerd refinement_ladder_rover_rung2c_6dof_IR 6 0 [0, 1, 4, 5, 6, 7, 2, 3]
        none (some (lowFace (b6 l) (Rv 1))) (1 : ℝ) l l :=
  pin_of rfl

end RelCertifier.Verdicts
