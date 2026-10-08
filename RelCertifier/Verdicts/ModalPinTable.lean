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

This file removes that gap. For each of the 36 base verdict packs (and the 5 packs of the mode-keyed instances) it states, and proves by
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
the bare three-route disjunction over the whole invariant row, which eight instances
use; for those a companion `comps_*` pin states as a plain `List` equality that the
runner's component list really is that single row, so the two shapes agree on what
gets sent to Z3.
-/
import RelCertifier.Verdicts.ModalVerd
import RelCertifier.Instances.ModalSpecs
import RelCertifier.Verdicts.RunModal

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse DL

set_option autoImplicit false

/-- The runner's own table row. Quoting `dim`, `invRow` and `order` from here rather
than restating them means those three fields exist in exactly one place: change the
table and the pin stops compiling. λ and the region/ceiling heads cannot be quoted
this way — see `docs/VERDICT-EVIDENCE-AUDIT.md` — so they stay written out, with
`ModalTablePins` tying the rest of the row. -/
noncomputable def row (i : ℕ) : ModalSpecs.VerdSpec × RunInfo × List ℕ :=
  modalTable.getD i (ModalSpecs.Watertank.spec, { dim := 0 }, [])

/-! ## One-component instances

Their `Verd` is a bare disjunction over the whole invariant row. The `comps_*` pin
beside each one states that the runner's rebuilt component list is exactly that row,
so its single loop iteration issues these same three queries. -/

open RelCertifier.ArmChainRung1Modal in
theorem pin_ArmChainRung1 (l : ℕ) :
    VerdC l = modalVerd1 arm_chain_rung1_IR (row 0).2.1.dim (row 0).2.1.invRow (lamC l : ℝ) l 0 := pin1_of rfl

theorem comps_ArmChainRung1 :
    modalComps arm_chain_rung1_IR (row 0).2.1.invRow (row 0).2.1.dim (row 0).2.2 none none
      = [modalRowG arm_chain_rung1_IR (row 0).2.1.invRow (row 0).2.1.dim] := by rfl

open RelCertifier.ArmChainRung2Modal in
theorem pin_ArmChainRung2 (l : ℕ) :
    VerdD l = modalVerd1 arm_chain_rung2_IR (row 1).2.1.dim (row 1).2.1.invRow (lamD l : ℝ) l 1 := pin1_of rfl

theorem comps_ArmChainRung2 :
    modalComps arm_chain_rung2_IR (row 1).2.1.invRow (row 1).2.1.dim (row 1).2.2 none none
      = [modalRowG arm_chain_rung2_IR (row 1).2.1.invRow (row 1).2.1.dim] := by rfl

open RelCertifier.ArmFidelityLowModal in
theorem pin_ArmFidelityLow (l : ℕ) :
    VerdF l = modalVerd1 arm_fidelity_low_IR (row 3).2.1.dim (row 3).2.1.invRow (5 : ℝ) l 0 := pin1_of rfl

theorem comps_ArmFidelityLow :
    modalComps arm_fidelity_low_IR (row 3).2.1.invRow (row 3).2.1.dim (row 3).2.2 none none
      = [modalRowG arm_fidelity_low_IR (row 3).2.1.invRow (row 3).2.1.dim] := by rfl

open RelCertifier.RobotBrakingModal in
theorem pin_RobotBraking (l : ℕ) :
    Verd3 l = modalVerd1 robot_braking_IR (row 10).2.1.dim (row 10).2.1.invRow (1 : ℝ) l 2 := pin1_of rfl

theorem comps_RobotBraking :
    modalComps robot_braking_IR (row 10).2.1.invRow (row 10).2.1.dim (row 10).2.2 none none
      = [modalRowG robot_braking_IR (row 10).2.1.invRow (row 10).2.1.dim] := by rfl

open RelCertifier.Rover3tierM1Modal in
theorem pin_Rover3tierM1 (l : ℕ) :
    Verd3 l = modalVerd1 rover3tier_M1_IR (row 11).2.1.dim (row 11).2.1.invRow (1 : ℝ) l 0 := pin1_of rfl

theorem comps_Rover3tierM1 :
    modalComps rover3tier_M1_IR (row 11).2.1.invRow (row 11).2.1.dim (row 11).2.2 none none
      = [modalRowG rover3tier_M1_IR (row 11).2.1.invRow (row 11).2.1.dim] := by rfl

open RelCertifier.Rover4dBoxModal in
theorem pin_Rover4dBox (l : ℕ) :
    Verd3 l = modalVerd1 rover_4d_box_IR (row 14).2.1.dim (row 14).2.1.invRow (1 : ℝ) l 1 := pin1_of rfl

theorem comps_Rover4dBox :
    modalComps rover_4d_box_IR (row 14).2.1.invRow (row 14).2.1.dim (row 14).2.2 none none
      = [modalRowG rover_4d_box_IR (row 14).2.1.invRow (row 14).2.1.dim] := by rfl

open RelCertifier.RoverDragModal in
theorem pin_RoverDrag :
    VerdRD = modalVerd1 rover_drag_IR (row 20).2.1.dim (row 20).2.1.invRow (1 : ℝ) 0 0 := pin1_of rfl

theorem comps_RoverDrag :
    modalComps rover_drag_IR (row 20).2.1.invRow (row 20).2.1.dim (row 20).2.2 none none
      = [modalRowG rover_drag_IR (row 20).2.1.invRow (row 20).2.1.dim] := by rfl

open RelCertifier.WatertankModal in
theorem pin_Watertank (l m : ℕ) :
    VerdW l m = modalVerd1 watertank_IR (row 35).2.1.dim (row 35).2.1.invRow (1 : ℝ) l m := pin1_of rfl

theorem comps_Watertank :
    modalComps watertank_IR (row 35).2.1.invRow (row 35).2.1.dim (row 35).2.2 none none
      = [modalRowG watertank_IR (row 35).2.1.invRow (row 35).2.1.dim] := by rfl

/-! ## Multi-component instances, no extra head -/

open RelCertifier.AttitudeRateModal in
theorem pin_AttitudeRate (m : ℕ) :
    VerdW m = modalVerd attitude_rate_IR
        (row 5).2.1.dim (row 5).2.1.invRow (row 5).2.2 none none (2 : ℝ) 0 m := pin_of rfl

open RelCertifier.EnduranceGainM1Modal in
theorem pin_EnduranceGainM1 (l m : ℕ) :
    VerdG l m = modalVerd endurance_gain_M1_IR
        (row 6).2.1.dim (row 6).2.1.invRow (row 6).2.2 none none (1 : ℝ) l m := pin_of rfl

open RelCertifier.EnduranceOrderlift1to2Modal in
theorem pin_EnduranceOrderlift1to2 (l m : ℕ) :
    VerdO l m = modalVerd endurance_orderlift_1to2_IR
        (row 7).2.1.dim (row 7).2.1.invRow (row 7).2.2 none none (2 : ℝ) l m :=
  pin_of rfl

open RelCertifier.EnduranceOrderlift2to3Modal in
theorem pin_EnduranceOrderlift2to3 (l m : ℕ) :
    VerdJ l m = modalVerd endurance_orderlift_2to3_IR
        (row 8).2.1.dim (row 8).2.1.invRow (row 8).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.MatchMultiRateModal in
theorem pin_MatchMultiRate (l : ℕ) :
    VerdM l = modalVerd match_multi_rate_IR
        (row 9).2.1.dim (row 9).2.1.invRow (row 9).2.2 none none (lamM l : ℝ) l 0 :=
  pin_of rfl

open RelCertifier.Rover3tierRung12Modal in
theorem pin_Rover3tierRung12Accel (m : ℕ) :
    VerdQA m = modalVerd rover3tier_rung12_IR
        (row 12).2.1.dim (row 12).2.1.invRow (row 12).2.2 none none (2 : ℝ) 0 m :=
  pin_of rfl

open RelCertifier.Rover3tierRung12Modal in
theorem pin_Rover3tierRung12Coast (m : ℕ) :
    VerdQC m = modalVerd rover3tier_rung12_IR
        (row 13).2.1.dim (row 13).2.1.invRow (row 13).2.2 none none (1 : ℝ) 1 m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung1Modal in
theorem pin_RoverDofTerrainRung1 (l m : ℕ) :
    VerdE l m = modalVerd rover_dof_terrain_rung1_IR
        (row 16).2.1.dim (row 16).2.1.invRow (row 16).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung2Modal in
theorem pin_RoverDofTerrainRung2 (l m : ℕ) :
    VerdT l m = modalVerd rover_dof_terrain_rung2_IR
        (row 17).2.1.dim (row 17).2.1.invRow (row 17).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung38dModal in
theorem pin_RoverDofTerrainRung38d (l m : ℕ) :
    VerdU l m =
      modalVerd rover_dof_terrain_rung3_8d_IR
        (row 18).2.1.dim (row 18).2.1.invRow (row 18).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverDofTerrainRung3Modal in
theorem pin_RoverDofTerrainRung3 (l m : ℕ) :
    VerdW l m = modalVerd rover_dof_terrain_rung3_IR
        (row 19).2.1.dim (row 19).2.1.invRow (row 19).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung1Modal in
theorem pin_RoverLadderRung1 (l m : ℕ) :
    VerdE l m =
      modalVerd refinement_ladder_rover_rung1_2to3_IR
        (row 21).2.1.dim (row 21).2.1.invRow (row 21).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung2Modal in
theorem pin_RoverLadderRung2 (l m : ℕ) :
    Verd36 l m =
      modalVerd refinement_ladder_rover_rung2_3to6_IR
        (row 22).2.1.dim (row 22).2.1.invRow (row 22).2.2 none none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.RoverTerrainM1Modal in
theorem pin_RoverTerrainM1 (l m : ℕ) :
    VerdT l m = modalVerd rover_terrain_M1_IR
        (row 26).2.1.dim (row 26).2.1.invRow (row 26).2.2 none none (1 : ℝ) l m := pin_of rfl

open RelCertifier.Story1AttdistRungAModal in
theorem pin_Story1AttdistRungA (l m : ℕ) :
    VerdD l m =
      modalVerd story1_attdist_rung_a_6to8_IR
        (row 28).2.1.dim (row 28).2.1.invRow (row 28).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story2LateralAModal in
theorem pin_Story2LateralA (l m : ℕ) :
    VerdY l m =
      modalVerd story2_lateral_rung_a_8dof_IR
        (row 30).2.1.dim (row 30).2.1.invRow (row 30).2.2 none none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story2LateralBModal in
theorem pin_Story2LateralB (l m : ℕ) :
    VerdZ l m =
      modalVerd story2_lateral_rung_b_12dof_IR
        (row 31).2.1.dim (row 31).2.1.invRow (row 31).2.2 none none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story3RolloverRungBModal in
theorem pin_Story3RolloverRungB (l m : ℕ) :
    VerdV l m =
      modalVerd story3_rollover_ladder_rung_b_IR
        (row 34).2.1.dim (row 34).2.1.invRow (row 34).2.2 none none (1 : ℝ) l m :=
  pin_of rfl

/-! ## Ceiling-head instances

The head `R_c − k_m` is per right mode, so it is a function of the pin's own `m`
rather than a constant. -/

open RelCertifier.RoverAttitudeConeModal in
theorem pin_RoverAttitudeCone (l m : ℕ) :
    VerdC l m =
      modalVerd rover_attitude_cone_12dof_IR
        (row 15).2.1.dim (row 15).2.1.invRow (row 15).2.2 (some (ceilC m)) none
        ((17 : ℝ) / 10) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung3Modal in
theorem pin_RoverLadderRung3 (l m : ℕ) :
    VerdR l m =
      modalVerd refinement_ladder_rover_rung3_6to8_IR
        (row 23).2.1.dim (row 23).2.1.invRow (row 23).2.2 (some (ceilR m))
        none ((9 : ℝ) / 4) l m :=
  pin_of rfl

open RelCertifier.RoverLadderRung4Modal in
theorem pin_RoverLadderRung4 (l m : ℕ) :
    VerdF l m =
      modalVerd refinement_ladder_rover_rung4_8to12_IR
        (row 24).2.1.dim (row 24).2.1.invRow (row 24).2.2 (some (ceilF m)) none
        ((17 : ℝ) / 10) l m :=
  pin_of rfl

open RelCertifier.RoverTierR1Modal in
theorem pin_RoverTierR1 (l m : ℕ) :
    VerdX l m =
      modalVerd rover_tier_r1_IR
        (row 27).2.1.dim (row 27).2.1.invRow (row 27).2.2 (some (ceilX m)) none ((19 : ℝ) / 4) l m :=
  pin_of rfl

open RelCertifier.Story1AttdistRungBModal in
theorem pin_Story1AttdistRungB (l m : ℕ) :
    VerdF l m =
      modalVerd story1_attdist_rung_b_12dof_IR
        (row 29).2.1.dim (row 29).2.1.invRow (row 29).2.2 (some (ceilF m)) none
        (1 : ℝ) l m :=
  pin_of rfl

open RelCertifier.Story3RolloverBaseModal in
theorem pin_Story3RolloverBase (l m : ℕ) :
    VerdB l m =
      modalVerd story3_rollover_base_12dof_IR
        (row 32).2.1.dim (row 32).2.1.invRow (row 32).2.2 (some (ceilB m)) none
        ((5 : ℝ) / 4) l m :=
  pin_of rfl

open RelCertifier.Story3RolloverRungAModal in
theorem pin_Story3RolloverRungA (l m : ℕ) :
    VerdA l m =
      modalVerd story3_rollover_ladder_rung_a_IR
        (row 33).2.1.dim (row 33).2.1.invRow (row 33).2.2 (some (ceilA m)) none
        ((27 : ℝ) / 20) l m :=
  pin_of rfl

/-! ## Region-head instances

The five whose `Hold` case the audit found vacuous. The repair added the landing
region `3/5 − θ_R` as component 0, so the invariant's own component is narrowed by it
— which is what makes the `Hold` query discharge. -/

open RelCertifier.ArmChainRung3Modal in
theorem pin_ArmChainRung3 (l : ℕ) :
    Verd3 l = modalVerd arm_chain_rung3_IR
        (row 2).2.1.dim (row 2).2.1.invRow (row 2).2.2 (some regA) none (1 : ℝ) l 3 :=
  pin_of rfl

open RelCertifier.ArmFidelityMidModal in
theorem pin_ArmFidelityMid (l : ℕ) :
    Verd3 l = modalVerd arm_fidelity_mid_IR
        (row 4).2.1.dim (row 4).2.1.invRow (row 4).2.2 (some regA) none (1 : ℝ) l 2 :=
  pin_of rfl

/-! ## Tail-face instance

`rover_rung2c` carries its mode region as the *last* component rather than the first,
and runs left mode `l` against right mode `l`. -/

open RelCertifier.RoverRung2cModal in
theorem pin_RoverRung2c (l : ℕ) :
    VerdR6 l =
      modalVerd refinement_ladder_rover_rung2c_6dof_IR
        (row 25).2.1.dim (row 25).2.1.invRow (row 25).2.2
        none (some (lowFace (b6 l) (Rv (1 : Fin 6)))) (1 : ℝ) l l :=
  pin_of rfl

/-! ## The mode-keyed instances' packs (`Instances/*Handoff.lean`)

The STEEP window at its full declared row (three components, the `v` conjunct first),
and `story1_attdist_rung_b`'s three rows, each with the right mode's ceiling head. -/

open RelCertifier.Story1AttdistRungAHandoff in
theorem pin_Story1AttdistRungASteep (m : ℕ) :
    VerdS m = modalVerd story1_attdist_rung_a_6to8_IR
        (row 36).2.1.dim (row 36).2.1.invRow (row 36).2.2 none none (1 : ℝ) 0 m :=
  pin_of rfl

open RelCertifier.Story3RolloverRungBHandoff in
theorem pin_Story3RolloverRungBSteep (m : ℕ) :
    VerdS m = modalVerd story3_rollover_ladder_rung_b_IR
        (row 37).2.1.dim (row 37).2.1.invRow (row 37).2.2 none none (1 : ℝ) 0 m :=
  pin_of rfl

open RelCertifier.Story1AttdistRungBHandoff RelCertifier.Story1AttdistRungBModal in
theorem pin_Story1AttdistRungBRow0 (m : ℕ) :
    VerdR 0 m = modalVerd story1_attdist_rung_b_12dof_IR
        (row 38).2.1.dim (row 38).2.1.invRow (row 38).2.2 (some (ceilF m)) none (1 : ℝ) 0 m :=
  pin_of rfl

open RelCertifier.Story1AttdistRungBHandoff RelCertifier.Story1AttdistRungBModal in
theorem pin_Story1AttdistRungBRow1 (m : ℕ) :
    VerdR 1 m = modalVerd story1_attdist_rung_b_12dof_IR
        (row 39).2.1.dim (row 39).2.1.invRow (row 39).2.2 (some (ceilF m)) none (1 : ℝ) 1 m :=
  pin_of rfl

open RelCertifier.Story1AttdistRungBHandoff RelCertifier.Story1AttdistRungBModal in
theorem pin_Story1AttdistRungBRow2 (m : ℕ) :
    VerdR 2 m = modalVerd story1_attdist_rung_b_12dof_IR
        (row 40).2.1.dim (row 40).2.1.invRow (row 40).2.2 (some (ceilF m)) none (1 : ℝ) 2 m :=
  pin_of rfl

end RelCertifier.Verdicts
