/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Tying the rest of the runner's table row

`ModalPinTable` quotes `dim`, `invRow` and `order` straight out of `modalTable`, so
those three fields live in one place. The remaining `RunInfo` fields cannot be quoted
into a pin: λ and the region/ceiling heads have to cross into `ℝ` and `Term`, and
`List.getD` is stuck at a symbolic mode index (see `docs/VERDICT-EVIDENCE-AUDIT.md`).

This file pins them as data instead. For each row it states, by `rfl`:

* `(row i).1.bench` — so a wrong row *index* in `ModalPinTable` fails to compile
  rather than silently pinning a different benchmark;
* `modalPairs (row i).1 (row i).2.1` — the `(left, right)` pairs the runner actually
  visits. This is `RunModal`'s own function, not a copy of it, so the theorem
  constrains the runner. Two of the three defects found on 2026-07-31 were here:
  `rover_rung2c` was visiting `(0, l)` instead of `(l, l)`, and `rover_drag`'s list
  came out empty so it was checked at nothing;
* the λ and head fields, as a change-detector: they still have to agree with the
  literals `ModalPinTable` writes out, and that agreement is by inspection, but a
  table edit that forgets the pin now breaks the build here.
-/
import RelCertifier.Verdicts.ModalPinTable

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.ModalSpecs

set_option autoImplicit false

theorem ties_ArmChainRung3 :
    ((row 0).1.bench, modalPairs (row 0).1 (row 0).2.1,
     (row 0).2.1.lamN, (row 0).2.1.lamD, (row 0).2.1.lamPerL,
     (row 0).2.1.region, (row 0).2.1.ceilCo, (row 0).2.1.ceilFlip,
     (row 0).2.1.ceilKs, (row 0).2.1.tailCo, (row 0).2.1.tailFlip,
     (row 0).2.1.tailKs)
    = ("arm_chain_rung3", [(0, 3), (1, 3)],
       1, 1, [],
       some (3/5), none, false,
       [], none, false,
       []) := by rfl

theorem ties_ArmFidelityMid :
    ((row 1).1.bench, modalPairs (row 1).1 (row 1).2.1,
     (row 1).2.1.lamN, (row 1).2.1.lamD, (row 1).2.1.lamPerL,
     (row 1).2.1.region, (row 1).2.1.ceilCo, (row 1).2.1.ceilFlip,
     (row 1).2.1.ceilKs, (row 1).2.1.tailCo, (row 1).2.1.tailFlip,
     (row 1).2.1.tailKs)
    = ("arm_fidelity_mid", [(0, 2), (1, 2)],
       1, 1, [],
       some (3/5), none, false,
       [], none, false,
       []) := by rfl

theorem ties_AttitudeRate :
    ((row 2).1.bench, modalPairs (row 2).1 (row 2).2.1,
     (row 2).2.1.lamN, (row 2).2.1.lamD, (row 2).2.1.lamPerL,
     (row 2).2.1.region, (row 2).2.1.ceilCo, (row 2).2.1.ceilFlip,
     (row 2).2.1.ceilKs, (row 2).2.1.tailCo, (row 2).2.1.tailFlip,
     (row 2).2.1.tailKs)
    = ("attitude_rate", [(0, 0), (0, 1)],
       2, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_EnduranceGainM1 :
    ((row 3).1.bench, modalPairs (row 3).1 (row 3).2.1,
     (row 3).2.1.lamN, (row 3).2.1.lamD, (row 3).2.1.lamPerL,
     (row 3).2.1.region, (row 3).2.1.ceilCo, (row 3).2.1.ceilFlip,
     (row 3).2.1.ceilKs, (row 3).2.1.tailCo, (row 3).2.1.tailFlip,
     (row 3).2.1.tailKs)
    = ("endurance_gain_M1", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_EnduranceOrderlift1to2 :
    ((row 4).1.bench, modalPairs (row 4).1 (row 4).2.1,
     (row 4).2.1.lamN, (row 4).2.1.lamD, (row 4).2.1.lamPerL,
     (row 4).2.1.region, (row 4).2.1.ceilCo, (row 4).2.1.ceilFlip,
     (row 4).2.1.ceilKs, (row 4).2.1.tailCo, (row 4).2.1.tailFlip,
     (row 4).2.1.tailKs)
    = ("endurance_orderlift_1to2", [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2)],
       2, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_EnduranceOrderlift2to3 :
    ((row 5).1.bench, modalPairs (row 5).1 (row 5).2.1,
     (row 5).2.1.lamN, (row 5).2.1.lamD, (row 5).2.1.lamPerL,
     (row 5).2.1.region, (row 5).2.1.ceilCo, (row 5).2.1.ceilFlip,
     (row 5).2.1.ceilKs, (row 5).2.1.tailCo, (row 5).2.1.tailFlip,
     (row 5).2.1.tailKs)
    = ("endurance_orderlift_2to3", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_MatchMultiRate :
    ((row 6).1.bench, modalPairs (row 6).1 (row 6).2.1,
     (row 6).2.1.lamN, (row 6).2.1.lamD, (row 6).2.1.lamPerL,
     (row 6).2.1.region, (row 6).2.1.ceilCo, (row 6).2.1.ceilFlip,
     (row 6).2.1.ceilKs, (row 6).2.1.tailCo, (row 6).2.1.tailFlip,
     (row 6).2.1.tailKs)
    = ("match_multi_rate", [(0, 0), (1, 0), (2, 0), (3, 0)],
       1, 1, [(3,1),(2,1),(1,1)],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Rover3tierRung12Accel :
    ((row 7).1.bench, modalPairs (row 7).1 (row 7).2.1,
     (row 7).2.1.lamN, (row 7).2.1.lamD, (row 7).2.1.lamPerL,
     (row 7).2.1.region, (row 7).2.1.ceilCo, (row 7).2.1.ceilFlip,
     (row 7).2.1.ceilKs, (row 7).2.1.tailCo, (row 7).2.1.tailFlip,
     (row 7).2.1.tailKs)
    = ("rover3tier_rung12", [(0, 0), (0, 1)],
       2, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Rover3tierRung12Coast :
    ((row 8).1.bench, modalPairs (row 8).1 (row 8).2.1,
     (row 8).2.1.lamN, (row 8).2.1.lamD, (row 8).2.1.lamPerL,
     (row 8).2.1.region, (row 8).2.1.ceilCo, (row 8).2.1.ceilFlip,
     (row 8).2.1.ceilKs, (row 8).2.1.tailCo, (row 8).2.1.tailFlip,
     (row 8).2.1.tailKs)
    = ("rover3tier_rung12", [(1, 0), (1, 1)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Rover4dBox :
    ((row 9).1.bench, modalPairs (row 9).1 (row 9).2.1,
     (row 9).2.1.lamN, (row 9).2.1.lamD, (row 9).2.1.lamPerL,
     (row 9).2.1.region, (row 9).2.1.ceilCo, (row 9).2.1.ceilFlip,
     (row 9).2.1.ceilKs, (row 9).2.1.tailCo, (row 9).2.1.tailFlip,
     (row 9).2.1.tailKs)
    = ("rover_4d_box", [(0, 1)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverAttitudeCone :
    ((row 10).1.bench, modalPairs (row 10).1 (row 10).2.1,
     (row 10).2.1.lamN, (row 10).2.1.lamD, (row 10).2.1.lamPerL,
     (row 10).2.1.region, (row 10).2.1.ceilCo, (row 10).2.1.ceilFlip,
     (row 10).2.1.ceilKs, (row 10).2.1.tailCo, (row 10).2.1.tailFlip,
     (row 10).2.1.tailKs)
    = ("rover_attitude_cone_12dof", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       17, 10, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_RoverDofTerrainRung1 :
    ((row 11).1.bench, modalPairs (row 11).1 (row 11).2.1,
     (row 11).2.1.lamN, (row 11).2.1.lamD, (row 11).2.1.lamPerL,
     (row 11).2.1.region, (row 11).2.1.ceilCo, (row 11).2.1.ceilFlip,
     (row 11).2.1.ceilKs, (row 11).2.1.tailCo, (row 11).2.1.tailFlip,
     (row 11).2.1.tailKs)
    = ("rover_dof_terrain_rung1", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverDofTerrainRung2 :
    ((row 12).1.bench, modalPairs (row 12).1 (row 12).2.1,
     (row 12).2.1.lamN, (row 12).2.1.lamD, (row 12).2.1.lamPerL,
     (row 12).2.1.region, (row 12).2.1.ceilCo, (row 12).2.1.ceilFlip,
     (row 12).2.1.ceilKs, (row 12).2.1.tailCo, (row 12).2.1.tailFlip,
     (row 12).2.1.tailKs)
    = ("rover_dof_terrain_rung2", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverDofTerrainRung38d :
    ((row 13).1.bench, modalPairs (row 13).1 (row 13).2.1,
     (row 13).2.1.lamN, (row 13).2.1.lamD, (row 13).2.1.lamPerL,
     (row 13).2.1.region, (row 13).2.1.ceilCo, (row 13).2.1.ceilFlip,
     (row 13).2.1.ceilKs, (row 13).2.1.tailCo, (row 13).2.1.tailFlip,
     (row 13).2.1.tailKs)
    = ("rover_dof_terrain_rung3_8d", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverDofTerrainRung3 :
    ((row 14).1.bench, modalPairs (row 14).1 (row 14).2.1,
     (row 14).2.1.lamN, (row 14).2.1.lamD, (row 14).2.1.lamPerL,
     (row 14).2.1.region, (row 14).2.1.ceilCo, (row 14).2.1.ceilFlip,
     (row 14).2.1.ceilKs, (row 14).2.1.tailCo, (row 14).2.1.tailFlip,
     (row 14).2.1.tailKs)
    = ("rover_dof_terrain_rung3", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverDrag :
    ((row 15).1.bench, modalPairs (row 15).1 (row 15).2.1,
     (row 15).2.1.lamN, (row 15).2.1.lamD, (row 15).2.1.lamPerL,
     (row 15).2.1.region, (row 15).2.1.ceilCo, (row 15).2.1.ceilFlip,
     (row 15).2.1.ceilKs, (row 15).2.1.tailCo, (row 15).2.1.tailFlip,
     (row 15).2.1.tailKs)
    = ("rover_drag", [(0, 0)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverLadderRung1 :
    ((row 16).1.bench, modalPairs (row 16).1 (row 16).2.1,
     (row 16).2.1.lamN, (row 16).2.1.lamD, (row 16).2.1.lamPerL,
     (row 16).2.1.region, (row 16).2.1.ceilCo, (row 16).2.1.ceilFlip,
     (row 16).2.1.ceilKs, (row 16).2.1.tailCo, (row 16).2.1.tailFlip,
     (row 16).2.1.tailKs)
    = ("refinement_ladder_rover_rung1_2to3", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverLadderRung2 :
    ((row 17).1.bench, modalPairs (row 17).1 (row 17).2.1,
     (row 17).2.1.lamN, (row 17).2.1.lamD, (row 17).2.1.lamPerL,
     (row 17).2.1.region, (row 17).2.1.ceilCo, (row 17).2.1.ceilFlip,
     (row 17).2.1.ceilKs, (row 17).2.1.tailCo, (row 17).2.1.tailFlip,
     (row 17).2.1.tailKs)
    = ("refinement_ladder_rover_rung2_3to6", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverLadderRung3 :
    ((row 18).1.bench, modalPairs (row 18).1 (row 18).2.1,
     (row 18).2.1.lamN, (row 18).2.1.lamD, (row 18).2.1.lamPerL,
     (row 18).2.1.region, (row 18).2.1.ceilCo, (row 18).2.1.ceilFlip,
     (row 18).2.1.ceilKs, (row 18).2.1.tailCo, (row 18).2.1.tailFlip,
     (row 18).2.1.tailKs)
    = ("refinement_ladder_rover_rung3_6to8", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       9, 4, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_RoverLadderRung4 :
    ((row 19).1.bench, modalPairs (row 19).1 (row 19).2.1,
     (row 19).2.1.lamN, (row 19).2.1.lamD, (row 19).2.1.lamPerL,
     (row 19).2.1.region, (row 19).2.1.ceilCo, (row 19).2.1.ceilFlip,
     (row 19).2.1.ceilKs, (row 19).2.1.tailCo, (row 19).2.1.tailFlip,
     (row 19).2.1.tailKs)
    = ("refinement_ladder_rover_rung4_8to12", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       17, 10, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_RoverRung2c :
    ((row 20).1.bench, modalPairs (row 20).1 (row 20).2.1,
     (row 20).2.1.lamN, (row 20).2.1.lamD, (row 20).2.1.lamPerL,
     (row 20).2.1.region, (row 20).2.1.ceilCo, (row 20).2.1.ceilFlip,
     (row 20).2.1.ceilKs, (row 20).2.1.tailCo, (row 20).2.1.tailFlip,
     (row 20).2.1.tailKs)
    = ("refinement_ladder_rover_rung2c_6dof", [(0, 0), (1, 1), (2, 2)],
       1, 1, [],
       none, none, false,
       [], some 1, true,
       [0, 3/5, 7/5]) := by rfl

theorem ties_RoverTerrainM1 :
    ((row 21).1.bench, modalPairs (row 21).1 (row 21).2.1,
     (row 21).2.1.lamN, (row 21).2.1.lamD, (row 21).2.1.lamPerL,
     (row 21).2.1.region, (row 21).2.1.ceilCo, (row 21).2.1.ceilFlip,
     (row 21).2.1.ceilKs, (row 21).2.1.tailCo, (row 21).2.1.tailFlip,
     (row 21).2.1.tailKs)
    = ("rover_terrain_M1", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_RoverTierR1 :
    ((row 22).1.bench, modalPairs (row 22).1 (row 22).2.1,
     (row 22).2.1.lamN, (row 22).2.1.lamD, (row 22).2.1.lamPerL,
     (row 22).2.1.region, (row 22).2.1.ceilCo, (row 22).2.1.ceilFlip,
     (row 22).2.1.ceilKs, (row 22).2.1.tailCo, (row 22).2.1.tailFlip,
     (row 22).2.1.tailKs)
    = ("rover_tier_r1", [(0, 0)],
       19, 4, [],
       none, some 1, true,
       [3/10], none, false,
       []) := by rfl

theorem ties_Story1AttdistRungA :
    ((row 23).1.bench, modalPairs (row 23).1 (row 23).2.1,
     (row 23).2.1.lamN, (row 23).2.1.lamD, (row 23).2.1.lamPerL,
     (row 23).2.1.region, (row 23).2.1.ceilCo, (row 23).2.1.ceilFlip,
     (row 23).2.1.ceilKs, (row 23).2.1.tailCo, (row 23).2.1.tailFlip,
     (row 23).2.1.tailKs)
    = ("story1_attdist_rung_a_6to8", [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Story1AttdistRungB :
    ((row 24).1.bench, modalPairs (row 24).1 (row 24).2.1,
     (row 24).2.1.lamN, (row 24).2.1.lamD, (row 24).2.1.lamPerL,
     (row 24).2.1.region, (row 24).2.1.ceilCo, (row 24).2.1.ceilFlip,
     (row 24).2.1.ceilKs, (row 24).2.1.tailCo, (row 24).2.1.tailFlip,
     (row 24).2.1.tailKs)
    = ("story1_attdist_rung_b_12dof", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_Story2LateralA :
    ((row 25).1.bench, modalPairs (row 25).1 (row 25).2.1,
     (row 25).2.1.lamN, (row 25).2.1.lamD, (row 25).2.1.lamPerL,
     (row 25).2.1.region, (row 25).2.1.ceilCo, (row 25).2.1.ceilFlip,
     (row 25).2.1.ceilKs, (row 25).2.1.tailCo, (row 25).2.1.tailFlip,
     (row 25).2.1.tailKs)
    = ("story2_lateral_rung_a_8dof", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Story2LateralB :
    ((row 26).1.bench, modalPairs (row 26).1 (row 26).2.1,
     (row 26).2.1.lamN, (row 26).2.1.lamD, (row 26).2.1.lamPerL,
     (row 26).2.1.region, (row 26).2.1.ceilCo, (row 26).2.1.ceilFlip,
     (row 26).2.1.ceilKs, (row 26).2.1.tailCo, (row 26).2.1.tailFlip,
     (row 26).2.1.tailKs)
    = ("story2_lateral_rung_b_12dof", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Story3RolloverBase :
    ((row 27).1.bench, modalPairs (row 27).1 (row 27).2.1,
     (row 27).2.1.lamN, (row 27).2.1.lamD, (row 27).2.1.lamPerL,
     (row 27).2.1.region, (row 27).2.1.ceilCo, (row 27).2.1.ceilFlip,
     (row 27).2.1.ceilKs, (row 27).2.1.tailCo, (row 27).2.1.tailFlip,
     (row 27).2.1.tailKs)
    = ("story3_rollover_base_12dof", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       5, 4, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_Story3RolloverRungA :
    ((row 28).1.bench, modalPairs (row 28).1 (row 28).2.1,
     (row 28).2.1.lamN, (row 28).2.1.lamD, (row 28).2.1.lamPerL,
     (row 28).2.1.region, (row 28).2.1.ceilCo, (row 28).2.1.ceilFlip,
     (row 28).2.1.ceilKs, (row 28).2.1.tailCo, (row 28).2.1.tailFlip,
     (row 28).2.1.tailKs)
    = ("story3_rollover_ladder_rung_a", [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)],
       27, 20, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_Story3RolloverRungB :
    ((row 29).1.bench, modalPairs (row 29).1 (row 29).2.1,
     (row 29).2.1.lamN, (row 29).2.1.lamD, (row 29).2.1.lamPerL,
     (row 29).2.1.region, (row 29).2.1.ceilCo, (row 29).2.1.ceilFlip,
     (row 29).2.1.ceilKs, (row 29).2.1.tailCo, (row 29).2.1.tailFlip,
     (row 29).2.1.tailKs)
    = ("story3_rollover_ladder_rung_b", [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Story1AttdistRungASteep :
    ((row 30).1.bench, modalPairs (row 30).1 (row 30).2.1,
     (row 30).2.1.lamN, (row 30).2.1.lamD, (row 30).2.1.lamPerL,
     (row 30).2.1.region, (row 30).2.1.ceilCo, (row 30).2.1.ceilFlip,
     (row 30).2.1.ceilKs, (row 30).2.1.tailCo, (row 30).2.1.tailFlip,
     (row 30).2.1.tailKs)
    = ("story1_attdist_rung_a_6to8", [(0, 0), (0, 1), (0, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Story3RolloverRungBSteep :
    ((row 31).1.bench, modalPairs (row 31).1 (row 31).2.1,
     (row 31).2.1.lamN, (row 31).2.1.lamD, (row 31).2.1.lamPerL,
     (row 31).2.1.region, (row 31).2.1.ceilCo, (row 31).2.1.ceilFlip,
     (row 31).2.1.ceilKs, (row 31).2.1.tailCo, (row 31).2.1.tailFlip,
     (row 31).2.1.tailKs)
    = ("story3_rollover_ladder_rung_b", [(0, 0), (0, 1), (0, 2)],
       1, 1, [],
       none, none, false,
       [], none, false,
       []) := by rfl

theorem ties_Story1AttdistRungBRow0 :
    ((row 32).1.bench, modalPairs (row 32).1 (row 32).2.1,
     (row 32).2.1.lamN, (row 32).2.1.lamD, (row 32).2.1.lamPerL,
     (row 32).2.1.region, (row 32).2.1.ceilCo, (row 32).2.1.ceilFlip,
     (row 32).2.1.ceilKs, (row 32).2.1.tailCo, (row 32).2.1.tailFlip,
     (row 32).2.1.tailKs)
    = ("story1_attdist_rung_b_12dof", [(0, 0), (0, 1), (0, 2)],
       1, 1, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_Story1AttdistRungBRow1 :
    ((row 33).1.bench, modalPairs (row 33).1 (row 33).2.1,
     (row 33).2.1.lamN, (row 33).2.1.lamD, (row 33).2.1.lamPerL,
     (row 33).2.1.region, (row 33).2.1.ceilCo, (row 33).2.1.ceilFlip,
     (row 33).2.1.ceilKs, (row 33).2.1.tailCo, (row 33).2.1.tailFlip,
     (row 33).2.1.tailKs)
    = ("story1_attdist_rung_b_12dof", [(1, 1), (1, 2)],
       1, 1, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

theorem ties_Story1AttdistRungBRow2 :
    ((row 34).1.bench, modalPairs (row 34).1 (row 34).2.1,
     (row 34).2.1.lamN, (row 34).2.1.lamD, (row 34).2.1.lamPerL,
     (row 34).2.1.region, (row 34).2.1.ceilCo, (row 34).2.1.ceilFlip,
     (row 34).2.1.ceilKs, (row 34).2.1.tailCo, (row 34).2.1.tailFlip,
     (row 34).2.1.tailKs)
    = ("story1_attdist_rung_b_12dof", [(2, 2)],
       1, 1, [],
       none, some 0, false,
       [3/10, 1/2, 13/20], none, false,
       []) := by rfl

end RelCertifier.Verdicts
