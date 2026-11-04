/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 modal verdict runner

The verdict phases of `--run-verdicts-v2` and `--check-quick-v2` (Appendix B.7, the tool's
own re-sent queries): the modal packs, the reposition packs, the handoffs and the
non-connection checks, each against a declared total.

The modal phase walks `packsV2`, one row per joint flow certificate (Definition 5) the
replay of an emitted cover consumes (benchmark, dimension, invariant row, strata order, i.e.
the rounds of the Lie conditions, stretch λ, left and right mode). It rebuilds the pack's
queries from the emitted IR (`benchIRTableV2`) and the emitted extended mode-fact certificate
(`cutTableV2`) through `modalVerdXQueries` (the builder `modalVerdX_of_queries` proves they
denote the host-level hypothesis `modalVerdX`), prints them with the tool's own `toScript`,
and reports Z3's verdict per component. The total is declared (`expectedModalV2`). Anything
it cannot rebuild is a SKIP and makes the run non-green.
-/
import RelCertifier.VerdictsV2.ModalX
import RelCertifier.VerdictsV2.ModalDynX
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.Cuts
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage
import RelCertifier.Verdicts.RunHandoff
import RelCertifier.Trusted.NonConnQuery
import RelCertifier.Trusted.JointVars
import RelCertifier.InstancesV2.BenchCovers
import RelCertifier.InstancesV2.BenchProgress
import RelCertifier.InstancesV2.BenchPrelanding
import RelCertifier.Proofs.Encoding.Emitted.Progress

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse RelCertifier.Oracle

/-- One verdict pack. -/
structure PackV2 where
  bench  : String
  dim    : ℕ
  invRow : ℕ := 0
  order  : List ℕ
  lamN   : ℕ := 1
  lamD   : ℕ := 1
  l      : ℕ
  m      : ℕ
  deriving Repr, Inhabited

def irV2 (b : String) : PProblem :=
  ((benchIRTableV2.find? (·.1 == b)).map (·.2)).getD default

def cutV2 (b : String) : EvolStrengtheningX :=
  ((cutTableV2.find? (·.1 == b)).map (·.2.2)).getD ⟨[], []⟩

def packLam (r : PackV2) : ℚ := (r.lamN : ℚ) / (r.lamD : ℚ)

/-- The pack's queries, as the runner builds them. -/
def packQueries (r : PackV2) : Option (List (List (IForm r.dim))) :=
  modalVerdXQueries (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order (packLam r) r.l r.m

/-- The hypothesis a pack row stands for: the joint flow certificate of the pairing at the
row's stretch, by the Lie conditions of Lemma 2. -/
noncomputable def packVerd (r : PackV2) : Prop :=
  modalVerdX (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order ((packLam r : ℚ) : ℝ) r.l r.m

/-- The packs. Watertank: the seven admissible joint (left mode, right mode) pairs the replay
consumes, order `[0, 1]`. -/
def packsV2 : List PackV2 :=
  [ ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 0⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 1⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 2⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 3⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 1, 3⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 3⟩,
    -- acc_spoof_limp (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 1, 0⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    -- rover_ladder_2to3 (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 2, 2⟩,
    -- quad_light_lag
    ⟨"quad_light_lag", 3, 0, [2, 3, 0, 1], 6, 5, 0, 0⟩,
    -- rover_ladder_3to6 (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 0, 0⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 0, 1⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 0, 2⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 1, 1⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 1, 2⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 2, 2⟩,
    -- acc_spoof_lag (cover replay at λ = 3/2, budget 2: the dominant-mode claim)
    ⟨"acc_spoof_lag", 2, 0, [1, 0], 3, 2, 0, 0⟩,
    -- rover_ladder_6to8 (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7, 20, 21], 11, 10, 0, 0⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7, 20, 21], 11, 10, 0, 1⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7, 20, 21], 11, 10, 0, 2⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7, 20, 21], 11, 10, 1, 1⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7, 20, 21], 11, 10, 1, 2⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7, 20, 21], 11, 10, 2, 2⟩,
    -- rover_ladder_8to12 (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 25, 26, 27, 2, 3, 6, 7, 12, 13, 16, 17, 20, 21, 24, 1], 11, 10, 0, 0⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 24, 25, 26, 27, 2, 3, 6, 7, 12, 13, 16, 17, 20, 21, 1], 11, 10, 0, 1⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 24, 25, 26, 27, 2, 3, 6, 7, 12, 13, 16, 17, 20, 21, 1], 11, 10, 0, 2⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 18, 19, 22, 23, 24, 25, 26, 27, 2, 3, 6, 7, 14, 15, 16, 17, 20, 21, 1, 12, 13], 11, 10, 1, 1⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 18, 19, 22, 23, 24, 25, 26, 27, 2, 3, 6, 7, 14, 15, 16, 17, 20, 21, 1, 12, 13], 11, 10, 1, 2⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 18, 19, 22, 23, 24, 25, 26, 27, 2, 3, 6, 7, 14, 15, 16, 17, 20, 21, 1, 12, 13], 11, 10, 2, 2⟩,
    -- stopline_drag (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"stopline_drag", 15, 0, [2, 3, 5, 7, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 28, 29, 30, 0, 1, 4, 6, 12, 13, 14, 15, 16, 17, 26, 27, 24, 25], 1, 1, 0, 0⟩,
    ⟨"stopline_drag", 15, 1, [0, 3, 10, 11, 12, 13, 14, 15, 20, 21, 22, 2, 4, 5, 6, 7, 8, 9, 18, 19, 1, 16, 17], 1, 1, 1, 1⟩,
    ⟨"stopline_drag", 15, 1, [0, 3, 10, 11, 12, 13, 14, 15, 20, 21, 22, 2, 4, 5, 6, 7, 8, 9, 18, 19, 1, 16, 17], 1, 1, 1, 2⟩,
    ⟨"stopline_drag", 15, 2, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], 1, 1, 2, 1⟩,
    ⟨"stopline_drag", 15, 2, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], 1, 1, 2, 2⟩,
    -- stopline_friction (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"stopline_friction", 8, 0, [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 1], 1, 1, 0, 0⟩,
    ⟨"stopline_friction", 8, 1, [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 2], 9, 10, 1, 1⟩,
    ⟨"stopline_friction", 8, 1, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 9, 10, 1, 2⟩,
    ⟨"stopline_friction", 8, 2, [0, 1, 2, 3, 4, 5, 6, 7, 8], 1, 1, 2, 1⟩,
    ⟨"stopline_friction", 8, 2, [0, 1, 2, 3, 4, 5, 6, 7, 8], 1, 1, 2, 2⟩,
    -- stopline_lag (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"stopline_lag", 5, 0, [2, 3, 4, 5, 6, 7, 8, 0, 1], 1, 1, 0, 0⟩,
    ⟨"stopline_lag", 5, 1, [0, 1, 2, 3, 4], 1, 1, 1, 1⟩,
    ⟨"stopline_lag", 5, 1, [0, 1, 2, 3, 4], 1, 1, 1, 2⟩,
    ⟨"stopline_lag", 5, 2, [0, 1, 2, 3, 4], 1, 1, 2, 1⟩,
    ⟨"stopline_lag", 5, 2, [0, 1, 2, 3, 4], 1, 1, 2, 2⟩,
    -- stopline_tyre (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"stopline_tyre", 11, 0, [2, 3, 5, 6, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 0, 1, 4, 10, 11, 12, 13], 1, 1, 0, 0⟩,
    ⟨"stopline_tyre", 11, 1, [0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 2, 3, 4, 5], 1, 1, 1, 1⟩,
    ⟨"stopline_tyre", 11, 1, [0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 2, 3, 4, 5], 1, 1, 1, 2⟩,
    ⟨"stopline_tyre", 11, 2, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], 1, 1, 2, 1⟩,
    ⟨"stopline_tyre", 11, 2, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], 1, 1, 2, 2⟩,
    -- gantry_speed_zones (cover replay): each speed zone against MOVE at its override, λ = 3, 2, 1
    ⟨"gantry_speed_zones", 2, 0, [0, 1, 2, 3], 3, 1, 0, 0⟩,
    ⟨"gantry_speed_zones", 2, 0, [0, 1, 2, 3], 2, 1, 1, 0⟩,
    ⟨"gantry_speed_zones", 2, 0, [0, 1, 2, 3], 1, 1, 2, 0⟩,
    -- watertank_twospeed (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 2, 1, 0, 1⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 3, 2, 0, 2⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 0, 3⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 0, 4⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 1, 3⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 1, 4⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 2, 4⟩,
    -- engine_start_highidle (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"engine_start_highidle", 3, 0, [0, 1, 2, 3], 1, 1, 0, 0⟩,
    ⟨"engine_start_highidle", 3, 0, [0, 1, 2, 3], 1, 1, 0, 2⟩,
    ⟨"engine_start_highidle", 3, 0, [0, 1, 2, 3], 1, 1, 0, 3⟩,
    ⟨"engine_start_highidle", 3, 0, [0, 1, 2, 3], 1, 1, 0, 4⟩,
    ⟨"engine_start_highidle", 3, 1, [0, 1, 2, 3], 1, 1, 1, 1⟩,
    ⟨"engine_start_highidle", 3, 1, [0, 1, 2, 3], 1, 1, 1, 2⟩,
    ⟨"engine_start_highidle", 3, 1, [0, 1, 2, 3], 1, 1, 1, 3⟩,
    ⟨"engine_start_highidle", 3, 1, [0, 1, 2, 3], 1, 1, 1, 4⟩,
    ⟨"engine_start_highidle", 3, 2, [0], 1, 1, 2, 2⟩,
    ⟨"engine_start_highidle", 3, 2, [0], 1, 1, 2, 3⟩,
    ⟨"engine_start_highidle", 3, 2, [0], 1, 1, 2, 4⟩,
    ⟨"engine_start_highidle", 3, 3, [0], 1, 1, 3, 3⟩,
    ⟨"engine_start_highidle", 3, 3, [0], 1, 1, 3, 4⟩,
    ⟨"engine_start_highidle", 3, 4, [0], 1, 1, 4, 4⟩,
    ⟨"engine_start_highidle", 3, 5, [0], 1, 1, 5, 0⟩,
    ⟨"engine_start_highidle", 3, 5, [0], 1, 1, 5, 1⟩,
    ⟨"engine_start_highidle", 3, 5, [0], 1, 1, 5, 2⟩,
    ⟨"engine_start_highidle", 3, 5, [0], 1, 1, 5, 3⟩,
    ⟨"engine_start_highidle", 3, 5, [0], 1, 1, 5, 4⟩,
    ⟨"engine_start_highidle", 3, 5, [0], 1, 1, 5, 5⟩,
    -- train_ato_odometry: a stretch per pairing, below 1 against faster design levels (31/40 .. 6/5)
    ⟨"train_ato_odometry", 2, 0, [0, 1], 39, 40, 0, 0⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 43, 40, 0, 1⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 6, 5, 0, 2⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 7, 8, 1, 0⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 39, 40, 1, 1⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 11, 10, 1, 2⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 31, 40, 2, 0⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 7, 8, 2, 1⟩,
    ⟨"train_ato_odometry", 2, 0, [0, 1], 39, 40, 2, 2⟩,
    -- turbine_startup_gearratio (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"turbine_startup_gearratio", 3, 0, [0, 1, 2, 3, 4], 1, 1, 0, 0⟩,
    ⟨"turbine_startup_gearratio", 3, 0, [0, 1, 2, 3, 4], 1, 1, 0, 2⟩,
    ⟨"turbine_startup_gearratio", 3, 0, [0, 1, 2, 3, 4], 1, 1, 0, 3⟩,
    ⟨"turbine_startup_gearratio", 3, 1, [0, 1, 2, 3, 4], 1, 1, 1, 1⟩,
    ⟨"turbine_startup_gearratio", 3, 1, [0, 1, 2, 3, 4], 1, 1, 1, 2⟩,
    ⟨"turbine_startup_gearratio", 3, 1, [0, 1, 2, 3, 4], 1, 1, 1, 3⟩,
    ⟨"turbine_startup_gearratio", 3, 2, [0, 1, 2, 3, 4], 1, 1, 2, 2⟩,
    ⟨"turbine_startup_gearratio", 3, 2, [0, 1, 2, 3, 4], 1, 1, 2, 3⟩,
    ⟨"turbine_startup_gearratio", 3, 3, [0, 1, 2, 3, 4, 5], 1, 1, 3, 3⟩,
    ⟨"turbine_startup_gearratio", 3, 4, [1, 2, 3, 4, 5, 0], 1, 1, 4, 4⟩,
    -- elevator_start_discbrake (mode-keyed rows; UP_L's right-only LIFT node is below)
    ⟨"elevator_start_discbrake", 3, 0, [0, 1, 2, 3, 4], 1, 1, 0, 0⟩,
    ⟨"elevator_start_discbrake", 3, 0, [0, 1, 2, 3, 4], 1, 1, 0, 2⟩,
    ⟨"elevator_start_discbrake", 3, 0, [0, 1, 2, 3, 4], 1, 1, 0, 3⟩,
    ⟨"elevator_start_discbrake", 3, 1, [2, 3, 0, 1], 1, 1, 1, 1⟩,
    ⟨"elevator_start_discbrake", 3, 2, [2, 3, 0, 1], 1, 1, 2, 2⟩,
    ⟨"elevator_start_discbrake", 3, 3, [2, 3, 0, 1], 1, 1, 3, 3⟩,
    -- hydro_rejection_gatecal (mode-keyed rows; cover replay at λ = 1)
    ⟨"hydro_rejection_gatecal", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 0, 0⟩,
    ⟨"hydro_rejection_gatecal", 3, 1, [0, 1, 4, 5, 2, 3], 1, 1, 1, 1⟩,
    -- syringe_relay_prearm (mode-keyed rows; the right-only TAKEUP2 and RUN2 nodes are below)
    ⟨"syringe_relay_prearm", 4, 0, [0, 1, 2, 3, 4, 5, 6], 1, 1, 0, 0⟩,
    ⟨"syringe_relay_prearm", 4, 0, [1, 2, 3, 4, 5, 6, 0], 1, 1, 0, 3⟩,
    ⟨"syringe_relay_prearm", 4, 1, [0, 1, 2, 3, 4, 5, 6], 1, 1, 1, 0⟩,
    ⟨"syringe_relay_prearm", 4, 1, [1, 2, 3, 4, 5, 6, 0], 1, 1, 1, 3⟩,
    ⟨"syringe_relay_prearm", 4, 2, [0, 1, 2, 3, 4, 5, 6], 1, 1, 2, 0⟩,
    ⟨"syringe_relay_prearm", 4, 2, [1, 2, 3, 4, 5, 6, 0], 1, 1, 2, 3⟩,
    ⟨"syringe_relay_prearm", 4, 3, [0, 1, 2, 3, 4, 5, 6], 1, 1, 3, 1⟩,
    ⟨"syringe_relay_prearm", 4, 3, [0, 1, 2, 3, 4, 5, 6], 1, 1, 3, 3⟩,
    ⟨"syringe_relay_prearm", 4, 4, [0, 1, 2, 3, 4], 1, 1, 4, 2⟩,
    ⟨"syringe_relay_prearm", 4, 5, [0, 1, 2, 3, 4], 1, 1, 5, 3⟩,
    -- ventilator_vc_cuffleak (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"ventilator_vc_cuffleak", 3, 0, [0, 1, 2, 4, 5, 3], 1, 1, 0, 0⟩,
    ⟨"ventilator_vc_cuffleak", 3, 1, [0, 1, 2, 4, 5, 3], 1, 1, 1, 1⟩,
    -- furnace_program_timebase (cover replay at λ = 4/5)
    ⟨"furnace_program_timebase", 2, 0, [0, 1, 4, 5, 2, 3], 4, 5, 0, 0⟩,
    ⟨"furnace_program_timebase", 2, 0, [0, 1, 2, 3, 4, 5], 4, 5, 0, 2⟩,
    ⟨"furnace_program_timebase", 2, 0, [0, 1, 4, 5, 2, 3], 4, 5, 1, 1⟩,
    ⟨"furnace_program_timebase", 2, 0, [0, 1, 3, 4, 5, 2], 4, 5, 2, 2⟩,
    -- tank_dos_3to1 (cover replay): each left stage against its own and the next two right stages
    -- (the staging chain P2 -> P3 -> P4 -> P5) at λ = 1
    ⟨"tank_dos_3to1", 2, 0, [2, 3, 0, 1], 1, 1, 0, 0⟩,
    ⟨"tank_dos_3to1", 2, 0, [2, 3, 0, 1], 1, 1, 0, 1⟩,
    ⟨"tank_dos_3to1", 2, 0, [2, 3, 0, 1], 1, 1, 0, 2⟩,
    ⟨"tank_dos_3to1", 2, 0, [2, 3, 0, 1], 1, 1, 1, 1⟩,
    ⟨"tank_dos_3to1", 2, 0, [2, 3, 0, 1], 1, 1, 1, 2⟩,
    ⟨"tank_dos_3to1", 2, 0, [2, 3, 0, 1], 1, 1, 1, 3⟩,
    ⟨"tank_dos_3to1", 2, 0, [2, 3, 0, 1], 1, 1, 2, 2⟩,
    ⟨"tank_dos_3to1", 2, 0, [1, 2, 3, 0], 1, 1, 2, 3⟩,
    ⟨"tank_dos_3to1", 2, 0, [1, 2, 3, 0], 1, 1, 3, 3⟩,
    -- lit_nahs25_salt_tank (cover replay, budget 1: On_L at λ = 1, Off_L at stretch 0
    -- (admitted by the IR flag `stutter`); rows derived from the emitted cover; dimension 3, that of its
    -- Assumption 1 proof)
    ⟨"lit_nahs25_salt_tank", 3, 0, [0, 1, 2, 3], 1, 1, 0, 0⟩,
    ⟨"lit_nahs25_salt_tank", 3, 0, [1, 2, 3, 0], 1, 1, 0, 1⟩,
    ⟨"lit_nahs25_salt_tank", 3, 0, [0, 1, 2, 3], 0, 1, 1, 0⟩,
    ⟨"lit_nahs25_salt_tank", 3, 0, [0, 1, 2, 3], 0, 1, 1, 1⟩,
    -- bottling_fill_strainer (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"bottling_fill_strainer", 2, 0, [0, 1, 2, 3], 17, 20, 0, 0⟩,
    ⟨"bottling_fill_strainer", 2, 0, [0, 1, 2, 3], 1, 1, 1, 1⟩,
    -- flaps_slow_approach (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"flaps_slow_approach", 2, 0, [0, 1, 2, 3], 1, 2, 0, 0⟩,
    ⟨"flaps_slow_approach", 2, 0, [0, 1, 2, 3], 1, 1, 1, 1⟩,
    -- platoon_profiles (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"platoon_profiles", 3, 0, [2, 3, 4, 5, 6, 7, 0, 1], 6, 5, 0, 0⟩,
    -- h2_refuel_ambientbias (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"h2_refuel_ambientbias", 3, 0, [0], 1, 1, 0, 0⟩,
    ⟨"h2_refuel_ambientbias", 3, 0, [0], 1, 1, 0, 1⟩,
    ⟨"h2_refuel_ambientbias", 3, 0, [0], 1, 1, 0, 2⟩,
    ⟨"h2_refuel_ambientbias", 3, 0, [0], 1, 1, 0, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 0, [0], 1, 1, 0, 4⟩,
    ⟨"h2_refuel_ambientbias", 3, 1, [0], 1, 1, 1, 1⟩,
    ⟨"h2_refuel_ambientbias", 3, 1, [0], 1, 1, 1, 2⟩,
    ⟨"h2_refuel_ambientbias", 3, 1, [0], 1, 1, 1, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 1, [0], 1, 1, 1, 4⟩,
    ⟨"h2_refuel_ambientbias", 3, 2, [0], 1, 1, 2, 2⟩,
    ⟨"h2_refuel_ambientbias", 3, 2, [0], 1, 1, 2, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 2, [0], 1, 1, 2, 4⟩,
    ⟨"h2_refuel_ambientbias", 3, 3, [0], 1, 1, 3, 2⟩,
    ⟨"h2_refuel_ambientbias", 3, 3, [0], 1, 1, 3, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 3, [0], 1, 1, 3, 4⟩,
    ⟨"h2_refuel_ambientbias", 3, 4, [0], 1, 1, 4, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 4, [0], 1, 1, 4, 4⟩,
    ⟨"h2_refuel_ambientbias", 3, 5, [0], 1, 1, 5, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 5, [0], 1, 1, 5, 4⟩,
    ⟨"h2_refuel_ambientbias", 3, 6, [0], 1, 1, 6, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 6, [0], 1, 1, 6, 4⟩,
    -- reactor_feed_wireless (cover replay at λ = 1, budget 2; the
    -- four pruned edges into the live levels F1 and F4): each left level against the joint levels
    -- of its cover
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 0, 0⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 0, 1⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 0, 2⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 1, 0⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 1, 1⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 1, 2⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 1, 3⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 2, 0⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 2, 1⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 2, 2⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 2, 3⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 3, 1⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 3, 2⟩,
    ⟨"reactor_feed_wireless", 2, 0, [2, 3, 0, 1], 1, 1, 3, 3⟩,
    -- extruder_pe100_manualstart (rows derived from the emitted cover: every joint
    -- pairing of each left step, λ = 1, budget 2; the four pruned edges into the live steps N1 and N4)
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 0, 0⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 0, 1⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 0, 2⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 1, 0⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 1, 1⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 1, 2⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 1, 3⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 2, 0⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 2, 1⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 2, 2⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 2, 3⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 3, 1⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 3, 2⟩,
    ⟨"extruder_pe100_manualstart", 2, 0, [2, 3, 0, 1], 1, 1, 3, 3⟩,
    -- lit_nahs25_engine_cooling (rows derived from the emitted cover: the joint pairing of each
    -- left mode, λ = 1, budget 1; its right-only nodes, certified on the restricted mode, are
    -- discharged by the bridge runner, not here)
    ⟨"lit_nahs25_engine_cooling", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"lit_nahs25_engine_cooling", 3, 0, [0, 1], 1, 1, 1, 1⟩,
    -- antenna_track_kvretune (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"antenna_track_kvretune", 3, 0, [0, 1, 2, 3, 6, 7, 4, 5], 1, 1, 0, 0⟩,
    ⟨"antenna_track_kvretune", 3, 1, [0, 1, 2, 3, 6, 7, 4, 5], 1, 1, 1, 1⟩,
    ⟨"antenna_track_kvretune", 3, 2, [0, 1, 2, 3, 6, 7, 4, 5], 1, 1, 2, 2⟩,
    -- canal_gate_notches (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 2, 3⟩,
    -- rampmeter_poll_2to1 (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 0, 0⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 0, 1⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 0, 2⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 0, 3⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 1, 0⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 1, 1⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 1, 2⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 1, 3⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 1, 4⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 2, 0⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 2, 1⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 2, 2⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 2, 3⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 2, 4⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 2, 5⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 3, 1⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 3, 2⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 3, 3⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 3, 4⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 3, 5⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 4, 1⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 4, 2⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 4, 3⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 4, 4⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 4, 5⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 5, 2⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 5, 3⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 5, 4⟩,
    ⟨"rampmeter_poll_2to1", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 5, 5⟩,
    -- lit_csf25_salt_tank_hold (rows derived from the emitted cover: the stale-reading
    -- hold, one held left mode per decision, four keyed rows each)
    ⟨"lit_csf25_salt_tank_hold", 3, 0, [0, 2, 3, 1], 1, 3, 0, 0⟩,
    ⟨"lit_csf25_salt_tank_hold", 3, 1, [0, 1, 2, 3], 1, 3, 1, 1⟩,
    -- molding_pack_checkring (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"molding_pack_checkring", 3, 0, [0, 1, 2, 4, 6, 3, 5], 1, 1, 0, 0⟩,
    ⟨"molding_pack_checkring", 3, 1, [0, 1, 2, 3, 4], 1, 1, 1, 1⟩,
    -- boiler_purge_vfd (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"boiler_purge_vfd", 3, 0, [0, 1, 2, 3, 4, 5], 1, 1, 0, 0⟩,
    ⟨"boiler_purge_vfd", 3, 1, [1, 2, 3, 4, 0], 1, 1, 1, 1⟩,
    -- autoclave_liquid_steambank (rows derived from the emitted cover: the joint pairings reached in each left mode)
    ⟨"autoclave_liquid_steambank", 3, 0, [0, 1, 2, 3, 6, 7, 4, 5], 3, 4, 0, 0⟩,
    ⟨"autoclave_liquid_steambank", 3, 1, [0, 1, 2, 3, 4, 5, 6, 7], 1, 1, 1, 1⟩,
    ⟨"autoclave_liquid_steambank", 3, 2, [0, 1, 2, 3], 1, 1, 2, 2⟩,
    ⟨"autoclave_liquid_steambank", 3, 3, [0, 1, 2, 3], 1, 1, 3, 3⟩ ]

/-- Declared: the number of component queries the packs owe (one per component), the modal
count of Appendix B.7. The rows are derived from the emitted covers by
`scripts/gen_pack_rows.py --joint` (`--joint-swap` replaces one benchmark's rows by
another's). -/
def expectedModalV2 : Nat := 1421

/-- Run one pack. -/
def runPack (s : Z3Session) (r : PackV2) : IO Bool := do
  let p := irV2 r.bench
  let vars := p.L.stateVars
  let coord := fun (i : Fin r.dim) => vars.getD i.val s!"pad{i.val}"
  match packQueries r with
  | none =>
      IO.println s!"  SKIP  {r.bench} (l={r.l},m={r.m})  (rebuild failed)"
      pure false
  | some qss =>
      if qss.isEmpty then
        IO.println s!"  SKIP  {r.bench} (l={r.l},m={r.m})  (no component)"
        return false
      let mut ok := true
      for i in List.range qss.length do
        let qs := qss.getD i []
        let mut good := false
        let mut detail := ""
        for (rn, q) in [("A", qs.getD 0 IForm.tt), ("B", qs.getD 1 IForm.tt),
            ("C", qs.getD 2 IForm.tt)] do
          if good then pure () else
          match ← s.check (q.toScript coord) with
          | .ok .unsat => good := true; detail := detail ++ s!"{rn}=unsat"
          | .ok .sat => detail := detail ++ s!"{rn}=sat "
          | .ok v => detail := detail ++ s!"{rn}={reprStr v} "
          | .error e => detail := detail ++ s!"{rn}=err({e}) "
        if good then
          IO.println s!"  UNSAT ({detail})  {r.bench} (l={r.l},m={r.m}) comp={i}"
          RelCertifier.Verdicts.counted
        else
          IO.println s!"  FAIL  {r.bench} (l={r.l},m={r.m}) comp={i} : {detail}"
          ok := false
      pure ok

def runModalV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 modal instances : {packsV2.length} verdict packs =="
      let mut ok := true
      for r in packsV2 do
        ok := (← runPack s r) && ok
      s.close
      pure ok

/-! ## The right-only flow certificates (Lemma 4) of the cover replays

One row per right-only flow-certificate pack (Definition 5, right-only kind) a cover replay
consumes: right mode `m` against left mode `l`, pre-joint (`pre = true`: the left guard
conjoined) or post-joint, the invariant row's components in the cover's right-only strata order
(`dynPreOrder` / `dynPostOrder` of the emitted cover, or the order of the record of right-only
certificates on the restricted mode). A row with `preland = true` is certified on the restricted
mode `M|¬L` of Lemma 4, `L` the landing target of the node's reposition certificate (Definition
7, the closed half-space past its last stage's threshold): its pack is on that region, read off
the benchmark's records exactly as the bridge does (`Emitted.dynRegionI` on the cover merged
with that record and the reposition record), and is sent as groups (one per component, its
routes A/B/C as members, `modalVerdDynXGroups`). A row with `preland = false` is on the whole
domain, one query per component (`modalVerdDynXQueries`, the builder `modalVerdDynX_of_queries`
proves it denotes the hypothesis). Every row of the table has `preland = true`. The runner owes
one `unsat` per group. The rows are generated from the emitted leaves by
`scripts/gen_pack_rows.py --dyn` (the replay of the verified checker on the merged cover). -/

/-- The emitted cover of a suite benchmark. -/
def coverV2 (b : String) : CoverEmitE :=
  ((coverTableV2.find? (·.1 == b)).map (·.2)).getD ⟨b, [], []⟩

/-- The cover the bridge groups are built on: the emitted cover, merged with the benchmark's
record of right-only certificates on the restricted mode (`Emitted.withPL`, `docs/PRELANDING.md`;
the instance's `covM`). -/
def coverV2M (b : String) : CoverEmitE :=
  match Preland.prelandTableV2.find? (·.1 == b) with
  | some (_, pl) => Emitted.withPL (coverV2 b) pl
  | none => coverV2 b

/-- The emitted reposition certificates (Definition 7) of a suite benchmark. -/
def progV2 (b : String) : Progress.ProgressEmitE :=
  ((Progress.progressTableV2.find? (·.1 == b)).map (·.2)).getD ⟨b, []⟩

structure DynPackV2 where
  bench  : String
  dim    : ℕ
  invRow : ℕ := 0
  order  : List ℕ
  pre    : Bool := true
  l      : ℕ
  m      : ℕ
  /-- a node certified on the restricted mode: the pack on its region (`Emitted.dynRegionI`) -/
  preland : Bool := false
  deriving Repr, Inhabited

def dynPackQueries (r : DynPackV2) : Option (List (IForm r.dim)) :=
  modalVerdDynXQueries (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order r.pre r.l r.m

/-- The node's region (a row on the restricted mode), read off the records as the bridge's
`dynGroups` does; `none` for a whole-domain row. -/
def dynPackRegion (r : DynPackV2) : Option (IForm r.dim × IForm r.dim × List Bool) :=
  if r.preland then
    Emitted.dynRegionI (irV2 r.bench) r.dim (coverV2M r.bench) (progV2 r.bench) r.l r.m r.pre
  else none

/-- The pack's groups as the runner sends them: one group per component (the routes as
members), `modalVerdDynXGroups` on the row's region. -/
def dynPackGroups (r : DynPackV2) : Option (List (List (IForm r.dim))) :=
  modalVerdDynXGroups (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order r.pre r.l r.m
    (dynPackRegion r)

noncomputable def dynPackVerd (r : DynPackV2) : Prop :=
  modalVerdDynX (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order r.pre r.l r.m

/-- The reposition packs. -/
def dynPacksV2 : List DynPackV2 :=
  [
    -- acc_spoof_limp: the right-only nodes the replay consumes (2 of 2 on the restricted mode)
    ⟨"acc_spoof_limp", 3, 0, [0, 1], true, 1, 1, true⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], false, 1, 1, true⟩,
    -- autoclave_liquid_steambank: the right-only nodes the replay consumes (1 of 1 on the restricted mode)
    ⟨"autoclave_liquid_steambank", 3, 2, [0, 1, 2, 3], true, 2, 1, true⟩,
    -- boiler_purge_vfd: the right-only nodes the replay consumes (1 of 1 on the restricted mode)
    ⟨"boiler_purge_vfd", 3, 1, [0, 1, 2, 3, 4], true, 1, 0, true⟩,
    -- canal_gate_notches: the right-only nodes the replay consumes (8 of 8 on the restricted mode)
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 0, 1, true⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 0, 2, true⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 0, 3, true⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 1, 0, true⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 1, 3, true⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 2, 0, true⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 2, 1, true⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], true, 2, 2, true⟩,
    -- elevator_start_discbrake: the right-only nodes the replay consumes (1 of 1 on the restricted mode)
    ⟨"elevator_start_discbrake", 3, 1, [0, 1, 2, 3], true, 1, 0, true⟩,
    -- engine_start_highidle: the right-only nodes the replay consumes (2 of 2 on the restricted mode)
    ⟨"engine_start_highidle", 3, 3, [0], true, 3, 2, true⟩,
    ⟨"engine_start_highidle", 3, 4, [0], true, 4, 3, true⟩,
    -- h2_refuel_ambientbias: the right-only nodes the replay consumes (2 of 2 on the restricted mode)
    ⟨"h2_refuel_ambientbias", 3, 4, [0], true, 4, 2, true⟩,
    ⟨"h2_refuel_ambientbias", 3, 5, [0], true, 5, 2, true⟩,
    -- lit_csf21_vehicle_bus: the right-only nodes the replay consumes (48 of 48 on the restricted mode)
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 4, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 5, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 6, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 7, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 8, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 9, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 10, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 0, 11, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 4, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 5, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 6, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 7, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 8, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 9, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 10, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 1, 11, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 0, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 1, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 2, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 3, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 8, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 9, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 10, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 2, 11, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 0, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 1, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 2, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 3, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 8, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 9, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 10, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 3, 11, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 0, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 1, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 2, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 3, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 4, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 5, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 6, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 4, 7, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 0, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 1, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 2, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 3, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 4, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 5, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 6, true⟩,
    ⟨"lit_csf21_vehicle_bus", 3, 0, [0, 1, 2, 3], true, 5, 7, true⟩,
    -- lit_csf21_vehicle_thermo: the right-only nodes the replay consumes (24 of 24 on the restricted mode)
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 0, 2, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 0, 3, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 0, 4, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 0, 5, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 1, 2, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 1, 3, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 1, 4, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 1, 5, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 2, 0, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 2, 1, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 2, 4, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 2, 5, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 3, 0, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 3, 1, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 3, 4, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 3, 5, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 4, 0, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 4, 1, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 4, 2, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 4, 3, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 5, 0, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 5, 1, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 5, 2, true⟩,
    ⟨"lit_csf21_vehicle_thermo", 3, 0, [0, 1, 2, 3], true, 5, 3, true⟩,
    -- lit_drl_lane_control: the right-only nodes the replay consumes (30 of 30 on the restricted mode)
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 0, 1, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 0, 2, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 0, 3, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 0, 4, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 0, 5, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 1, 0, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 1, 2, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 1, 3, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 1, 4, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 1, 5, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 2, 0, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 2, 1, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 2, 3, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 2, 4, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 2, 5, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 3, 0, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 3, 1, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 3, 2, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 3, 4, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 3, 5, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 4, 0, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 4, 1, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 4, 2, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 4, 3, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 4, 5, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 5, 0, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 5, 1, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 5, 2, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 5, 3, true⟩,
    ⟨"lit_drl_lane_control", 3, 0, [0, 1, 2, 3, 4, 5], true, 5, 4, true⟩,
    -- lit_freedm_meter: the right-only nodes the replay consumes (74 of 74 on the restricted mode)
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 0, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 0, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 0, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 0, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 1, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 1, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 1, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 1, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 2, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 2, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 2, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 2, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 3, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 3, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 3, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 3, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 4, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 4, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 4, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 4, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 5, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 5, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 5, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 5, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 6, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 6, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 6, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 6, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 0, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 1, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 2, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 3, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 4, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 5, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 6, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 9, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 7, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 0, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 1, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 2, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 3, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 4, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 5, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 6, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 9, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 8, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 9, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 9, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 9, 10, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 9, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 0, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 1, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 2, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 3, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 4, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 5, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 6, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 8, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 9, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 10, 11, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 0, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 1, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 2, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 3, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 4, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 5, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 6, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 7, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 9, true⟩,
    ⟨"lit_freedm_meter", 3, 0, [0, 1], true, 11, 10, true⟩,
    -- lit_girard08_robot: the right-only nodes the replay consumes (30 of 30 on the restricted mode)
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 0, 1, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 3, 4, 0, 2], true, 0, 2, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 2, 3, 4, 0], true, 0, 3, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 2, 4, 0, 3], true, 0, 4, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 2, 4, 1, 3], true, 0, 5, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 2, 3, 4, 1], true, 1, 0, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 3, 4, 0, 2], true, 1, 2, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 2, 3, 4, 0], true, 1, 3, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 2, 4, 0, 3], true, 1, 4, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 2, 4, 1, 3], true, 1, 5, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 2, 0, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 2, 1, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 2, 3, 4, 0], true, 2, 3, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 2, 4, 0, 3], true, 2, 4, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 2, 4, 1, 3], true, 2, 5, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 3, 0, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 3, 1, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 3, 4, 0, 2], true, 3, 2, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 2, 4, 0, 3], true, 3, 4, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 2, 4, 1, 3], true, 3, 5, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 2, 3, 4, 1], true, 4, 0, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 4, 1, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 3, 4, 0, 2], true, 4, 2, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 4, 3, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 2, 4, 1, 3], true, 4, 5, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 5, 0, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 5, 1, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [1, 3, 4, 0, 2], true, 5, 2, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 5, 3, true⟩,
    ⟨"lit_girard08_robot", 6, 0, [0, 1, 2, 3, 4], true, 5, 4, true⟩,
    -- lit_lz21_vehicle_position: the right-only nodes the replay consumes (6 of 6 on the restricted mode)
    ⟨"lit_lz21_vehicle_position", 3, 0, [0, 1, 2, 3, 4], true, 0, 1, true⟩,
    ⟨"lit_lz21_vehicle_position", 3, 0, [0, 1, 2, 3, 4], true, 0, 2, true⟩,
    ⟨"lit_lz21_vehicle_position", 3, 0, [0, 1, 2, 3, 4], true, 1, 0, true⟩,
    ⟨"lit_lz21_vehicle_position", 3, 0, [0, 1, 2, 3, 4], true, 1, 2, true⟩,
    ⟨"lit_lz21_vehicle_position", 3, 0, [0, 1, 2, 3, 4], true, 2, 0, true⟩,
    ⟨"lit_lz21_vehicle_position", 3, 0, [0, 1, 2, 3, 4], true, 2, 1, true⟩,
    -- lit_nahs25_engine_cooling: the right-only nodes the replay consumes (2 of 2 on the restricted mode)
    ⟨"lit_nahs25_engine_cooling", 3, 0, [0, 1], true, 0, 1, true⟩,
    ⟨"lit_nahs25_engine_cooling", 3, 0, [0, 1], true, 1, 0, true⟩,
    -- quad_light_profiles: the right-only nodes the replay consumes (12 of 12 on the restricted mode)
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], true, 0, 0, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], false, 0, 0, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], true, 0, 2, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], false, 0, 2, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], true, 1, 1, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], false, 1, 1, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], true, 1, 2, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], false, 1, 2, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], true, 2, 0, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], false, 2, 0, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], true, 2, 1, true⟩,
    ⟨"quad_light_profiles", 3, 0, [0, 1, 2, 3, 4, 5], false, 2, 1, true⟩,
    -- syringe_relay_prearm: the right-only nodes the replay consumes (1 of 1 on the restricted mode)
    ⟨"syringe_relay_prearm", 4, 4, [0, 1, 2, 3, 4], true, 4, 1, true⟩,
    -- turbine_startup_gearratio: the right-only nodes the replay consumes (6 of 6 on the restricted mode)
    ⟨"turbine_startup_gearratio", 3, 0, [0, 1, 2, 3, 4], true, 0, 1, true⟩,
    ⟨"turbine_startup_gearratio", 3, 0, [0, 1, 2, 3, 4], true, 0, 4, true⟩,
    ⟨"turbine_startup_gearratio", 3, 1, [0, 1, 2, 3, 4], true, 1, 4, true⟩,
    ⟨"turbine_startup_gearratio", 3, 2, [0, 1, 2, 3, 4], true, 2, 4, true⟩,
    ⟨"turbine_startup_gearratio", 3, 3, [0, 1, 2, 3, 4, 5], true, 3, 4, true⟩,
    ⟨"turbine_startup_gearratio", 3, 4, [0, 1, 2, 3, 4, 5], true, 4, 3, true⟩,
    -- watertank: the right-only nodes the replay consumes (1 of 1 on the restricted mode)
    ⟨"watertank", 2, 0, [0, 1], true, 1, 1, true⟩,
    -- watertank_twospeed: the right-only nodes the replay consumes (1 of 1 on the restricted mode)
    ⟨"watertank_twospeed", 2, 0, [0, 1], true, 1, 2, true⟩ ]

/-- Declared: the number of component groups the right-only packs owe (one per component), the
reposition count of Appendix B.7: every right-only pack the replay consumes over the suite (252
packs in 19 benchmarks, `scripts/gen_pack_rows.py --dyn`), each on its restricted mode. -/
def expectedDynV2 : Nat := 950

def runDynPack (s : Z3Session) (r : DynPackV2) : IO Bool := do
  let p := irV2 r.bench
  let vars := p.L.stateVars
  let coord := fun (i : Fin r.dim) => vars.getD i.val s!"pad{i.val}"
  let tag := s!"{r.bench} (l={r.l},m={r.m},pre={r.pre}{if r.preland then ",pre-landing" else ""})"
  if r.preland && (dynPackRegion r).isNone then
    IO.println s!"  FAIL  {tag}  (no landing stage in the records)"
    return false
  match dynPackGroups r with
  | none =>
      IO.println s!"  SKIP  {tag}  (rebuild failed)"
      pure false
  | some gs =>
      if gs.isEmpty then
        IO.println s!"  SKIP  {tag}  (no component)"
        return false
      let mut ok := true
      for i in List.range gs.length do
        let g := gs.getD i []
        let mut hit := false
        for q in g do
          if !hit then
            match ← s.check (q.toScript coord) with
            | .ok .unsat => hit := true
            | _ => pure ()
        if hit then
          IO.println s!"  UNSAT  {tag} comp={i}"
          RelCertifier.Verdicts.counted
        else
          IO.println s!"  FAIL  {tag} comp={i} : no route unsat ({g.length} tried)"
          ok := false
      pure ok

def runDynV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 reposition packs : {dynPacksV2.length} verdict packs =="
      let mut ok := true
      for r in dynPacksV2 do
        ok := (← runDynPack s r) && ok
      s.close
      pure ok

/-! ## The handoff phase over suite_v2 -/

/-- Declared: one handoff query (Eq. (13), Theorem 2) per declared left mode change over the
suite_v2 files, self-loops included, the handoff count of Appendix B.7. The 48 abstraction modes
of `lit_gpt10_boost_converter`, every one a successor of every other, alone declare 2256 of them,
all vacuous as its rows are identical. -/
def expectedHandoffV2 : Nat := 2846

/-- Declared handoff failures in suite_v2: none. -/
def expectedHandoffFailuresV2 : List (String × Nat × Nat) := []

def runHandoffAllV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 handoff : {benchIRTableV2.length} benchmarks =="
      let mut ok := true
      let mut fails : List (String × ℕ × ℕ) := []
      for (name, p) in benchIRTableV2 do
        let r ← RelCertifier.Verdicts.runHandoffBench s cfg name p (verbose := false)
        IO.println r.line
        if r.checked != r.declared then
          IO.eprintln s!"  [handoff] {name}: {r.checked} checked but {r.declared} declared"
          ok := false
        fails := fails ++ r.failing.map (fun f => (name, f.1.1, f.1.2))
      s.close
      let extra := fails.filter (fun f => !expectedHandoffFailuresV2.contains f)
      let stale := expectedHandoffFailuresV2.filter (fun f => !fails.contains f)
      if !extra.isEmpty then
        IO.eprintln s!"  [handoff] UNDECLARED failures: {extra}"; ok := false
      if !stale.isEmpty then
        IO.eprintln s!"  [handoff] stale declared failures: {stale}"; ok := false
      pure ok

/-! ## The non-connection phase over suite_v2 (the pruned edges of the emitted covers,
Definition 6, the source mode's mode fact rebuilt from the EXTENDED certificate, as the tool
narrows it) -/

def prunedEdgesV2 : List (String × String × String) :=
  coverTableV2.flatMap (fun c => c.2.pruned.map (fun e => (c.1, e.1, e.2)))

/-- Declared: pruned edges in the suite_v2 covers, and two queries per edge, the pruned-edge and
non-connection counts of Appendix B.7: `source` (no entry state satisfies the successor's guard)
and `barrier` (the flow points away from the guard's threshold), the pruning of Section 6.1. -/
def expectedPrunedEdgesV2 : Nat := 16
def expectedNonConnV2 : Nat := 32

def nonConnQueriesOfV2 (p : PProblem) (cX : EvolStrengtheningX) (src tgt : String) :
    Option ((n : ℕ) × (Fin n → String) × IForm n × IForm n) := do
  let vars := p.jointVars
  let n := vars.length
  let mR ← p.R.modes.find? (·.name == src)
  let mSuc ← p.R.modes.find? (·.name == tgt)
  let cutR ← RelCertifier.NonConn.cutOfAtoms vars n ((cutAtomsOfX cX.R src).map (·.atom))
  let (q1, q2) ← RelCertifier.NonConn.queries vars n cutR mR mSuc
  pure ⟨n, fun i => vars.getD i.val s!"pad{i.val}", q1, q2⟩

def runNonConnAllV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 non-connection : {prunedEdgesV2.length} pruned edge(s) =="
      let mut ok := true
      for (bench, src, tgt) in prunedEdgesV2 do
        match nonConnQueriesOfV2 (irV2 bench) (cutV2 bench) src tgt with
        | none =>
            IO.println s!"  FAIL  {bench} {src} -> {tgt}  (pruning queries did not rebuild)"
            ok := false
        | some ⟨_, coord, q1, q2⟩ =>
            for (tag, q) in [("source", q1), ("barrier", q2)] do
              match ← s.check (q.toScript coord) with
              | .ok .unsat =>
                  IO.println s!"  UNSAT [{tag}]  {bench} {src} -> {tgt}"
                  RelCertifier.Verdicts.counted
              | v =>
                  IO.println s!"  FAIL  {bench} {src} -> {tgt} [{tag}] → {reprStr (match v with | .ok r => reprStr r | .error e => e)}"
                  ok := false
      s.close
      pure ok

/-! ## The suite tally -/

/-- What a certification run over `benchmarks/suite_v2/*/input.txt` must produce, with
`RELCERT_IMPLIED_CUT=1` (the implied mode-fact candidates on): all 50 certified, 0 declined (in
the strict well-formedness mode of `--check-quick-v2`); and what the strict Assumption 1 gate of
the right models must produce (Appendix B.7): every one of the 181 right modes `ok` on both
clauses (`wfModes`), none `UNKNOWN` (`wfUnknown`), none `BLOCKING` (`wfBlocking`, the
nonblocking clause). -/
structure ExpectedSuiteV2 where
  paths     : Nat := 50
  certified : Nat := 50
  declined  : Nat := 0
  errors    : Nat := 0
  wfModes   : Nat := 181  -- right modes over the suite (Appendix B.7)
  wfUnknown : Nat := 0
  wfBlocking : Nat := 0
  deriving Repr

def expectedSuiteV2 : ExpectedSuiteV2 := {}

def checkSuiteV2 (nPaths certified declined errors : Nat) : IO Bool := do
  let e := expectedSuiteV2
  if nPaths != e.paths then
    IO.println s!"  [suite_v2] {certified} certified, {declined} declined, {errors} error(s) \
over {nPaths} path(s) — tally not enforced (the declared suite is {e.paths} paths)"
    return true
  else if certified == e.certified && declined == e.declined && errors == e.errors then
    IO.println s!"  [suite_v2] {certified} certified, {declined} declined, {errors} error(s) \
— matches the declared suite"
    return true
  else
    IO.eprintln s!"  [suite_v2] {certified} certified, {declined} declined, {errors} error(s) \
but the declared suite is {e.certified}/{e.declined}/{e.errors}"
    return false

end RelCertifier.VerdictsV2
