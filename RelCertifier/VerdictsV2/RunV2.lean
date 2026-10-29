/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 modal verdict runner

Walks `packsV2` — one row per verdict pack an instance of `InstancesV2/Modal/` assumes
(benchmark, dimension, invariant row, strata order, λ, left and right mode) — rebuilds the
pack's queries from the emitted IR (`benchIRTableV2`) and the emitted extended cut
certificate (`cutTableV2`) through `modalVerdXQueries` (the builder `modalVerdX_of_queries`
proves denotes the instance's hypothesis), prints them with the tool's own `toScript`, and
reports Z3's verdict per component. Each instance's `Verd` is pinned to its row in
`VerdictsV2/PinsV2.lean`; the total is declared (`expectedModalV2`) and derived from the
table in `VerdictsV2/CoveragePinsV2.lean`. Anything it cannot rebuild is a SKIP and makes
the run non-green.
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

/-- The hypothesis a pack row stands for (what the instances' `Verd`s are pinned to). -/
noncomputable def packVerd (r : PackV2) : Prop :=
  modalVerdX (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order ((packLam r : ℚ) : ℝ) r.l r.m

/-- The packs. Watertank: the seven admissible jointOK (window, right mode) pairs the replay
consumes, order `[0, 1]`. -/
def packsV2 : List PackV2 :=
  [ ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 0⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 1⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 2⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 1⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 2⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 3⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 3⟩,
    -- acc_spoof_limp (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 1, 0⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    -- platoon_linkloss (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"platoon_linkloss", 3, 0, [0, 1, 2, 3, 4, 5, 6, 7], 1, 1, 0, 0⟩,
    ⟨"platoon_linkloss", 3, 1, [0, 1, 2, 3, 4, 5, 6, 7], 1, 1, 1, 0⟩,
    -- at λ = 1 (budget 2 since batch I9: the 0.2 s link-loss decision)
    -- platoon_latency (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"platoon_latency", 3, 0, [8, 9, 0, 1, 2, 3, 4, 5, 7, 6], 1, 1, 0, 0⟩,
    ⟨"platoon_latency", 3, 1, [8, 9, 0, 1, 2, 3, 4, 5, 7, 6], 1, 1, 1, 0⟩,
    -- pruned): the CACC_UP/CACC_DN windows against CACC, AEB against AEB, at λ = 1, budget 1
    -- quad_light_lag
    ⟨"quad_light_lag", 3, 0, [2, 3, 0, 1], 6, 5, 0, 0⟩,
    -- acc_tune_lag (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"acc_tune_lag", 2, 0, [0, 1, 2, 3], 2, 1, 0, 0⟩,
    -- acc_spoof_lag (cover replay at λ = 3/2, budget 2: the dominant-mode claim, batch I9)
    ⟨"acc_spoof_lag", 2, 0, [1, 0], 3, 2, 0, 0⟩,
    -- rover_patrol_lag (cover replay; FAST at 11/8; the right-only nodes are below)
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 0, 0⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 0, 1⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 0, 2⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 0, 3⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 1, 1⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 1, 2⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 1, 3⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 2, 2⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 1, 1, 2, 3⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 11, 8, 3, 2⟩,
    ⟨"rover_patrol_lag", 3, 0, [1, 0], 11, 8, 3, 3⟩,
    -- rover_terrain_2to4 (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"rover_terrain_2to4", 4, 0, [0, 1, 2, 3], 1, 1, 0, 0⟩,
    ⟨"rover_terrain_2to4", 4, 0, [0, 1, 2, 3], 1, 1, 0, 1⟩,
    ⟨"rover_terrain_2to4", 4, 0, [0, 1, 2, 3], 1, 1, 0, 2⟩,
    ⟨"rover_terrain_2to4", 4, 0, [0, 1, 2, 3], 67, 50, 1, 1⟩,
    ⟨"rover_terrain_2to4", 4, 0, [0, 1, 2, 3], 67, 50, 1, 2⟩,
    ⟨"rover_terrain_2to4", 4, 0, [0, 1, 2, 3], 27, 10, 2, 2⟩,
    -- rover_terrain_4to6 (cover replay)
    ⟨"rover_terrain_4to6", 6, 0, [2, 3, 5, 6, 0, 1, 4, 7], 1, 1, 0, 0⟩,
    ⟨"rover_terrain_4to6", 6, 0, [2, 3, 5, 6, 4, 7, 0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_terrain_4to6", 6, 0, [2, 3, 5, 6, 4, 7, 0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_terrain_4to6", 6, 0, [2, 3, 5, 6, 0, 1, 4, 7], 1, 1, 1, 1⟩,
    ⟨"rover_terrain_4to6", 6, 0, [2, 3, 5, 6, 4, 7, 0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_terrain_4to6", 6, 0, [2, 3, 5, 6, 7, 0, 1, 4], 1, 1, 2, 2⟩,
    -- rover_terrain_6to12 (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"rover_terrain_6to12", 12, 0, [2, 3, 4, 6, 7, 0, 1, 5, 9, 8], 1, 1, 0, 0⟩,
    ⟨"rover_terrain_6to12", 12, 0, [2, 3, 4, 6, 7, 5, 9, 0, 1, 8], 1, 1, 0, 1⟩,
    ⟨"rover_terrain_6to12", 12, 0, [2, 3, 4, 6, 7, 5, 9, 0, 1, 8], 1, 1, 0, 2⟩,
    ⟨"rover_terrain_6to12", 12, 0, [2, 3, 4, 6, 7, 0, 1, 5, 9, 8], 1, 1, 1, 1⟩,
    ⟨"rover_terrain_6to12", 12, 0, [2, 3, 4, 6, 7, 5, 9, 0, 1, 8], 1, 1, 1, 2⟩,
    ⟨"rover_terrain_6to12", 12, 0, [2, 3, 4, 6, 7, 9, 0, 1, 5, 8], 1, 1, 2, 2⟩,
    -- rover_ladder_2to3 (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_ladder_2to3", 3, 0, [0, 1], 1, 1, 2, 2⟩,
    -- rover_ladder_6to8 (cover replay)
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7], 11, 10, 0, 0⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7], 11, 10, 0, 1⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7], 11, 10, 0, 2⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7], 11, 10, 1, 1⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7], 11, 10, 1, 2⟩,
    ⟨"rover_ladder_6to8", 8, 0, [0, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 2, 3, 6, 7], 11, 10, 2, 2⟩,
    -- rover_ladder_8to12 (cover replay)
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 25, 2, 3, 6, 7, 12, 13, 16, 17, 20, 21, 24, 1], 11, 10, 0, 0⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 24, 25, 2, 3, 6, 7, 12, 13, 16, 17, 20, 21, 1], 11, 10, 0, 1⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 24, 25, 2, 3, 6, 7, 12, 13, 16, 17, 20, 21, 1], 11, 10, 0, 2⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 18, 19, 22, 23, 24, 25, 2, 3, 6, 7, 14, 15, 16, 17, 20, 21, 1, 12, 13], 11, 10, 1, 1⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 18, 19, 22, 23, 24, 25, 2, 3, 6, 7, 14, 15, 16, 17, 20, 21, 1, 12, 13], 11, 10, 1, 2⟩,
    ⟨"rover_ladder_8to12", 12, 0, [0, 4, 5, 8, 9, 10, 11, 18, 19, 22, 23, 24, 25, 2, 3, 6, 7, 14, 15, 16, 17, 20, 21, 1, 12, 13], 11, 10, 2, 2⟩,
    -- rover_ladder_3to6 (cover replay)
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 0, 0⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 0, 1⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 0, 2⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 1, 1⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 1, 2⟩,
    ⟨"rover_ladder_3to6", 6, 0, [0, 2, 3, 4, 5, 1], 1, 1, 2, 2⟩,
    -- gantry_speed_zones (cover replay): each speed zone against MOVE at its override, λ = 3, 2, 1
    ⟨"gantry_speed_zones", 2, 0, [0, 1, 2, 3], 3, 1, 0, 0⟩,
    ⟨"gantry_speed_zones", 2, 0, [0, 1, 2, 3], 2, 1, 1, 0⟩,
    ⟨"gantry_speed_zones", 2, 0, [0, 1, 2, 3], 1, 1, 2, 0⟩,
    -- (the staging chain P2 -> P3 -> P4 -> P5) at λ = 1
    -- watertank_twospeed (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 2, 1, 0, 1⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 3, 2, 0, 2⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 0, 3⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 0, 4⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 2, 1, 1, 2⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 2, 1, 1, 3⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 2, 1, 1, 4⟩,
    ⟨"watertank_twospeed", 2, 0, [0, 1], 1, 1, 2, 4⟩,
    -- MidEco 3/2, MidBoost 1, High 1), Mid at 2 against MidEco/MidBoost/High, High at 1
    -- engine_start_highidle (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
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
    -- turbine_startup_gearratio (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"turbine_startup_gearratio", 3, 0, [0], 1, 1, 0, 0⟩,
    ⟨"turbine_startup_gearratio", 3, 0, [0], 1, 1, 0, 2⟩,
    ⟨"turbine_startup_gearratio", 3, 1, [0], 1, 1, 1, 1⟩,
    ⟨"turbine_startup_gearratio", 3, 1, [0], 1, 1, 1, 2⟩,
    ⟨"turbine_startup_gearratio", 3, 2, [0], 1, 1, 2, 2⟩,
    ⟨"turbine_startup_gearratio", 3, 3, [0], 1, 1, 3, 0⟩,
    ⟨"turbine_startup_gearratio", 3, 3, [0], 1, 1, 3, 1⟩,
    ⟨"turbine_startup_gearratio", 3, 3, [0], 1, 1, 3, 2⟩,
    ⟨"turbine_startup_gearratio", 3, 3, [0], 1, 1, 3, 3⟩,
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
    -- ventilator_vc_cuffleak (mode-keyed rows; cover replay at λ = 1)
    ⟨"ventilator_vc_cuffleak", 3, 0, [0, 1, 2, 3], 1, 1, 0, 0⟩,
    ⟨"ventilator_vc_cuffleak", 3, 1, [0, 1, 2, 3], 1, 1, 1, 1⟩,
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
    -- lit_nahs25_salt_tank (cover replay at λ = 1, budget 1; dimension 3, the Assumption 1 lemma's)
    ⟨"lit_nahs25_salt_tank", 3, 0, [0, 1, 2, 3], 1, 1, 0, 0⟩,
    ⟨"lit_nahs25_salt_tank", 3, 0, [1, 2, 3, 0], 1, 1, 0, 1⟩,
    ⟨"lit_nahs25_salt_tank", 3, 0, [0, 1, 2, 3], 1, 1, 1, 0⟩,
    ⟨"lit_nahs25_salt_tank", 3, 0, [0, 1, 2, 3], 1, 1, 1, 1⟩,
    -- bottling_fill_strainer (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"bottling_fill_strainer", 2, 0, [0, 1, 2, 3], 17, 20, 0, 0⟩,
    ⟨"bottling_fill_strainer", 2, 0, [0, 1, 2, 3], 1, 1, 1, 1⟩,
    -- charger_fast_tapers (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"charger_fast_tapers", 3, 0, [0], 5, 4, 0, 0⟩,
    ⟨"charger_fast_tapers", 3, 0, [0], 5, 4, 0, 1⟩,
    ⟨"charger_fast_tapers", 3, 0, [0], 5, 4, 0, 2⟩,
    ⟨"charger_fast_tapers", 3, 0, [0], 5, 4, 0, 3⟩,
    ⟨"charger_fast_tapers", 3, 0, [0], 5, 4, 0, 4⟩,
    ⟨"charger_fast_tapers", 3, 1, [0], 5, 4, 1, 1⟩,
    ⟨"charger_fast_tapers", 3, 1, [0], 5, 4, 1, 4⟩,
    ⟨"charger_fast_tapers", 3, 2, [0], 5, 4, 2, 1⟩,
    ⟨"charger_fast_tapers", 3, 2, [0], 5, 4, 2, 2⟩,
    ⟨"charger_fast_tapers", 3, 2, [0], 5, 4, 2, 3⟩,
    ⟨"charger_fast_tapers", 3, 2, [0], 5, 4, 2, 4⟩,
    ⟨"charger_fast_tapers", 3, 3, [0], 5, 4, 3, 2⟩,
    ⟨"charger_fast_tapers", 3, 3, [0], 5, 4, 3, 3⟩,
    ⟨"charger_fast_tapers", 3, 3, [0], 5, 4, 3, 4⟩,
    -- since 2026-10-28; the joint pairings of each window's admissible starts, the right-only
    -- nodes are below)
    -- flaps_slow_approach (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"flaps_slow_approach", 2, 0, [0, 1, 2, 3], 1, 2, 0, 0⟩,
    ⟨"flaps_slow_approach", 2, 0, [0, 1, 2, 3], 1, 1, 1, 1⟩,
    -- platoon_profiles (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"platoon_profiles", 3, 0, [2, 3, 4, 5, 6, 7, 0, 1], 6, 5, 0, 0⟩,
    -- h2_refuel_ambientbias (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
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
    ⟨"h2_refuel_ambientbias", 3, 3, [0], 1, 1, 3, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 3, [0], 1, 1, 3, 4⟩,
    ⟨"h2_refuel_ambientbias", 3, 4, [0], 1, 1, 4, 3⟩,
    ⟨"h2_refuel_ambientbias", 3, 4, [0], 1, 1, 4, 4⟩,
    -- reactor_feed_wireless (batch I11, from the reserve; cover replay at λ = 1, budget 2; the
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
    -- antenna_track_kvretune (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"antenna_track_kvretune", 3, 0, [0, 1, 2, 3, 6, 7, 4, 5], 1, 1, 0, 0⟩,
    ⟨"antenna_track_kvretune", 3, 1, [0, 1, 2, 3, 6, 7, 4, 5], 1, 1, 1, 1⟩,
    ⟨"antenna_track_kvretune", 3, 2, [0, 1, 2, 3, 6, 7, 4, 5], 1, 1, 2, 2⟩,
    -- canal_gate_notches (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"canal_gate_notches", 3, 0, [0, 1], 1, 1, 2, 3⟩,
    -- rampmeter_poll_2to1 (rows derived from the emitted cover, 2026-10-29: the joint pairings reached in each window)
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
    -- lit_csf25_salt_tank_hold (rows derived from the emitted cover, 2026-10-29: one held window, keyed rows)
    ⟨"lit_csf25_salt_tank_hold", 3, 0, [0, 2, 1], 1, 3, 0, 0⟩,
    ⟨"lit_csf25_salt_tank_hold", 3, 1, [0, 2, 1], 1, 3, 1, 1⟩ ]

/-- Declared: the number of component queries the packs owe (one per component). -/
def expectedModalV2 : Nat := 1160

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

/-! ## The reposition packs (Lemma 4's flow certificates) of the cover replays

One row per dynamic-reposition pack a replaying instance assumes: the reposition of right
mode `m` against left window `l`, before the window's first joint segment (`pre = true`: the
left guard conjoined) or after it, the invariant row's components in the cover's reposition
strata order (`dynPreOrder` / `dynPostOrder` of the emitted cover). The runner rebuilds each
pack with `modalVerdDynXQueries` (the builder `modalVerdDynX_of_queries` proves denotes the
instance's hypothesis), prints it with `toScript`, and owes one `unsat` per component. -/

structure DynPackV2 where
  bench  : String
  dim    : ℕ
  invRow : ℕ := 0
  order  : List ℕ
  pre    : Bool := true
  l      : ℕ
  m      : ℕ
  deriving Repr, Inhabited

def dynPackQueries (r : DynPackV2) : Option (List (IForm r.dim)) :=
  modalVerdDynXQueries (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order r.pre r.l r.m

noncomputable def dynPackVerd (r : DynPackV2) : Prop :=
  modalVerdDynX (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order r.pre r.l r.m

/-- The reposition packs. -/
def dynPacksV2 : List DynPackV2 :=
  [ -- rover_terrain_4to6
    -- rover_patrol_lag: MEDIUM_ECO_L and MEDIUM_BRISK_L reposition through right-only SLOW,
    -- MEDIUM_BRISK_L and FAST_L through right-only MEDIUM_ECO
    ⟨"rover_patrol_lag", 3, 0, [0, 1], true, 1, 0⟩,
    ⟨"rover_patrol_lag", 3, 0, [0, 1], true, 2, 0⟩,
    ⟨"rover_patrol_lag", 3, 0, [0, 1], true, 2, 1⟩,
    ⟨"rover_patrol_lag", 3, 0, [0, 1], true, 3, 1⟩,
    -- engine_start_highidle: right-only reposition nodes of the emitted cover (2026-10-29)
    ⟨"engine_start_highidle", 3, 3, [0], true, 3, 2⟩,
    ⟨"engine_start_highidle", 3, 4, [0], true, 4, 3⟩,
    -- h2_refuel_ambientbias: right-only reposition nodes of the emitted cover (2026-10-29)
    ⟨"h2_refuel_ambientbias", 3, 3, [0], true, 3, 2⟩,
    -- turbine_startup_gearratio: right-only reposition nodes of the emitted cover (2026-10-29)
    ⟨"turbine_startup_gearratio", 3, 0, [0], true, 0, 1⟩,
    ⟨"turbine_startup_gearratio", 3, 2, [0], true, 2, 1⟩,
    -- elevator_start_discbrake: right-only reposition nodes
    ⟨"elevator_start_discbrake", 3, 1, [0, 1, 2, 3], true, 1, 0⟩,
    -- syringe_relay_prearm: right-only reposition nodes
    ⟨"syringe_relay_prearm", 4, 0, [0, 1, 2, 3, 4, 5, 6], true, 0, 1⟩,
    ⟨"syringe_relay_prearm", 4, 0, [0, 1, 2, 3, 4, 5, 6], true, 0, 2⟩,
    ⟨"syringe_relay_prearm", 4, 1, [0, 1, 2, 3, 4, 5, 6], true, 1, 1⟩,
    ⟨"syringe_relay_prearm", 4, 1, [0, 1, 2, 3, 4, 5, 6], true, 1, 2⟩,
    ⟨"syringe_relay_prearm", 4, 2, [0, 1, 2, 3, 4, 5, 6], true, 2, 1⟩,
    ⟨"syringe_relay_prearm", 4, 2, [0, 1, 2, 3, 4, 5, 6], true, 2, 2⟩,
    ⟨"syringe_relay_prearm", 4, 3, [0, 1, 2, 4, 6, 3, 5], true, 3, 2⟩,
    ⟨"syringe_relay_prearm", 4, 4, [0, 1, 2, 3, 4], true, 4, 1⟩,
    -- charger_fast_tapers: right-only reposition nodes of the emitted cover (2026-10-29)
    ⟨"charger_fast_tapers", 3, 1, [0], true, 1, 0⟩,
    ⟨"charger_fast_tapers", 3, 1, [0], true, 1, 2⟩,
    ⟨"charger_fast_tapers", 3, 1, [0], true, 1, 3⟩ ]

/-- Declared: the number of component queries the reposition packs owe. -/
def expectedDynV2 : Nat := 74

def runDynPack (s : Z3Session) (r : DynPackV2) : IO Bool := do
  let p := irV2 r.bench
  let vars := p.L.stateVars
  let coord := fun (i : Fin r.dim) => vars.getD i.val s!"pad{i.val}"
  match dynPackQueries r with
  | none =>
      IO.println s!"  SKIP  {r.bench} (l={r.l},m={r.m},pre={r.pre})  (rebuild failed)"
      pure false
  | some qs =>
      if qs.isEmpty then
        IO.println s!"  SKIP  {r.bench} (l={r.l},m={r.m},pre={r.pre})  (no component)"
        return false
      let mut ok := true
      for i in List.range qs.length do
        let q := qs.getD i IForm.tt
        match ← s.check (q.toScript coord) with
        | .ok .unsat =>
            IO.println s!"  UNSAT (A=unsat)  {r.bench} (l={r.l},m={r.m},pre={r.pre}) comp={i}"
            RelCertifier.Verdicts.counted
        | .ok v =>
            IO.println s!"  FAIL  {r.bench} (l={r.l},m={r.m},pre={r.pre}) comp={i} : A={reprStr v}"
            ok := false
        | .error e =>
            IO.println s!"  FAIL  {r.bench} (l={r.l},m={r.m},pre={r.pre}) comp={i} : A=err({e})"
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

/-- Declared: one handoff query per declared left transition over the suite_v2 files
(self-loops included; `CoveragePinsV2.derivedHandoffV2_eq` derives it from the IR table; 537 until
the literature migration of 2026-10-29, 2827 since: the 48 abstraction modes of
`lit_gpt10_boost_converter`, every one a successor of every other, alone declare 2256
transitions, all vacuous as its rows are identical). -/
def expectedHandoffV2 : Nat := 2827

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
the source mode's cut rebuilt from the EXTENDED certificate, as the tool narrows it) -/

def prunedEdgesV2 : List (String × String × String) :=
  coverTableV2.flatMap (fun c => c.2.pruned.map (fun e => (c.1, e.1, e.2)))

/-- Declared: pruned edges in the suite_v2 covers, and two queries per edge. -/
def expectedPrunedEdgesV2 : Nat := 22
def expectedNonConnV2 : Nat := 44

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
`RELCERT_IMPLIED_CUT=1`: all 49 certified (in the strict well-formedness mode of
`--check-quick-v2`); and what the strict Assumption 1 check of the right models must produce:
every one of the 179 right modes `ok` on both clauses (`wfModes`; the kernel pin
`CoveragePinsV2.suiteV2_wfModes` of that count was archived with the standalone route), none
`UNKNOWN` (`wfUnknown`; 16 UNKNOWN in 9 benchmarks until the 2026-10-10 repairs, when the
check was informational), none `BLOCKING` (`wfBlocking`; the nonblocking clause is checked
since 2026-10-26). -/
structure ExpectedSuiteV2 where
  paths     : Nat := 50
  certified : Nat := 50
  declined  : Nat := 0
  errors    : Nat := 0
  wfModes   : Nat := 181
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
