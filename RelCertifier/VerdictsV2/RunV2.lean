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
import RelCertifier.Verdicts.RunModal
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

/-- The packs. Watertank: eleven (window, right mode) pairs, order `[0, 1]`. -/
def packsV2 : List PackV2 :=
  [ ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 0⟩, ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 1⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 2⟩, ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 3⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 1⟩, ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 2⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 3⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 0⟩, ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 1⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 2⟩, ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 3⟩,
    -- platoon_delay_profiles: two windows (rows 0, 1), right FOLLOW/GENTLE/ASSERTIVE, λ = 1
    ⟨"platoon_delay_profiles", 2, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"platoon_delay_profiles", 2, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"platoon_delay_profiles", 2, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"platoon_delay_profiles", 2, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"platoon_delay_profiles", 2, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"platoon_delay_profiles", 2, 1, [0, 1], 1, 1, 1, 2⟩,
    -- acc_spoof_limp
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 5, 4, 0, 0⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 5, 4, 0, 1⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 5, 4, 0, 2⟩,
    ⟨"acc_spoof_limp", 3, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"acc_spoof_limp", 3, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"acc_spoof_limp", 3, 1, [0, 1], 1, 1, 1, 2⟩,
    -- acc_tune_limp
    ⟨"acc_tune_limp", 3, 0, [0, 1], 3, 2, 0, 0⟩,
    ⟨"acc_tune_limp", 3, 0, [0, 1], 3, 2, 0, 1⟩,
    ⟨"acc_tune_limp", 3, 0, [0, 1], 3, 2, 0, 2⟩,
    ⟨"acc_tune_limp", 3, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"acc_tune_limp", 3, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"acc_tune_limp", 3, 1, [0, 1], 1, 1, 1, 2⟩,
    -- platoon_delay_linkloss
    ⟨"platoon_delay_linkloss", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"platoon_delay_linkloss", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"platoon_delay_linkloss", 3, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"platoon_delay_linkloss", 3, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"platoon_delay_linkloss", 3, 2, [0, 1], 1, 1, 2, 0⟩,
    ⟨"platoon_delay_linkloss", 3, 2, [0, 1], 1, 1, 2, 1⟩,
    -- quad_light_airframe_20
    ⟨"quad_light_airframe_20", 2, 0, [0, 1], 7, 4, 0, 0⟩,
    -- quad_light_profiles
    ⟨"quad_light_profiles", 2, 0, [0, 1], 5, 2, 0, 0⟩,
    ⟨"quad_light_profiles", 2, 0, [0, 1], 5, 2, 0, 1⟩,
    ⟨"quad_light_profiles", 2, 0, [0, 1], 5, 2, 0, 2⟩,
    -- quad_light_lag
    ⟨"quad_light_lag", 2, 0, [0], 7, 4, 0, 0⟩,
    -- charger_fast_setpoints
    ⟨"charger_fast_setpoints", 2, 0, [0], 1, 1, 0, 1⟩,
    ⟨"charger_fast_setpoints", 2, 0, [0], 1, 1, 0, 2⟩,
    ⟨"charger_fast_setpoints", 2, 1, [0], 1, 1, 1, 1⟩,
    ⟨"charger_fast_setpoints", 2, 1, [0], 1, 1, 1, 2⟩,
    ⟨"charger_fast_setpoints", 2, 2, [0], 1, 1, 2, 0⟩,
    ⟨"charger_fast_setpoints", 2, 2, [0], 1, 1, 2, 1⟩,
    ⟨"charger_fast_setpoints", 2, 2, [0], 1, 1, 2, 2⟩,
    -- acc_tune_lag
    ⟨"acc_tune_lag", 2, 0, [0], 5, 4, 0, 0⟩,
    -- acc_spoof_lag
    ⟨"acc_spoof_lag", 2, 0, [0], 5, 2, 0, 0⟩,
    -- charger_fast_tapers
    ⟨"charger_fast_tapers", 2, 0, [0], 1, 1, 0, 3⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 0⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 1⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 2⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 3⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 0⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 1⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 2⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 3⟩,
    -- story3_rollover_ladder_rung_b
    ⟨"story3_rollover_ladder_rung_b", 12, 0, [0, 1, 2], 1, 1, 0, 0⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 0, [0, 1, 2], 1, 1, 0, 1⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 0, [0, 1, 2], 1, 1, 0, 2⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 1, [0, 1], 1, 1, 1, 2⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 2, [0, 1], 1, 1, 2, 0⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 2, [0, 1], 1, 1, 2, 1⟩,
    ⟨"story3_rollover_ladder_rung_b", 12, 2, [0, 1], 1, 1, 2, 2⟩,
    -- sat_detumble_nominal
    ⟨"sat_detumble_nominal", 4, 0, [0, 1], 1, 1, 0, 0⟩,
    -- platoon3_profiles
    ⟨"platoon3_profiles", 6, 0, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], 1, 1, 0, 0⟩,
    ⟨"platoon3_profiles", 6, 0, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], 1, 1, 0, 1⟩,
    ⟨"platoon3_profiles", 6, 0, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], 1, 1, 0, 2⟩,
    -- platoon3_linkloss
    ⟨"platoon3_linkloss", 6, 0, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 1, 1, 0, 0⟩,
    ⟨"platoon3_linkloss", 6, 1, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], 1, 1, 1, 0⟩,
    -- sat_detumble_weak
    ⟨"sat_detumble_weak", 4, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"sat_detumble_weak", 4, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"sat_detumble_weak", 4, 0, [0, 1], 1, 1, 0, 2⟩,
    -- sat3w_detumble_nominal
    ⟨"sat3w_detumble_nominal", 6, 0, [0, 1], 1, 1, 0, 0⟩,
    -- sat3w_detumble_weak
    ⟨"sat3w_detumble_weak", 6, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"sat3w_detumble_weak", 6, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"sat3w_detumble_weak", 6, 0, [0, 1], 1, 1, 0, 2⟩,
    -- sat_detumble_phases
    ⟨"sat_detumble_phases", 4, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"sat_detumble_phases", 4, 1, [0, 1], 1, 1, 1, 0⟩,
    -- sat3w_detumble_phases
    ⟨"sat3w_detumble_phases", 6, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"sat3w_detumble_phases", 6, 1, [0, 1], 1, 1, 1, 0⟩,
    -- rover_patrol_zones
    ⟨"rover_patrol_zones", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"rover_patrol_zones", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_patrol_zones", 3, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_patrol_zones", 3, 0, [0, 1], 1, 1, 0, 3⟩,
    ⟨"rover_patrol_zones", 3, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"rover_patrol_zones", 3, 1, [0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_patrol_zones", 3, 1, [0, 1], 1, 1, 1, 3⟩,
    ⟨"rover_patrol_zones", 3, 2, [0, 1], 1, 1, 2, 2⟩,
    ⟨"rover_patrol_zones", 3, 2, [0, 1], 1, 1, 2, 3⟩,
    ⟨"rover_patrol_zones", 3, 3, [0, 1], 1, 1, 3, 3⟩,
    -- rover_patrol_refine
    ⟨"rover_patrol_refine", 3, 0, [0, 1], 9, 4, 0, 0⟩,
    ⟨"rover_patrol_refine", 3, 0, [0, 1], 9, 4, 0, 1⟩,
    ⟨"rover_patrol_refine", 3, 0, [0, 1], 9, 4, 0, 2⟩,
    ⟨"rover_patrol_refine", 3, 0, [0, 1], 9, 4, 0, 3⟩,
    ⟨"rover_patrol_refine", 3, 1, [0, 1], 9, 4, 1, 1⟩,
    ⟨"rover_patrol_refine", 3, 1, [0, 1], 9, 4, 1, 2⟩,
    ⟨"rover_patrol_refine", 3, 1, [0, 1], 9, 4, 1, 3⟩,
    ⟨"rover_patrol_refine", 3, 2, [0, 1], 9, 4, 2, 2⟩,
    ⟨"rover_patrol_refine", 3, 2, [0, 1], 9, 4, 2, 3⟩,
    ⟨"rover_patrol_refine", 3, 3, [0, 1], 9, 4, 3, 3⟩,
    -- rover_dof_terrain_rung1 (cover replay): the joint nodes of each window, λ = 1
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], 1, 1, 2, 2⟩,
    -- rover_dof_terrain_rung2 (cover replay)
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], 1, 1, 2, 2⟩,
    -- rover_dof_terrain_rung3 (cover replay)
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], 1, 1, 2, 2⟩,
    -- rover_dof_terrain_rung3_8d (cover replay)
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], 1, 1, 2, 2⟩,
    -- refinement_ladder_rover_rung1_2to3 (cover replay)
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], 1, 1, 1, 1⟩,
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], 1, 1, 1, 2⟩,
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], 1, 1, 2, 2⟩,
    -- refinement_ladder_rover_rung3_6to8 (cover replay)
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], 9, 4, 0, 0⟩,
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], 9, 4, 0, 1⟩,
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], 9, 4, 0, 2⟩,
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], 9, 4, 1, 1⟩,
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], 9, 4, 1, 2⟩,
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], 9, 4, 2, 2⟩,
    -- refinement_ladder_rover_rung4_8to12 (cover replay)
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], 17, 10, 0, 0⟩,
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], 17, 10, 0, 1⟩,
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], 17, 10, 0, 2⟩,
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], 17, 10, 1, 1⟩,
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], 17, 10, 1, 2⟩,
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], 17, 10, 2, 2⟩,
    -- story3_rollover_base_12dof (cover replay)
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], 5, 4, 0, 0⟩,
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], 5, 4, 0, 1⟩,
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], 5, 4, 0, 2⟩,
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], 5, 4, 1, 1⟩,
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], 5, 4, 1, 2⟩,
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], 5, 4, 2, 2⟩,
    -- story3_rollover_ladder_rung_a (cover replay)
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], 27, 20, 0, 0⟩,
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], 27, 20, 0, 1⟩,
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], 27, 20, 0, 2⟩,
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], 27, 20, 1, 1⟩,
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], 27, 20, 1, 2⟩,
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], 27, 20, 2, 2⟩,
    -- refinement_ladder_rover_rung2_6dof (cover replay)
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], 1001, 1000, 0, 0⟩,
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], 1001, 1000, 0, 1⟩,
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], 1001, 1000, 0, 2⟩,
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], 1001, 1000, 1, 1⟩,
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], 1001, 1000, 1, 2⟩,
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], 1001, 1000, 2, 2⟩,
    -- refinement_ladder_rover_rung2b_6dof (cover replay)
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], 1001, 1000, 0, 0⟩,
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], 1001, 1000, 0, 1⟩,
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], 1001, 1000, 0, 2⟩,
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], 1001, 1000, 1, 1⟩,
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], 1001, 1000, 1, 2⟩,
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], 1001, 1000, 2, 2⟩,
    -- refinement_ladder_rover_rung2_3to6 (cover replay)
    ⟨"refinement_ladder_rover_rung2_3to6", 6, 0, [0, 2, 3, 1], 1, 1, 0, 0⟩,
    ⟨"refinement_ladder_rover_rung2_3to6", 6, 0, [0, 2, 3, 1], 1, 1, 0, 1⟩,
    ⟨"refinement_ladder_rover_rung2_3to6", 6, 0, [0, 2, 3, 1], 1, 1, 0, 2⟩,
    ⟨"refinement_ladder_rover_rung2_3to6", 6, 0, [0, 2, 3, 1], 1, 1, 1, 1⟩,
    ⟨"refinement_ladder_rover_rung2_3to6", 6, 0, [0, 2, 3, 1], 1, 1, 1, 2⟩,
    ⟨"refinement_ladder_rover_rung2_3to6", 6, 0, [0, 2, 3, 1], 1, 1, 2, 2⟩,
    -- story2_lateral_rung_a_8dof (cover replay)
    ⟨"story2_lateral_rung_a_8dof", 8, 0, [0, 1, 3, 4, 5, 6, 2], 1, 1, 0, 0⟩,
    ⟨"story2_lateral_rung_a_8dof", 8, 0, [0, 1, 3, 4, 5, 6, 2], 1, 1, 0, 1⟩,
    ⟨"story2_lateral_rung_a_8dof", 8, 0, [0, 1, 3, 4, 5, 6, 2], 1, 1, 0, 2⟩,
    ⟨"story2_lateral_rung_a_8dof", 8, 0, [0, 1, 3, 4, 5, 6, 2], 1, 1, 1, 1⟩,
    ⟨"story2_lateral_rung_a_8dof", 8, 0, [0, 1, 3, 4, 5, 6, 2], 1, 1, 1, 2⟩,
    ⟨"story2_lateral_rung_a_8dof", 8, 0, [0, 1, 3, 4, 5, 6, 2], 1, 1, 2, 2⟩,
    -- story2_lateral_rung_b_12dof (cover replay)
    ⟨"story2_lateral_rung_b_12dof", 12, 0, [0, 1, 2, 4, 5, 6, 7, 3], 1, 1, 0, 0⟩,
    ⟨"story2_lateral_rung_b_12dof", 12, 0, [0, 1, 2, 4, 5, 6, 7, 3], 1, 1, 0, 1⟩,
    ⟨"story2_lateral_rung_b_12dof", 12, 0, [0, 1, 2, 4, 5, 6, 7, 3], 1, 1, 0, 2⟩,
    ⟨"story2_lateral_rung_b_12dof", 12, 0, [0, 1, 2, 4, 5, 6, 7, 3], 1, 1, 1, 1⟩,
    ⟨"story2_lateral_rung_b_12dof", 12, 0, [0, 1, 2, 4, 5, 6, 7, 3], 1, 1, 1, 2⟩,
    ⟨"story2_lateral_rung_b_12dof", 12, 0, [0, 1, 2, 4, 5, 6, 7, 3], 1, 1, 2, 2⟩,
    -- story1_attdist_rung_a_6to8 (cover replay)
    ⟨"story1_attdist_rung_a_6to8", 8, 0, [0, 1, 2], 1, 1, 0, 0⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 0, [0, 1, 2], 1, 1, 0, 1⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 0, [0, 1, 2], 1, 1, 0, 2⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 1, [0, 1], 1, 1, 1, 2⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 2, [0, 1], 1, 1, 2, 0⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 2, [0, 1], 1, 1, 2, 1⟩,
    ⟨"story1_attdist_rung_a_6to8", 8, 2, [0, 1], 1, 1, 2, 2⟩,
    -- story1_attdist_rung_b_12dof (cover replay)
    ⟨"story1_attdist_rung_b_12dof", 12, 0, [0, 1, 2], 1, 1, 0, 0⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 0, [0, 1, 2], 1, 1, 0, 1⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 0, [0, 1, 2], 1, 1, 0, 2⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 1, [0, 1], 1, 1, 1, 2⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 2, [0, 1], 1, 1, 2, 0⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 2, [0, 1], 1, 1, 2, 1⟩,
    ⟨"story1_attdist_rung_b_12dof", 12, 2, [0, 1], 1, 1, 2, 2⟩ ]

/-- Declared: the number of component queries the packs owe (one per component). -/
def expectedModalV2 : Nat := 574

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

/-! ## The reposition packs (certificate 3) of the cover replays

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
  [ -- rover_dof_terrain_rung1: MODER window from STEEP, FLAT window from MODER
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], true, 1, 0⟩,
    ⟨"rover_dof_terrain_rung1", 3, 0, [0, 1], true, 2, 1⟩,
    -- rover_dof_terrain_rung2
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], true, 1, 0⟩,
    ⟨"rover_dof_terrain_rung2", 6, 0, [0, 1], true, 2, 1⟩,
    -- rover_dof_terrain_rung3
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], true, 1, 0⟩,
    ⟨"rover_dof_terrain_rung3", 12, 0, [0, 1], true, 2, 1⟩,
    -- rover_dof_terrain_rung3_8d
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], true, 1, 0⟩,
    ⟨"rover_dof_terrain_rung3_8d", 8, 0, [0, 1], true, 2, 1⟩,
    -- refinement_ladder_rover_rung1_2to3
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], true, 1, 0⟩,
    ⟨"refinement_ladder_rover_rung1_2to3", 3, 0, [0, 1], true, 2, 1⟩,
    -- refinement_ladder_rover_rung3_6to8
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], true, 1, 0⟩,
    ⟨"refinement_ladder_rover_rung3_6to8", 8, 0, [0, 1, 2, 3], true, 2, 1⟩,
    -- refinement_ladder_rover_rung4_8to12
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], true, 1, 0⟩,
    ⟨"refinement_ladder_rover_rung4_8to12", 12, 0, [0, 1], true, 2, 1⟩,
    -- story3_rollover_base_12dof
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], true, 1, 0⟩,
    ⟨"story3_rollover_base_12dof", 12, 0, [0, 1, 2, 3, 4], true, 2, 1⟩,
    -- story3_rollover_ladder_rung_a
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], true, 1, 0⟩,
    ⟨"story3_rollover_ladder_rung_a", 12, 0, [0, 1, 2], true, 2, 1⟩,
    -- refinement_ladder_rover_rung2_6dof
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], true, 1, 0⟩,
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], true, 2, 0⟩,
    ⟨"refinement_ladder_rover_rung2_6dof", 4, 0, [0], true, 2, 1⟩,
    -- refinement_ladder_rover_rung2b_6dof
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], true, 1, 0⟩,
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], true, 2, 0⟩,
    ⟨"refinement_ladder_rover_rung2b_6dof", 6, 0, [0], true, 2, 1⟩ ]

/-- Declared: the number of component queries the reposition packs owe. -/
def expectedDynV2 : Nat := 54

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

/-- Declared: one handoff query per declared left transition over the 45 suite_v2 files
(self-loops included; `CoveragePinsV2.derivedHandoffV2_eq` derives it from the IR table). -/
def expectedHandoffV2 : Nat := 186

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
def expectedPrunedEdgesV2 : Nat := 44
def expectedNonConnV2 : Nat := 88

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
`RELCERT_IMPLIED_CUT=1`: all 45 certified (in the strict well-formedness mode of
`--check-quick-v2`); and what the strict Assumption 1 check of the right models must produce:
every one of the 146 right modes `ok` (`wfModes`, kernel-checked against the IR table by
`CoveragePinsV2.suiteV2_wfModes`), none `UNKNOWN` (`wfUnknown`; 16 UNKNOWN in 9 benchmarks
until the 2026-10-10 repairs, when the check was informational). -/
structure ExpectedSuiteV2 where
  paths     : Nat := 45
  certified : Nat := 45
  declined  : Nat := 0
  errors    : Nat := 0
  wfModes   : Nat := 146
  wfUnknown : Nat := 0
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

/-! ## The 19 carried-over benchmarks: their legacy modal packs

Their suite_v2 files are byte-identical copies of files of the retired legacy suite, and
their suite_v2 literal IS the literal the legacy theorems quote (`InstancesV2/SameIR.lean`,
`rfl`), so the legacy theorems (`Instances/`) and their verdict packs (the rows of
`Verdicts/RunModal.modalTable`, pinned by `Verdicts/ModalPinTable`, `ModalTablePins`,
`ModalCodePins`) are about the suite_v2 files. `modalTable` holds exactly the rows of these
benchmarks: 22 rows over the 17 that carry packs (`refinement_ladder_rover_rung2_6dof` and
`rung2b_6dof` are Z3-free); `rover3tier_rung12` has two per-left-mode packs, and the
mode-keyed `story1_attdist_rung_a` / `_rung_b` add one and three packs to their base pack.
This phase re-runs them all, so
`--run-verdicts-v2` alone discharges every hypothesis of the suite_v2 battery (the one
non-connection hypothesis among them, `match_multi_rate_nonconn`'s `VerdNC`, is discharged
by the non-connection phase above: `VerdictsV2/NonConnPinV2`). -/

def sameBenchV2 : List String :=
  ["match_multi_rate", "refinement_ladder_rover_rung1_2to3",
   "refinement_ladder_rover_rung2_3to6", "refinement_ladder_rover_rung2_6dof",
   "refinement_ladder_rover_rung2b_6dof", "refinement_ladder_rover_rung2c_6dof",
   "refinement_ladder_rover_rung3_6to8", "refinement_ladder_rover_rung4_8to12",
   "rover3tier_rung12", "rover_dof_terrain_rung1", "rover_dof_terrain_rung2",
   "rover_dof_terrain_rung3", "rover_dof_terrain_rung3_8d",
   "story1_attdist_rung_a_6to8", "story1_attdist_rung_b_12dof",
   "story2_lateral_rung_a_8dof", "story2_lateral_rung_b_12dof",
   "story3_rollover_base_12dof", "story3_rollover_ladder_rung_a"]

def sameModalTable : List (RelCertifier.ModalSpecs.VerdSpec × RelCertifier.Verdicts.RunInfo × List ℕ) :=
  RelCertifier.Verdicts.modalTable.filter (fun r => sameBenchV2.contains r.1.bench)

/-- Declared: the legacy modal queries of the 19 carried-over benchmarks
(`CoveragePinsV2.derivedSameModalV2_eq` derives it from `modalTable`). -/
def expectedSameModalV2 : Nat := 385

def runSameModalV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 copied benchmarks : {sameModalTable.length} legacy verdict packs =="
      let mut ok := true
      for (spec, info, order) in sameModalTable do
        ok := (← RelCertifier.Verdicts.runSpec s spec info order) && ok
      s.close
      pure ok

end RelCertifier.VerdictsV2
