/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Kernel replays of the suite_v2 covers (GENERATED — `scripts/gen_v2_data.py`)

Per benchmark, for every emitted left-mode cover and every admissible start, the verified
`decideCovered`, run on the same structural graph the tool built (`buildCoverGraph` over
the emitted flags, successors and pruned edges, same fuel, same budget, σ = preJ), accepts,
by kernel computation (`decide`). This replays the tool's CERTIFIED gate inside the kernel:
three standard axioms, no Z3, no IO.
-/
import RelCertifier.Checker.Checker
import RelCertifier.Trusted.Run
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.BenchCovers

namespace RelCertifier

/-- The replay predicate: every window, every admissible start, the checker accepts. -/
def coverReplays (p : Parse.PProblem) (c : CoverEmitE) : Bool :=
  c.covers.all (fun lc =>
    lc.admissible.all (fun q0 =>
      decideCovered (V := Var 1)
        (buildCoverGraph lc.flags (Run.succOf p)
          (fun a b => c.pruned.contains (a, b)))
        (coverFuel lc.flags lc.bBudget)
        ⟨nodeIdx lc.flags q0, lc.bBudget, SrcSetting.preJ⟩))

theorem acc_spoof_lag_coverV2_replay : coverReplays Parse.acc_spoof_lag_IRv2 acc_spoof_lag_coverV2 = true := by decide

theorem acc_spoof_limp_coverV2_replay : coverReplays Parse.acc_spoof_limp_IRv2 acc_spoof_limp_coverV2 = true := by decide

theorem acc_tune_lag_coverV2_replay : coverReplays Parse.acc_tune_lag_IRv2 acc_tune_lag_coverV2 = true := by decide

theorem acc_tune_limp_coverV2_replay : coverReplays Parse.acc_tune_limp_IRv2 acc_tune_limp_coverV2 = true := by decide

theorem arm_plateau_crit_coverV2_replay : coverReplays Parse.arm_plateau_crit_IRv2 arm_plateau_crit_coverV2 = true := by decide

theorem arm_plateau_profiles_coverV2_replay : coverReplays Parse.arm_plateau_profiles_IRv2 arm_plateau_profiles_coverV2 = true := by decide

theorem arm_plateau_slow_coverV2_replay : coverReplays Parse.arm_plateau_slow_IRv2 arm_plateau_slow_coverV2 = true := by decide

theorem charger_fast_setpoints_coverV2_replay : coverReplays Parse.charger_fast_setpoints_IRv2 charger_fast_setpoints_coverV2 = true := by decide

theorem charger_fast_tapers_coverV2_replay : coverReplays Parse.charger_fast_tapers_IRv2 charger_fast_tapers_coverV2 = true := by decide

theorem match_multi_rate_coverV2_replay : coverReplays Parse.match_multi_rate_IRv2 match_multi_rate_coverV2 = true := by decide

theorem platoon3_linkloss_coverV2_replay : coverReplays Parse.platoon3_linkloss_IRv2 platoon3_linkloss_coverV2 = true := by decide

theorem platoon3_profiles_coverV2_replay : coverReplays Parse.platoon3_profiles_IRv2 platoon3_profiles_coverV2 = true := by decide

theorem platoon_delay_linkloss_coverV2_replay : coverReplays Parse.platoon_delay_linkloss_IRv2 platoon_delay_linkloss_coverV2 = true := by decide

theorem platoon_delay_profiles_coverV2_replay : coverReplays Parse.platoon_delay_profiles_IRv2 platoon_delay_profiles_coverV2 = true := by decide

theorem quad_light_airframe_20_coverV2_replay : coverReplays Parse.quad_light_airframe_20_IRv2 quad_light_airframe_20_coverV2 = true := by decide

theorem quad_light_lag_coverV2_replay : coverReplays Parse.quad_light_lag_IRv2 quad_light_lag_coverV2 = true := by decide

theorem quad_light_profiles_coverV2_replay : coverReplays Parse.quad_light_profiles_IRv2 quad_light_profiles_coverV2 = true := by decide

theorem refinement_ladder_rover_rung1_2to3_coverV2_replay : coverReplays Parse.refinement_ladder_rover_rung1_2to3_IRv2 refinement_ladder_rover_rung1_2to3_coverV2 = true := by decide

theorem refinement_ladder_rover_rung2_3to6_coverV2_replay : coverReplays Parse.refinement_ladder_rover_rung2_3to6_IRv2 refinement_ladder_rover_rung2_3to6_coverV2 = true := by decide

theorem refinement_ladder_rover_rung2_6dof_coverV2_replay : coverReplays Parse.refinement_ladder_rover_rung2_6dof_IRv2 refinement_ladder_rover_rung2_6dof_coverV2 = true := by decide

theorem refinement_ladder_rover_rung2b_6dof_coverV2_replay : coverReplays Parse.refinement_ladder_rover_rung2b_6dof_IRv2 refinement_ladder_rover_rung2b_6dof_coverV2 = true := by decide

theorem refinement_ladder_rover_rung2c_6dof_coverV2_replay : coverReplays Parse.refinement_ladder_rover_rung2c_6dof_IRv2 refinement_ladder_rover_rung2c_6dof_coverV2 = true := by decide

theorem refinement_ladder_rover_rung3_6to8_coverV2_replay : coverReplays Parse.refinement_ladder_rover_rung3_6to8_IRv2 refinement_ladder_rover_rung3_6to8_coverV2 = true := by decide

theorem refinement_ladder_rover_rung4_8to12_coverV2_replay : coverReplays Parse.refinement_ladder_rover_rung4_8to12_IRv2 refinement_ladder_rover_rung4_8to12_coverV2 = true := by decide

theorem rover3tier_rung12_coverV2_replay : coverReplays Parse.rover3tier_rung12_IRv2 rover3tier_rung12_coverV2 = true := by decide

theorem rover_dof_terrain_rung1_coverV2_replay : coverReplays Parse.rover_dof_terrain_rung1_IRv2 rover_dof_terrain_rung1_coverV2 = true := by decide

theorem rover_dof_terrain_rung2_coverV2_replay : coverReplays Parse.rover_dof_terrain_rung2_IRv2 rover_dof_terrain_rung2_coverV2 = true := by decide

theorem rover_dof_terrain_rung3_coverV2_replay : coverReplays Parse.rover_dof_terrain_rung3_IRv2 rover_dof_terrain_rung3_coverV2 = true := by decide

theorem rover_dof_terrain_rung3_8d_coverV2_replay : coverReplays Parse.rover_dof_terrain_rung3_8d_IRv2 rover_dof_terrain_rung3_8d_coverV2 = true := by decide

theorem rover_patrol_refine_coverV2_replay : coverReplays Parse.rover_patrol_refine_IRv2 rover_patrol_refine_coverV2 = true := by decide

theorem rover_patrol_zones_coverV2_replay : coverReplays Parse.rover_patrol_zones_IRv2 rover_patrol_zones_coverV2 = true := by decide

theorem sat3w_detumble_nominal_coverV2_replay : coverReplays Parse.sat3w_detumble_nominal_IRv2 sat3w_detumble_nominal_coverV2 = true := by decide

theorem sat3w_detumble_phases_coverV2_replay : coverReplays Parse.sat3w_detumble_phases_IRv2 sat3w_detumble_phases_coverV2 = true := by decide

theorem sat3w_detumble_weak_coverV2_replay : coverReplays Parse.sat3w_detumble_weak_IRv2 sat3w_detumble_weak_coverV2 = true := by decide

theorem sat_detumble_nominal_coverV2_replay : coverReplays Parse.sat_detumble_nominal_IRv2 sat_detumble_nominal_coverV2 = true := by decide

theorem sat_detumble_phases_coverV2_replay : coverReplays Parse.sat_detumble_phases_IRv2 sat_detumble_phases_coverV2 = true := by decide

theorem sat_detumble_weak_coverV2_replay : coverReplays Parse.sat_detumble_weak_IRv2 sat_detumble_weak_coverV2 = true := by decide

theorem story1_attdist_rung_a_6to8_coverV2_replay : coverReplays Parse.story1_attdist_rung_a_6to8_IRv2 story1_attdist_rung_a_6to8_coverV2 = true := by decide

theorem story1_attdist_rung_b_12dof_coverV2_replay : coverReplays Parse.story1_attdist_rung_b_12dof_IRv2 story1_attdist_rung_b_12dof_coverV2 = true := by decide

theorem story2_lateral_rung_a_8dof_coverV2_replay : coverReplays Parse.story2_lateral_rung_a_8dof_IRv2 story2_lateral_rung_a_8dof_coverV2 = true := by decide

theorem story2_lateral_rung_b_12dof_coverV2_replay : coverReplays Parse.story2_lateral_rung_b_12dof_IRv2 story2_lateral_rung_b_12dof_coverV2 = true := by decide

theorem story3_rollover_base_12dof_coverV2_replay : coverReplays Parse.story3_rollover_base_12dof_IRv2 story3_rollover_base_12dof_coverV2 = true := by decide

theorem story3_rollover_ladder_rung_a_coverV2_replay : coverReplays Parse.story3_rollover_ladder_rung_a_IRv2 story3_rollover_ladder_rung_a_coverV2 = true := by decide

theorem story3_rollover_ladder_rung_b_coverV2_replay : coverReplays Parse.story3_rollover_ladder_rung_b_IRv2 story3_rollover_ladder_rung_b_coverV2 = true := by decide

theorem watertank_coverV2_replay : coverReplays Parse.watertank_IRv2 watertank_coverV2 = true := by decide

end RelCertifier
