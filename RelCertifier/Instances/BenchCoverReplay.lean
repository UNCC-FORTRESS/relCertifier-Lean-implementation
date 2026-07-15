/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Kernel replays of the tool's cover gate (R5 — generated, do not edit)

Per benchmark: for EVERY emitted left-mode cover and EVERY admissible start, the
verified `decideCovered` — on the SAME structural graph the tool built
(`buildCoverGraph` over the SAME emitted flags/successors/prunes, same fuel, same
budget, σ = preJ) — accepts, by kernel computation. This replays the tool's CERTIFIED
gate inside the kernel: three standard axioms, no Z3, no IO.

Regenerate: `scripts/gen_cover_replay.py`.
-/
import RelCertifier.Instances.BenchCovers
import RelCertifier.Checker.Checker
import RelCertifier.Instances.BenchIR
import RelCertifier.Trusted.Run

namespace RelCertifier

/-- The replay predicate: every window, every admissible start, checker accepts. -/
def coverReplays (p : Parse.PProblem) (c : CoverEmitE) : Bool :=
  c.covers.all (fun lc =>
    lc.admissible.all (fun q0 =>
      decideCovered (V := Var 1)
        (buildCoverGraph lc.flags (Run.succOf p)
          (fun a b => c.pruned.contains (a, b)))
        (coverFuel lc.flags lc.bBudget)
        ⟨nodeIdx lc.flags q0, lc.bBudget, SrcSetting.preJ⟩))

theorem arm_chain_rung1_cover_replay : coverReplays Parse.arm_chain_rung1_IR arm_chain_rung1_cover = true := by decide

theorem arm_chain_rung2_cover_replay : coverReplays Parse.arm_chain_rung2_IR arm_chain_rung2_cover = true := by decide

theorem arm_chain_rung3_cover_replay : coverReplays Parse.arm_chain_rung3_IR arm_chain_rung3_cover = true := by decide

theorem arm_fidelity_high_cover_replay : coverReplays Parse.arm_fidelity_high_IR arm_fidelity_high_cover = true := by decide

theorem arm_fidelity_low_cover_replay : coverReplays Parse.arm_fidelity_low_IR arm_fidelity_low_cover = true := by decide

theorem arm_fidelity_mid_cover_replay : coverReplays Parse.arm_fidelity_mid_IR arm_fidelity_mid_cover = true := by decide

theorem arm_refinement_cover_replay : coverReplays Parse.arm_refinement_IR arm_refinement_cover = true := by decide

theorem attitude_rate_cover_replay : coverReplays Parse.attitude_rate_IR attitude_rate_cover = true := by decide

theorem endurance_gain_M1_cover_replay : coverReplays Parse.endurance_gain_M1_IR endurance_gain_M1_cover = true := by decide

theorem endurance_orderlift_1to2_cover_replay : coverReplays Parse.endurance_orderlift_1to2_IR endurance_orderlift_1to2_cover = true := by decide

theorem endurance_orderlift_2to3_cover_replay : coverReplays Parse.endurance_orderlift_2to3_IR endurance_orderlift_2to3_cover = true := by decide

theorem match_multi_eps_cover_replay : coverReplays Parse.match_multi_eps_IR match_multi_eps_cover = true := by decide

theorem match_multi_rate_cover_replay : coverReplays Parse.match_multi_rate_IR match_multi_rate_cover = true := by decide

theorem plant_fan_high_cover_replay : coverReplays Parse.plant_fan_high_IR plant_fan_high_cover = true := by decide

theorem plant_fan_low_cover_replay : coverReplays Parse.plant_fan_low_IR plant_fan_low_cover = true := by decide

theorem plant_fan_mid_cover_replay : coverReplays Parse.plant_fan_mid_IR plant_fan_mid_cover = true := by decide

theorem refinement_ladder_rover_rung1_2to3_cover_replay : coverReplays Parse.refinement_ladder_rover_rung1_2to3_IR refinement_ladder_rover_rung1_2to3_cover = true := by decide

theorem refinement_ladder_rover_rung2_3to6_cover_replay : coverReplays Parse.refinement_ladder_rover_rung2_3to6_IR refinement_ladder_rover_rung2_3to6_cover = true := by decide

theorem refinement_ladder_rover_rung2_6dof_cover_replay : coverReplays Parse.refinement_ladder_rover_rung2_6dof_IR refinement_ladder_rover_rung2_6dof_cover = true := by decide

theorem refinement_ladder_rover_rung2b_6dof_cover_replay : coverReplays Parse.refinement_ladder_rover_rung2b_6dof_IR refinement_ladder_rover_rung2b_6dof_cover = true := by decide

theorem refinement_ladder_rover_rung2c_6dof_cover_replay : coverReplays Parse.refinement_ladder_rover_rung2c_6dof_IR refinement_ladder_rover_rung2c_6dof_cover = true := by decide

theorem refinement_ladder_rover_rung3_6to8_cover_replay : coverReplays Parse.refinement_ladder_rover_rung3_6to8_IR refinement_ladder_rover_rung3_6to8_cover = true := by decide

theorem refinement_ladder_rover_rung4_8to12_cover_replay : coverReplays Parse.refinement_ladder_rover_rung4_8to12_IR refinement_ladder_rover_rung4_8to12_cover = true := by decide

theorem robot_braking_cover_replay : coverReplays Parse.robot_braking_IR robot_braking_cover = true := by decide

theorem rover3_M1_cover_replay : coverReplays Parse.rover3_M1_IR rover3_M1_cover = true := by decide

theorem rover3tier_M1_cover_replay : coverReplays Parse.rover3tier_M1_IR rover3tier_M1_cover = true := by decide

theorem rover3tier_rung12_cover_replay : coverReplays Parse.rover3tier_rung12_IR rover3tier_rung12_cover = true := by decide

theorem rover_4d_box_cover_replay : coverReplays Parse.rover_4d_box_IR rover_4d_box_cover = true := by decide

theorem rover_attitude_cone_12dof_cover_replay : coverReplays Parse.rover_attitude_cone_12dof_IR rover_attitude_cone_12dof_cover = true := by decide

theorem rover_coupled_cover_replay : coverReplays Parse.rover_coupled_IR rover_coupled_cover = true := by decide

theorem rover_dof_terrain_rung1_cover_replay : coverReplays Parse.rover_dof_terrain_rung1_IR rover_dof_terrain_rung1_cover = true := by decide

theorem rover_dof_terrain_rung2_cover_replay : coverReplays Parse.rover_dof_terrain_rung2_IR rover_dof_terrain_rung2_cover = true := by decide

theorem rover_dof_terrain_rung3_cover_replay : coverReplays Parse.rover_dof_terrain_rung3_IR rover_dof_terrain_rung3_cover = true := by decide

theorem rover_dof_terrain_rung3_8d_cover_replay : coverReplays Parse.rover_dof_terrain_rung3_8d_IR rover_dof_terrain_rung3_8d_cover = true := by decide

theorem rover_drag_cover_replay : coverReplays Parse.rover_drag_IR rover_drag_cover = true := by decide

theorem rover_position_cover_replay : coverReplays Parse.rover_position_IR rover_position_cover = true := by decide

theorem rover_terrain_M1_cover_replay : coverReplays Parse.rover_terrain_M1_IR rover_terrain_M1_cover = true := by decide

theorem rover_tier_r1_cover_replay : coverReplays Parse.rover_tier_r1_IR rover_tier_r1_cover = true := by decide

theorem story1_attdist_rung_a_6to8_cover_replay : coverReplays Parse.story1_attdist_rung_a_6to8_IR story1_attdist_rung_a_6to8_cover = true := by decide

theorem story1_attdist_rung_b_12dof_cover_replay : coverReplays Parse.story1_attdist_rung_b_12dof_IR story1_attdist_rung_b_12dof_cover = true := by decide

theorem story2_lateral_rung_a_8dof_cover_replay : coverReplays Parse.story2_lateral_rung_a_8dof_IR story2_lateral_rung_a_8dof_cover = true := by decide

theorem story2_lateral_rung_b_12dof_cover_replay : coverReplays Parse.story2_lateral_rung_b_12dof_IR story2_lateral_rung_b_12dof_cover = true := by decide

theorem story3_rollover_base_12dof_cover_replay : coverReplays Parse.story3_rollover_base_12dof_IR story3_rollover_base_12dof_cover = true := by decide

theorem story3_rollover_ladder_rung_a_cover_replay : coverReplays Parse.story3_rollover_ladder_rung_a_IR story3_rollover_ladder_rung_a_cover = true := by decide

theorem story3_rollover_ladder_rung_b_cover_replay : coverReplays Parse.story3_rollover_ladder_rung_b_IR story3_rollover_ladder_rung_b_cover = true := by decide

theorem watertank_cover_replay : coverReplays Parse.watertank_IR watertank_cover = true := by decide

end RelCertifier
