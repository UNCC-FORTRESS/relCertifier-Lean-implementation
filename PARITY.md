# Stage-4 parity — Lean relCertifier vs Python (46 benchmarks)

**Lean: 22/46 VERIFIED** (Python: 46/46). Every Lean `VERIFIED` is sound — 
backed by `flow_cert_sound_strict` (per segment) composed by the verified cover 
(`cover_sound`); Z3 UNSAT is the only trusted leaf. Non-verified = `declined` 
(sound one-sided: cover could not close with the handled invariant/λ shapes) — a 
completeness gap, never an unsound claim.

## By category

| cat | name | Lean | Python |
|---|---|---|---|
| **A** (offset/ordering) | — | **18/22** | 22/22 |
| **B** (mode-scoped) | — | **1/1** | 1/1 |
| **C** (partial/coupled) | — | **2/14** | 14/14 |
| **D** (pair-scoped) | — | **1/3** | 3/3 |
| **E** (quadratic/energy) | — | **0/3** | 3/3 |
| **F** (nonlinear product) | — | **0/3** | 3/3 |

## Per benchmark

| benchmark | cat | Lean | Python |
|---|---|---|---|
| arm_chain_rung1 | A | ✅ VERIFIED | ✅ VERIFIED |
| arm_chain_rung2 | A | ✅ VERIFIED | ✅ VERIFIED |
| arm_chain_rung3 | A | ✅ VERIFIED | ✅ VERIFIED |
| arm_fidelity_high | A | ✅ VERIFIED | ✅ VERIFIED |
| arm_fidelity_low | A | ✅ VERIFIED | ✅ VERIFIED |
| arm_fidelity_mid | A | ✅ VERIFIED | ✅ VERIFIED |
| arm_refinement | A | ✅ VERIFIED | ✅ VERIFIED |
| endurance_gain_M1 | A | ➖ declined | ✅ VERIFIED |
| endurance_orderlift_1to2 | A | ➖ declined | ✅ VERIFIED |
| endurance_orderlift_2to3 | A | ➖ declined | ✅ VERIFIED |
| match_multi_eps | A | ✅ VERIFIED | ✅ VERIFIED |
| match_multi_rate | A | ✅ VERIFIED | ✅ VERIFIED |
| plant_fan_high | A | ✅ VERIFIED | ✅ VERIFIED |
| plant_fan_low | A | ✅ VERIFIED | ✅ VERIFIED |
| plant_fan_mid | A | ✅ VERIFIED | ✅ VERIFIED |
| robot_braking | A | ✅ VERIFIED | ✅ VERIFIED |
| rover3tier_M1 | A | ✅ VERIFIED | ✅ VERIFIED |
| rover_4d_box | A | ✅ VERIFIED | ✅ VERIFIED |
| rover_drag | A | ✅ VERIFIED | ✅ VERIFIED |
| rover_terrain_M1 | A | ➖ declined | ✅ VERIFIED |
| rover_tier_r1 | A | ✅ VERIFIED | ✅ VERIFIED |
| watertank | A | ✅ VERIFIED | ✅ VERIFIED |
| rover_position | B | ✅ VERIFIED | ✅ VERIFIED |
| attitude_rate | C | ✅ VERIFIED | ✅ VERIFIED |
| refinement_ladder_rover_rung1_2to3 | C | ➖ declined | ✅ VERIFIED |
| refinement_ladder_rover_rung2_3to6 | C | ➖ declined | ✅ VERIFIED |
| refinement_ladder_rover_rung2_6dof | C | ➖ declined | ✅ VERIFIED |
| refinement_ladder_rover_rung2b_6dof | C | ➖ declined | ✅ VERIFIED |
| refinement_ladder_rover_rung2c_6dof | C | ➖ declined | ✅ VERIFIED |
| refinement_ladder_rover_rung4_8to12 | C | ➖ declined | ✅ VERIFIED |
| rover3_M1 | C | ✅ VERIFIED | ✅ VERIFIED |
| rover_dof_terrain_rung1 | C | ➖ declined | ✅ VERIFIED |
| rover_dof_terrain_rung2 | C | ➖ declined | ✅ VERIFIED |
| rover_dof_terrain_rung3 | C | ➖ declined | ✅ VERIFIED |
| rover_dof_terrain_rung3_8d | C | ➖ declined | ✅ VERIFIED |
| story2_lateral_rung_a_8dof | C | ➖ declined | ✅ VERIFIED |
| story2_lateral_rung_b_12dof | C | ➖ declined | ✅ VERIFIED |
| rover_coupled | D | ✅ VERIFIED | ✅ VERIFIED |
| story1_attdist_rung_a_6to8 | D | ➖ declined | ✅ VERIFIED |
| story1_attdist_rung_b_12dof | D | ➖ declined | ✅ VERIFIED |
| refinement_ladder_rover_rung3_6to8 | E | ➖ declined | ✅ VERIFIED |
| rover3tier_rung12 | E | ⏱ TIMEOUT | ✅ VERIFIED |
| rover_attitude_cone_12dof | E | ➖ declined | ✅ VERIFIED |
| story3_rollover_base_12dof | F | ➖ declined | ✅ VERIFIED |
| story3_rollover_ladder_rung_a | F | ➖ declined | ✅ VERIFIED |
| story3_rollover_ladder_rung_b | F | ➖ declined | ✅ VERIFIED |

## Why the 24 decline (completeness, not soundness)

- **C/E/F (coupled / quadratic / nonlinear invariants):** the runner's `invToG` lowers only the *primary* offset component of a multi-conjunct relational invariant; benchmarks whose coupling/quadratic term is load-bearing decline. The verified core (`lieDeriv`, `tderiv`) already handles polynomial terms — extending `invToG` to the full conjunction is the next completeness step.
- **A stragglers (endurance_*, rover_terrain_M1):** the coarse λ grid `{λmin, εR/εL, λmax}` misses the stretch these need; a finer search would recover them.
- **rover3tier_rung12:** exceeds the 60 s Z3 budget (many-mode cover).
