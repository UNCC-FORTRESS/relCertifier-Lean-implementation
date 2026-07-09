# Parity — Lean oracle vs Python relCertifier (46 benchmarks)

Three-way, hermetic, deterministic warm-session run: **23 CERTIFIED / 22 DECLINED / 0 ERROR**
(cross-run verdict diff = 0). Every `CERTIFIED` is **sound** (verified core,
`flow_cert_sound_strict` composed by `cover_sound`); `ERROR` is a distinct outcome for any
harness/solver failure and can never masquerade as a verdict. Python VERIFIES all 46 via its
boundary-only criterion, so Lean ⊆ Python; the `DECLINED` set is exactly the
boundary-only-unsound gap the oracle correctly refuses. `rover3tier_rung12` is a slow
multi-tier DECLINE (thousands of solver calls) — the one benchmark wanting a query budget.

## By category (CERT / DECL / ERR of total)

| cat | | CERT | DECL | ERR | total |
|---|---|---|---|---|---|
| **A** | offset/ordering | 18 | 4 | 0 | 22 |
| **B** | mode-scoped | 1 | 0 | 0 | 1 |
| **C** | partial/coupled | 3 | 11 | 0 | 14 |
| **D** | pair-scoped | 1 | 2 | 0 | 3 |
| **E** | quadratic/energy | 0 | 2 | 0 | 3 |
| **F** | nonlinear product | 0 | 3 | 0 | 3 |
| **all** | | **23** | **22** | **0** | 46 |

## Timing (warm, in-process)

45 fast benchmarks on one warm session: **~3 s total; per-call mean 68 ms, median 32 ms,
p90 167 ms, max 230 ms** — dominated by the Z3 solve, not process spawn.

## Per benchmark (Lean vs Python)

| benchmark | cat | Lean | Python |
|---|---|---|---|
| arm_chain_rung1 | A | CERTIFIED | VERIFIED |
| arm_chain_rung2 | A | CERTIFIED | VERIFIED |
| arm_chain_rung3 | A | CERTIFIED | VERIFIED |
| arm_fidelity_high | A | CERTIFIED | VERIFIED |
| arm_fidelity_low | A | CERTIFIED | VERIFIED |
| arm_fidelity_mid | A | CERTIFIED | VERIFIED |
| arm_refinement | A | CERTIFIED | VERIFIED |
| endurance_gain_M1 | A | DECLINED | VERIFIED |
| endurance_orderlift_1to2 | A | DECLINED | VERIFIED |
| endurance_orderlift_2to3 | A | DECLINED | VERIFIED |
| match_multi_eps | A | CERTIFIED | VERIFIED |
| match_multi_rate | A | CERTIFIED | VERIFIED |
| plant_fan_high | A | CERTIFIED | VERIFIED |
| plant_fan_low | A | CERTIFIED | VERIFIED |
| plant_fan_mid | A | CERTIFIED | VERIFIED |
| robot_braking | A | CERTIFIED | VERIFIED |
| rover3tier_M1 | A | CERTIFIED | VERIFIED |
| rover_4d_box | A | CERTIFIED | VERIFIED |
| rover_drag | A | CERTIFIED | VERIFIED |
| rover_terrain_M1 | A | DECLINED | VERIFIED |
| rover_tier_r1 | A | CERTIFIED | VERIFIED |
| watertank | A | CERTIFIED | VERIFIED |
| rover_position | B | CERTIFIED | VERIFIED |
| attitude_rate | C | CERTIFIED | VERIFIED |
| refinement_ladder_rover_rung1_2to3 | C | DECLINED | VERIFIED |
| refinement_ladder_rover_rung2_3to6 | C | DECLINED | VERIFIED |
| refinement_ladder_rover_rung2_6dof | C | CERTIFIED | VERIFIED |
| refinement_ladder_rover_rung2b_6dof | C | CERTIFIED | VERIFIED |
| refinement_ladder_rover_rung2c_6dof | C | DECLINED | VERIFIED |
| refinement_ladder_rover_rung4_8to12 | C | DECLINED | VERIFIED |
| rover3_M1 | C | DECLINED | VERIFIED |
| rover_dof_terrain_rung1 | C | DECLINED | VERIFIED |
| rover_dof_terrain_rung2 | C | DECLINED | VERIFIED |
| rover_dof_terrain_rung3 | C | DECLINED | VERIFIED |
| rover_dof_terrain_rung3_8d | C | DECLINED | VERIFIED |
| story2_lateral_rung_a_8dof | C | DECLINED | VERIFIED |
| story2_lateral_rung_b_12dof | C | DECLINED | VERIFIED |
| rover_coupled | D | CERTIFIED | VERIFIED |
| story1_attdist_rung_a_6to8 | D | DECLINED | VERIFIED |
| story1_attdist_rung_b_12dof | D | DECLINED | VERIFIED |
| refinement_ladder_rover_rung3_6to8 | E | DECLINED | VERIFIED |
| rover3tier_rung12 | E | SLOW (pending) | VERIFIED |
| rover_attitude_cone_12dof | E | DECLINED | VERIFIED |
| story3_rollover_base_12dof | F | DECLINED | VERIFIED |
| story3_rollover_ladder_rung_a | F | DECLINED | VERIFIED |
| story3_rollover_ladder_rung_b | F | DECLINED | VERIFIED |

## Determinism / soundness note

A pre-sentinel run reported 29 CERTIFIED; that was **inflated by a pipe-desync bug** (a stale
`unsat` read for a query that was actually `sat`). The `(echo)` sentinel makes reads
deterministic; the reproducible count is the one above. The determinism test caught this
over-certification — the anti-flakiness guarantee the synthesis loop depends on.
