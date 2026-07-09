# Parity — Lean oracle vs Python relCertifier (46 benchmarks)

Three-way, hermetic, deterministic warm-session run: **24 CERTIFIED / 22 DECLINED / 0 ERROR**
(cross-run verdict diff = 0; all 46 in ~2–3 s). Every `CERTIFIED` is **sound** (verified
core, `flow_cert_sound_strict` composed by `cover_sound`); `ERROR` is a distinct outcome for
any harness/solver failure and can never masquerade as a verdict. Python VERIFIES all 46 via
its boundary-only criterion, so Lean ⊆ Python; the `DECLINED` set is exactly the
boundary-only-unsound gap the oracle correctly refuses — moving synthesis to this oracle is a
soundness upgrade.

## By category (CERT / DECL / ERR of total)

| cat | | CERT | DECL | ERR | total |
|---|---|---|---|---|---|
| **A** | offset/ordering | 18 | 4 | 0 | 22 |
| **B** | mode-scoped | 1 | 0 | 0 | 1 |
| **C** | partial/coupled | 3 | 11 | 0 | 14 |
| **D** | pair-scoped | 1 | 2 | 0 | 3 |
| **E** | quadratic/energy | 1 | 2 | 0 | 3 |
| **F** | nonlinear product | 0 | 3 | 0 | 3 |
| **all** | | **24** | **22** | **0** | 46 |

## Timing (warm, in-process)

All 46 on one warm session, **~2–3 s total; per-call mean 49 ms, median 26 ms, p90 101 ms,
max 199 ms** — dominated by the Z3 solve. The cover is memoized on `(mode, fuel)` so a large
time-stretch (tiny budget step) can't blow up the pure search.

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
| rover3tier_rung12 | E | CERTIFIED | VERIFIED |
| rover_attitude_cone_12dof | E | DECLINED | VERIFIED |
| story3_rollover_base_12dof | F | DECLINED | VERIFIED |
| story3_rollover_ladder_rung_a | F | DECLINED | VERIFIED |
| story3_rollover_ladder_rung_b | F | DECLINED | VERIFIED |

## Determinism / soundness notes

- A pre-sentinel run reported 29 CERTIFIED; that was **inflated by a pipe-desync bug** (a stale
  `unsat` read). The `(echo)` sentinel makes reads deterministic. A separate cover-DFS fuel
  explosion (Lean, not Z3) both hung one benchmark and corrupted its verdict; memoizing the
  cover fixed it. The determinism test surfaced both — the anti-flakiness guarantee at work.
- Reliability bounds (all deterministic): query-count budget, SMT-size guard, wall deadline, and
  Z3 `:rlimit` (machine-independent) — every call terminates with a definite outcome.
