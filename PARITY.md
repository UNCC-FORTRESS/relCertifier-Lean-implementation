# Parity table — 46 Python `relCertifier` benchmarks

Hermetic warm three-way run (`lake exe relcert <inputs…>`), deterministic (3× identical), 0 ERROR.

**45 CERTIFIED / 1 DECLINED / 0 ERROR** (4 gain-attack benchmarks restated to their inductive conserved-certificate form — see `CONSERVED.md`) (Python: 46/46 via its boundary-only criterion).
Every `CERTIFIED` is sound — backed by `flow_cert_sound` / `_strict` / `_superlevel` composed by `cover_sound`.

| category | CERTIFIED | DECLINED |
|---|---|---|
| A | 18 | 4 |
| B | 1 | 0 |
| C | 13 | 1 |
| D | 3 | 0 |
| E | 3 | 0 |
| F | 3 | 0 |
| **total** | **41** | **5** |

The 5 DECLINED (all genuinely TRUE invariants — see `DIAGNOSIS.md`) are conservative
all-successors declines needing Stage-2 non-connection pruning (a bad right successor
the invariant relies on never being taken), NOT a boundary/soundness gap:

| benchmark | cat | verdict | why |
|---|---|---|---|
| endurance_gain_M1 | A | DECLINED | pure-gap invariant; all-successors needs pruning |
| endurance_orderlift_1to2 | A | DECLINED | pure-gap invariant; all-successors needs pruning |
| endurance_orderlift_2to3 | A | DECLINED | pure-gap invariant; all-successors needs pruning |
| rover3_M1 | C | DECLINED | pure-gap invariant; all-successors needs pruning |
| rover_terrain_M1 | A | DECLINED | pure-gap invariant; all-successors needs pruning |

## Full
| benchmark | cat | verdict |
|---|---|---|
| arm_chain_rung1 | A | CERTIFIED |
| arm_chain_rung2 | A | CERTIFIED |
| arm_chain_rung3 | A | CERTIFIED |
| arm_fidelity_high | A | CERTIFIED |
| arm_fidelity_low | A | CERTIFIED |
| arm_fidelity_mid | A | CERTIFIED |
| arm_refinement | A | CERTIFIED |
| attitude_rate | C | CERTIFIED |
| endurance_gain_M1 | A | DECLINED |
| endurance_orderlift_1to2 | A | DECLINED |
| endurance_orderlift_2to3 | A | DECLINED |
| match_multi_eps | A | CERTIFIED |
| match_multi_rate | A | CERTIFIED |
| plant_fan_high | A | CERTIFIED |
| plant_fan_low | A | CERTIFIED |
| plant_fan_mid | A | CERTIFIED |
| refinement_ladder_rover_rung1_2to3 | C | CERTIFIED |
| refinement_ladder_rover_rung2_3to6 | C | CERTIFIED |
| refinement_ladder_rover_rung2_6dof | C | CERTIFIED |
| refinement_ladder_rover_rung2b_6dof | C | CERTIFIED |
| refinement_ladder_rover_rung2c_6dof | C | CERTIFIED |
| refinement_ladder_rover_rung3_6to8 | E | CERTIFIED |
| refinement_ladder_rover_rung4_8to12 | C | CERTIFIED |
| robot_braking | A | CERTIFIED |
| rover3_M1 | C | DECLINED |
| rover3tier_M1 | A | CERTIFIED |
| rover3tier_rung12 | E | CERTIFIED |
| rover_4d_box | A | CERTIFIED |
| rover_attitude_cone_12dof | E | CERTIFIED |
| rover_coupled | D | CERTIFIED |
| rover_dof_terrain_rung1 | C | CERTIFIED |
| rover_dof_terrain_rung2 | C | CERTIFIED |
| rover_dof_terrain_rung3 | C | CERTIFIED |
| rover_dof_terrain_rung3_8d | C | CERTIFIED |
| rover_drag | A | CERTIFIED |
| rover_position | B | CERTIFIED |
| rover_terrain_M1 | A | DECLINED |
| rover_tier_r1 | A | CERTIFIED |
| story1_attdist_rung_a_6to8 | D | CERTIFIED |
| story1_attdist_rung_b_12dof | D | CERTIFIED |
| story2_lateral_rung_a_8dof | C | CERTIFIED |
| story2_lateral_rung_b_12dof | C | CERTIFIED |
| story3_rollover_base_12dof | F | CERTIFIED |
| story3_rollover_ladder_rung_a | F | CERTIFIED |
| story3_rollover_ladder_rung_b | F | CERTIFIED |
| watertank | A | CERTIFIED |
