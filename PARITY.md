# Parity table — 46 Python `relCertifier` benchmarks

Hermetic warm three-way run, deterministic (3× identical), 0 ERROR.

**38 CERTIFIED / 8 DECLINED / 0 ERROR** (Python: 46/46 via its boundary-only criterion).
**Every `CERTIFIED` is sound** — the flow-certificate domain is the EVOLUTION domain (holds
throughout the segment), never the mode *guard* (entry condition). 4 gain-attack benchmarks
are restated to their inductive conserved-certificate form (`CONSERVED.md`).

> **Soundness fix (this revision).** An earlier version conjoined the mode *guards* into the
> flow-certificate domain to make some benchmarks certify. That was **unsound**: a guard is
> the entry/transition condition, not the throughout-domain, so conjoining it narrowed the
> certificate to a sliver the real flow leaves (e.g. a Return mode entered at `θ≥0.7` flows to
> `θ<0.7`) — vacuously/falsely certifying. Using the evolution domain only, **7 previously
> "CERTIFIED" benchmarks correctly move to DECLINED** (arm_chain_rung1/2, arm_fidelity_low,
> arm_refinement, match_multi_eps, plant_fan_low, rover3tier_M1): their guard-narrowed
> certificates never proved invariance on the actual flow. 45 → **38**, now sound.

| category | CERTIFIED | DECLINED |
|---|---|---|
| A | 15 | 7 |
| B | 1 | 0 |
| C | 13 | 1 |
| D | 3 | 0 |
| E | 3 | 0 |
| F | 3 | 0 |
| **total** | **38** | **8** |

## Full
| benchmark | cat | verdict |
|---|---|---|
| arm_chain_rung1 | A | DECLINED |
| arm_chain_rung2 | A | DECLINED |
| arm_chain_rung3 | A | CERTIFIED |
| arm_fidelity_high | A | CERTIFIED |
| arm_fidelity_low | A | DECLINED |
| arm_fidelity_mid | A | CERTIFIED |
| arm_refinement | A | DECLINED |
| attitude_rate | C | CERTIFIED |
| endurance_gain_M1 | A | CERTIFIED |
| endurance_orderlift_1to2 | A | CERTIFIED |
| endurance_orderlift_2to3 | A | CERTIFIED |
| match_multi_eps | A | DECLINED |
| match_multi_rate | A | CERTIFIED |
| plant_fan_high | A | CERTIFIED |
| plant_fan_low | A | DECLINED |
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
| rover3tier_M1 | A | DECLINED |
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
| rover_terrain_M1 | A | CERTIFIED |
| rover_tier_r1 | A | CERTIFIED |
| story1_attdist_rung_a_6to8 | D | CERTIFIED |
| story1_attdist_rung_b_12dof | D | CERTIFIED |
| story2_lateral_rung_a_8dof | C | CERTIFIED |
| story2_lateral_rung_b_12dof | C | CERTIFIED |
| story3_rollover_base_12dof | F | CERTIFIED |
| story3_rollover_ladder_rung_a | F | CERTIFIED |
| story3_rollover_ladder_rung_b | F | CERTIFIED |
| watertank | A | CERTIFIED |
