# Benchmark suite: `suite_v2`

`suite_v2/<name>/input.txt` is the complete specification of one benchmark: the left
(ideal) and right (implementation) hybrid automata, the relational invariant (one row per
left mode) and the time-stretch range. **45 benchmarks.** With the widened cut channel on
(`RELCERT_IMPLIED_CUT=1`, as every suite_v2 run sets it) the tool CERTIFIES all 45, and
every one carries a kernel-checked Theorem 3 (`RelCertifier/InstancesV2/BatteryV2.lean`;
check recipe: `docs/CERTIFICATION-CHECK.md`). Without the widened channel 12 of them
DECLINE.

The suite's design, the per-family rationale, the domain audit (every evolve bound is a
physical limit of the plant; `scripts/domain_widening.py` re-runs the tool with every bound
widened) and the mechanism matrix (which certifier mechanism each benchmark actually
needs, read off counter-runs; `scripts/suite_v2_matrix.py`) are in
`docs/SUITE-REDESIGN.md`. Each file written for this suite states in its header the
physical story, the units, the measured cover and the mechanisms it exercises
(`# scenario:` and `# mechanisms:` lines).

## The 19 carried-over benchmarks

Nineteen files (the rover refinement ladder, the rover terrain rungs, `rover3tier_rung12`,
`match_multi_rate`, and the story1, story2 and story3 benchmarks except `story3_rollover_ladder_rung_b`) are byte-identical copies of files of the retired legacy
suite `suite_uniform` (removed from the tree on 2026-10-10; git history keeps it). Their
Theorem 3 instances were proved against the legacy files; since the parsed literals are
equal (`RelCertifier/InstancesV2/SameIR.lean`, `rfl`), those theorems are theorems about
these files, and the suite_v2 battery re-exports them. Their headers are the legacy ones
(no `# scenario:` line). `story3_rollover_ladder_rung_b` was repaired on the left (attitude
domains and the zone-switch entry condition) and `watertank` was redesigned as the paper's
running example; both carry new instances.

## The benchmarks

State variables and modes are given as left / right. Notes: *carried over* (see above),
*mode-keyed* (per-left-mode invariant rows, Theorem 3 at the mode-keyed invariant),
*widened cuts* (DECLINES without `RELCERT_IMPLIED_CUT=1`), *Z3-free* (the theorem has no
verdict hypothesis), *nonblocking region* (the theorem is stated on the conserved-momentum
band of the model; `docs/SUITE-REDESIGN.md` §19.2).

| benchmark | state vars | modes | scenario | notes |
|---|---|---|---|---|
| `acc_spoof_lag` | 2 / 2 | 1 / 2 | model-refinement | widened cuts |
| `acc_spoof_limp` | 1 / 1 | 2 / 4 | sensor-attack | mode-keyed |
| `acc_tune_lag` | 2 / 2 | 1 / 2 | model-refinement |  |
| `acc_tune_limp` | 1 / 1 | 2 / 4 | degraded-controller | mode-keyed |
| `arm_plateau_crit` | 2 / 1 | 2 / 4 | model-refinement | widened cuts, Z3-free |
| `arm_plateau_profiles` | 2 / 1 | 2 / 5 | degraded-controller | widened cuts, Z3-free |
| `arm_plateau_slow` | 2 / 1 | 2 / 4 | degraded-actuator | widened cuts, Z3-free |
| `charger_fast_setpoints` | 1 / 1 | 3 / 4 | degraded-controller | widened cuts |
| `charger_fast_tapers` | 1 / 1 | 3 / 5 | degraded-controller |  |
| `match_multi_rate` | 2 / 2 | 4 / 2 |  | carried over |
| `platoon3_linkloss` | 6 / 6 | 2 / 4 | sensor-attack | mode-keyed, widened cuts |
| `platoon3_profiles` | 6 / 6 | 1 / 6 | sensor-attack | widened cuts |
| `platoon_delay_linkloss` | 1 / 1 | 3 / 3 | sensor-attack | mode-keyed, widened cuts |
| `platoon_delay_profiles` | 1 / 1 | 2 / 4 | sensor-attack | widened cuts |
| `quad_light_airframe_20` | 1 / 1 | 1 / 2 | model-refinement |  |
| `quad_light_lag` | 2 / 2 | 1 / 1 | model-refinement |  |
| `quad_light_profiles` | 1 / 1 | 1 / 4 | model-refinement |  |
| `refinement_ladder_rover_rung1_2to3` | 3 / 2 | 3 / 3 |  | carried over |
| `refinement_ladder_rover_rung2_3to6` | 6 / 6 | 3 / 3 |  | carried over |
| `refinement_ladder_rover_rung2_6dof` | 4 / 4 | 3 / 3 |  | carried over, Z3-free |
| `refinement_ladder_rover_rung2b_6dof` | 6 / 6 | 3 / 3 |  | carried over, Z3-free |
| `refinement_ladder_rover_rung2c_6dof` | 6 / 6 | 3 / 3 |  | carried over |
| `refinement_ladder_rover_rung3_6to8` | 8 / 8 | 3 / 3 |  | carried over |
| `refinement_ladder_rover_rung4_8to12` | 12 / 12 | 3 / 3 |  | carried over |
| `rover3tier_rung12` | 3 / 3 | 2 / 2 |  | carried over, mode-keyed |
| `rover_dof_terrain_rung1` | 3 / 3 | 3 / 3 |  | carried over |
| `rover_dof_terrain_rung2` | 6 / 6 | 3 / 3 |  | carried over |
| `rover_dof_terrain_rung3` | 12 / 12 | 3 / 3 |  | carried over |
| `rover_dof_terrain_rung3_8d` | 8 / 8 | 3 / 3 |  | carried over |
| `rover_patrol_refine` | 3 / 3 | 4 / 4 | model-refinement | mode-keyed, widened cuts |
| `rover_patrol_zones` | 2 / 2 | 4 / 5 | degraded-actuator | mode-keyed |
| `sat3w_detumble_nominal` | 6 / 6 | 1 / 2 | model-refinement | nonblocking region |
| `sat3w_detumble_phases` | 6 / 6 | 2 / 2 | model-refinement | mode-keyed, nonblocking region |
| `sat3w_detumble_weak` | 6 / 6 | 1 / 4 | degraded-actuator | nonblocking region |
| `sat_detumble_nominal` | 4 / 4 | 1 / 2 | model-refinement | nonblocking region |
| `sat_detumble_phases` | 4 / 4 | 2 / 2 | model-refinement | mode-keyed, nonblocking region |
| `sat_detumble_weak` | 4 / 4 | 1 / 4 | degraded-actuator | nonblocking region |
| `story1_attdist_rung_a_6to8` | 8 / 8 | 3 / 3 |  | carried over, mode-keyed |
| `story1_attdist_rung_b_12dof` | 12 / 12 | 3 / 3 |  | carried over, mode-keyed |
| `story2_lateral_rung_a_8dof` | 8 / 8 | 3 / 3 |  | carried over |
| `story2_lateral_rung_b_12dof` | 12 / 12 | 3 / 3 |  | carried over |
| `story3_rollover_base_12dof` | 12 / 12 | 3 / 3 |  | carried over |
| `story3_rollover_ladder_rung_a` | 12 / 12 | 3 / 3 |  | carried over |
| `story3_rollover_ladder_rung_b` | 12 / 12 | 3 / 3 |  | mode-keyed, widened cuts |
| `watertank` | 1 / 1 | 3 / 5 | sensor-attack | widened cuts |

## File format

INI-style sections. The parser is `RelCertifier/Trusted/Parse.lean` and it is **strict**:
it rejects rather than weakens, and the CLI additionally refuses unknown keys and unknown
sections (`Trusted/KeyAudit.lean`). Lines starting with `#` are comments. An excerpt of
`watertank`:

```ini
[problem]
name = watertank
max_depth = 8            # accepted, deliberately unread (see below)
lambda_min = 1.0
lambda_max = 6.0
bound_T = 40.0           # accepted, deliberately unread

[Lsys]                   # the ideal system; [Rsys] is the implementation
state_vars = [x]
epsilon = 1.0

[Lsys.mode.Low]          # one section per mode, named [<Lsys|Rsys>.mode.<Name>]
ode = x' = smt2:(* 0.6 (- 15.5 x));
guard = x >= 5.0 and x < 13.0
evolve = x >= 0.0 and x <= 25.0
next = [Low, Mid]

[relational_invariant]   # one row per LEFT mode name
Low  = x[l] <= x[r] + 3 and x[r] <= x[l] + 3
Mid  = x[l] <= x[r] + 3 and x[r] <= x[l] + 3
High = x[l] <= x[r] + 3 and x[r] <= x[l] + 3
```

Key points, each of which the parser enforces:

* **`ode`** (singular) holds the whole vector field as one `;`-separated list:
  `ode = px' = vx; py' = vy; vx' = 0.2; vy' = 0;`. A right-hand side is either infix
  arithmetic or an `smt2:`-prefixed S-expression (`vx' = smt2:(* -0.5 vx)`).
* **`guard`** is the mode's entry condition, **`evolve`** the domain the flow may not
  leave, **`next`** the declared successors (the transition relation; the trust base's
  successor-completeness assumption quantifies over exactly this list).
* **`state_vars`** is per system; the coordinate order is the order the Lean instances
  index by. A right list may be a sublist of the left one (four suite_v2 benchmarks); a
  right-only variable would get a coordinate after the left variables, held fixed on the
  left (`Trusted/JointVars.lean`).
* **`[relational_invariant]`** has one row per left mode, over `[l]`/`[r]`-suffixed
  variables. When the rows differ, the benchmark is mode-keyed: the tool checks the
  handoff at every declared left transition (`docs/HANDOFF.md`).
* **`lambda_min` / `lambda_max`** bound the time stretch the right side may use.

**`max_depth` and `bound_T`** are present in all 45 files and read by no stage: search
depth is a tool parameter, not part of the specification. They are whitelisted so that the
key audit can still reject genuinely unknown keys.

## Running one

```bash
lake build relcert
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/suite_v2/watertank/input.txt
```

The tool parses, lowers, searches for a cover and prints CERTIFIED / DECLINED / ERROR.
`relcert --emit-ir`, `--emit-cover` and `--emit-cuts` print the Lean literals the
kernel-checked data layer is generated from (`scripts/gen_v2_data.py`), and
`relcert-test`'s `[ir-drift-v2]` re-parses every file and compares it with its literal, so
a file and its theorem cannot drift apart silently.
