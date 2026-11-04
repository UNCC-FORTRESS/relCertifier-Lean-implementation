# Benchmark suite: `suite_v2`

`suite_v2/<name>/input.txt` is the complete specification of one benchmark: the left
(ideal) and right (implementation) hybrid automata, the relational invariant (one row per
left mode) and the stretch range. **50 benchmarks**, 10 of them from the literature (`lit_*`).
With the implied mode-fact candidates on (`RELCERT_IMPLIED_CUT=1`, as every suite_v2 run sets
it) the tool CERTIFIES all 50, and every one carries a kernel-checked Theorem 3 (the paper's
Soundness of Synthesis) with the paper's left program over the guard-gated right automaton
(`RelCertifier/InstancesV2/Bridge/`; check recipe: `docs/CERTIFICATION-CHECK.md`). Without
the implied candidates 5 of them DECLINE (the rows marked *widened cuts* below;
`NO_IMPLIED_CUT` in `docs/paper-numbers/matrix.log`).

`benchmarks/reserve/` and `benchmarks/skipped/` (designs outside the suite) were removed; their
last state is kept at the git tag `pre-cleanup-2026-11`.

**Assumption 1 of each right model** (the paper's Well-Formedness: from every guard state a
full control interval of flow exists, and every evolution of at most `ε_r` ends in a declared
successor's guard) is proved per file in Lean without Z3 (`WellFormedR`, `docs/WELLFORMED.md`).
It holds for all 50 literally; the 3 satellite files are proved on the momentum band their
domain declares. Every benchmark has one physical evolve domain, the same on every mode of a
side (`scripts/check_one_domain.py`). `relcert --wellformed <input.txt>…` runs the tool's
sufficient check per right mode (all 181 right modes of the suite are `ok`: 75 by invariance,
106 by exit); `--check-quick-v2` runs it strict and fails on any `UNKNOWN` or `BLOCKING`.

The suite's design rules, the per-family rationale, the domain audit (every evolve bound is a
physical limit of the plant; `scripts/domain_widening.py` re-runs the tool with every bound
widened) and the mechanism matrix (`scripts/suite_v2_matrix.py`) are in
`docs/SUITE-REDESIGN.md`. Each file states in its header the physical story, the units, the
measured cover and the mechanisms it exercises (`# scenario:` and `# mechanisms:` lines).

## Other directories

| directory | contents |
|---|---|
| `choice/` | the 2 committed-subset exhibits (`watertank_choice`, `vehicle_accel_copy`), bridge instances beside the suite's (52 in all) |
| `negative/` | 3 files the tool must DECLINE (below) |
| `negative_wellformed/` | 1 right model that violates Assumption 1 (below) |
| `stutter_demo/` | `salt_tank_stutter`, the stretch-0 demo (`docs/STUTTER.md`) |
| `prelanding_demo/` | `engine_cooling_prelanding` and `hold_reposition_strict`, the restricted-mode right-only demos (`docs/PRELANDING.md`) |
| `progress_demo/` | `stopline_friction_mixed`, two reposition stages crossing in opposite directions (`docs/PRELANDING.md`) |
| `strict_demo/` | `watertank_strict`, a strict-invariant exhibit |
| `refute_mutants/` | the 140 known-false invariant variants with a Lean refutation (`docs/REFUTATION-RESULTS.md`); their text is pinned by sha256 in `docs/refute/witnesses.jsonl`, do not edit |

## Headers and mechanism letters

Every header describes its current file: a `# scenario:` line, a `# mechanisms:` line in the
paper's Table 1 letters, what each side is and the one cause between them, the requirement
behind each constant with its tightest certifying value, the domains and any coverage gap of
the right guards, and the verdict under every configuration. Where only a model change could
make a header claim true, the header states the limitation.

The letters (the paper's Table 1): **S** stretching (a pairing at a stretch other than 1,
stretch 0 included), **M** multi-step cover, **R** right-only segment (the restricted-mode
right-only certificates included), **B** branching, **P** pruning, **D** mode-dependent
invariant, **I** mode fact, **X** committed successor subset. A certificate *uses* a letter
when it appears in the certificate found (the replayed cover and its records). A letter is
*needed* when switching the mechanism off declines: S under `RELCERT_SYNC=1`, R under
`RELCERT_NO_REPO=1`, P under `RELCERT_NO_PRUNE=1`, I under `RELCERT_NO_CUT=1`, X under
`RELCERT_NO_CHOICE=1`; D by the uniform-row test (every uniform invariant that keeps the stated
requirements declines); M and B have no switch-off and are marked used only. Both flags per
file are in `docs/paper-numbers/letters.md` / `letters.json`, the rules in the docstring of
`scripts/suite_v2_letters.py`, and the paper's tables in `docs/paper-numbers/table1.tex` and
`table_per_benchmark.tex`. Stretch 0 and the restricted-mode right-only certificate are on for
every benchmark; `RELCERT_NO_STUTTER=1` and `RELCERT_NO_PRELANDING=1` switch them off for an
ablation (`docs/STUTTER.md`, `docs/PRELANDING.md`).

## The benchmarks

Ordered by the paper's application areas (Table 1). Dimension and modes are left / right.
Letters as in `docs/paper-numbers/letters.md`: the letters the certificate uses, needed ones
in bold. Notes: *mode-keyed* (Theorem 3 at the mode-keyed invariant, `keyedClaim`; the others
are `windowClaim`), *widened cuts* (DECLINES without the implied mode-fact candidates),
*literature* (a model taken from a cited paper; its header states the source and what changed
in the sampled form).

| benchmark | area | scenario | dim | modes | inv | letters used (needed in bold) | notes |
|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | Automotive | sensor-attack | 2/2 | 1/1 | linear | **S** M I |  |
| `acc_spoof_limp` | Automotive | sensor-attack | 1/1 | 2/3 | linear | M R B **I** |  |
| `acc_tune_limp` | Automotive | degraded-controller | 1/1 | 2/2 | linear | **S** M P **D** **I** | mode-keyed |
| `platoon_profiles` | Automotive | controller-refinement | 2/2 | 1/1 | linear | **S** M I | mode-keyed |
| `train_ato_odometry` | Automotive | degraded-sensor | 1/1 | 3/3 | linear | **S** M B I |  |
| `rover_ladder_2to3` | Rovers | model-refinement | 3/3 | 3/3 | linear | I |  |
| `rover_ladder_3to6` | Rovers | model-refinement | 6/6 | 3/3 | linear | I |  |
| `rover_ladder_6to8` | Rovers | model-refinement | 8/8 | 3/3 | quadratic | **S** M **I** |  |
| `rover_ladder_8to12` | Rovers | model-refinement | 12/12 | 3/3 | quadratic | **S** M **I** |  |
| `stopline_drag` | Rovers | model-refinement | 15/15 | 3/3 | quadratic | **D** I | mode-keyed |
| `stopline_friction` | Rovers | model-refinement | 8/8 | 3/3 | quadratic | **S** **D** I | mode-keyed |
| `stopline_lag` | Rovers | model-refinement | 5/5 | 3/3 | quadratic | **D** I | mode-keyed |
| `stopline_tyre` | Rovers | model-refinement | 11/11 | 3/3 | quadratic | **D** I | mode-keyed |
| `engine_start_highidle` | Aerospace | controller-change | 3/3 | 6/6 | linear | **R** **D** **I** | mode-keyed, widened cuts |
| `flaps_slow_approach` | Aerospace | degraded-actuator | 2/2 | 2/2 | linear | **S** I |  |
| `quad_light_lag` | Aerospace | model-refinement | 3/3 | 1/1 | linear | **S** M I |  |
| `quad_light_profiles` | Aerospace | model-refinement | 2/2 | 3/3 | linear | **S** M R B I **X** |  |
| `sat3w_detumble_phases` | Aerospace | model-refinement | 6/6 | 2/3 | quadratic | M P **I** **X** |  |
| `sat_detumble_phases` | Aerospace | model-refinement | 4/4 | 2/3 | quadratic | M P **I** **X** |  |
| `sat_detumble_weak` | Aerospace | degraded-actuator | 4/4 | 1/4 | quadratic | **S** M B P I **X** |  |
| `autoclave_liquid_steambank` | Process | degraded-actuator | 3/3 | 4/4 | linear | **S** **R** **D** I | mode-keyed |
| `boiler_purge_vfd` | Process | refinement | 3/3 | 2/2 | linear | **R** **D** I | mode-keyed |
| `bottling_fill_strainer` | Process | degraded-actuator | 2/2 | 2/2 | linear | **S** **I** |  |
| `extruder_pe100_manualstart` | Process | degraded-controller | 2/2 | 4/4 | linear | M B **P** **I** |  |
| `furnace_program_timebase` | Process | controller-change | 2/2 | 3/3 | linear | **S** **I** | widened cuts |
| `molding_pack_checkring` | Process | degraded-actuator | 3/3 | 2/2 | linear | **D** I | mode-keyed |
| `reactor_feed_wireless` | Process | degraded-sensor | 2/2 | 4/4 | linear | M B **P** I |  |
| `tank_dos_3to1` | Process | dos-attack | 2/2 | 4/4 | linear | M **I** |  |
| `h2_refuel_ambientbias` | Energy | sensor-fault | 1/1 | 7/5 | linear | **R** **D** **I** | mode-keyed |
| `hydro_rejection_gatecal` | Energy | degraded-sensor | 3/3 | 2/2 | linear | **D** I | mode-keyed |
| `turbine_startup_gearratio` | Energy | degraded-controller | 3/3 | 5/5 | linear | **R** **D** **I** | mode-keyed, widened cuts |
| `syringe_relay_prearm` | Medical | controller-change | 4/4 | 6/4 | linear | **R** **D** I | mode-keyed |
| `ventilator_vc_cuffleak` | Medical | degraded-actuator | 2/2 | 2/2 | linear | **D** **I** | mode-keyed, widened cuts |
| `antenna_track_kvretune` | Infrastructure | controller-change | 3/3 | 3/3 | linear | **D** I | mode-keyed |
| `canal_gate_notches` | Infrastructure | controller-refinement | 1/1 | 3/4 | linear | R I **X** |  |
| `elevator_start_discbrake` | Infrastructure | actuator-change | 3/3 | 4/4 | linear | **R** D I | mode-keyed |
| `gantry_speed_zones` | Infrastructure | controller-refinement | 2/2 | 3/1 | linear | **S** M I |  |
| `rampmeter_poll_2to1` | Infrastructure | degraded-network | 3/3 | 6/6 | linear | M B P I |  |
| `watertank` | Water tank | sensor-attack | 1/1 | 3/5 | linear | **S** M R B P I |  |
| `watertank_twospeed` | Water tank | sensor-attack | 1/1 | 3/6 | linear | **S** M R B I |  |
| `lit_csf21_vehicle_bus` | Literature | sensor-attack | 3/3 | 6/12 | linear | R I **X** | literature |
| `lit_csf21_vehicle_thermo` | Literature | sensor-attack | 3/3 | 6/6 | linear | R I **X** | literature |
| `lit_csf25_salt_tank_hold` | Literature | dos-attack | 2/2 | 2/2 | linear | **S** **D** **I** | mode-keyed, widened cuts, literature |
| `lit_drl_lane_control` | Literature | controller-refinement | 3/3 | 6/6 | linear | R I **X** | literature |
| `lit_freedm_meter` | Literature | information-flow | 2/2 | 12/12 | linear | R I **X** | literature |
| `lit_girard08_robot` | Literature | abstraction | 6/2 | 6/6 | quadratic | R I **X** | literature |
| `lit_gpt10_boost_converter` | Literature | abstraction | 2/2 | 48/2 | quadratic | I **X** | literature |
| `lit_lz21_vehicle_position` | Literature | opacity | 2/2 | 3/3 | linear | R I **X** | literature |
| `lit_nahs25_engine_cooling` | Literature | sensor-attack | 1/1 | 2/2 | linear | **R** | literature |
| `lit_nahs25_salt_tank` | Literature | sensor-attack | 1/1 | 2/2 | linear | **S** I | literature |

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
ode = x' = smt2:(* 2.0 (- 15.5 x));
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
  leave, **`next`** the declared successors (the transition relation; Assumption 1's
  successor-completeness, verified per file as `WellFormedR`, quantifies over exactly this
  list; a mode with no catch-all successor must keep every one-interval evolution inside a
  declared successor's guard).
* **`state_vars`** is per system; the coordinate order is the order the Lean instances
  index by. A right list may be a sublist of the left one (`lit_girard08_robot`); a
  right-only variable would get a coordinate after the left variables, held fixed on the
  left (`Trusted/JointVars.lean`).
* **`[relational_invariant]`** has one row per left mode, over `[l]`/`[r]`-suffixed
  variables. When the rows differ, the benchmark is mode-keyed: the tool checks the
  handoff at every declared left transition (`docs/HANDOFF.md`).
* **`lambda_min` / `lambda_max`** bound the time stretch the right side may use.

**`max_depth` and `bound_T`** are present in every suite file and read by no stage: search
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

## Negative exhibits (`benchmarks/negative/`)

Files the tool is expected to DECLINE, kept beside the suite to show what a decline looks like;
they enter no declared count. `lit_freedm_meter_leaky`: the deterministic controller `batI` of the
FREEDM case study on both sides of `lit_freedm_meter` (the battery whenever it can still charge or
discharge, the grid otherwise); a surplus at a full battery, or a demand at an empty one, goes to
the grid while a run from another level keeps it on the battery, so no matching run keeps the
meters equal. A DECLINE is
not a proof of insecurity (the certifier is sound, not complete); the source proves the leak by
exhibiting the two runs. `lit_csf21_vehicle_thermo_leaky`: `lit_csf21_vehicle_thermo` with an
air-conditioning load on the drive on both sides (accelerating while cooling gives 0.8 m/s^2
instead of 1); the thermostat command now changes the velocity, so the attacker who sets the
temperature reading sets the acceleration profile. Its header exhibits the leak by hand (five
windows of AccHeat then three of AccCool need a genuine start temperature that does not exist),
which the source's lock-step equivalence also rules out. `lit_csf21_vehicle_bus_thermoprio`:
`lit_csf21_vehicle_bus` with the bus arbitration reversed on both sides (a cycle whose
thermostat reading asks for the other setting sends the thermostat message, and the drive holds its
action for that cycle; the source gives acceleration messages priority); the temperature reading
now reaches the velocity through the bus. Its header exhibits the leak by hand (an attacked run that
no genuine message/setting sequence matches, checked exhaustively over four cycles). The check
`RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt` must print
`DECLINED` for all three files.

## Assumption 1 negative exhibit (`benchmarks/negative_wellformed/`)

`lit_hypercert_vehicle_s8`: `lit_hypercert_vehicle` (a former suite benchmark, no longer in the
repository; the exhibit is self-contained) with the position bound `s ≤ 8` in every evolve
domain (a round-2 design variant). The certifier CERTIFIES it (the relational invariant does
not see the bound), but its right model can block: every right guard admits `s = 8` with
`v > 0`, where the flow leaves the domain at once, so no evolution spans the control interval
and Assumption 1's nonblocking clause is false. The check of the successor clause alone
reports all five right modes `ok`; the two-clause check reports all five
`BLOCKING (leaves s <= 8.0)`, and `RELCERT_WELLFORMED_STRICT=1` DECLINES the file. It enters no
declared count (`docs/WELLFORMED.md` §4).

## Former names

Older records (git history, the dated docs, the branch `archive/legacy-2026-10`) use earlier
benchmark names. Only names changed in these renames (directory, `name =`, header lines,
derived Lean identifiers and modules); several renamed files have since left the suite.

### Renamed 2026-10-25

| old | new |
|---|---|
| `refinement_ladder_rover_rung1_2to3` | `rover_ladder_2to3` |
| `refinement_ladder_rover_rung2_3to6` | `rover_ladder_3to6` |
| `refinement_ladder_rover_rung3_6to8` | `rover_ladder_6to8` |
| `refinement_ladder_rover_rung4_8to12` | `rover_ladder_8to12` |
| `refinement_ladder_rover_rung2_6dof` | `rover_ladder_2to4` |
| `refinement_ladder_rover_rung2b_6dof` | `rover_ladder_2to6` |
| `refinement_ladder_rover_rung2c_6dof` | `rover_ladder_4to6` |
| `rover_dof_terrain_rung1` | `rover_terrain_2to3` |
| `rover_dof_terrain_rung2` | `rover_terrain_3to6` |
| `rover_dof_terrain_rung3` | `rover_terrain_6to12` |
| `rover_dof_terrain_rung3_8d` | `rover_terrain_6to8` |
| `story1_attdist_rung_a_6to8` | `rover_attitude_6to8` |
| `story1_attdist_rung_b_12dof` | `rover_attitude_8to12` |
| `story2_lateral_rung_a_8dof` | `rover_lateral_6to8` |
| `story2_lateral_rung_b_12dof` | `rover_lateral_8to12` |
| `story3_rollover_ladder_rung_a` | `rover_rollover_6to7` |
| `story3_rollover_ladder_rung_b` | `rover_rollover_7to12` |
| `story3_rollover_base_12dof` | `rover_rollover_6to12` |
| `rover_patrol_refine` | `rover_patrol_lag` |
| `rover3tier_rung12` | `rover_tier_1to2` |

### Renamed 2026-10-26: the terrain chain

| old | new |
|---|---|
| `rover_terrain_3to6` | `rover_terrain_2to4` (no-slip plan -> wheel slip and soil sinkage) |
| `rover_terrain_6to8` | `rover_terrain_4to6` (+ drive lag and rough-terrain heave) |
| `rover_terrain_6to12` | unchanged name (+ heave rate, bank grade, chassis pitch, acceleration, squat) |

### Renamed 2026-10-27

| old | new |
|---|---|
| `platoon_delay_linkloss` | `platoon_linkloss` (redesigned: a two-coordinate CACC follower, gap `g` and range rate `r`, that falls back to radar ACC when the V2V link is lost, against the design follower with the link up; AEB on a time-to-collision floor) |
| `match_multi_rate` | `gantry_speed_zones` (both models new: a pick-and-place gantry whose production program runs zone-scheduled speed overrides, against the program as commissioned at reduced speed; 10 mm path tolerance; replaces the synthetic unitless rate-ratio exhibit in the same multi-cycle matching role) |
| `platoon_delay_profiles` | `platoon_profiles` (redesigned: the CACC follower driven in the SPORT profile, a shorter time gap, against the design follower verified in NORMAL; its right model is `platoon_linkloss`'s, Assumption 1 through the shared `PlatoonCaccAeb` lemmas) |

### Renamed 2026-10-28: the literature group

The case studies reproduced from published work carry the prefix `lit_`, with the source's venue
and year where the old name lacked it; the exhibits sharing a stem were renamed with them.

| old | new |
|---|---|
| `drl_car_stop` | `lit_drl_car_stop` |
| `drl_lane_control` | `lit_drl_lane_control` |
| `vehicle_hypercert` | `lit_hypercert_vehicle` |
| `freedm_meter` | `lit_freedm_meter` |
| `csf21_vehicle_thermo` | `lit_csf21_vehicle_thermo` |
| `csf21_vehicle_bus` | `lit_csf21_vehicle_bus` |
| `lz_vehicle_position` | `lit_lz21_vehicle_position` |
| `girard_robot` | `lit_girard08_robot` |
| `salt_tank_sensor` | `lit_nahs25_salt_tank` |
| `negative/csf21_vehicle_thermo_leaky` | `negative/lit_csf21_vehicle_thermo_leaky` |
| `negative/freedm_meter_leaky` | `negative/lit_freedm_meter_leaky` |
| `negative_wellformed/vehicle_hypercert_s8` | `negative_wellformed/lit_hypercert_vehicle_s8` |
