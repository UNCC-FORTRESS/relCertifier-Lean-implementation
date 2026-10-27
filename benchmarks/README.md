# Benchmark suite: `suite_v2`

`suite_v2/<name>/input.txt` is the complete specification of one benchmark: the left
(ideal) and right (implementation) hybrid automata, the relational invariant (one row per
left mode) and the time-stretch range. **42 benchmarks.** With the widened cut channel on
(`RELCERT_IMPLIED_CUT=1`, as every suite_v2 run sets it) the tool CERTIFIES all 42, and
every one carries a kernel-checked Theorem 3 (the paper's Soundness of Synthesis) with the paper's left program over the
guard-gated right automaton, at the mode-consistent region (`RelCertifier/InstancesV2/Bridge/`;
check recipe: `docs/CERTIFICATION-CHECK.md`). Without the widened channel 6 of them
DECLINE (the rows marked *widened cuts* below). Near-duplicates and weak benchmarks are kept
outside the suite in `benchmarks/reserve/` (inputs, headers and verdicts only; `reserve/README.md`).

**Assumption 1 of each right model** (the paper's Well-Formedness: from every guard state a
full control interval of flow exists, and every evolution of at most `ε_r` ends in a declared
successor's guard) is verified per file (`WellFormedR`, `docs/WELLFORMED.md`): it holds for
all 42 literally (the 6 satellite files carry their conserved momentum band in the right evolve
domain since 2026-10-15).
Nine files had a blocking mode until 2026-10-10 and were repaired (`docs/SUITE-REDESIGN.md`
§21; each header says how and why; `arm_plateau_profiles` and `platoon3_{linkloss,profiles}`
are in `benchmarks/reserve/` since 2026-10-27, and `platoon_delay_{linkloss,profiles}` were
replaced by the redesigned `platoon_linkloss` and `platoon_profiles`): `arm_plateau_{crit,profiles,slow}` (the ApproachA /
ApproachB bands are narrower than one control interval of their own rate: the sampled
planner's successor sets now name every band a sample can find), `platoon_delay_{linkloss,
profiles}` (the sink `BRAKE` left its guard: it now re-engages `FOLLOW`),
`platoon3_{linkloss,profiles}` (the sinks `BRAKE1`–`BRAKE3`: now latched, speed-matching, with
an invariant guard) and `quad_light_{airframe_20,profiles}` (the sink `LIMIT`: it handed back to
the climb controller, whose operating range reached the limiter threshold; both were redesigned
on 2026-10-27 with the altitude coordinate and no limiter mode).
`relcert --wellformed <input.txt>…` runs the tool's sufficient check per right mode (every one
of the 145 is `ok`); `--check-quick-v2` runs it strict and fails on any `UNKNOWN` or `BLOCKING`.

The suite's design, the per-family rationale, the domain audit (every evolve bound is a
physical limit of the plant; `scripts/domain_widening.py` re-runs the tool with every bound
widened) and the mechanism matrix (which certifier mechanism each benchmark actually
needs, read off counter-runs; `scripts/suite_v2_matrix.py`) are in
`docs/SUITE-REDESIGN.md`. Each file written for this suite states in its header the
physical story, the units, the measured cover and the mechanisms it exercises
(`# scenario:` and `# mechanisms:` lines).

## Renamed 2026-10-25

Twenty benchmarks were renamed so that the name states the system, the property and the
refinement step (e.g. deployed DOF refining reasoning DOF). Only names changed (directory,
`name =`, header lines, derived Lean identifiers and modules); models, invariants, certificates
and proofs are unchanged (the 2026-10-26 right-model change of `rover_lateral_6to8` is
separate, see below). Older records (git history, branch `archive/legacy-2026-10`, dated docs)
use the old names.

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

Retired 2026-10-26: `rover_tier_1to2`, replaced by `tank_dos_3to1` (the suite stays at 50; no
honest variant of its right model certified, `tank_dos_3to1` is the second Multi-cycle matching
benchmark).

Retired 2026-10-26: `rover_ladder_4to6`, replaced by `airheader_dos_3to1` (the suite stays at 50;
its step was vacuous: the two sides had identical dynamics on every coordinate the claim reads, the
added heave and roll were filler, and the ladder reaches 6-DOF through `rover_ladder_3to6` and
directly through `rover_ladder_2to6`; `airheader_dos_3to1` is a non-connection pruning benchmark, DECLINED under
`RELCERT_NO_PRUNE=1`).

Retired 2026-10-26: `rover_terrain_2to3`, replaced by `hvac_fan_staging` (the suite stays at 50;
it duplicated `rover_ladder_2to3`, the same 2 -> 3 heading step on the same route;
`hvac_fan_staging` is an existential mode-choice benchmark, DECLINED under `RELCERT_NO_CHOICE=1`).

Moved to the reserve 2026-10-27 (`benchmarks/reserve/`, inputs with headers and verdicts, no Lean
integration; one line of reason each in `reserve/README.md`): `airheader_dos_3to1` (the claim
does not depend on the attack), `arm_plateau_profiles` (the planner choice is never
load-bearing), `platoon3_profiles` (three identical time-scaled links; stored as its round-2
design), `platoon3_linkloss` (exact copies on links 2 and 3; stored as its round-2 design). The
suite had fewer than 50 benchmarks until batch I2 (52 after it).

## Renamed 2026-10-27: the platoon link-loss file

| old | new |
|---|---|
| `platoon_delay_linkloss` | `platoon_linkloss` (redesigned: a two-coordinate CACC follower, gap `g` and range rate `r`, that falls back to radar ACC when the V2V link is lost, against the design follower with the link up; AEB on a time-to-collision floor) |

New 2026-10-27: `platoon_latency` (the same follower with a late V2V feed-forward against an
ideal link; its right model is `platoon_linkloss`'s, and the two share one Assumption 1 lemma,
`InstancesV2/WellFormed/PlatoonCaccAeb.lean`); it takes the place of `platoon3_linkloss`.

New 2026-10-27: `engine_start_highidle` (a turbofan ground start with the high-idle schedule
against ground idle; right-only repositioning, mode-dependent rows, load-bearing mode facts) and
`train_ato_odometry` (automatic train operation with an odometry bias against the design speed
loop; the first suite file with stretches below 1, `lambda_min = 0.75`; time stretch per pairing,
multi-step and branching covers). The reserve keeps `engine_start_highidle`'s twin
`h2_refuel_ambientbias`.

New 2026-10-27 (batch I2): `bms_chiller_undercharge` (an EV battery pack in DC fast charge whose
chiller lost refrigerant, against the pack's thermal strategy; the reference commits to the half
compressor level to track the degraded full level: mode choice), `canal_gate_notches` (an
irrigation-canal pool under a three-position automatic gate against the manual operating rule's
four notches: mode choice) and `turbine_startup_gearratio` (a wind turbine start-up whose
controller uses a stale gearbox ratio; right-only repositioning, pruned parking edges and
load-bearing mode facts, all three present already at the correct ratio: the one-sided claim
form, disclosed in its header). Suite 49 -> 52. The reserve adds `grid_ffr_dos` (round-A design,
never in the suite: the bound is the no-FFR worst case and does not depend on the hold).

## Renamed 2026-10-27: batch I2

| old | new |
|---|---|
| `match_multi_rate` | `gantry_speed_zones` (both models new: a pick-and-place gantry whose production program runs zone-scheduled speed overrides, against the program as commissioned at reduced speed; 10 mm path tolerance; replaces the synthetic unitless rate-ratio exhibit in the same multi-cycle matching role) |
| `platoon_delay_profiles` | `platoon_profiles` (redesigned: the CACC follower driven in the SPORT profile, a shorter time gap, against the design follower verified in NORMAL; its right model is `platoon_linkloss`'s, Assumption 1 through the shared `PlatoonCaccAeb` lemmas) |

## Retired 2026-10-27: the rover hierarchy (batch I3)

The rover files now follow one canonical hierarchy (a four-wheel UGV on one route, zones `STEEP`
/ `MODER` / `FLAT` at 60 m and 140 m, set points 3 / 5 / 6.5 m/s; levels L2, L3, L6, L8, L12, each
right model the coarser level with the finer level's extra coordinates pinned). The four ladder
rungs `rover_ladder_2to3`, `rover_ladder_3to6`, `rover_ladder_6to8`, `rover_ladder_8to12` were
reinstalled on its models (new left and right models) and carry the requirements of the
dynamics each step adds, including the rollover (LTR) and lane rows of the former rollover and
lateral files with the same model pair; `rover_patrol_lag` was reinstalled (the rover with its
motor lag against the first-order planning model, the same zone planner on both sides). The
terrain chain is unchanged.

Left the suite (suite 52 -> 42): `rover_rollover_6to7`, `rover_rollover_7to12`,
`rover_rollover_6to12`, `rover_lateral_6to8`, `rover_lateral_8to12`, `rover_attitude_6to8`,
`rover_attitude_8to12`, `rover_ladder_2to4`, `rover_ladder_2to6`, `rover_patrol_zones`. Inputs,
Lean leaves, Assumption 1 proofs, bridge instances and refutations are in git history (last at
commit 14e0405). Kept in `benchmarks/reserve/` as round-2 / round-A designs (one line of reason
each in `reserve/README.md`): `rover_rollover_6to8`, `rover_rollover_8to12` (the round-2 names of
`rover_rollover_6to7`, `rover_rollover_7to12`) and `rover_lateral_8to12` (the same model pair and
cause as a ladder rung; their rows are folded into it), and `rover_patrol_zones` (its letters
come only from a stretch the claim does not need). The others are retired (history only).

## Renamed 2026-10-26: the terrain chain

The three terrain files were redesigned as one chain that refines terrain physics (soil, drive
lag and roughness, slope and chassis), while the ladder refines attitude: both sides of every
step run the same terrain law on the coordinates they share, and the right of each step is the
coarser model with the finer model's extra coordinates pinned. All three models (left and right)
are new; two names changed with their steps (the retired `rover_terrain_2to3` is not reused):

| old | new |
|---|---|
| `rover_terrain_3to6` | `rover_terrain_2to4` (no-slip plan -> wheel slip and soil sinkage) |
| `rover_terrain_6to8` | `rover_terrain_4to6` (+ drive lag and rough-terrain heave) |
| `rover_terrain_6to12` | unchanged name (+ heave rate, bank grade, chassis pitch, acceleration, squat) |

## The 15 carried-over benchmarks

Since 2026-10-27 (batch I3, "Retired 2026-10-27" above) none of these files is in the suite in
its carried-over form: the ladder rungs were reinstalled on the canonical rover hierarchy, the
terrain rungs had been redesigned as the terrain chain, and the attitude, lateral and rollover
files left the suite. The rest of this section is their history.

Fifteen files (the rover refinement ladder, the rover terrain rungs, and the attitude, lateral
and rollover benchmarks except `rover_rollover_7to12`) come from files of the retired legacy
suite `suite_uniform` (removed from the tree on 2026-10-10; git history keeps it); at the
2026-10-25 rename (above) they were byte-identical to them up to the name lines and the first header line of
`rover_ladder_2to6`, except `rover_lateral_6to8`: since 2026-10-26 its right model freezes the
lateral pair (`y' = 0`, `w' = 0`; before, left and right were identical), so the step is a
genuine 6 -> 8 refinement. Their
Assumption 1 proofs were first written against the legacy literals and now quote these
files' literals directly (`RelCertifier/InstancesV2/WellFormed/`); their standalone Theorem 3
instances are archived on branch `archive/legacy-2026-10`. Their headers were rewritten in the 2026-10-26
header pass (below). `rover_rollover_7to12` was repaired on the left (attitude
domains and the zone-switch entry condition; on 2026-10-26 the three rollover files were aligned
so that 6to7 and 7to12 carry 6to12's rows on shared models and compose to it, with headers
and `# scenario:` lines). On 2026-10-26 the ladder, terrain, attitude and `rover_lateral_8to12` files were rewritten as well
(the terrain files then redesigned as the terrain chain, see "Renamed 2026-10-26: the terrain chain") (pinned
right coordinates, forward-invariant left boxes, requirement rows, roles for filler coordinates,
new headers with `# scenario:` lines; the commit messages list each change), so they are no
longer copies of the legacy files; and `watertank` was redesigned as the paper's
running example; both carry new instances.

**Header pass (2026-10-26).** Every header now describes its current file: a `# scenario:` line,
a `# mechanisms:` line in the paper's Table 1 letters (S M R B P D I X, measured on the file:
S = `RELCERT_SYNC=1` declines and a cover stretches, M multi-step cover, R right-only segment,
B branching, P = `RELCERT_NO_PRUNE=1` declines, D mode-dependent rows with unsat handoffs,
I = `RELCERT_NO_CUT=1` declines, X = `RELCERT_NO_CHOICE=1` declines), what each side is and the
one cause between them, the requirement behind each constant with its tightest certifying value,
the domains and any coverage gap of the right guards, and the verdict under every configuration.
Where only a model change could make a header claim true, the header states the limitation.

## The benchmarks

State variables and modes are given as left / right. Notes: *carried over* (see above),
*mode-keyed* (per-left-mode invariant rows, Theorem 3 at the mode-keyed invariant),
*widened cuts* (DECLINES without `RELCERT_IMPLIED_CUT=1`), *Z3-free* (the theorem has no
verdict hypothesis), *nonblocking region* (the standalone theorem carries the model's conserved-momentum
band in its right region; since 2026-10-15 the band is also in the right evolve domain;
`docs/SUITE-REDESIGN.md` §19.2), *literature* (a model taken from a cited paper; its header
states the source and what changed in the sampled form), *mode choice* (the cover needs the
existential mode choice: the right commits to the left's mode; DECLINES with
`RELCERT_NO_CHOICE=1`).

| benchmark | state vars | modes | scenario | notes |
|---|---|---|---|---|
| `acc_spoof_lag` | 2 / 2 | 1 / 1 | sensor-attack | redesigned 2026-10-26: same lag both sides |
| `acc_spoof_limp` | 1 / 1 | 2 / 4 | sensor-attack | redesigned 2026-10-27: the same two requirement rows in both modes (no longer mode-keyed), closed right guards |
| `acc_tune_lag` | 2 / 2 | 1 / 1 | degraded-controller | redesigned 2026-10-26: same lag both sides |
| `acc_tune_limp` | 1 / 1 | 2 / 4 | degraded-controller | mode-keyed, mode choice |
| `arm_plateau_crit` | 2 / 1 | 2 / 4 | model-refinement | widened cuts, Z3-free; successor sets repaired (§21) |
| `arm_plateau_slow` | 2 / 1 | 2 / 4 | model-refinement | widened cuts, Z3-free; successor sets repaired (§21) |
| `bms_chiller_undercharge` | 1 / 1 | 2 / 3 | degraded-actuator | new 2026-10-27: mode choice (the reference commits to a cooling level that is not the deployed's) |
| `canal_gate_notches` | 1 / 1 | 3 / 4 | controller-refinement | new 2026-10-27: mode choice (the reference commits to a nearby permitted notch) |
| `charger_fast_setpoints` | 1 / 1 | 5 / 5 | degraded-controller | mode-keyed, widened cuts |
| `charger_fast_tapers` | 1 / 1 | 5 / 6 | degraded-controller | mode-keyed, widened cuts |
| `drl_car_stop` | 2 / 2 | 3 / 3 | controller-refinement | literature (dRL), mode choice |
| `drl_lane_control` | 3 / 3 | 6 / 6 | controller-refinement | literature (dRL), mode choice |
| `engine_start_highidle` | 1 / 1 | 5 / 5 | controller-change | new 2026-10-27: mode-keyed, widened cuts |
| `freedm_meter` | 2 / 2 | 12 / 12 | information-flow | literature (dHL, FREEDM), mode choice |
| `gantry_speed_zones` | 2 / 2 | 3 / 1 | controller-refinement | new 2026-10-27 (replaces `match_multi_rate`): a time stretch per speed zone (3, 2, 1), multi-step covers |
| `hvac_fan_staging` | 1 / 1 | 3 / 3 | controller-refinement | new 2026-10-26 (replaces `rover_terrain_2to3`): mode choice |
| `platoon_latency` | 3 / 2 | 3 / 2 | degraded-network | new 2026-10-27: mode-keyed (AEB row), right model shared with `platoon_linkloss` |
| `platoon_linkloss` | 2 / 2 | 3 / 2 | dos-attack | redesigned 2026-10-27 (was `platoon_delay_linkloss`): mode-keyed (AEB row), CACC -> ACC fallback |
| `platoon_profiles` | 2 / 2 | 2 / 2 | controller-refinement | redesigned 2026-10-27 (was `platoon_delay_profiles`): mode-keyed (AEB row), SPORT time gap against NORMAL, right model shared with `platoon_linkloss` |
| `quad_light_airframe_20` | 2 / 2 | 1 / 1 | model-refinement | redesigned 2026-10-27: altitude coordinate, rows from the 0.8 m altitude acceptance radius, the time scaling fixed to 6/5 (`lambda_min = lambda_max = 1.2`) |
| `quad_light_lag` | 3 / 3 | 1 / 1 | model-refinement | redesigned 2026-10-27: altitude coordinate, rows from the 0.8 m altitude acceptance radius |
| `quad_light_profiles` | 2 / 2 | 1 / 3 | model-refinement | redesigned 2026-10-27: altitude coordinate, real-time conformance to the reference's SPORT profile (lambda 1); mode choice |
| `rover_ladder_2to3` | 3 / 3 | 3 / 3 | model-refinement | reinstalled 2026-10-27 on the canonical rover hierarchy (L3 / L2): clearance and heading rows, lambda 1 |
| `rover_ladder_3to6` | 6 / 6 | 3 / 3 | model-refinement | reinstalled 2026-10-27 (L6 / L3): clearance, heading and pitch rows, lambda 1 |
| `rover_ladder_6to8` | 8 / 8 | 3 / 3 | model-refinement | reinstalled 2026-10-27 (L8 / L6): + roll and rollover (LTR) rows; lambda [1, 1.25] from the timetable tolerance (S M I from the re-timed claim form, header) |
| `rover_ladder_8to12` | 12 / 12 | 3 / 3 | model-refinement | reinstalled 2026-10-27 (L12 / L8): heading, roll, rollover (LTR) and lane rows; lambda [1, 1.25] (S M I from the re-timed claim form, header) |
| `rover_terrain_2to4` | 4 / 4 | 3 / 3 | model-refinement | redesigned 2026-10-26 (was `rover_terrain_3to6`): terrain chain, wheel slip and sinkage; zone-only right plan |
| `rover_terrain_4to6` | 6 / 6 | 3 / 3 | model-refinement | redesigned 2026-10-26 (was `rover_terrain_6to8`): terrain chain, drive lag and roughness heave; right cap `w <= c_T` |
| `rover_terrain_6to12` | 12 / 12 | 3 / 3 | model-refinement | redesigned 2026-10-26: terrain chain, heave rate, bank grade, pitch, acceleration, squat; right cap `u <= c_T` |
| `rover_patrol_lag` | 3 / 2 | 4 / 4 | model-refinement | reinstalled 2026-10-27: the rover with its motor lag against the first-order planning model; lead bound as an order property up to a 3/2 re-timing (S M R B from the claim form, header) |
| `sat3w_detumble_nominal` | 6 / 6 | 1 / 2 | model-refinement | nonblocking region |
| `sat3w_detumble_phases` | 6 / 6 | 2 / 2 | model-refinement | mode-keyed, nonblocking region |
| `sat3w_detumble_weak` | 6 / 6 | 1 / 4 | degraded-actuator | nonblocking region |
| `sat_detumble_nominal` | 4 / 4 | 1 / 2 | model-refinement | nonblocking region |
| `sat_detumble_phases` | 4 / 4 | 2 / 2 | model-refinement | mode-keyed, nonblocking region |
| `sat_detumble_weak` | 4 / 4 | 1 / 4 | degraded-actuator | nonblocking region |
| `tank_dos_3to1` | 2 / 2 | 4 / 4 | dos-attack | redesigned 2026-10-27: a demand-paced four-pump station, the same staging law on both sides, the DoS holds the staging decision for up to three polls |
| `train_ato_odometry` | 1 / 1 | 3 / 3 | degraded-sensor | new 2026-10-27: stretches per pairing from 31/40 to 6/5 (`lambda_min = 0.75`) |
| `turbine_startup_gearratio` | 1 / 1 | 4 / 4 | degraded-controller | new 2026-10-27: widened cuts; right-only repositioning, pruned parking edges (the letters R P I come from the one-sided claim form, header) |
| `vehicle_hypercert` | 2 / 2 | 5 / 5 | opacity | literature (HyperCertificates), mode choice; position coordinate and start-offset row (2026-10-27) |
| `watertank` | 1 / 1 | 3 / 5 | sensor-attack | the paper's running example |
| `watertank_twospeed` | 1 / 1 | 3 / 6 | sensor-attack | redesigned 2026-10-27: six right modes (two-speed low fill, eco/boost mid fill, high, pump off), one uniform claim; per-pairing stretch, pruned `Fast -> PumpOff` |

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
  index by. A right list may be a sublist of the left one (four suite_v2 benchmarks); a
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
they enter no declared count. `freedm_meter_leaky`: the deterministic controller `batI` of the
FREEDM case study on both sides of `freedm_meter` (the battery whenever it can still charge or
discharge, the grid otherwise); a surplus at a full battery, or a demand at an empty one, goes to
the grid while a run from another level keeps it on the battery, so no matching run keeps the
meters equal. A DECLINE is
not a proof of insecurity (the certifier is sound, not complete); the source proves the leak by
exhibiting the two runs.

## Assumption 1 negative exhibit (`benchmarks/negative_wellformed/`)

`vehicle_hypercert_s8`: `vehicle_hypercert` with the position bound `s ≤ 8` in every evolve
domain (a round-2 design variant). The certifier CERTIFIES it (the relational invariant does
not see the bound), but its right model can block: every right guard admits `s = 8` with
`v > 0`, where the flow leaves the domain at once, so no evolution spans the control interval
and Assumption 1's nonblocking clause is false. The check of the successor clause alone
reports all five right modes `ok`; the two-clause check (since 2026-10-26) reports all five
`BLOCKING (leaves s <= 8.0)`, and `RELCERT_WELLFORMED_STRICT=1` DECLINES the file. It enters no
declared count (`docs/WELLFORMED.md` §4).
