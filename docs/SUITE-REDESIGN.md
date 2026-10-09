# Suite redesign — `benchmarks/suite_v2` (2026-10-08, branch `suite-redesign`)

Status: tool-side, landed on `suite-redesign` in two passes. Pass 1 (`1830a12`,
`910ae8e`): the suite and this document, no tool change. Pass 2 (2026-10-08, from
`7c5a11c`): the tool's cut channel widened (§7 L1, L2 — implied-contraction atoms and
closures of strict guard conjuncts, behind `RELCERT_IMPLIED_CUT=1`), L5 corrected
(per-mode evolve domains are the model class), five scenarios that pass 1 had dropped
re-tried and added, three weaker members retired. Pass 3 (2026-10-08, the domain
audit, §13): every evolve domain must state a PHYSICAL limit of the plant, never a
reachable-set estimate that closes the certificate; the arm family is rebuilt on
physical domains with critically / over-damped loops and its claims re-derived through
a new cut kind (§7 L7, the linear-form chain), the underdamped `arm_plateau_pd`
replaced, `arm_plateau_lowgain` added, the three per-mode-domain files dropped by the
user's choice, and `story3_rollover_ladder_rung_b` flagged; **suite size 39**.
Pass 4 (2026-10-08, §13.6 and §14): the user's decisions A1 (the story-3 rung_b attitude
domains made physical, with a settled-attitude guard entry condition) and A2 (the three
lag rungs remodeled with critically / over-damped lags, so the linear-form chain derives
the acceleration bound and the claims are re-set to the tightest certifiable slack)
installed; then branching / mode-dependent variants and the rigid-body polynomial family
(§14).
`benchmarks/suite_uniform/` and every Lean instance, pin and coverage constant are
untouched (the Lean build reads `suite_uniform`; the regression record is §12); the Lean
mechanization of the new suite — including the lift of the two new atom kinds and of
per-mode domains — is a separate later task. Every number below was measured with
`scripts/suite_v2_matrix.py` (§2) and `scripts/domain_widening.py` (§13), Z3 4.15.1,
the `relcert` binary of `049991c` (`RELCERT_IMPLIED_CUT=1` on every run but the
implied-cut counter-run), warm persistent session; the generated sections (§3, §8, §9,
the §13 table) are their output verbatim.

## 1. What changed

The user's rule: KEEP the terrain/position ladder (`refinement_ladder_rover_*` ×7,
`rover_dof_terrain_*` ×4), the three story ladders (7) and `watertank` — 19 benchmarks,
copied unchanged. Everything else was replaceable. Two replaceable benchmarks earn their
place in the matrix and are kept, copied unchanged: `match_multi_rate` (the validated
pruning exhibit: λ = 3 / 2 with budgets 3 / 2 and the pruned `DRIVE → STALL`) and
`rover3tier_rung12` (the one benchmark whose mode-dependent rows are not nested: the
ACCEL row recovers its velocity conjunct from the evolve floor, `docs/HANDOFF.md`). The
other 19 replaceable benchmarks (`arm_chain_rung1-3`, `arm_fidelity_low/mid`,
`robot_braking`, `endurance_*` ×3, `attitude_rate`, `rover3_M1`, `rover3tier_M1`,
`rover_4d_box`, `rover_coupled`, `rover_position`, `rover_terrain_M1`, `rover_tier_r1`,
`rover_drag`, `rover_attitude_cone_12dof`) are not in `suite_v2`; `shield_unreachable`
(the held-out DECLINED input) is not either.

18 new benchmarks in six families replace them. **Suite size 39**: 19 kept + 2
kept-replaceable + 18 new; 39 / 39 CERTIFIED; no two files normalize to the same model.
Pass 2 replaced `charger_fast_bulk` by `charger_fast_setpoints` (the three-set-point
charger pass 1 had dropped under L1; cells a superset) and `platoon_delay_bias` by
`platoon_delay_band` (the same platoon with its original half-open band, dropped under
L2; cells a superset), retired `acc_spoof_cruise_50` (a magnitude variant of
`acc_spoof_cruise` with identical cells) and added the three per-mode-domain scenarios
pass 1 had dropped under L5: `charger_bias_estimator`, `charger_fast_thermal`,
`heater_cycle`. Pass 3 (§13) DROPPED those three again — dropped: per-mode band domains
encode event-triggered switching, which the user chose not to claim — rebuilt the arm
family on physical domains (`arm_plateau_crit` is now the nominal critically damped
loop, `arm_plateau_slow` an over-damped worn joint, `arm_plateau_lowgain` new; the
underdamped `arm_plateau_pd` and the underdamped half-torque `_slow` are replaced) and
flagged `story3_rollover_ladder_rung_b` (§13).

| family | benchmarks | scenario kind (M7) | dims |
|---|---|---|---|
| ACC under sensor spoofing / retune | `acc_spoof_limp`, `acc_spoof_modes`, `acc_spoof_lag`, `acc_tune_limp`, `acc_tune_modes`, `acc_tune_lag` (pass 4: `_limp` replace `acc_spoof_cruise`, `acc_tune_gain`) | sensor-attack ×2, degraded-controller ×2, model-refinement ×2 (the `_lag` rungs) | 1, 2 |
| Quadrotor climb, lighter airframe | `quad_light_airframe_20`, `quad_light_profiles` (pass 4, replaces `quad_light_airframe_40`), `quad_light_lag` | model-refinement (plant mismatch, polynomial drag) | 1, 2 |
| Battery charger | `charger_fast_setpoints`, `charger_fast_tapers` | degraded-controller ×2 | 1 |
| Platoon follower, delayed link | `platoon_delay_linkloss` (pass 4, replaces `platoon_delay_band`), `platoon_delay_profiles` | sensor-attack (stale link) | 1 |
| Rover patrol (zones) | `rover_patrol_zones`, `rover_patrol_refine` (+ kept `rover3tier_rung12`, `match_multi_rate`) | degraded-actuator, model-refinement | 2, 3 |
| Arm, leading reference | `arm_plateau_crit`, `arm_plateau_slow`, `arm_plateau_profiles` (pass 4, replaces `arm_plateau_lowgain`) | model-refinement, degraded-actuator, degraded-controller | 2 / 1 |

Every new benchmark exercises at least two of M1–M6 non-vacuously (§3; `quad_light_lag`
exercises exactly two) and belongs to one scenario kind. Every mechanism is exercised by
at least three benchmarks: M1 18 (ACC ×6, quadrotor ×3, rover ×3, ladders ×6), M2 26,
M3 6 (ACC ×2, charger, platoon, rover ×2), M4 13 (ACC ×6, quadrotor ×2, charger ×2,
platoon ×2, rover), M5 6 (rover ×3, stories ×3), M6 19 (arm ×3, charger ×2, platoon ×2,
rover ×2, ACC, ladders ×9); the widened cut kinds are load-bearing in 6 (M6+: arm ×3,
charger, platoon ×2) and the linear-form chain in 3 (M6L: the arm family). No file
declares per-mode domains any more.

## 2. Method — how a cell is earned

`scripts/suite_v2_matrix.py` runs every `benchmarks/suite_v2/<name>/input.txt`:

1. `RELCERT_DEBUG=1 relcert <input>` — verdict and wall time; the `[prune]`,
   `[admissible]`, `[cut]` lines.
2. `relcert --emit-cover <input> x` — the emitted cover: per left mode the λ, the
   budget `⌈λ εL / εR⌉`, the flag row of every right mode (`jointOK, repoPre, repoPost,
   dynPre, dynPost`) and the admissible starts. The script then REPLAYS the verified
   checker's structural cover (`decideCovered`, `RelCertifier/Checker/Checker.lean`,
   over `buildCoverGraph` of `Checker/CoverEmit.lean`: nodes = flag rows with any
   certificate, edges = the file's declared successors minus the pruned ones, the
   sentinel for an uncertified target) from every admissible start, in the checker's
   alternative order (base, joint step, static reposition, dynamic reposition), and
   records the derivation it finds: the right modes on the path, the right-only
   (reposition) steps, and the largest number of distinct non-self retained successors
   at a joint step.
3. `RELCERT_NO_PRUNE=1 relcert <input>`, `RELCERT_NO_CUT=1 relcert <input>`,
   `RELCERT_NO_IMPLIED_CUT=1 relcert <input>` and `RELCERT_NO_LINEAR_CUT=1 relcert
   <input>` — the counter-runs (the third: legacy guard-conjunct cuts only; the fourth:
   closures and implied atoms kept, the linear-form chain of §7 L7 off).
4. `relcert --handoff <input>` — the cross-mode handoff queries; `vacuous` is the
   tool's own word for a benchmark whose rows are all identical.

Every run except the third counter-run sets `RELCERT_IMPLIED_CUT=1`, the widened cut
channel of §7 (off by default so that the `suite_uniform` pins keep reading the legacy
certificate); the `[cut-x]` lines are its widened atoms with kind, O1 justification and
O2 route.
5. The normalized-hash duplicate check of `docs/SUITE-DEDUPE.md` (comments, blank lines
   and the `name =` line removed, md5 of the rest).

Crediting rules (a cell is `yes` only if the counter-run or the replayed derivation
shows the mechanism mattered; everything else is printed as `no` or `vacuous`):

| cell | credited when |
|---|---|
| M1 | some left mode's emitted cover has λ ≠ 1 (the grid point the tool reports is the first that certifies); "polynomial" if some right-hand side has degree ≥ 2 in the state variables |
| M2 | some left mode's budget is ≥ 2 and its derivation takes a joint step (several right segments per left window); `+RO` if a reposition step is on the path |
| M3 | some joint step on the path has ≥ 2 distinct non-self retained successors (the self-loop is not counted, nor pruned edges), each of which covers |
| M4 | the tool prunes ≥ 1 edge AND `RELCERT_NO_PRUNE=1` DECLINES |
| M5 | the rows differ between left modes, `--handoff` is non-vacuous with every query unsat, and the benchmark is CERTIFIED |
| M6 | some mode keeps a checked cut AND `RELCERT_NO_CUT=1` DECLINES |
| M6+ | some mode keeps a WIDENED atom (closure / implied-contraction / linear-form / derived-bound, §7) AND `RELCERT_NO_IMPLIED_CUT=1` DECLINES: the cuts are load-bearing only with the widened atoms |
| M6L | some mode keeps a linear-form or derived-bound atom (§7 L7) AND `RELCERT_NO_LINEAR_CUT=1` DECLINES: the linear-form chain is load-bearing |
| M7 | the scenario kind from the file's `# scenario:` line (the kept files carry none; the script maps them: ladders and stories model-refinement, watertank sensor-attack); dimension and invariant shape computed from the file; `per-mode domains` if some side's modes declare different evolve domains (the paper's Eq. 2 model, §7 L5) |

A benchmark that keeps cuts but still certifies without them is printed `M6 vacuous`
(e.g. every ACC file keeps its band floor as a cut, but only `acc_tune_modes` needs it);
a benchmark whose fallback is pruned but which would certify anyway is printed `M4
vacuous` (one is: `rover_patrol_zones`, §5 finding 9).

## 3. Feature matrix (generated)

| benchmark | verdict (ms) | M1 λ≠1 | M2 multi-step | M3 branch | M4 prune | M5 mode-dep | M6 cut | M6+ widened cut | M6L linear-form chain | M7 scenario; dim; invariant; domains |
|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | CERTIFIED (164) | yes: CRUISE λ=5/2 (affine dynamics) | yes: CRUISE B=5 via CRUISE | no (max non-self successors at a joint step = 0) | vacuous: pruned CRUISE->DISENGAGE but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | yes: L.CRUISE: 4 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE:... | yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entr... | yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entr... | model-refinement; dim 2; linear |
| `acc_spoof_limp` | CERTIFIED (317) | yes: CRUISE λ=5/4 (affine dynamics) | yes: CRUISE B=3 via ECO/NORMAL/SPORT, LIMP B=2 via ECO/NORMAL/SPORT | yes: CRUISE branch=2, LIMP branch=2 | yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO... | yes: 3/3 handoffs unsat, rows differ | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `acc_spoof_modes` | CERTIFIED (158) | yes: CRUISE λ=5/4 (affine dynamics) | yes: CRUISE B=3 via ECO/NORMAL/SPORT | yes: CRUISE branch=2 | yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO... | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `acc_tune_lag` | CERTIFIED (153) | yes: CRUISE λ=2 (affine dynamics) | yes: CRUISE B=4 via CRUISE | no (max non-self successors at a joint step = 0) | vacuous: pruned CRUISE->DISENGAGE but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | yes: L.CRUISE: 6 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE:... | yes: L.CRUISE: (a + (1 * (v - 30))) <= 2 kind=linear-form entry=rat... | yes: L.CRUISE: (a + (1 * (v - 30))) <= 2 kind=linear-form entry=rat... | model-refinement; dim 2; linear |
| `acc_tune_limp` | CERTIFIED (320) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=3 via COMFORT/NORMAL/SPORT, LIMP B=2 via COMFORT/NORM... | yes: CRUISE branch=2, LIMP branch=2 | yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE... | yes: 3/3 handoffs unsat, rows differ | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure en... | no (no linear-form atom kept) | degraded-controller; dim 1; conjunctive |
| `acc_tune_modes` | CERTIFIED (277) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=3 via COMFORT/NORMAL/SPORT | yes: CRUISE branch=2 | yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE... | no (rows identical; handoff vacuous) | yes: L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.COMFORT: 2... | vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure en... | no (no linear-form atom kept) | degraded-controller; dim 1; conjunctive |
| `arm_plateau_crit` | CERTIFIED (214) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/ApproachB/ApproachC/Hold, Brake B... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.Accelerate: 4 conjunct(s); L.Brake: 2 conjunct(s); R.Approac... | yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=di... | yes: L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-f... | model-refinement; dim 2+-1; linear |
| `arm_plateau_profiles` | CERTIFIED (245) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/ApproachB/ApproachCfast/ApproachC... | yes: Accelerate branch=2, Brake branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.Approac... | yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=di... | yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear... | degraded-controller; dim 2+-1; linear |
| `arm_plateau_slow` | CERTIFIED (140) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/ApproachC/Hold +RO, Brake B=2 via... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.Approac... | yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=di... | yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear... | degraded-actuator; dim 2+-1; linear |
| `charger_fast_setpoints` | CERTIFIED (209) | no (λ=1 everywhere) | yes: BULK B=2 via ABSORB/FULL +RO, ABSORB B=2 via ABSORB/FULL +RO, ... | no (max non-self successors at a joint step = 1) | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conj... | yes: L.BULK: x <= 90.0 kind=implied-contraction entry=rational rout... | no (no linear-form atom kept) | degraded-controller; dim 1; linear |
| `charger_fast_tapers` | CERTIFIED (281) | no (λ=1 everywhere) | yes: BULK B=2 via FULL +RO, ABSORB B=2 via ABSORB_FAST/ABSORB_SLOW/... | yes: ABSORB branch=2 | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conj... | vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contra... | no (no linear-form atom kept) | degraded-controller; dim 1; linear |
| `match_multi_rate` | CERTIFIED (330) | yes: FAST λ=3, MEDIUM λ=2 (affine dynamics) | yes: FAST B=3 via DRIVE, MEDIUM B=2 via DRIVE | no (max non-self successors at a joint step = 0) | yes: pruned DRIVE->STALL; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.FAST: 2 conjunct(s); L.MEDIUM: 2 conjunct(s);... | vacuous: widened atoms kept (L.FAST: v <= 1.0 kind=implied-contract... | no (no linear-form atom kept) | model-refinement; dim 2; linear |
| `platoon_delay_linkloss` | CERTIFIED (309) | no (λ=1 everywhere) | yes: FOLLOW B=2 via CATCH/FOLLOW, CATCH B=2 via CATCH/FOLLOW, LOST ... | no (max non-self successors at a joint step = 1) | yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED | yes: 7/7 handoffs unsat, rows differ | yes: L.FOLLOW: 2 conjunct(s); L.CATCH: 1 conjunct(s); L.LOST: 2 con... | yes: L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; ... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `platoon_delay_profiles` | CERTIFIED (265) | no (λ=1 everywhere) | yes: FOLLOW B=2 via ASSERTIVE/FOLLOW/GENTLE, GENTLE B=2 via ASSERTI... | yes: FOLLOW branch=2, GENTLE branch=2 | yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.FOLLOW: 2 conjunct(s); L.GENTLE: 1 conjunct(s); R.FOLLOW: 2 ... | yes: L.GENTLE: g >= 29.0 kind=implied-contraction entry=rational ro... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `quad_light_airframe_20` | CERTIFIED (211) | yes: CLIMB λ=7/4 (polynomial dynamics) | yes: CLIMB B=4 via CLIMB | no (max non-self successors at a joint step = 0) | yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s);... | vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contracti... | no (no linear-form atom kept) | model-refinement; dim 1; conjunctive |
| `quad_light_lag` | CERTIFIED (143) | yes: CLIMB λ=7/4 (polynomial dynamics) | yes: CLIMB B=4 via CLIMB | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 2 conjunct(s))... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 2; linear |
| `quad_light_profiles` | CERTIFIED (490) | yes: CLIMB λ=5/2 (polynomial dynamics) | yes: CLIMB B=5 via ECO/NORMAL/SPORT | yes: CLIMB branch=2 | yes: pruned NORMAL->LIMIT, ECO->LIMIT, SPORT->LIMIT; NO_PRUNE=DECLI... | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 1 conjunct(s); R.NORMAL: 2 conjunct(s)... | vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contracti... | no (no linear-form atom kept) | model-refinement; dim 1; conjunctive |
| `refinement_ladder_rover_rung1_2to3` | CERTIFIED (227) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3+-1; conjunctive |
| `refinement_ladder_rover_rung2_3to6` | CERTIFIED (739) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `refinement_ladder_rover_rung2_6dof` | CERTIFIED (270) | yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polyno... | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 4; linear |
| `refinement_ladder_rover_rung2b_6dof` | CERTIFIED (298) | yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polyno... | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; linear |
| `refinement_ladder_rover_rung2c_6dof` | CERTIFIED (1288) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `refinement_ladder_rover_rung3_6to8` | CERTIFIED (2976) | yes: STEEP λ=9/4, MODER λ=9/4, FLAT λ=9/4 (polynomial dynamics) | yes: STEEP B=3 via FLAT/MODER/STEEP, MODER B=3 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; quadratic |
| `refinement_ladder_rover_rung4_8to12` | CERTIFIED (985) | yes: STEEP λ=17/10, MODER λ=17/10, FLAT λ=17/10 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `rover3tier_rung12` | CERTIFIED (266) | yes: ACCEL λ=7/4 (affine dynamics) | yes: ACCEL B=6 via ACCEL/COAST, COAST B=4 via ACCEL/COAST | no (max non-self successors at a joint step = 1) | no (nothing pruned) | yes: 4/4 handoffs unsat, rows differ | vacuous: cuts kept (R.ACCEL: 1 conjunct(s); R.COAST: 1 conjunct(s))... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive+linear |
| `rover_dof_terrain_rung1` | CERTIFIED (220) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive |
| `rover_dof_terrain_rung2` | CERTIFIED (348) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `rover_dof_terrain_rung3` | CERTIFIED (387) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `rover_dof_terrain_rung3_8d` | CERTIFIED (381) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; conjunctive |
| `rover_patrol_refine` | CERTIFIED (1271) | yes: SLOW λ=7/4, MEDIUM_ECO λ=7/4, MEDIUM_BRISK λ=7/4, FAST λ=5/2 (... | yes: SLOW B=4 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, MEDIUM_ECO B=4 ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | yes: 10/10 handoffs unsat, rows differ | yes: L.SLOW: 5 conjunct(s); L.MEDIUM_ECO: 5 conjunct(s); L.MEDIUM_B... | yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry... | yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry... | model-refinement; dim 3; conjunctive |
| `rover_patrol_zones` | CERTIFIED (464) | no (λ=1 everywhere) | yes: SLOW B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=2... | yes: SLOW branch=2 | vacuous: pruned SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL... | yes: 10/10 handoffs unsat, rows differ | yes: L.SLOW: 3 conjunct(s); L.MEDIUM_ECO: 3 conjunct(s); L.MEDIUM_B... | vacuous: widened atoms kept (R.STALL: v <= 0.2 kind=closure entry=w... | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `story1_attdist_rung_a_6to8` | CERTIFIED (20477) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; conjunctive |
| `story1_attdist_rung_b_12dof` | CERTIFIED (408) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `story2_lateral_rung_a_8dof` | CERTIFIED (1136) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; conjunctive |
| `story2_lateral_rung_b_12dof` | CERTIFIED (1506) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `story3_rollover_base_12dof` | CERTIFIED (1188) | yes: STEEP λ=5/4, MODER λ=5/4, FLAT λ=5/4 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; quadratic |
| `story3_rollover_ladder_rung_a` | CERTIFIED (828) | yes: STEEP λ=27/20, MODER λ=27/20, FLAT λ=27/20 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; quadratic |
| `story3_rollover_ladder_rung_b` | CERTIFIED (744) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | yes: L.STEEP: 5 conjunct(s); L.MODER: 5 conjunct(s); L.FLAT: 5 conj... | yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-for... | yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-for... | model-refinement; dim 12; quadratic |
| `watertank` | CERTIFIED (226) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Low: 1 conjunct(s); L.Mid: 1 conjunct(s); L.H... | vacuous: widened atoms kept (L.High: x <= 22.45 kind=closure entry=... | no (no linear-form atom kept) | sensor-attack; dim 1; linear |

## 4. The families — stories, parameters, measured covers

Each file's header states the story, the units, the parameters, the claim and the
measured cover; this section summarizes the design and what each member adds.

### 4.1 ACC under sensor spoofing / retune (6)

A cruise controller with a first-order speed loop `v' = k (vset − v)`, `k = 0.5 /s`,
`vset = 30 m/s`, operating band `20 ≤ v`, physical envelope `0 ≤ v ≤ 40`. The
engage/disengage logic reads the wheel-speed sensor (floor 20 m/s), the speed loop the
fused GPS/radar ground speed. The reference (right) is the stock controller with its
declared DISENGAGE fallback below the floor (`v' = −0.5 v`, sink).

* (`acc_spoof_cruise`, the single-reference spoof rung, M1 M2 M4, was REPLACED in pass 4 by
  `acc_spoof_limp`, whose cells are a superset; `acc_spoof_cruise_50` was retired in pass 2.)
* `acc_spoof_limp` (pass 4) — the spoofed CRUISE loop plus a fault-LATCHED limp-home mode
  (`LIMP: v' = 0.3 (22 − v)`, entered at 20..30 m/s, no way back) against the selectable
  ECO/NORMAL/SPORT reference; mode-dependent rows `v_L ≤ v_R ∧ v_R ≤ v_L + 9` (CRUISE) and
  `+ 12` (LIMP), each the tightest for its mode (8.5 / 11.5 DECLINED); λ = 5/4 (CRUISE,
  budget 3) and 1 (LIMP, budget 2); branching 2 in both windows; the LIMP band is a
  load-bearing cut; DISENGAGE ×3 pruned. (M1 M2 M3 M4 M5 M6)
* `acc_spoof_modes` — the reference's driver may select the set speed ECO 27 / NORMAL
  30 / SPORT 33 at any time; rows `v_L ≤ v_R ∧ v_R ≤ v_L + 9.5`; λ = 5/4, budget 3; the
  cover from NORMAL takes a joint step whose retained successors ECO and SPORT both
  cover (branching 2); three DISENGAGE edges pruned. (M1 M2 M3 M4)
* `acc_spoof_lag` — refinement of the spoofed vehicle with the powertrain lag, remodeled
  in pass 4 (§13.6): lag time constant 0.4 s (`v' = a, a' = 2.5 (a_cmd − a)`, critically
  damped, double root 1.25), engagement `23 ≤ v ≤ 30`, `|a| ≤ 2`, physical domain
  `|a| ≤ 10` (1 g). The chain `q = a + 1.25 (v − 24) ∈ [−3.25, 9.5]`, `v ∈ [21.4, 31.6]`
  DERIVES the acceleration bound; row = the lifted functional `a_L + 2.5 v_L ≤ 2.5 v_R −
  5.5` (`w = v + 0.4 a`, `w' = a_cmd`), the tightest slack on the 0.25 grid (−5.75
  DECLINED); λ = 5/2, budget 5. DISENGAGE still pruned but no longer load-bearing (the
  derived floor empties the pairing). (M1 M2 M6 M6+ M6L)
* (`acc_tune_gain`, the single-reference tune rung, M1 M2 M4, was REPLACED in pass 4 by
  `acc_tune_limp`, whose cells are a superset.)
* `acc_tune_limp` (pass 4) — the tune plus a fault-latched limp-home map (`LIMP: v' = 0.3
  (25 − v)`, entered at 22..30 m/s) against the COMFORT/NORMAL/SPORT reference; rows
  `|v_L − v_R| ≤ 2` (CRUISE; 1.5 DECLINED) and `v_L ≤ v_R + 2 ∧ v_R ≤ v_L + 6.5` (LIMP;
  6.0 DECLINED); λ = 3/2 (CRUISE, budget 3) and 1 (LIMP, budget 2); branching 2; band
  cuts load-bearing; DISENGAGE ×3 pruned. (M1 M2 M3 M4 M5 M6)
* `acc_tune_modes` — the reference's driver selects a response gain COMFORT 0.4 /
  NORMAL 0.5 / SPORT 0.6; rows `|v_L − v_R| ≤ 2`; λ = 3/2, budget 3, branching 2;
  three edges pruned; the band bounds `20 ≤ v ≤ 36` are checked cuts the COMFORT and
  SPORT segments need: NO_CUT DECLINED. (M1 M2 M3 M4 M6)
* `acc_tune_lag` — the tune with the powertrain lag, remodeled in pass 4 (§13.6): lag
  0.25 s (`a' = 4 (a_cmd − a)`, over-damped, roots 1 and 3), engagement `25 ≤ v ≤ 30`,
  `|a| ≤ 2`, domain `|a| ≤ 10`; chain `q_1 = a + (v − 30) ∈ [−7, 2]`, `q_3 = a + 3 (v −
  30) ∈ [−17, 2]`, `v ∈ [23, 32]`; row `a_L + 4 v_L ≤ 4 v_R + 2` (`w_L ≤ v_R + 0.5`),
  tightest on the 0.25 grid (1.75 DECLINED); λ = 2, budget 4; DISENGAGE pruned, not
  load-bearing. (M1 M2 M6 M6+ M6L)

### 4.2 Quadrotor climb, lighter airframe (3) — polynomial dynamics

`w' = a − c w²` (climb rate, net specific thrust, drag per unit mass); reference
`a = 4, c = 1` (terminal 2 m/s), envelope `0 ≤ w ≤ 3.5`. The deployed airframe is
lighter than the reference model assumed, so `a_L = m/m_L (a + g) − g` and
`c_L = m/m_L · c` (not a pure time scaling because of `g`).

* `quad_light_airframe_20` — 20 % lighter (`a_L = 7.45, c_L = 1.25`); rows
  `w_L ≤ w_R + 1 ∧ w_R ≤ w_L + 0.5`; λ = 7/4, budget 4; climb-rate LIMITER above 3 m/s
  (`w' = −2 w`) pruned from CLIMB (drag wins at the threshold), excluded as a start by
  `w_L ≤ 2.5 ∧ w_R ≤ w_L + 0.5`. (M1 M2 M4)
* (`quad_light_airframe_40`, M1 M2 M4, was REPLACED in pass 4 by `quad_light_profiles`.)
* `quad_light_profiles` (pass 4) — the 40 %-lighter airframe (`a_L = 9.524, c_L = 1.4`)
  against the autopilot's selectable climb-thrust profiles NORMAL `a = 4`, ECO 3.6, SPORT
  4.4 (`c = 1`), limiter above 3.2 m/s; rows `w_L ≤ w_R + 0.95 ∧ w_R ≤ w_L + 0.8` (the
  tightest pair; 0.9 / 0.75 DECLINED); the deployed engages at `w ≤ 2.2` so the limiter is
  not an admissible start; λ = 5/2 (SPORT passes from 2, NORMAL from 9/4, ECO from 5/2),
  budget 5; branching 2 from NORMAL; three LIMIT edges pruned. (M1 polynomial, M2 M3 M4)
* `quad_light_lag` — the 20 % airframe with the motor thrust lag `a' = 5 (7.45 − a)`;
  row = the lifted functional `a_L + 5 w_L ≤ 5 w_R + 12.45`; λ = 7/4, budget 4; no
  fallback (the functional cannot exclude a limiter as a start). (M1 M2)

### 4.3 Battery charger (2)

State of charge `x` (%), two-rate certified profile BULK (`15 ≤ x < 80`), ABSORB
(`80 ≤ x < 99`), FULL hold (`x ≥ 99`), CELL FAULT below 10 % (`x' = −0.01 x`, sink).

* `charger_fast_setpoints` — the certified bulk phase targets a 90 % set point
  (`x' = 0.1 (90 − x)`), the taper 100 % (`0.05 (100 − x)`); deployed: current limit
  raised 25 % (rates × 1.25); row `x_L ≤ x_R + 5`. λ = 1, budget 2: the BULK window is
  covered by the right-only reposition BULK → ABSORB → FULL and a joint hold (the
  time-scaled BULK pair would need λ = 5/4, found later, so M1 is NOT credited). The
  reposition out of BULK needs the implied atom `x_R ≤ 90` (`[cut-x] R.BULK: x <= 90.0
  kind=implied-contraction entry=rational route=shape`): `RELCERT_NO_IMPLIED_CUT=1`
  DECLINES (M6+), as the file did under pass 1 (§6). The floors `x ≥ 80`, `x ≥ 99` are
  load-bearing guard-conjunct cuts (NO_CUT DECLINED); BULK → FAULT pruned (NO_PRUNE
  DECLINED). (M2+RO M4 M6 M6+) Replaces `charger_fast_bulk` (both set points 100; cells
  M2+RO M4 M6).
* `charger_fast_tapers` — the certified profile offers two tapers, ABSORB_SLOW 0.05 /
  ABSORB_FAST 0.07, chosen when leaving BULK; in the deployed ABSORB window a reference
  still in BULK takes a joint step whose retained successors ABSORB_SLOW and
  ABSORB_FAST both cover (branching 2). (M2 M3 M4 M6)
* (dropped in pass 3, §13: `charger_fast_thermal` and `charger_bias_estimator` —
  per-mode band domains encode event-triggered switching, which the user chose not to
  claim. Their records are in §6 and in the pass-2 history of this file.)

### 4.4 Platoon follower, delayed link (2)

Gap `g` to a constant-speed leader, loops `g' = −k (g − 30)`: FOLLOW `k = 0.5`
(band `20 ≤ g < 40`), CATCH/GENTLE `0.6` and ASSERTIVE `0.7` (re-engagement,
`g ≥ 30`), BRAKE fallback below 20 m (`g' = +1.5`, sink); physical domain `0 ≤ g ≤ 60`
(`63bd64a`; the pass-2 floor of 15 m was not a limit of the plant). The
deployed follower acts on the delayed link's 1 m gap overstatement (loops toward 29 m).

* (`platoon_delay_band`, M2 M4 M6 M6+, was REPLACED in pass 4 by `platoon_delay_linkloss`,
  which keeps its half-open FOLLOW band and its closure cut.)
* `platoon_delay_linkloss` (pass 4) — the delayed-link follower of `platoon_delay_band`
  (FOLLOW `21 ≤ g < 40`, CATCH `g ≥ 30`, rows `g_L ≤ g_R + 1 ∧ g_R ≤ g_L + 3`) plus a
  LATCHED radar-only mode after a V2V link loss (`LOST: g' = −0.5 (g − 35)`, entered at any
  gap 21..60 m) with a RANGE-PROPORTIONAL row `g_L − g_R ≤ 1 + 0.45 (g_L − 21)` (slope 0.40
  DECLINED; a constant tolerance cannot follow a CATCH reference re-engaging from a wide
  gap); the handoffs into LOST hold only on LOST's guard `g_L ≥ 21` (domain-conditioned,
  7/7 unsat); λ = 1, budget 2; the closure `g ≤ 40` is load-bearing (M6+); FOLLOW → BRAKE
  pruned. (M2 M4 M5 M6 M6+)
* `platoon_delay_profiles` — two reference re-engagement profiles (closed band); the
  deployed uses the gentle one only; rows `g_L ≤ g_R + 4 ∧ g_R ≤ g_L + 3` (an assertive
  reference re-engaging from 60 m outruns the gentle deployed follower by up to 4 m; the
  1 m tolerance of `platoon_delay_band` is false for that pairing — measured, §6);
  branching 2 at FOLLOW and GENTLE. With the physical floor 0 m the re-engagement
  profiles' lower bound comes from the dynamics: the implied atoms `g ≥ 30`
  (`R.GENTLE`, `R.ASSERTIVE`) and `g ≥ 29` (`L.GENTLE`), rational, shape, are
  load-bearing (`RELCERT_NO_IMPLIED_CUT=1` DECLINED). (M2 M3 M4 M6 M6+)

### 4.5 Rover patrol, zones (2 new + 2 kept)

Odometer-keyed zones SLOW (`s < 20`, 0.6 m/s), MEDIUM (`20 ≤ s < 50`, profile ECO 0.9
or BRISK 1.1 selected on zone entry), FAST (`s ≥ 50`, 1.5 m/s); speed loops
`v' = vcmd − v`, floors 0.3 m/s, caps at the zone command; STALL fallback below 0.2 m/s
(`v' = −2 v`, sink) from every zone. Deployed: worn drivetrain, `v' = 1.25 (0.8 vcmd − v)`.

* `rover_patrol_zones` — rows `v_L ≤ v_R ∧ s_L ≤ s_R + d_zone` with
  `d = 0.5 / 1 / 2` m along the route (10 non-vacuous handoffs, all unsat); λ = 1,
  budget 2; branching 2 at SLOW; a reference in an earlier zone (or in ECO while the
  deployed runs BRISK) repositions right-only, which needs the zone caps as cuts
  (NO_CUT DECLINED); four STALL edges pruned (NO_PRUNE DECLINED). The BRISK window is
  covered from ECO by reposition at λ = 1, so the time-scaled λ = 5/4 pairing is not
  needed and M1 is NOT credited. (M2 M3 M4 M5 M6)
* `rover_patrol_refine` — the deployed with its motor lag, remodeled in pass 4 (§13.6):
  lag 0.2 s (`a' = 5 (a_cmd − a)`, critically damped, double root 2.5), zone hand-over
  only with `|a| ≤ 0.5` (bumpless transfer), domain `|a| ≤ 2` (traction); per-zone chain
  `q = a + 2.5 (v − c)`; rows = `a_L + 5 v_L ≤ 5 v_R − 0.25` (`w_L ≤ v_R − 0.05`, the
  tightest on the 0.25 grid; −0.5 DECLINED) plus the zone margins; λ = 7/4 (budget 4) in
  SLOW/MEDIUM, 5/2 (budget 5) in FAST; 10 handoffs unsat. The tight claim costs the
  branching of the pass-3 rung (at slack +0.5 the SLOW window branches; not claimed).
  (M1 M2 M5 M6 M6+ M6L)
* kept: `rover3tier_rung12` (λ = 7/4 budget 6 / λ = 1 budget 4, non-nested rows),
  `match_multi_rate` (λ = 3 / 2, pruned `DRIVE → STALL`).

### 4.6 Arm, leading reference (3) — rebuilt in the domain audit (§13)

A PD joint tracking the step command 0.5 rad from rest, `θ' = v, v' = −k_p (θ − 0.5) −
k_d v` (modes Accelerate, `v ≥ 0` below the command, and Brake, `v ≤ 0` past it);
reference = a three-step leading ramp (0.5 / 0.35 / 0.2 rad/s) to a plateau of 0.6 rad,
then Hold (`θ' = 0`, guard `θ ≥ 0.6`); εL = 2, εR = 1, so budget 2. PHYSICAL domains on
both sides: `θ ∈ [0, 1.2]` rad (the joint's range, the reference's too) and `v ∈ [−1, 1]`
rad/s (the actuator's speed limit) — no reachable-set estimate (the pass-2 family closed
the Hold phase with the cap `θ ≤ 0.65`, the simulated peak; §13). Only critically or
over-damped loops (`k_d² ≥ 4 k_p`, rational eigenvalues): their overshoot is bounded by
the LINEAR-FORM CHAIN of §7 L7, which an underdamped loop does not have. Guards are entry
conditions: Accelerate with the engagement velocity `v < 0.355`; Brake past the command
with `v ≤ 0` and the entry cap the chain proves for Accelerate, its only other
predecessor. The claim is re-set to the bound the chain derives (smallest slack that
certifies; the next 0.005 step down is DECLINED):

| rung | gains `k_p, k_d` | roots `r` | chain (Accelerate guard box `θ < 0.5, v < 0.355`) | derived bound | claim |
|---|---|---|---|---|---|
| `arm_plateau_crit` (nominal, model-refinement) | 1, 2 (critical, double −1) | 1 | `q = v + (θ − 0.5) ≤ 0.355`, `q' = −q` | `θ_L ≤ 0.5 + 0.355/1 = 0.855` | `θ_L ≤ θ_R + 0.255` (0.25 DECLINED) |
| `arm_plateau_slow` (worn joint, extra friction; degraded-actuator) | 1, 2.5 (over-damped, −0.5 and −2) | 0.5, 2 | `q_2 = v + 2 (θ − 0.5) ≤ 0.355` (and `q_0.5 ≤ 0.355`) | `θ_L ≤ 0.5 + 0.355/2 = 0.6775` (Brake: from `q_0.5 ≤ 0.08875`) | `θ_L ≤ θ_R + 0.0775` (0.075 DECLINED) |
| `arm_plateau_lowgain` (detuned; degraded-controller) | 0.5, 1.5 (over-damped, −0.5 and −1) | 0.5, 1 | `q_1 = v + (θ − 0.5) ≤ 0.355` (and `q_0.5 ≤ 0.355`) | `θ_L ≤ 0.855` (Brake: from `q_0.5 ≤ 0.1775`) | `θ_L ≤ θ_R + 0.255` |

Every chain atom is `linear-form` (O1 rational from the guard box, O2 `linear-shape`, no
Z3) or `derived-bound` (O1 rational, O2 `derived-shape` given its linear form, no Z3).
In the Hold phase the reference's frozen guard conjunct `θ_R ≥ 0.6` (legacy cut) and the
derived bound put the row's boundary at the single tangent point `(θ_L, θ_R) = (bound,
0.6)`, decided by the superlevel route. The bound is the chain's, not the true peak
(critically damped from the engagement corner: `θ = 0.5 + 0.355 t e^{−t}`, peak 0.631 at
t = 1 s): linear cuts cannot see the `e^{−t}` factor. Covers: λ = 1, budget 2; from an
approach step the reference repositions right-only up the ramp to Hold (M2+RO). All
three: NO_CUT DECLINED (M6), NO_IMPLIED_CUT DECLINED (M6+), NO_LINEAR_CUT DECLINED (M6L);
the widening test passes (§13). No fallback: the arm starts at θ = 0 and the row is
one-sided (§6). Replaced: the underdamped `arm_plateau_pd` (`k_p = k_d = 1`) and the
underdamped half-torque `_slow` (`k_p = k_d = 0.5`) — an oscillatory loop has no real
decoupling form and both certified only through the domain cap. (M2+RO M6 M6+ M6L each)

Pass 4: `arm_plateau_lowgain` is REPLACED by `arm_plateau_profiles` — the same detuned
deployed arm (row as in the table, 0.25 DECLINED) against a reference whose planner SELECTS
the final approach on entering the last segment, `ApproachCfast` (0.25 rad/s) or
`ApproachCslow` (0.15 rad/s, fragile payload); from `ApproachB` the cover takes a joint
step whose retained successors are both final approaches, both covering (branching 2).
Cells M2 M3 M6 M6+ M6L (lowgain's M2 M6 M6+ M6L plus M3).

### 4.7 Heater cycle — dropped in pass 3

`heater_cycle` (pass 2: HEAT ↔ OFF on a `55..65` hysteresis band with per-mode domains
`[50, 65]` / `[55, 70]`, rows `|T_L − T_R| ≤ 10.5`) is dropped: per-mode band domains
encode event-triggered switching, which the user chose not to claim (§13). The L6 finding
(§7) it exhibited stands as recorded.

### 4.8 Kept groups (19 + 2)

Terrain/position ladder (11), story ladders (7), watertank (1): unchanged files, their
cells measured like the rest. Five of them exercise no mechanism of M1–M6 non-vacuously
(`watertank`, `refinement_ladder_rover_rung2_3to6`, `rung2c_6dof`, `story2_lateral_*`
×2) and `story1_*` exercise only M5 — they are kept by the user's rule and reported as measured.

## 5. Design findings — the recipes that worked

These are the facts the runs established; each is visible in a trace in §9.

1. **Fallback below a floor (M4).** The validated recipe of `docs/PRUNING.md` and the
   user's experiments holds: the right source guards carry the floor (the source check
   uses `guard ∧ evolve ∧ cut` of the source only), the left guards carry a floor at
   least `d` above the threshold where `d` is the offset of a conjunct that bounds the
   LEFT variable by the RIGHT one (`x_L ≤ x_R + d`), the source flow is strictly
   positive at the threshold (set-point relaxations with the set point above the
   threshold do this; a constant-rate or zero field does not), the fallback's field
   breaks the invariant, and `εR / εL < λmin` so every cover is multi-step. A row that
   bounds the right by the left (`x_R ≤ x_L + d`) cannot exclude a floor fallback: the
   platoon's first draft was DECLINED with `[admissible] FOLLOW_L: [FOLLOW, CATCH,
   BRAKE]` for exactly this reason; the two-sided rows fix it.
2. **Offset 0 is the natural exclusion.** When the deployed is slower in value
   (over-reading spoof, worn drivetrain, delayed link), the conjunct `x_L ≤ x_R` holds
   with offset 0, and then the left and right floors can coincide (ACC, rover zones).
   When the deployed leads (retune, fast charger, light airframe) the left floor must
   sit `d` above the right one, which the deployed's own engagement logic can justify.
3. **λ ≠ 1 needs the deployed to be faster in time.** The right's stretch λ ≥ 1 means
   the right runs faster; a deployed with a higher effective loop gain (gain spoof,
   retune, lighter airframe) forces λ > 1, while an under-reading spoof or a degraded
   motor would need λ < 1 (not used; λmin = 1 throughout).
4. **Guards are entry conditions, evolve is uniform per side.** A left mode's residence
   is bounded only by the shared envelope, so every admissible cross-phase pairing must
   certify on the whole envelope. Set-point relaxations whose equilibrium lies within
   the band, speed zones ordered so that a reference AHEAD is never in a SLOWER zone
   (a slower zone ahead makes the ∀∃ claim false: `rover_patrol_zones` v1, §6), and
   closed bands that the flow keeps (cuts) are what make these pairings certify.
5. **Right-only repositioning needs a conjunct set the right's lone motion preserves
   on the whole domain.** One-sided left-leads-right rows are preserved by any right
   motion that increases the bounded variable (charging, climbing the ramp, driving);
   two-sided rows and a thermal conjunct are not (§6).
6. **Branching (M3) needs successors that are all compatible with the current left
   window**: selectable reference profiles toward the same set point (ACC gains,
   charger tapers, platoon re-engagement profiles) or faster zone profiles under a
   one-sided row (rover). Profiles must be selected on entry on the right side: mutual
   switching between two reposition-only modes never grounds (the checker's fuel runs
   out), which is how the first `rover_patrol_zones` draft was DECLINED in the FAST
   window (§6).
7. **Mode-dependent rows (M5) in a cycle** are either nested along an acyclic chain
   (rover zones: 0.5 → 1 → 2 m) or, in a cycle, equivalent on the switching states
   given the domain (`rover3tier_rung12`). Nothing else survives the domain-conditioned
   handoff; a bound cannot tighten at a switch.
8. **Lag refinements** certify with a lifted functional `a + k v` whose derivative is
   the first-order loop's rate (ACC `a + 2v`, rover `a + 2v`, quadrotor `a + 5w`), at
   the price of the envelope's slack on `a` and, with a tune, of a larger stretch.
9. **A sink fallback is handled by two devices once closures are candidates** (pass 2).
   A fallback's guard is a strict threshold (`v < 0.2`, `x < 10`) and its own flow keeps
   the closure (decay toward 0, the `shape` route), so with `RELCERT_IMPLIED_CUT=1` the
   closure is a cut of the sink and the sink becomes a joint node whenever the pairing
   is certifiable on it. In `rover_patrol_zones` the pairing region is EMPTY under the
   cuts (`v_L ≥ 0.3` from the left zone floors, `v_R ≤ 0.2` from the closure, row
   `v_L ≤ v_R`), every query is unsat, the four STALL edges need no pruning and
   `RELCERT_NO_PRUNE=1` CERTIFIES — M4 is now `vacuous` there (the only cell of pass 1
   that changed, §3). In `match_multi_rate` and the chargers the row's boundary stays
   reachable on the sink pairing (`[FAST_L] STALL=fail` at every λ; `[BULK_L]
   FAULT=fail`: the deployed charges at 15 % while the fault self-discharges) and the
   non-connection certificate remains the only route (M4 `yes`). The paper's Section 4.3
   exhibit is `match_multi_rate`; the M4 total is unchanged at 15.
10. **(Pass 2; the scenarios were dropped in pass 3, §13.) Per-mode domains are what
   hysteresis and early-switching scenarios need** (§7 L5): with each phase's band as its domain, cross-phase pairings become static
   (`x_L ≤ 75 < 80 ≤ x_R`) and the forced hand-over replaces the "unforced switching"
   objection of pass 1. The price is at the Lean side (the uniform-evolve discipline),
   not in the model or the tool.
11. **Second-order overshoot needs a linear-form chain, not a domain cap** (pass 3,
   §7 L7, §13). A threshold cut on the position of a damped second-order loop is not
   forward-invariant (the loop overshoots it from a start with the wrong velocity), and
   a domain cap at the simulated peak makes the certificate rest on the domain. For a
   critically / over-damped loop the decoupling form `q = v + r (x − c)` is bounded by
   the guard at entry and decays, and the position bound follows inside it; the claim
   is then whatever that bound supports (0.855 for the nominal arm, 0.6775 for the
   over-damped one). For an underdamped loop no such chain exists and the benchmark was
   replaced.

## 6. Scenarios tried and dropped, and why

Each was run through the tool; the deciding trace line is quoted. "model-false" means
the ∀∃ claim is false for the model as written (the tool is right to decline);
"tool scope" means the claim is plausible but outside what the certifier's query forms
can establish (§7).

| scenario | what was tried | deciding evidence | verdict |
|---|---|---|---|
| charger, three set points (BULK toward 90, ABSORB toward 100) | `charger_fast_bulk` v1 | `[repo-dyn-pre] ABSORB_L: [ABSORB, FULL]` (BULK missing): the right-only BULK flow reverses above its set point 90, which lies inside the envelope, so route A over the whole domain is sat; `ABSORB_L` DECLINED | was tool scope (L1); **now CERTIFIED** with the implied atom `x ≤ 90` (`RELCERT_IMPLIED_CUT=1`, §7 L1) — in the suite as `charger_fast_setpoints`, replacing `charger_fast_bulk` (its cells are a superset: M2+RO M4 M6 M6+) |
| charger with the cell temperature (`charger_fast_thermal`, rows `x_L ≤ x_R + 5 ∧ T_L ≤ T_R + 6`) | 2-D refinement | `[repo-dyn-pre] BULK_L: []` — the reference cooling alone lowers `T_R` and breaks the thermal conjunct, so no reposition; jointly `BULK=fail ABSORB=fail` at λ = 1 (the `x` conjunct needs 5/4) and at 5/4 the `BULK_L/ABSORB_R` pair fails on the whole envelope | was "model-false on the whole envelope"; **now CERTIFIED with per-mode evolve domains** (each phase's SoC band is its domain, §7 L5), rows `x_L ≤ x_R + 5 ∧ x_R ≤ x_L + 5 ∧ T_L ≤ T_R + 20`, λ = 5/4 — in the pass-2 suite as `charger_fast_thermal`; **dropped in pass 3** (§13.4) |
| charger with a +5 % SoC estimator bias (sensor attack) | analysis of the `BULK_L/ABSORB_R` pairing | the deployed in BULK overtakes a reference in ABSORB (`x_L ≤ x_R` fails for `x_R < 90`); the model lets the deployed stay in BULK past 75 % | was "model-false (unforced switching)"; **now CERTIFIED with per-mode evolve domains** (`x_L ≤ 75` in the deployed BULK, `x_R ≥ 80` in the reference ABSORB make the pairing static), rows `x_L ≤ x_R ∧ x_R ≤ x_L + 6`; the same file with one uniform envelope is DECLINED (`[BULK_L λ=1] ABSORB=fail`, every λ) — in the pass-2 suite as `charger_bias_estimator`; **dropped in pass 3** (§13.4) |
| rover zones ordered SLOW → TRANSIT → APPROACH (last zone slower) | `rover_patrol_zones` v1 | `[SLOW_L λ=1 #comps=2] ... APPROACH=fail` at every λ: a reference ahead in the slow approach zone cannot keep `v_L ≤ v_R` against a deployed in SLOW; APPROACH is a sink (no reposition) | model-false; zones reordered so speeds do not decrease along the route |
| rover zones with the reference switching between the MEDIUM profiles | `rover_patrol_zones` v2 | FAST_L window DECLINED: `MEDIUM_ECO ---dd`, `MEDIUM_BRISK ---dd` are reposition-only nodes whose exits include each other, so `decideCovered` never grounds | tool semantics (the all-successors reposition rule, §7 L4); profiles selected on zone entry instead |
| platoon with a CATCH mode relaxing to 35 m, or declared FOLLOW → CATCH | analysis | the right-only CATCH flow opens the gap below its set point (`g_R ≥ 40` is not flow-invariant, so no cut keeps it); `FOLLOW_L/CATCH_R` fails on `g_R ∈ [20, 60]` | model-false as drafted: re-run in pass 2 with `RELCERT_IMPLIED_CUT=1` (CATCH toward 35 / 34, guard `g ≥ 40`), the implied atom IS kept (`[cut-x] R.CATCH: g >= 35.0 kind=implied-contraction entry=rational route=shape`) and the file is still DECLINED, `[FOLLOW_L λ=1] FOLLOW=pass CATCH=fail` — the right settles 6 m wider than the deployed loop's 29 m, outside the 3 m row; both profiles relax toward 30 and CATCH's guard is `g ≥ 30` |
| platoon with its original half-open FOLLOW band `20 ≤ g < 40` | `platoon_delay_bias` v0 | DECLINED: `[repo-pre] FOLLOW_L: [] … [repo-dyn-pre]: []` and the mixed FOLLOW/CATCH segments fail without the band cap; the strict conjunct `g < 40` was not a cut candidate | was tool scope (L2); **now CERTIFIED** with the closure `g ≤ 40` (`RELCERT_IMPLIED_CUT=1`, §7 L2) — in the suite as `platoon_delay_band`, replacing the closed-band `platoon_delay_bias` (same scenario, cells a superset: M2 M4 M6 M6+) |
| platoon, deployed with two profiles too (`d1 = 1`) | `platoon_delay_profiles` v1 | DECLINED: `ASSERTIVE_L/GENTLE_R` and `GENTLE_L/ASSERTIVE_R` violate `g_L ≤ g_R + 1` from a 60 m gap (0.1 g − 4.2 > 0 for g > 42) | model-false; deployed restricted to the gentle profile, tolerance 4 m |
| platoon with the delayed link as a lag state `m` (2-D left) | analysis | the lag conjunct `m − g ≤ d` is preserved only on a bounded `m` envelope and the right-only CATCH flow still fails | not run; `platoon_delay_band` models the latency as a bias |
| heater with a hysteresis cycle HEAT ↔ OFF and a two-sided row | analysis | `HEAT_L/OFF_R` is admissible (`T_L = 55, T_R = 62`) and uncertifiable (the left heats on the whole envelope while the right cools); a one-sided row is preserved by the fault's own cooling, so the fault would not be decisive | was "model-false under unforced switching"; **now CERTIFIED with per-mode evolve domains** at the band width plus 0.5 (`heater_cycle`, rows `|T_L − T_R| ≤ 10.5`, bands `[50, 65]` / `[55, 70]`): opposite phases are admissible, so no bound below the band width is true; at exactly the band width the DI routes fail at the domain corner (§7 L6); **dropped in pass 3** (§13.4) |
| quadrotor with altitude and a HOVER plateau (M6 for the quadrotor) | analysis | `CLIMB_L/HOVER_R` is admissible (altitude unrelated) and `w_L ≤ w_R` fails against a hovering reference; HOVER is a sink | model-false; the quadrotor family has no cut-reliant member |
| quadrotor with a degraded motor (20 % less thrust) | analysis | the deployed is slower in time, so the rows need λ ≈ 0.7 < λmin = 1 | not used (λ < 1 is nowhere in the suite; the lighter-airframe rungs give the polynomial M1) |
| arm with a drop-back fallback (M4) | analysis | the arm starts at θ = 0 and the row is one-sided (`θ_L ≤ θ_R + 0.15`); a reference threshold `θ_R < T` is admissible for every `T > −0.15` and a ceiling needs a conjunct bounding `θ_R` above, which the leading reference violates | model-false; the arm family exercises M2+RO and M6 |
| arm, underdamped deployed loop on physical domains (`arm_plateau_pd`, `k_p = k_d = 1`; the half-torque `_slow`, `k_p = k_d = 0.5`) | pass-3 domain audit (§13) | both certified only with the evolve cap `θ ≤ 0.65`, a reachable-set envelope that closes the Hold phase (`0.65 ≤ 0.6 + 0.15`); `b² − 4a < 0`, so `[lin-skip] … no positive rational root` — no decoupling linear form, and a threshold cut on θ is not invariant | replaced by `arm_plateau_crit` (nominal, critical), `arm_plateau_slow` (over-damped) and `arm_plateau_lowgain`, whose claims are the chain-derived bounds (§4.6) |
| per-mode band domains (`charger_bias_estimator`, `charger_fast_thermal`, `heater_cycle`) | pass 2 (CERTIFIED with per-mode domains, §7 L5) | each phase's domain is its switching band, so the switch is forced at the band edge: an event-triggered switching semantics | **dropped (pass 3)**: per-mode band domains encode event-triggered switching, which the user chose not to claim |
| `story3_rollover_ladder_rung_b` with physical left attitude domains | widening `psi, theta_p ≥ −0.5` on the left (§13) | widened to −1: ERROR (time budget) after `[STEEP_L λ=1] STEEP=fail MODER=fail FLAT=fail` and the same at 27/20; at `ψ_L = −0.95, ω_L = 0.232, ψ_R = −0.5` (energy row at 0.25) its derivative is `−0.522 + 0.668 λ > 0` for every λ ≥ 1; `[lin-skip] STEEP: pair (psi, omega_psi) with 1 root(s) but the guard bounds neither side … no O1 constant` | pass 3: flagged. **Resolved in pass 4 (user decision, §13.6 A1)**: left attitude domains `[−1, 1]` plus the guard entry condition `ψ, ω_ψ, θ_p, ω_θ ≥ −0.25` (attitude settled at a zone switch) CERTIFIES (705 ms) with `q = ω_ψ + ψ ≥ −0.5` then `ψ ≥ −0.5` (linear-form, derived-bound, rational shapes); all three cut counter-runs DECLINE |
| ACC "launch → cruise" (pass 4): deployed tune with LAUNCH (22..28 m/s) → CRUISE (≥ 28), a tighter row in CRUISE | per-mode tightest rows | LAUNCH needs `|v_L − v_R| ≤ 2` (1.5 DECLINED), CRUISE certifies at 1.5 (1.0 DECLINED): tighter AFTER the switch, so the handoff LAUNCH → CRUISE fails; a speed-scheduled LAUNCH row `1.5 + k (28 − v_L)` (k = 0.25, 0.5, 1) DECLINED — the scheduled bound tightens during the LAUNCH residence, which the guard does not end | model-false as a mode-dependent claim (finding 7: a bound cannot tighten at a switch); replaced by the fault-LATCHED limp modes (`acc_spoof_limp`, `acc_tune_limp`), where the row loosens at the one-way switch |
| `acc_spoof_limp` v1, limp set speed 27 m/s (pass 4) | per-mode tightest | CRUISE and LIMP both tightest at `v_R ≤ v_L + 6` (5.5 DECLINED in both): identical rows, no genuine mode dependence | limp set speed lowered to 22 m/s (CRUISE 9, LIMP 12 with the selectable reference) |
| battery charger with mode-dependent rows (pass 4): per-phase two-sided rows `x_L ≤ x_R + 5 ∧ x_R ≤ x_L + e`, and a latched thermal DERATE mode | `charger_fast_tapers` + DERATE (`x' = 0.05 (100 − x)`) | two-sided rows DECLINED in BULK for `e` = 5, 10, 20 (the BULK windows are covered by right-only reposition, which a two-sided row does not survive — finding 5) and in DERATE for every `e` tried; the one-sided per-phase tightest are equal (BULK and ABSORB ≈ 1, `0.5` DECLINED; FULL vacuous) | not added: no genuine per-phase difference. Finding: `charger_fast_tapers`' stated slack 5 is not tight (1 certifies); left unchanged |
| quadrotor with a latched motor-fault mode (pass 4): left LIMP `w' = 3.0 − 1.4 w²` (and 2.5) | `quad_light_profiles` + LIMP | DECLINED for every slack `w_R ≤ w_L + e`, e = 0.8, 0.9, 1.0: the weakened deployed is slower in time near hover, which needs λ < 1 = λmin | not added (finding 3) |
| platoon link loss with a CONSTANT tolerance (pass 4): LOST `g' = −0.4 (g − 35)` / `−0.5 (g − 35)`, rows `g_L ≤ g_R + d` | `platoon_delay_linkloss` drafts | DECLINED for d = 4..10: against a CATCH reference re-engaging from 60 m the radar-only follower falls behind faster than any constant allows; with large d BRAKE becomes an admissible start at small gaps | replaced by the range-proportional row (slope 0.45 certifies, 0.40 DECLINED) |
| rigid-body nominal with the default stretch grid (pass 4) | `sat_detumble_nominal` with λ ∈ [1, 6] | CERTIFIED with pruning, but `RELCERT_NO_PRUNE=1` returns ERROR (`inconclusive Z3 verdict`, 77 s): the joint DETUMBLE segment is `incon` at λ = 3/2, 7/4, 3, 13/4, … (the exact-equality energy rows at a non-unit stretch) | the claim is stated synchronous, λ ∈ [1, 1] (§7 L8); then NO_PRUNE DECLINES |
| rigid-body rungs at the analytic tolerance (pass 4) | `sat_detumble_weak` at `d* = 0.2`, `sat_detumble_phases` at `d* = 0.08` | ERROR (`inconclusive Z3 verdict on a candidate route`): at `d*` the boundary is tangent and the cubic route-C query returns `unknown`; 0.205 / 0.085 CERTIFY, 0.15 / 0.07 DECLINE | claims at the smallest certifying slack on the 0.005 grid (§7 L8) |
| `sat_detumble_fast` (pass 4): deployed torquers upsized, `k_L = 0.625`, exact energy rows | built and run | CERTIFIED at λ = 5/4, budget 3 (M1 polynomial, M2) | not added (suite size; the family's three rungs cover nominal, degraded and refined) |

## 7. Tool limitations found; fixes made

Each limitation below was met by a sensible scenario. L1 and L2 are FIXED on this branch
(2026-10-08, second pass; tool side only, the Lean lift of the new certificate is a later
pass). L3 and L4 stand as recorded. L5 was misattributed to the model class and is
corrected (its three scenarios were then dropped by the user's choice in pass 3). L6 is
new. L7 is FIXED in pass 3 (the domain audit). None weakens a soundness check; all are
incompleteness.

* **L1 — FIXED: implied atoms from the dynamics.** Right-only reposition is a
  whole-domain route-A certificate (`checkDynRepo`: `UNSAT(evolveL ∧ evolveR ∧ cuts
  [∧ guardL] ∧ ġ > 0)`, left frozen). A contractive right mode whose set point lies inside
  the envelope reverses the bounded variable above it, so it never repositioned, although
  from its own guard its flow never gets there (`charger_fast_bulk` v1: `[repo-dyn-pre]
  ABSORB_L: [ABSORB, FULL]`). The fix (`Checker/EvolStrengtheningX.lean`,
  `OracleAPI.checkedCutX`, behind `RELCERT_IMPLIED_CUT=1`): for a mode whose field for `x`
  is a contraction `x' = k (c − x)`, `k > 0` (`contractEq`: the three shapes the `shape`
  route already recognized plus `k (x − c)` with `k < 0`), the atoms `x ≤ c` and `x ≥ c`
  are offered as cut candidates of KIND `impliedContract`. They are the tightest
  flow-invariant half-lines the guard can imply (`{x ≤ K}` is invariant iff `K ≥ c`, and
  a guard cap below `c` makes `x ≤ c` implied; a cap above `c` makes the cap itself, a
  guard conjunct or its closure, the tighter atom). O1 (entry) is the IMPLICATION
  `guard → atom`: decided by rational comparison when the guard carries a threshold
  conjunct on `x` at least as tight (`guardImpliesRational`, no Z3; recorded as
  `CutEntry.rational`), otherwise by one counted Z3 query `UNSAT(guard ∧ ¬atom)`
  (`CutEntry.z3`). O2 (invariance) is the `shape` route over `contractEq`'s grammar
  (`contractShapeOKX`, equilibrium on the safe side, no Z3), with the frozen and the two
  DI routes as fallback. `charger_fast_setpoints` (the dropped three-set-point charger,
  §6) now certifies: `[cut-x] R.BULK: x <= 90.0 kind=implied-contraction entry=rational
  route=shape` and `[repo-dyn-pre] BULK_L: [BULK, ABSORB, FULL]`; with
  `RELCERT_NO_IMPLIED_CUT=1` it is DECLINED exactly as before (M6+).
* **L2 — FIXED: closures of strict guard atoms.** `cutAtoms` takes `<=`/`>=` conjuncts
  only, so a strict band bound `g < 40` whose closure `g ≤ 40` is flow-invariant was not a
  candidate and the platoon had to be written with closed bands. The fix (same module and
  switch): every strict guard conjunct `x < k` / `x > k` offers its closure `x ≤ k` /
  `x ≥ k` as a candidate of KIND `closure`; O1 holds by weakening (`CutEntry.weakening`);
  O2 as for any closed atom. `platoon_delay_band` (the platoon with its original
  half-open FOLLOW band `20 ≤ g < 40`) now certifies: `[cut-x] R.FOLLOW: g <= 40.0
  kind=closure entry=weakening route=shape`; `RELCERT_NO_IMPLIED_CUT=1` DECLINES (M6+).
* **The extended certificate.** With the switch on, every kept atom — the legacy guard
  conjuncts included, tagged `CutKind.guardConj` / `CutEntry.membership` with their
  legacy routes — is listed in one `EvolStrengtheningX` value (`atom`, `kind`, `entry`,
  `route`), printed by `--emit-cuts` as a second literal `<defname>X` after the unchanged
  legacy `<defname>`; `evolStrengtheningWFX` is its kernel-decidable well-formedness
  (guard-conjunct membership, closure of a strict conjunct, implied candidate of a
  recognized contraction, rational O1 re-checked, shape/frozen re-checked; the Z3-entry
  and DI-route obligations are left for the lift's Z3 leaf). An atom already kept is not
  offered twice (`atomEqQ`, rational equality of the constants), and an atom that passes
  the extended `shape` route is re-offered even where the legacy DI routes dropped it
  (the tangent case: `R.CATCH g >= 30.0` in the platoon, implied-contraction, rational).
* **Compatibility.** The channel is OFF by default: `checkedCut`, `cutAtoms`,
  `contractShapeOK`, `EvolStrengthening` and `evolStrengtheningWF` are untouched (the new
  definitions live in a new module, so nothing downstream of
  `Checker/EvolStrengthening.lean` was re-elaborated), and with the switch off the tool
  emits byte-for-byte what it did: all 41 `suite_uniform` `--emit-cuts` literals, all 41
  `--emit-cover` literals, every verdict and every `RELCERT_DEBUG` line were diffed
  against the `main` binary — identical (§12). `RELCERT_IMPLIED_CUT=1` is set by
  `scripts/suite_v2_matrix.py` for every `suite_v2` run except the counter-run
  `RELCERT_NO_IMPLIED_CUT=1`, which overrides it (legacy cuts only); the matrix's M6+
  cell is `yes` when a widened atom is kept AND that counter-run DECLINES.
* **L3 — the λ grid reports the first certifying point.** `lambdaCandidates` tries
  `εR/εL` and then 21 grid points from λmin; the tool reports the first that covers,
  which may be a reposition cover at λ = 1 even where the time-scaled joint pairing
  would need λ > 1 (`charger_fast_setpoints`, `rover_patrol_zones`). The matrix credits M1
  only from the reported λ, so those two are `M1 no` by construction. Not a defect; a
  "minimal λ" search is not what the tool claims.
* **L4 — the reposition rule's all-exits obligation does not ground through a cycle of
  reposition-only modes** (`decideCovered`: every non-self exit must cover at the same
  budget and σ, fuel-bounded). Two selectable profiles that may switch into each other
  on the right can only be covered if at least one is jointly certified. The design
  (select the profile on entry) is the physically honest statement anyway.
* **L5 — CORRECTED: per-mode evolve domains are the model class; "uniform evolve" is a
  mechanization discipline.** The first pass recorded "guards are entry-only, evolve is
  uniform per side" as the paper's model class and dropped the thermal charger, the
  estimator-bias charger and the heater cycle under it. That was wrong on the model: the
  paper's Eq. 2 gives each mode its OWN evolution domain, the parser accepts per-mode
  domains, and the tool's flow queries already use them (`segParts`/`segPartsRO` take
  `mL.evolve ∧ mR.evolve` of the pair). Only the Lean lift's uniform-evolve discipline
  (`UniformEvol.lean`, the handoff runner's `uniformEvolveR`) does not cover per-mode
  domains yet — that generalization is the later Lean pass. With each phase's band as
  its domain (the phase cannot persist beyond its switching threshold, so the switches
  are forced), all three scenarios certified in pass 2 (§6): `charger_bias_estimator` (whose
  uniform-envelope control is DECLINED), `charger_fast_thermal` (λ = 5/4) and
  `heater_cycle` (at the band width plus the L6 margin). Pass 3 dropped all three
  (§13.4): per-mode band domains encode event-triggered switching, which the user
  chose not to claim; the matrix's per-mode-domains count is now 0.
* **L6 — a row boundary at a domain corner.** With closed per-mode domains, a two-sided
  row whose slack equals the hysteresis band width (`T_L ≤ T_R + 10` for bands
  `[50, 65]` / `[55, 70]`) is true of the model but DECLINED: at the corner
  `(T_L, T_R) = (65, 55)` the boundary `g = 0` lies in both closed domains with `ġ > 0`
  (the left heats, the right cools), although the flow exits both domains there, so the
  trajectory cannot continue in these modes. Differential induction with an evolution
  domain cannot use that (routes A, B, C are all sat), and the certifier has no
  domain-exit argument. The suite states the claim with a 0.5 margin (`heater_cycle`:
  `T_L ≤ T_R + 10.5`); a sound fix would be a per-face Nagumo-style exit check at the
  domain boundary, not made here.

* **L7 — FIXED (pass 3): the overshoot of a damped second-order loop.** A threshold cut
  on one variable cannot bound it (the only invariant half-lines of a single coordinate
  are those the domain already gives) and a quadratic form cannot bound it tightly (its
  level sets are centrally symmetric about the equilibrium); the arm family had closed
  its Hold phase with an evolve cap at the simulated peak instead, which the domain audit
  forbids (§13). The fix (`Checker/EvolStrengtheningX.lean` §L7, `OracleAPI.checkedCutX`,
  behind `RELCERT_IMPLIED_CUT=1`; `RELCERT_NO_LINEAR_CUT=1` switches only these two kinds
  off): a mode's pair `x' = y, y' = −a (x − c) − b y` is recognized SYNTACTICALLY
  (`secondOrderPairs`); for every rational root `r` of `r² − b r + a = 0` with
  `0 < r < b` (`pairRoots`; critically / over-damped with a rational-square
  discriminant) the linear form `q = y + r (x − c)` satisfies `q' = −(b − r) q`. Round 1
  (`CutKind.linearForm`): `q ≤ sup q` / `q ≥ inf q` over the guard's threshold box —
  O1 rational, O2 `linearShape` (rational) or DI-B/A/C. Round 2
  (`CutKind.derivedBound`, STRATIFIED, recorded in the atom's `given` field): from
  `q ≤ K` the bound `x ≤ c + K/r` — O1 rational or one Z3 query, O2 `derivedShape`
  (rational) or DI-B/A/C over `evolve ∧ q ≤ K`; DI-C is the superlevel route
  `UNSAT(dom ∧ g ≥ 0 ∧ ġ > 0)`, the only one of the three that decides the tangent point.
  No other candidate generation is attempted (the channel is not an invariant
  synthesizer). Exercised by the three arm rungs (§4.6); a pair whose guard gives no box
  is skipped with a `[lin-skip]` debug line (`story3_rollover_ladder_rung_b`, §13).
  `CutRouteX` extends the legacy `CutRoute` (unchanged) by the three new routes; the
  emitted `<defname>X` literal now carries `given`. Default path: unchanged (§12).

* **L8 — NEW (pass 4): Z3 inconclusive on cubic flow queries at tangency and at non-unit
  stretch.** The rigid-body family's energy rows need Z3 to see the cancellation of the
  gyroscopic cubic terms. Two places return `unknown` and the run is an ERROR, not a
  decline: (i) at the analytic tolerance `d*` the row's boundary is tangent to the flow
  (`sat_detumble_weak` at 0.2, `sat_detumble_phases` at 0.08: `ERROR [inconclusive Z3
  verdict on a candidate route]`), so the suite states the smallest certifying slack on a
  0.005 grid (0.205, 0.085); (ii) with the default stretch grid the exact-equality rows of
  `sat_detumble_nominal` are `incon` at λ = 3/2, 7/4, 3, 13/4, …, which turns the
  `RELCERT_NO_PRUNE=1` counter-run into an ERROR (77 s) — the claim is therefore stated
  synchronous (λ ∈ [1, 1]). Sound (an inconclusive verdict never certifies); an
  incompleteness of the NRA back-end at tangent boundaries. Also observed (scope of L7, not
  new): the linear-form chain needs RATIONAL eigenvalues — the spoofed ACC with a 0.25 s lag
  is over-damped with roots `−2 ± √1.5` and gets no chain, so `acc_spoof_lag` uses the
  critically damped 0.4 s lag (§13.6).

Observed, not a limitation: the one-sided left-leads-right rows and the checked cuts
let the certifier certify every mixed-profile and cross-zone pairing it needed; all 39
inputs certify in under 0.6 s except the 6–12-dof ladders (`story1_attdist_rung_a_6to8`
≈ 20 s, `story3_rollover_ladder_rung_b` ≈ 5 s, the others ≤ 3 s).

## 8. Totals and the proposed Table-1 grouping (generated)

| mechanism | benchmarks (non-vacuous) | count |
|---|---|---|
| M1 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_spoof_modes`, `acc_tune_lag`, `acc_tune_limp`, `acc_tune_modes`, `match_multi_rate`, `quad_light_airframe_20`, `quad_light_lag`, `quad_light_profiles`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover3tier_rung12`, `rover_patrol_refine`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a` | 18 |
| M2 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_spoof_modes`, `acc_tune_lag`, `acc_tune_limp`, `acc_tune_modes`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `charger_fast_setpoints`, `charger_fast_tapers`, `match_multi_rate`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `quad_light_airframe_20`, `quad_light_lag`, `quad_light_profiles`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover3tier_rung12`, `rover_patrol_refine`, `rover_patrol_zones`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a` | 26 |
| M3 | `acc_spoof_limp`, `acc_spoof_modes`, `acc_tune_limp`, `acc_tune_modes`, `arm_plateau_profiles`, `charger_fast_tapers`, `platoon_delay_profiles`, `quad_light_profiles`, `rover_patrol_zones` | 9 |
| M4 | `acc_spoof_limp`, `acc_spoof_modes`, `acc_tune_limp`, `acc_tune_modes`, `charger_fast_setpoints`, `charger_fast_tapers`, `match_multi_rate`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `quad_light_airframe_20`, `quad_light_profiles` | 11 |
| M5 | `acc_spoof_limp`, `acc_tune_limp`, `platoon_delay_linkloss`, `rover3tier_rung12`, `rover_patrol_refine`, `rover_patrol_zones`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof`, `story3_rollover_ladder_rung_b` | 9 |
| M6 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_tune_lag`, `acc_tune_limp`, `acc_tune_modes`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `charger_fast_setpoints`, `charger_fast_tapers`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `refinement_ladder_rover_rung1_2to3`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover_dof_terrain_rung1`, `rover_dof_terrain_rung2`, `rover_dof_terrain_rung3`, `rover_dof_terrain_rung3_8d`, `rover_patrol_refine`, `rover_patrol_zones`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a`, `story3_rollover_ladder_rung_b` | 24 |
| M6+ | `acc_spoof_lag`, `acc_tune_lag`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `charger_fast_setpoints`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b` | 10 |
| M6L | `acc_spoof_lag`, `acc_tune_lag`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b` | 7 |
| per-mode domains |  | 0 |

| group | count | dim (L/R) | invariant forms | dynamics | discrete structure (modes L/R; pruned fallbacks; mode-dep. rows; cuts; widened cuts; linear-form chains; per-mode domains) |
|---|---|---|---|---|---|
| ACC under sensor spoofing / retune | 6 | 1, 2 | conjunctive, linear | affine | modes 1-2 / 2-4; 4 with a pruned fallback; 2 mode-dependent; 5 cut-reliant; 2 widened-cut-reliant; 2 linear-form-reliant; 0 per-mode domains |
| Quadrotor climb, lighter airframe | 3 | 1, 2 | conjunctive, linear | polynomial | modes 1-1 / 1-4; 2 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Battery charger | 2 | 1 | linear | affine | modes 3-3 / 4-5; 2 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Platoon follower, delayed link | 2 | 1 | conjunctive | affine | modes 2-3 / 3-4; 2 with a pruned fallback; 1 mode-dependent; 2 cut-reliant; 2 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Rover patrol (zones) | 4 | 2, 3 | conjunctive, conjunctive+linear, linear | affine | modes 2-4 / 2-5; 1 with a pruned fallback; 3 mode-dependent; 2 cut-reliant; 1 widened-cut-reliant; 1 linear-form-reliant; 0 per-mode domains |
| Arm, leading reference | 3 | 2/1 | linear | affine | modes 2-2 / 4-5; 0 with a pruned fallback; 0 mode-dependent; 3 cut-reliant; 3 widened-cut-reliant; 3 linear-form-reliant; 0 per-mode domains |
| Terrain/position ladder | 11 | 3/2, 3, 4, 6, 8, 12 | conjunctive, linear, quadratic | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 7 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Story ladders | 7 | 8, 12 | conjunctive, quadratic | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 3 mode-dependent; 3 cut-reliant; 1 widened-cut-reliant; 1 linear-form-reliant; 0 per-mode domains |
| Watertank | 1 | 1 | linear | affine | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| **total** | **39** | | | | |

Duplicate check: no two benchmarks normalize to the same model; no two benchmarks differ only in tolerance constants (rows' numerals masked)

## 9. Per-benchmark run records (generated)

### `acc_spoof_lag`

* family: ACC under sensor spoofing / retune; scenario: model-refinement; dims L/R 2/2; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `c6dd3244026b`
* `relcert`: **CERTIFIED** (164 ms); `[prune] acc_spoof_lag: [CRUISE->DISENGAGE]`; NO_PRUNE: **CERTIFIED** (218 ms); NO_CUT: **DECLINED** (333 ms); NO_IMPLIED_CUT: **DECLINED** (366 ms); NO_LINEAR_CUT: **DECLINED** (378 ms); domains: uniform
* `[cut] L.CRUISE: 4 conjunct(s)`
* `[cut] R.CRUISE: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.CRUISE: (a + (1.25 * (v - 24))) >= -3.25 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.CRUISE: v <= 31.6 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) <= 9.5]`
* `[cut-x] L.CRUISE: v >= 21.4 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) >= -3.25]`
* `[cut-x] R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (92 ms)
* cover `CRUISE_L`: λ = 5/2, budget 5, admissible ['CRUISE'], flags {'CRUISE': 'j----', 'DISENGAGE': 'j----'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=5)->[CRUISE@4, CRUISE@4]; CRUISE:joint(B=4)->[CRUISE@3, CRUISE@3]; CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/2 (affine dynamics); **M2** yes: CRUISE B=5 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned CRUISE->DISENGAGE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.CRUISE: 4 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1.25 * (v - 24))) >= -3.25 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 31.6 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) <= 9.5]; L.CRUISE: v >= 21.4 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) >= -3.25]; R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape; NO_IMPLIED=DECLINED; **M6L** yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1.25 * (v - 24))) >= -3.25 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 31.6 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) <= 9.5]; L.CRUISE: v >= 21.4 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) >= -3.25]; NO_LINEAR=DECLINED

### `acc_spoof_limp`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `900d3e553813`
* `relcert`: **CERTIFIED** (317 ms); `[prune] acc_spoof_limp: [NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1162 ms); NO_CUT: **DECLINED** (1154 ms); NO_IMPLIED_CUT: **CERTIFIED** (292 ms); NO_LINEAR_CUT: **CERTIFIED** (318 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] L.LIMP: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.ECO: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB`
* `[cut-x] R.NORMAL: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.ECO: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.SPORT: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL, ECO, SPORT]`
* `[admissible] LIMP_L: [NORMAL, ECO, SPORT]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (100 ms)
* cover `CRUISE_L`: λ = 5/4, budget 3, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j----', 'ECO': 'j----', 'SPORT': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1); ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]`
    * from `ECO`: `ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; SPORT:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; ECO:base(B=1)`
* cover `LIMP_L`: λ = 1, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j----', 'ECO': 'j----', 'SPORT': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1)`
    * from `ECO`: `ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/4 (affine dynamics); **M2** yes: CRUISE B=3 via ECO/NORMAL/SPORT, LIMP B=2 via ECO/NORMAL/SPORT; **M3** yes: CRUISE branch=2, LIMP branch=2; **M4** yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.ECO: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB; R.NORMAL: v <= 40.0 kind=closure entry=weakening route=shape; R.ECO: v <= 40.0 kind=closure entry=weakening route=shape; R.SPORT: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `acc_spoof_modes`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 1/1; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9ba6f4802d67`
* `relcert`: **CERTIFIED** (158 ms); `[prune] acc_spoof_modes: [NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1154 ms); NO_CUT: **CERTIFIED** (231 ms); NO_IMPLIED_CUT: **CERTIFIED** (219 ms); NO_LINEAR_CUT: **CERTIFIED** (196 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.ECO: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB`
* `[cut-x] R.NORMAL: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.ECO: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.SPORT: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL, ECO, SPORT]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (22 ms)
* cover `CRUISE_L`: λ = 5/4, budget 3, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j----', 'ECO': 'j----', 'SPORT': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1); ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]`
    * from `ECO`: `ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; SPORT:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; ECO:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/4 (affine dynamics); **M2** yes: CRUISE B=3 via ECO/NORMAL/SPORT; **M3** yes: CRUISE branch=2; **M4** yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.ECO: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB; R.NORMAL: v <= 40.0 kind=closure entry=weakening route=shape; R.ECO: v <= 40.0 kind=closure entry=weakening route=shape; R.SPORT: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `acc_tune_lag`

* family: ACC under sensor spoofing / retune; scenario: model-refinement; dims L/R 2/2; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `fd83c1cb18b6`
* `relcert`: **CERTIFIED** (153 ms); `[prune] acc_tune_lag: [CRUISE->DISENGAGE]`; NO_PRUNE: **CERTIFIED** (196 ms); NO_CUT: **DECLINED** (342 ms); NO_IMPLIED_CUT: **DECLINED** (363 ms); NO_LINEAR_CUT: **DECLINED** (353 ms); domains: uniform
* `[cut] L.CRUISE: 6 conjunct(s)`
* `[cut] R.CRUISE: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] L.CRUISE: (a + (1 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.CRUISE: (a + (1 * (v - 30))) >= -7 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.CRUISE: (a + (3 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.CRUISE: (a + (3 * (v - 30))) >= -17 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.CRUISE: v <= 32 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) <= 2]`
* `[cut-x] L.CRUISE: v >= 23 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) >= -7]`
* `[cut-x] R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (92 ms)
* cover `CRUISE_L`: λ = 2, budget 4, admissible ['CRUISE'], flags {'CRUISE': 'j----', 'DISENGAGE': 'j----'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=4)->[CRUISE@3, CRUISE@3]; CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=2 (affine dynamics); **M2** yes: CRUISE B=4 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned CRUISE->DISENGAGE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.CRUISE: 6 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.CRUISE: (a + (1 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1 * (v - 30))) >= -7 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) >= -17 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 32 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) <= 2]; L.CRUISE: v >= 23 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) >= -7]; R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape; NO_IMPLIED=DECLINED; **M6L** yes: L.CRUISE: (a + (1 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1 * (v - 30))) >= -7 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) >= -17 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 32 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) <= 2]; L.CRUISE: v >= 23 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) >= -7]; NO_LINEAR=DECLINED

### `acc_tune_limp`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `68a8a66b01d8`
* `relcert`: **CERTIFIED** (320 ms); `[prune] acc_tune_limp: [NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1061 ms); NO_CUT: **DECLINED** (993 ms); NO_IMPLIED_CUT: **CERTIFIED** (286 ms); NO_LINEAR_CUT: **CERTIFIED** (370 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] L.LIMP: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.COMFORT: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL, COMFORT, SPORT]`
* `[admissible] LIMP_L: [NORMAL, COMFORT, SPORT]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (20 ms)
* cover `CRUISE_L`: λ = 3/2, budget 3, admissible ['NORMAL', 'COMFORT', 'SPORT'], flags {'NORMAL': 'j----', 'COMFORT': 'j----', 'SPORT': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['COMFORT', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, COMFORT@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:base(B=1); SPORT:base(B=1); COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]`
    * from `COMFORT`: `COMFORT:joint(B=3)->[COMFORT@2, COMFORT@2, NORMAL@2]; COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; COMFORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; SPORT:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; COMFORT:base(B=1)`
* cover `LIMP_L`: λ = 1, budget 2, admissible ['NORMAL', 'COMFORT', 'SPORT'], flags {'NORMAL': 'j----', 'COMFORT': 'j----', 'SPORT': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['COMFORT', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:base(B=1); SPORT:base(B=1)`
    * from `COMFORT`: `COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; COMFORT:base(B=1); NORMAL:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=3 via COMFORT/NORMAL/SPORT, LIMP B=2 via COMFORT/NORMAL/SPORT; **M3** yes: CRUISE branch=2, LIMP branch=2; **M4** yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.COMFORT: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `acc_tune_modes`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 1/1; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `79594af327d8`
* `relcert`: **CERTIFIED** (277 ms); `[prune] acc_tune_modes: [NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1062 ms); NO_CUT: **DECLINED** (973 ms); NO_IMPLIED_CUT: **CERTIFIED** (283 ms); NO_LINEAR_CUT: **CERTIFIED** (216 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.COMFORT: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL, COMFORT, SPORT]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (84 ms)
* cover `CRUISE_L`: λ = 3/2, budget 3, admissible ['NORMAL', 'COMFORT', 'SPORT'], flags {'NORMAL': 'j----', 'COMFORT': 'j----', 'SPORT': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['COMFORT', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, COMFORT@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:base(B=1); SPORT:base(B=1); COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]`
    * from `COMFORT`: `COMFORT:joint(B=3)->[COMFORT@2, COMFORT@2, NORMAL@2]; COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; COMFORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; SPORT:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; COMFORT:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=3 via COMFORT/NORMAL/SPORT; **M3** yes: CRUISE branch=2; **M4** yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.COMFORT: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `arm_plateau_crit`

* family: Arm, leading reference; scenario: model-refinement; dims L/R 2/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `90ef24b3b08e`
* `relcert`: **CERTIFIED** (214 ms); `[prune] arm_plateau_crit: []`; NO_PRUNE: **CERTIFIED** (184 ms); NO_CUT: **DECLINED** (419 ms); NO_IMPLIED_CUT: **DECLINED** (366 ms); NO_LINEAR_CUT: **DECLINED** (388 ms); domains: uniform
* `[cut] L.Accelerate: 4 conjunct(s)`
* `[cut] L.Brake: 2 conjunct(s)`
* `[cut] R.ApproachA: 1 conjunct(s)`
* `[cut] R.ApproachB: 1 conjunct(s)`
* `[cut] R.ApproachC: 1 conjunct(s)`
* `[cut] R.Hold: 2 conjunct(s)`
* `[cut-x] L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB`
* `[cut-x] L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]`
* `[cut-x] L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]`
* `[cut-x] R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen`
* `[admissible] Accelerate_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `[admissible] Brake_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (82 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': 'jr-dd', 'ApproachC': 'jr-dd', 'Hold': 'jrrdd'}, kinds ['base', 'joint'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only False
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': '---dd', 'ApproachB': 'j--dd', 'ApproachC': 'j--dd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:repoDyn(B=2,preJ)->[ApproachB@2]; ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/ApproachB/ApproachC/Hold, Brake B=2 via ApproachB/ApproachC/Hold +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.Accelerate: 4 conjunct(s); L.Brake: 2 conjunct(s); R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachC: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB; L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** yes: L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; NO_LINEAR=DECLINED

### `arm_plateau_profiles`

* family: Arm, leading reference; scenario: degraded-controller; dims L/R 2/1; modes L/R 2/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `a1d06af51c8d`
* `relcert`: **CERTIFIED** (245 ms); `[prune] arm_plateau_profiles: []`; NO_PRUNE: **CERTIFIED** (232 ms); NO_CUT: **DECLINED** (440 ms); NO_IMPLIED_CUT: **DECLINED** (500 ms); NO_LINEAR_CUT: **DECLINED** (437 ms); domains: uniform
* `[cut] L.Accelerate: 6 conjunct(s)`
* `[cut] L.Brake: 3 conjunct(s)`
* `[cut] R.ApproachA: 1 conjunct(s)`
* `[cut] R.ApproachB: 1 conjunct(s)`
* `[cut] R.ApproachCfast: 1 conjunct(s)`
* `[cut] R.ApproachCslow: 1 conjunct(s)`
* `[cut] R.Hold: 2 conjunct(s)`
* `[cut-x] L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB`
* `[cut-x] L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]`
* `[cut-x] L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.1775 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.1775]`
* `[cut-x] R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen`
* `[admissible] Accelerate_L: [ApproachA, ApproachB, ApproachCfast, ApproachCslow, Hold]`
* `[admissible] Brake_L: [ApproachA, ApproachB, ApproachCfast, ApproachCslow, Hold]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (71 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': 'jr-dd', 'ApproachCfast': 'jr-dd', 'ApproachCslow': 'jr-dd', 'Hold': 'jrrdd'}, kinds ['base', 'joint'], path modes ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], branching 2, right-only False
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachCfast@1, ApproachCslow@1, ApproachB@1]; ApproachB:base(B=1); ApproachCfast:base(B=1); ApproachCslow:base(B=1)`
    * from `ApproachCfast`: `ApproachCfast:joint(B=2)->[ApproachCfast@1, Hold@1, ApproachCfast@1]; ApproachCfast:base(B=1); Hold:base(B=1)`
    * from `ApproachCslow`: `ApproachCslow:joint(B=2)->[ApproachCslow@1, Hold@1, ApproachCslow@1]; ApproachCslow:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': 'j--dd', 'ApproachCfast': 'j--dd', 'ApproachCslow': 'j--dd', 'Hold': 'jrrdd'}, kinds ['base', 'joint'], path modes ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], branching 2, right-only False
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachCfast@1, ApproachCslow@1, ApproachB@1]; ApproachB:base(B=1); ApproachCfast:base(B=1); ApproachCslow:base(B=1)`
    * from `ApproachCfast`: `ApproachCfast:joint(B=2)->[ApproachCfast@1, Hold@1, ApproachCfast@1]; ApproachCfast:base(B=1); Hold:base(B=1)`
    * from `ApproachCslow`: `ApproachCslow:joint(B=2)->[ApproachCslow@1, Hold@1, ApproachCslow@1]; ApproachCslow:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/ApproachB/ApproachCfast/ApproachCslow/Hold, Brake B=2 via ApproachA/ApproachB/ApproachCfast/ApproachCslow/Hold; **M3** yes: Accelerate branch=2, Brake branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachCfast: 1 conjunct(s); R.ApproachCslow: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB; L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.1775 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.1775]; R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.1775 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.1775]; NO_LINEAR=DECLINED

### `arm_plateau_slow`

* family: Arm, leading reference; scenario: degraded-actuator; dims L/R 2/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `19259816447b`
* `relcert`: **CERTIFIED** (140 ms); `[prune] arm_plateau_slow: []`; NO_PRUNE: **CERTIFIED** (221 ms); NO_CUT: **DECLINED** (383 ms); NO_IMPLIED_CUT: **DECLINED** (454 ms); NO_LINEAR_CUT: **DECLINED** (352 ms); domains: uniform
* `[cut] L.Accelerate: 6 conjunct(s)`
* `[cut] L.Brake: 3 conjunct(s)`
* `[cut] R.ApproachA: 1 conjunct(s)`
* `[cut] R.ApproachB: 1 conjunct(s)`
* `[cut] R.ApproachC: 1 conjunct(s)`
* `[cut] R.Hold: 2 conjunct(s)`
* `[cut-x] L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB`
* `[cut-x] L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: (v + (2 * (theta - 0.5))) >= -1 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Accelerate: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (2 * (theta - 0.5))) <= 0.355]`
* `[cut-x] L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.08875 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Brake: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.Brake: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.08875]`
* `[cut-x] R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen`
* `[admissible] Accelerate_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `[admissible] Brake_L: [ApproachB, ApproachC, Hold]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (22 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': '---dd', 'ApproachC': 'jr-dd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:base(B=1)`
    * from `ApproachB`: `ApproachB:repoDyn(B=2,preJ)->[ApproachC@2]; ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': 'j--dd', 'ApproachC': 'j--dd', 'Hold': 'jrrdd'}, kinds ['base', 'joint'], path modes ['ApproachB', 'ApproachC', 'Hold'], branching 1, right-only False
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/ApproachC/Hold +RO, Brake B=2 via ApproachB/ApproachC/Hold; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachC: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB; L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) >= -1 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (2 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.08875 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.08875]; R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) >= -1 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (2 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.08875 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.08875]; NO_LINEAR=DECLINED

### `charger_fast_setpoints`

* family: Battery charger; scenario: degraded-controller; dims L/R 1/1; modes L/R 3/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `a4fc327fbdea`
* `relcert`: **CERTIFIED** (209 ms); `[prune] charger_fast_setpoints: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (441 ms); NO_CUT: **DECLINED** (457 ms); NO_IMPLIED_CUT: **DECLINED** (521 ms); NO_LINEAR_CUT: **CERTIFIED** (249 ms); domains: uniform
* `[cut] L.BULK: 2 conjunct(s)`
* `[cut] L.ABSORB: 2 conjunct(s)`
* `[cut] L.FULL: 1 conjunct(s)`
* `[cut] R.BULK: 2 conjunct(s)`
* `[cut] R.ABSORB: 2 conjunct(s)`
* `[cut] R.FULL: 1 conjunct(s)`
* `[cut] R.FAULT: 1 conjunct(s)`
* `[cut-x] L.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape`
* `[admissible] BULK_L: [BULK, ABSORB, FULL]`
* `[admissible] ABSORB_L: [BULK, ABSORB, FULL]`
* `[admissible] FULL_L: [ABSORB, FULL]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (39 ms)
* cover `BULK_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB', 'FULL'], flags {'BULK': '---dd', 'ABSORB': 'jr-dd', 'FULL': 'jrrdd', 'FAULT': '-----'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only True
    * from `BULK`: `BULK:repoDyn(B=2,preJ)->[ABSORB@2]; ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `ABSORB_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB', 'FULL'], flags {'BULK': '---dd', 'ABSORB': 'j--dd', 'FULL': 'jrrdd', 'FAULT': 'j----'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only True
    * from `BULK`: `BULK:repoDyn(B=2,preJ)->[ABSORB@2]; ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FULL_L`: λ = 1, budget 2, admissible ['ABSORB', 'FULL'], flags {'BULK': 'j--dd', 'ABSORB': 'j--dd', 'FULL': 'jrrdd', 'FAULT': 'j----'}, kinds ['base', 'joint'], path modes ['ABSORB', 'FULL'], branching 1, right-only False
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: BULK B=2 via ABSORB/FULL +RO, ABSORB B=2 via ABSORB/FULL +RO, FULL B=2 via ABSORB/FULL; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape; R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `charger_fast_tapers`

* family: Battery charger; scenario: degraded-controller; dims L/R 1/1; modes L/R 3/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `956f8ffbe687`
* `relcert`: **CERTIFIED** (281 ms); `[prune] charger_fast_tapers: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (565 ms); NO_CUT: **DECLINED** (505 ms); NO_IMPLIED_CUT: **CERTIFIED** (251 ms); NO_LINEAR_CUT: **CERTIFIED** (280 ms); domains: uniform
* `[cut] L.BULK: 2 conjunct(s)`
* `[cut] L.ABSORB: 2 conjunct(s)`
* `[cut] L.FULL: 1 conjunct(s)`
* `[cut] R.BULK: 2 conjunct(s)`
* `[cut] R.ABSORB_SLOW: 2 conjunct(s)`
* `[cut] R.ABSORB_FAST: 2 conjunct(s)`
* `[cut] R.FULL: 1 conjunct(s)`
* `[cut] R.FAULT: 1 conjunct(s)`
* `[cut-x] L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABSORB_SLOW: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABSORB_FAST: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape`
* `[admissible] BULK_L: [BULK, ABSORB_SLOW, ABSORB_FAST, FULL]`
* `[admissible] ABSORB_L: [BULK, ABSORB_SLOW, ABSORB_FAST, FULL]`
* `[admissible] FULL_L: [ABSORB_SLOW, ABSORB_FAST, FULL]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (97 ms)
* cover `BULK_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'BULK': '---dd', 'ABSORB_SLOW': '-r-dd', 'ABSORB_FAST': '-r-dd', 'FULL': 'jrrdd', 'FAULT': '-----'}, kinds ['base', 'joint', 'repoDyn', 'repoStatic'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FULL'], branching 0, right-only True
    * from `BULK`: `BULK:repoDyn(B=2,preJ)->[ABSORB_SLOW@2, ABSORB_FAST@2]; ABSORB_SLOW:repoStatic(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1); ABSORB_FAST:repoStatic(B=2,preJ)->[FULL@2]`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:repoStatic(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:repoStatic(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `ABSORB_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'BULK': 'j--dd', 'ABSORB_SLOW': 'j--dd', 'ABSORB_FAST': 'j--dd', 'FULL': 'jrrdd', 'FAULT': 'j----'}, kinds ['base', 'joint'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FULL'], branching 2, right-only False
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB_SLOW@1, ABSORB_FAST@1, BULK@1]; BULK:base(B=1); ABSORB_SLOW:base(B=1); ABSORB_FAST:base(B=1)`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:joint(B=2)->[ABSORB_SLOW@1, FULL@1, ABSORB_SLOW@1]; ABSORB_SLOW:base(B=1); FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FULL_L`: λ = 1, budget 2, admissible ['ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'BULK': 'j--dd', 'ABSORB_SLOW': 'j--dd', 'ABSORB_FAST': 'j--dd', 'FULL': 'jrrdd', 'FAULT': 'j----'}, kinds ['base', 'joint'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'FULL'], branching 1, right-only False
    * from `ABSORB_SLOW`: `ABSORB_SLOW:joint(B=2)->[ABSORB_SLOW@1, FULL@1, ABSORB_SLOW@1]; ABSORB_SLOW:base(B=1); FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: BULK B=2 via FULL +RO, ABSORB B=2 via ABSORB_FAST/ABSORB_SLOW/BULK/FULL, FULL B=2 via ABSORB_FAST/ABSORB_SLOW/FULL; **M3** yes: ABSORB branch=2; **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB_SLOW: 2 conjunct(s); R.ABSORB_FAST: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_SLOW: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_FAST: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `match_multi_rate`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 2/2; modes L/R 4/2; εL/εR 0.3/0.3; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `8ea18edaad94`
* `relcert`: **CERTIFIED** (330 ms); `[prune] match_multi_rate: [DRIVE->STALL]`; NO_PRUNE: **DECLINED** (362 ms); NO_CUT: **CERTIFIED** (302 ms); NO_IMPLIED_CUT: **CERTIFIED** (323 ms); NO_LINEAR_CUT: **CERTIFIED** (337 ms); domains: uniform
* `[cut] L.FAST: 2 conjunct(s)`
* `[cut] L.MEDIUM: 2 conjunct(s)`
* `[cut] L.SLOW: 2 conjunct(s)`
* `[cut] L.RESET: 2 conjunct(s)`
* `[cut] R.DRIVE: 2 conjunct(s)`
* `[cut] R.STALL: 1 conjunct(s)`
* `[cut-x] L.FAST: v <= 1.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.MEDIUM: v <= 1.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.SLOW: v <= 1.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.RESET: v <= 1.0 kind=closure entry=weakening route=shape`
* `[cut-x] L.RESET: v >= 0.1 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.STALL: v <= 0.2 kind=closure entry=weakening route=shape`
* `[admissible] FAST_L: [DRIVE]`
* `[admissible] MEDIUM_L: [DRIVE]`
* `[admissible] SLOW_L: [DRIVE]`
* `[admissible] RESET_L: [DRIVE]`
* `--handoff`: 8/8 checked, 8 passed, failing -, VACUOUS (identical rows) (102 ms)
* cover `FAST_L`: λ = 3, budget 3, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': '-----'}, kinds ['base', 'joint'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:joint(B=3)->[DRIVE@2, DRIVE@2]; DRIVE:joint(B=2)->[DRIVE@1, DRIVE@1]; DRIVE:base(B=1)`
* cover `MEDIUM_L`: λ = 2, budget 2, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': 'j----'}, kinds ['base', 'joint'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:joint(B=2)->[DRIVE@1, DRIVE@1]; DRIVE:base(B=1)`
* cover `SLOW_L`: λ = 1, budget 1, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': 'j----'}, kinds ['base'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:base(B=1)`
* cover `RESET_L`: λ = 1, budget 1, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': '-----'}, kinds ['base'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:base(B=1)`
* cells: **M1** yes: FAST λ=3, MEDIUM λ=2 (affine dynamics); **M2** yes: FAST B=3 via DRIVE, MEDIUM B=2 via DRIVE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned DRIVE->STALL; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.FAST: 2 conjunct(s); L.MEDIUM: 2 conjunct(s); L.SLOW: 2 conjunct(s); L.RESET: 2 conjunct(s); R.DRIVE: 2 conjunct(s); R.STALL: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.FAST: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.MEDIUM: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.SLOW: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.RESET: v <= 1.0 kind=closure entry=weakening route=shape; L.RESET: v >= 0.1 kind=implied-contraction entry=rational route=shape; R.STALL: v <= 0.2 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `platoon_delay_linkloss`

* family: Platoon follower, delayed link; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/3; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `547981de689a`
* `relcert`: **CERTIFIED** (309 ms); `[prune] platoon_delay_linkloss: [FOLLOW->BRAKE]`; NO_PRUNE: **DECLINED** (877 ms); NO_CUT: **DECLINED** (656 ms); NO_IMPLIED_CUT: **DECLINED** (757 ms); NO_LINEAR_CUT: **CERTIFIED** (257 ms); domains: uniform
* `[cut] L.FOLLOW: 2 conjunct(s)`
* `[cut] L.CATCH: 1 conjunct(s)`
* `[cut] L.LOST: 2 conjunct(s)`
* `[cut] R.FOLLOW: 2 conjunct(s)`
* `[cut] R.CATCH: 1 conjunct(s)`
* `[cut-x] L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] L.CATCH: g >= 29.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.CATCH: g >= 30.0 kind=implied-contraction entry=rational route=shape`
* `[admissible] FOLLOW_L: [FOLLOW, CATCH]`
* `[admissible] CATCH_L: [FOLLOW, CATCH]`
* `[admissible] LOST_L: [FOLLOW, CATCH]`
* `--handoff`: 7/7 checked, 7 passed, failing -, non-vacuous (26 ms)
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j----', 'CATCH': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cover `CATCH_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j----', 'CATCH': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cover `LOST_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j----', 'CATCH': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via CATCH/FOLLOW, CATCH B=2 via CATCH/FOLLOW, LOST B=2 via CATCH/FOLLOW; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED; **M5** yes: 7/7 handoffs unsat, rows differ; **M6** yes: L.FOLLOW: 2 conjunct(s); L.CATCH: 1 conjunct(s); L.LOST: 2 conjunct(s); R.FOLLOW: 2 conjunct(s); R.CATCH: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; L.CATCH: g >= 29.0 kind=implied-contraction entry=rational route=shape; R.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; R.CATCH: g >= 30.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `platoon_delay_profiles`

* family: Platoon follower, delayed link; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `4a4d185cf637`
* `relcert`: **CERTIFIED** (265 ms); `[prune] platoon_delay_profiles: [FOLLOW->BRAKE]`; NO_PRUNE: **DECLINED** (1096 ms); NO_CUT: **DECLINED** (933 ms); NO_IMPLIED_CUT: **DECLINED** (1033 ms); NO_LINEAR_CUT: **CERTIFIED** (230 ms); domains: uniform
* `[cut] L.FOLLOW: 2 conjunct(s)`
* `[cut] L.GENTLE: 1 conjunct(s)`
* `[cut] R.FOLLOW: 2 conjunct(s)`
* `[cut] R.GENTLE: 1 conjunct(s)`
* `[cut] R.ASSERTIVE: 1 conjunct(s)`
* `[cut-x] L.GENTLE: g >= 29.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.GENTLE: g >= 30.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ASSERTIVE: g >= 30.0 kind=implied-contraction entry=rational route=shape`
* `[admissible] FOLLOW_L: [FOLLOW, GENTLE, ASSERTIVE]`
* `[admissible] GENTLE_L: [FOLLOW, GENTLE, ASSERTIVE]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (96 ms)
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['FOLLOW', 'GENTLE', 'ASSERTIVE'], flags {'FOLLOW': 'j----', 'GENTLE': 'j----', 'ASSERTIVE': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['ASSERTIVE', 'FOLLOW', 'GENTLE'], branching 2, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, GENTLE@1, ASSERTIVE@1, FOLLOW@1]; FOLLOW:base(B=1); GENTLE:base(B=1); ASSERTIVE:base(B=1)`
    * from `GENTLE`: `GENTLE:joint(B=2)->[GENTLE@1, FOLLOW@1, GENTLE@1]; GENTLE:base(B=1); FOLLOW:base(B=1)`
    * from `ASSERTIVE`: `ASSERTIVE:joint(B=2)->[ASSERTIVE@1, FOLLOW@1, ASSERTIVE@1]; ASSERTIVE:base(B=1); FOLLOW:base(B=1)`
* cover `GENTLE_L`: λ = 1, budget 2, admissible ['FOLLOW', 'GENTLE', 'ASSERTIVE'], flags {'FOLLOW': 'j----', 'GENTLE': 'j----', 'ASSERTIVE': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['ASSERTIVE', 'FOLLOW', 'GENTLE'], branching 2, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, GENTLE@1, ASSERTIVE@1, FOLLOW@1]; FOLLOW:base(B=1); GENTLE:base(B=1); ASSERTIVE:base(B=1)`
    * from `GENTLE`: `GENTLE:joint(B=2)->[GENTLE@1, FOLLOW@1, GENTLE@1]; GENTLE:base(B=1); FOLLOW:base(B=1)`
    * from `ASSERTIVE`: `ASSERTIVE:joint(B=2)->[ASSERTIVE@1, FOLLOW@1, ASSERTIVE@1]; ASSERTIVE:base(B=1); FOLLOW:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via ASSERTIVE/FOLLOW/GENTLE, GENTLE B=2 via ASSERTIVE/FOLLOW/GENTLE; **M3** yes: FOLLOW branch=2, GENTLE branch=2; **M4** yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.FOLLOW: 2 conjunct(s); L.GENTLE: 1 conjunct(s); R.FOLLOW: 2 conjunct(s); R.GENTLE: 1 conjunct(s); R.ASSERTIVE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.GENTLE: g >= 29.0 kind=implied-contraction entry=rational route=shape; R.GENTLE: g >= 30.0 kind=implied-contraction entry=rational route=shape; R.ASSERTIVE: g >= 30.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `quad_light_airframe_20`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 1/1; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9a7b144d8b09`
* `relcert`: **CERTIFIED** (211 ms); `[prune] quad_light_airframe_20: [CLIMB->LIMIT]`; NO_PRUNE: **DECLINED** (702 ms); NO_CUT: **CERTIFIED** (233 ms); NO_IMPLIED_CUT: **CERTIFIED** (245 ms); NO_LINEAR_CUT: **CERTIFIED** (254 ms); domains: uniform
* `[cut] L.CLIMB: 2 conjunct(s)`
* `[cut] R.CLIMB: 2 conjunct(s)`
* `[cut] R.LIMIT: 1 conjunct(s)`
* `[cut-x] R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (82 ms)
* cover `CLIMB_L`: λ = 7/4, budget 4, admissible ['CLIMB'], flags {'CLIMB': 'j----', 'LIMIT': '-----'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=4)->[CLIMB@3, CLIMB@3]; CLIMB:joint(B=3)->[CLIMB@2, CLIMB@2]; CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=7/4 (polynomial dynamics); **M2** yes: CLIMB B=4 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s); R.LIMIT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `quad_light_lag`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 2/2; modes L/R 1/1; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `e06b31eeeac1`
* `relcert`: **CERTIFIED** (143 ms); `[prune] quad_light_lag: []`; NO_PRUNE: **CERTIFIED** (84 ms); NO_CUT: **CERTIFIED** (136 ms); NO_IMPLIED_CUT: **CERTIFIED** (143 ms); NO_LINEAR_CUT: **CERTIFIED** (124 ms); domains: uniform
* `[cut] L.CLIMB: 3 conjunct(s)`
* `[cut] R.CLIMB: 2 conjunct(s)`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (94 ms)
* cover `CLIMB_L`: λ = 7/4, budget 4, admissible ['CLIMB'], flags {'CLIMB': 'j----'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=4)->[CLIMB@3, CLIMB@3]; CLIMB:joint(B=3)->[CLIMB@2, CLIMB@2]; CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=7/4 (polynomial dynamics); **M2** yes: CLIMB B=4 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `quad_light_profiles`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 1/1; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `4449578e8cfc`
* `relcert`: **CERTIFIED** (490 ms); `[prune] quad_light_profiles: [NORMAL->LIMIT, ECO->LIMIT, SPORT->LIMIT]`; NO_PRUNE: **DECLINED** (1152 ms); NO_CUT: **CERTIFIED** (503 ms); NO_IMPLIED_CUT: **CERTIFIED** (503 ms); NO_LINEAR_CUT: **CERTIFIED** (499 ms); domains: uniform
* `[cut] L.CLIMB: 1 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.ECO: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.LIMIT: 1 conjunct(s)`
* `[cut-x] R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape`
* `[admissible] CLIMB_L: [NORMAL, ECO, SPORT]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (87 ms)
* cover `CLIMB_L`: λ = 5/2, budget 5, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j----', 'ECO': 'j----', 'SPORT': 'j----', 'LIMIT': '-----'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=5)->[NORMAL@4, NORMAL@4, ECO@4, SPORT@4]; NORMAL:joint(B=4)->[NORMAL@3, NORMAL@3, ECO@3, SPORT@3]; NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1); ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; ECO:joint(B=4)->[ECO@3, ECO@3, NORMAL@3]; SPORT:joint(B=4)->[SPORT@3, SPORT@3, NORMAL@3]`
    * from `ECO`: `ECO:joint(B=5)->[ECO@4, ECO@4, NORMAL@4]; ECO:joint(B=4)->[ECO@3, ECO@3, NORMAL@3]; ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; SPORT:base(B=1); NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; NORMAL:joint(B=4)->[NORMAL@3, NORMAL@3, ECO@3, SPORT@3]; SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]`
    * from `SPORT`: `SPORT:joint(B=5)->[SPORT@4, SPORT@4, NORMAL@4]; SPORT:joint(B=4)->[SPORT@3, SPORT@3, NORMAL@3]; SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; ECO:base(B=1); NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; NORMAL:joint(B=4)->[NORMAL@3, NORMAL@3, ECO@3, SPORT@3]; ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]`
* cells: **M1** yes: CLIMB λ=5/2 (polynomial dynamics); **M2** yes: CLIMB B=5 via ECO/NORMAL/SPORT; **M3** yes: CLIMB branch=2; **M4** yes: pruned NORMAL->LIMIT, ECO->LIMIT, SPORT->LIMIT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 1 conjunct(s); R.NORMAL: 2 conjunct(s); R.ECO: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.LIMIT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung1_2to3`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 3/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `a55b07fd35ff`
* `relcert`: **CERTIFIED** (227 ms); `[prune] refinement_ladder_rover_rung1_2to3: []`; NO_PRUNE: **CERTIFIED** (292 ms); NO_CUT: **DECLINED** (838 ms); NO_IMPLIED_CUT: **CERTIFIED** (194 ms); NO_LINEAR_CUT: **CERTIFIED** (246 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (90 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2_3to6`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `1b9081f9b111`
* `relcert`: **CERTIFIED** (739 ms); `[prune] refinement_ladder_rover_rung2_3to6: []`; NO_PRUNE: **CERTIFIED** (732 ms); NO_CUT: **CERTIFIED** (618 ms); NO_IMPLIED_CUT: **CERTIFIED** (653 ms); NO_LINEAR_CUT: **CERTIFIED** (688 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (78 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '-----', 'MODER': '-----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 4/4; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.001, 6.0]; invariant shape linear; rows identical: True; normalized md5 `238c061085aa`
* `relcert`: **CERTIFIED** (270 ms); `[prune] refinement_ladder_rover_rung2_6dof: []`; NO_PRUNE: **CERTIFIED** (192 ms); NO_CUT: **CERTIFIED** (149 ms); NO_IMPLIED_CUT: **CERTIFIED** (142 ms); NO_LINEAR_CUT: **CERTIFIED** (254 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (100 ms)
* cover `STEEP_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'jr-dd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2b_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.001, 6.0]; invariant shape linear; rows identical: True; normalized md5 `b1ae87a5c1db`
* `relcert`: **CERTIFIED** (298 ms); `[prune] refinement_ladder_rover_rung2b_6dof: []`; NO_PRUNE: **CERTIFIED** (244 ms); NO_CUT: **CERTIFIED** (199 ms); NO_IMPLIED_CUT: **CERTIFIED** (215 ms); NO_LINEAR_CUT: **CERTIFIED** (216 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (69 ms)
* cover `STEEP_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'jr-dd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2c_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `724831255028`
* `relcert`: **CERTIFIED** (1288 ms); `[prune] refinement_ladder_rover_rung2c_6dof: []`; NO_PRUNE: **CERTIFIED** (1356 ms); NO_CUT: **CERTIFIED** (1239 ms); NO_IMPLIED_CUT: **CERTIFIED** (1181 ms); NO_LINEAR_CUT: **CERTIFIED** (1356 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP]`
* `[admissible] MODER_L: [MODER]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (95 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP'], flags {'STEEP': 'j----', 'MODER': '-----', 'FLAT': '-----'}, kinds ['base'], path modes ['STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER'], flags {'STEEP': '-----', 'MODER': 'j----', 'FLAT': '-----'}, kinds ['base'], path modes ['MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '-----', 'MODER': '-----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung3_6to8`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape quadratic; rows identical: True; normalized md5 `848946e281b6`
* `relcert`: **CERTIFIED** (2976 ms); `[prune] refinement_ladder_rover_rung3_6to8: []`; NO_PRUNE: **CERTIFIED** (2970 ms); NO_CUT: **DECLINED** (3081 ms); NO_IMPLIED_CUT: **CERTIFIED** (2816 ms); NO_LINEAR_CUT: **CERTIFIED** (2984 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (18 ms)
* cover `STEEP_L`: λ = 9/4, budget 3, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=3)->[STEEP@2, MODER@2, STEEP@2]; STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1); MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=3)->[MODER@2, FLAT@2, MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1); FLAT:joint(B=2)->[FLAT@1, FLAT@1]`
    * from `FLAT`: `FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 9/4, budget 3, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=3,preJ)->[MODER@3]; MODER:joint(B=3)->[MODER@2, FLAT@2, MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1); FLAT:joint(B=2)->[FLAT@1, FLAT@1]`
    * from `MODER`: `MODER:joint(B=3)->[MODER@2, FLAT@2, MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1); FLAT:joint(B=2)->[FLAT@1, FLAT@1]`
    * from `FLAT`: `FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 9/4, budget 3, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=3,preJ)->[FLAT@3]; FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=9/4, MODER λ=9/4, FLAT λ=9/4 (polynomial dynamics); **M2** yes: STEEP B=3 via FLAT/MODER/STEEP, MODER B=3 via FLAT/MODER +RO, FLAT B=3 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung4_8to12`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9f1c06c6a52c`
* `relcert`: **CERTIFIED** (985 ms); `[prune] refinement_ladder_rover_rung4_8to12: []`; NO_PRUNE: **CERTIFIED** (998 ms); NO_CUT: **DECLINED** (1240 ms); NO_IMPLIED_CUT: **CERTIFIED** (899 ms); NO_LINEAR_CUT: **CERTIFIED** (985 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (86 ms)
* cover `STEEP_L`: λ = 17/10, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 17/10, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 17/10, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=17/10, MODER λ=17/10, FLAT λ=17/10 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover3tier_rung12`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/3; modes L/R 2/2; εL/εR 1.0/0.3; λ ∈ [1.0, 6.0]; invariant shape conjunctive+linear; rows identical: False; normalized md5 `4b65ad8433aa`
* `relcert`: **CERTIFIED** (266 ms); `[prune] rover3tier_rung12: []`; NO_PRUNE: **CERTIFIED** (220 ms); NO_CUT: **CERTIFIED** (230 ms); NO_IMPLIED_CUT: **CERTIFIED** (248 ms); NO_LINEAR_CUT: **CERTIFIED** (217 ms); domains: uniform
* `[cut] R.ACCEL: 1 conjunct(s)`
* `[cut] R.COAST: 1 conjunct(s)`
* `[admissible] ACCEL_L: [ACCEL, COAST]`
* `[admissible] COAST_L: [ACCEL, COAST]`
* `--handoff`: 4/4 checked, 4 passed, failing -, non-vacuous (26 ms)
* cover `ACCEL_L`: λ = 7/4, budget 6, admissible ['ACCEL', 'COAST'], flags {'ACCEL': 'j--dd', 'COAST': 'j--dd'}, kinds ['base', 'joint'], path modes ['ACCEL', 'COAST'], branching 1, right-only False
    * from `ACCEL`: `ACCEL:joint(B=6)->[ACCEL@5, COAST@5, ACCEL@5]; ACCEL:joint(B=5)->[ACCEL@4, COAST@4, ACCEL@4]; ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:base(B=1); COAST:base(B=1); COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=5)->[COAST@4, ACCEL@4, COAST@4]`
    * from `COAST`: `COAST:joint(B=6)->[COAST@5, ACCEL@5, COAST@5]; COAST:joint(B=5)->[COAST@4, ACCEL@4, COAST@4]; COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:base(B=1); ACCEL:base(B=1); ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=5)->[ACCEL@4, COAST@4, ACCEL@4]`
* cover `COAST_L`: λ = 1, budget 4, admissible ['ACCEL', 'COAST'], flags {'ACCEL': 'j--dd', 'COAST': 'j--dd'}, kinds ['base', 'joint'], path modes ['ACCEL', 'COAST'], branching 1, right-only False
    * from `ACCEL`: `ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:base(B=1); COAST:base(B=1); COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]`
    * from `COAST`: `COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:base(B=1); ACCEL:base(B=1); ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]`
* cells: **M1** yes: ACCEL λ=7/4 (affine dynamics); **M2** yes: ACCEL B=6 via ACCEL/COAST, COAST B=4 via ACCEL/COAST; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** yes: 4/4 handoffs unsat, rows differ; **M6** vacuous: cuts kept (R.ACCEL: 1 conjunct(s); R.COAST: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung1`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 3/3; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `0b323c73c8d9`
* `relcert`: **CERTIFIED** (220 ms); `[prune] rover_dof_terrain_rung1: []`; NO_PRUNE: **CERTIFIED** (290 ms); NO_CUT: **DECLINED** (858 ms); NO_IMPLIED_CUT: **CERTIFIED** (240 ms); NO_LINEAR_CUT: **CERTIFIED** (302 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (30 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung2`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `05e0216a07ff`
* `relcert`: **CERTIFIED** (348 ms); `[prune] rover_dof_terrain_rung2: []`; NO_PRUNE: **CERTIFIED** (328 ms); NO_CUT: **DECLINED** (959 ms); NO_IMPLIED_CUT: **CERTIFIED** (281 ms); NO_LINEAR_CUT: **CERTIFIED** (345 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (86 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung3`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `8d149b9ca736`
* `relcert`: **CERTIFIED** (387 ms); `[prune] rover_dof_terrain_rung3: []`; NO_PRUNE: **CERTIFIED** (369 ms); NO_CUT: **DECLINED** (1101 ms); NO_IMPLIED_CUT: **CERTIFIED** (316 ms); NO_LINEAR_CUT: **CERTIFIED** (309 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (78 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung3_8d`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `675e7eb3a84a`
* `relcert`: **CERTIFIED** (381 ms); `[prune] rover_dof_terrain_rung3_8d: []`; NO_PRUNE: **CERTIFIED** (365 ms); NO_CUT: **DECLINED** (1044 ms); NO_IMPLIED_CUT: **CERTIFIED** (301 ms); NO_LINEAR_CUT: **CERTIFIED** (301 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (45 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_patrol_refine`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/3; modes L/R 4/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `f6b60807c2bd`
* `relcert`: **CERTIFIED** (1271 ms); `[prune] rover_patrol_refine: []`; NO_PRUNE: **CERTIFIED** (1183 ms); NO_CUT: **DECLINED** (1164 ms); NO_IMPLIED_CUT: **DECLINED** (2134 ms); NO_LINEAR_CUT: **DECLINED** (2132 ms); domains: uniform
* `[cut] L.SLOW: 5 conjunct(s)`
* `[cut] L.MEDIUM_ECO: 5 conjunct(s)`
* `[cut] L.MEDIUM_BRISK: 5 conjunct(s)`
* `[cut] L.FAST: 4 conjunct(s)`
* `[cut] R.SLOW: 3 conjunct(s)`
* `[cut] R.MEDIUM_ECO: 3 conjunct(s)`
* `[cut] R.MEDIUM_BRISK: 3 conjunct(s)`
* `[cut] R.FAST: 3 conjunct(s)`
* `[cut-x] L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.SLOW: (a + (2.5 * (v - 0.48))) >= -0.95 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.SLOW: v <= 0.8 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) <= 0.8]`
* `[cut-x] L.SLOW: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) >= -0.95]`
* `[cut-x] L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) <= 0.95 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) >= -1.55 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.MEDIUM_ECO: v <= 1.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) <= 0.95]`
* `[cut-x] L.MEDIUM_ECO: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) >= -1.55]`
* `[cut-x] L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) <= 1.05 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) >= -1.95 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.MEDIUM_BRISK: v <= 1.3 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) <= 1.05]`
* `[cut-x] L.MEDIUM_BRISK: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) >= -1.95]`
* `[cut-x] L.FAST: (a + (2.5 * (v - 1.2))) <= 1.25 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FAST: (a + (2.5 * (v - 1.2))) >= -2.75 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FAST: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 1.2))) >= -2.75]`
* `[admissible] SLOW_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_ECO_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_BRISK_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] FAST_L: [MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (92 ms)
* cover `SLOW_L`: λ = 7/4, budget 4, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': 'j--dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=4,preJ)->[MEDIUM_ECO@4, MEDIUM_BRISK@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]`
    * from `FAST`: `FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_ECO_L`: λ = 7/4, budget 4, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': '---dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=4,preJ)->[MEDIUM_ECO@4, MEDIUM_BRISK@4]; MEDIUM_ECO:repoDyn(B=4,preJ)->[FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1); MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=4,preJ)->[FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]`
    * from `FAST`: `FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_BRISK_L`: λ = 7/4, budget 4, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': '---dd', 'MEDIUM_BRISK': '---dd', 'FAST': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 0, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=4,preJ)->[MEDIUM_ECO@4, MEDIUM_BRISK@4]; MEDIUM_ECO:repoDyn(B=4,preJ)->[FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1); MEDIUM_BRISK:repoDyn(B=4,preJ)->[FAST@4]`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=4,preJ)->[FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:repoDyn(B=4,preJ)->[FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `FAST_L`: λ = 5/2, budget 5, admissible ['MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': '---dd', 'MEDIUM_BRISK': '---dd', 'FAST': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO'], branching 0, right-only True
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=5,preJ)->[FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:repoDyn(B=5,preJ)->[FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cells: **M1** yes: SLOW λ=7/4, MEDIUM_ECO λ=7/4, MEDIUM_BRISK λ=7/4, FAST λ=5/2 (affine dynamics); **M2** yes: SLOW B=4 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, MEDIUM_ECO B=4 via FAST/MEDIUM_BRISK +RO, MEDIUM_BRISK B=4 via FAST +RO, FAST B=5 via FAST +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.SLOW: 5 conjunct(s); L.MEDIUM_ECO: 5 conjunct(s); L.MEDIUM_BRISK: 5 conjunct(s); L.FAST: 4 conjunct(s); R.SLOW: 3 conjunct(s); R.MEDIUM_ECO: 3 conjunct(s); R.MEDIUM_BRISK: 3 conjunct(s); R.FAST: 3 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry=rational route=linear-shape; L.SLOW: (a + (2.5 * (v - 0.48))) >= -0.95 kind=linear-form entry=rational route=linear-shape; L.SLOW: v <= 0.8 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) <= 0.8]; L.SLOW: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) >= -0.95]; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) <= 0.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) >= -1.55 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: v <= 1.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) <= 0.95]; L.MEDIUM_ECO: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) >= -1.55]; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) <= 1.05 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) >= -1.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: v <= 1.3 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) <= 1.05]; L.MEDIUM_BRISK: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) >= -1.95]; L.FAST: (a + (2.5 * (v - 1.2))) <= 1.25 kind=linear-form entry=rational route=linear-shape; L.FAST: (a + (2.5 * (v - 1.2))) >= -2.75 kind=linear-form entry=rational route=linear-shape; L.FAST: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 1.2))) >= -2.75]; NO_IMPLIED=DECLINED; **M6L** yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry=rational route=linear-shape; L.SLOW: (a + (2.5 * (v - 0.48))) >= -0.95 kind=linear-form entry=rational route=linear-shape; L.SLOW: v <= 0.8 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) <= 0.8]; L.SLOW: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) >= -0.95]; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) <= 0.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) >= -1.55 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: v <= 1.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) <= 0.95]; L.MEDIUM_ECO: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) >= -1.55]; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) <= 1.05 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) >= -1.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: v <= 1.3 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) <= 1.05]; L.MEDIUM_BRISK: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) >= -1.95]; L.FAST: (a + (2.5 * (v - 1.2))) <= 1.25 kind=linear-form entry=rational route=linear-shape; L.FAST: (a + (2.5 * (v - 1.2))) >= -2.75 kind=linear-form entry=rational route=linear-shape; L.FAST: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 1.2))) >= -2.75]; NO_LINEAR=DECLINED

### `rover_patrol_zones`

* family: Rover patrol (zones); scenario: degraded-actuator; dims L/R 2/2; modes L/R 4/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `088224fb0842`
* `relcert`: **CERTIFIED** (464 ms); `[prune] rover_patrol_zones: [SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL, FAST->STALL]`; NO_PRUNE: **CERTIFIED** (443 ms); NO_CUT: **DECLINED** (1183 ms); NO_IMPLIED_CUT: **CERTIFIED** (453 ms); NO_LINEAR_CUT: **CERTIFIED** (460 ms); domains: uniform
* `[cut] L.SLOW: 3 conjunct(s)`
* `[cut] L.MEDIUM_ECO: 3 conjunct(s)`
* `[cut] L.MEDIUM_BRISK: 3 conjunct(s)`
* `[cut] L.FAST: 3 conjunct(s)`
* `[cut] R.SLOW: 3 conjunct(s)`
* `[cut] R.MEDIUM_ECO: 3 conjunct(s)`
* `[cut] R.MEDIUM_BRISK: 3 conjunct(s)`
* `[cut] R.FAST: 3 conjunct(s)`
* `[cut] R.STALL: 1 conjunct(s)`
* `[cut-x] R.STALL: v <= 0.2 kind=closure entry=weakening route=shape`
* `[admissible] SLOW_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_ECO_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_BRISK_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] FAST_L: [MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (52 ms)
* cover `SLOW_L`: λ = 1, budget 2, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': 'j--dd', 'MEDIUM_ECO': 'j--dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd', 'STALL': 'j----'}, kinds ['base', 'joint'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 2, right-only False
    * from `SLOW`: `SLOW:joint(B=2)->[SLOW@1, MEDIUM_ECO@1, MEDIUM_BRISK@1, SLOW@1]; SLOW:base(B=1); MEDIUM_ECO:base(B=1); MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_ECO_L`: λ = 1, budget 2, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': 'j--dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd', 'STALL': 'j----'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=2,preJ)->[MEDIUM_ECO@2, MEDIUM_BRISK@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_BRISK_L`: λ = 1, budget 2, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': '---dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd', 'STALL': 'j----'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=2,preJ)->[MEDIUM_ECO@2, MEDIUM_BRISK@2]; MEDIUM_ECO:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1); MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `FAST_L`: λ = 1, budget 2, admissible ['MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': '---dd', 'MEDIUM_BRISK': '---dd', 'FAST': 'j--dd', 'STALL': 'j----'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO'], branching 0, right-only True
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: SLOW B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, MEDIUM_BRISK B=2 via FAST/MEDIUM_BRISK +RO, FAST B=2 via FAST +RO; **M3** yes: SLOW branch=2; **M4** vacuous: pruned SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL, FAST->STALL but NO_PRUNE=CERTIFIED; **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.SLOW: 3 conjunct(s); L.MEDIUM_ECO: 3 conjunct(s); L.MEDIUM_BRISK: 3 conjunct(s); L.FAST: 3 conjunct(s); R.SLOW: 3 conjunct(s); R.MEDIUM_ECO: 3 conjunct(s); R.MEDIUM_BRISK: 3 conjunct(s); R.FAST: 3 conjunct(s); R.STALL: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.STALL: v <= 0.2 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `story1_attdist_rung_a_6to8`

* family: Story ladders; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `34c422712676`
* `relcert`: **CERTIFIED** (20477 ms); `[prune] story1_attdist_rung_a_6to8: []`; NO_PRUNE: **CERTIFIED** (20507 ms); NO_CUT: **CERTIFIED** (1574 ms); NO_IMPLIED_CUT: **CERTIFIED** (20332 ms); NO_LINEAR_CUT: **CERTIFIED** (20471 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (19 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story1_attdist_rung_b_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: False; normalized md5 `d5633710e2d8`
* `relcert`: **CERTIFIED** (408 ms); `[prune] story1_attdist_rung_b_12dof: []`; NO_PRUNE: **CERTIFIED** (499 ms); NO_CUT: **CERTIFIED** (383 ms); NO_IMPLIED_CUT: **CERTIFIED** (401 ms); NO_LINEAR_CUT: **CERTIFIED** (423 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (38 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story2_lateral_rung_a_8dof`

* family: Story ladders; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `cb0ec6031104`
* `relcert`: **CERTIFIED** (1136 ms); `[prune] story2_lateral_rung_a_8dof: []`; NO_PRUNE: **CERTIFIED** (1091 ms); NO_CUT: **CERTIFIED** (1007 ms); NO_IMPLIED_CUT: **CERTIFIED** (1029 ms); NO_LINEAR_CUT: **CERTIFIED** (1163 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (95 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '-----', 'MODER': '-----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story2_lateral_rung_b_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `5e62b7ea6ff9`
* `relcert`: **CERTIFIED** (1506 ms); `[prune] story2_lateral_rung_b_12dof: []`; NO_PRUNE: **CERTIFIED** (1464 ms); NO_CUT: **CERTIFIED** (1290 ms); NO_IMPLIED_CUT: **CERTIFIED** (1312 ms); NO_LINEAR_CUT: **CERTIFIED** (1500 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (50 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '-----', 'MODER': '-----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story3_rollover_base_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape quadratic; rows identical: True; normalized md5 `cf68fbeeef5c`
* `relcert`: **CERTIFIED** (1188 ms); `[prune] story3_rollover_base_12dof: []`; NO_PRUNE: **CERTIFIED** (1248 ms); NO_CUT: **DECLINED** (2964 ms); NO_IMPLIED_CUT: **CERTIFIED** (1158 ms); NO_LINEAR_CUT: **CERTIFIED** (1253 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (90 ms)
* cover `STEEP_L`: λ = 5/4, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 5/4, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 5/4, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=5/4, MODER λ=5/4, FLAT λ=5/4 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story3_rollover_ladder_rung_a`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape quadratic; rows identical: True; normalized md5 `af17da3f1b89`
* `relcert`: **CERTIFIED** (828 ms); `[prune] story3_rollover_ladder_rung_a: []`; NO_PRUNE: **CERTIFIED** (903 ms); NO_CUT: **DECLINED** (2325 ms); NO_IMPLIED_CUT: **CERTIFIED** (787 ms); NO_LINEAR_CUT: **CERTIFIED** (858 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (85 ms)
* cover `STEEP_L`: λ = 27/20, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 27/20, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': 'j--dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 27/20, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '---dd', 'MODER': '---dd', 'FLAT': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=27/20, MODER λ=27/20, FLAT λ=27/20 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story3_rollover_ladder_rung_b`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape quadratic; rows identical: False; normalized md5 `afd0663422a6`
* `relcert`: **CERTIFIED** (744 ms); `[prune] story3_rollover_ladder_rung_b: []`; NO_PRUNE: **CERTIFIED** (756 ms); NO_CUT: **DECLINED** (2553 ms); NO_IMPLIED_CUT: **DECLINED** (2485 ms); NO_LINEAR_CUT: **DECLINED** (2591 ms); domains: uniform
* `[cut] L.STEEP: 5 conjunct(s)`
* `[cut] L.MODER: 5 conjunct(s)`
* `[cut] L.FLAT: 5 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[cut-x] L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.STEEP: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.STEEP: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]`
* `[cut-x] L.STEEP: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]`
* `[cut-x] L.MODER: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.MODER: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.MODER: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]`
* `[cut-x] L.MODER: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]`
* `[cut-x] L.FLAT: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FLAT: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FLAT: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]`
* `[cut-x] L.FLAT: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (69 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** yes: L.STEEP: 5 conjunct(s); L.MODER: 5 conjunct(s); L.FLAT: 5 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.STEEP: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.MODER: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.MODER: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.FLAT: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.FLAT: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; NO_IMPLIED=DECLINED; **M6L** yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.STEEP: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.MODER: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.MODER: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.FLAT: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.FLAT: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; NO_LINEAR=DECLINED

### `watertank`

* family: Watertank; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 10.0]; invariant shape linear; rows identical: True; normalized md5 `a301828a2f41`
* `relcert`: **CERTIFIED** (226 ms); `[prune] watertank: []`; NO_PRUNE: **CERTIFIED** (202 ms); NO_CUT: **CERTIFIED** (198 ms); NO_IMPLIED_CUT: **CERTIFIED** (212 ms); NO_LINEAR_CUT: **CERTIFIED** (223 ms); domains: uniform
* `[cut] L.Low: 1 conjunct(s)`
* `[cut] L.Mid: 1 conjunct(s)`
* `[cut] L.High: 1 conjunct(s)`
* `[cut] R.Low: 1 conjunct(s)`
* `[cut] R.Mid: 1 conjunct(s)`
* `[cut] R.High: 1 conjunct(s)`
* `[cut-x] L.High: x <= 22.45 kind=closure entry=weakening route=diB`
* `[cut-x] R.High: x <= 22.45 kind=closure entry=weakening route=diB`
* `[admissible] Low_L: [Low, Mid, High]`
* `[admissible] Mid_L: [Mid, High]`
* `[admissible] High_L: [High]`
* `--handoff`: 6/6 checked, 6 passed, failing -, VACUOUS (identical rows) (102 ms)
* cover `Low_L`: λ = 1, budget 1, admissible ['Low', 'Mid', 'High'], flags {'Low': 'j----', 'Mid': 'jr-dd', 'High': '-r---'}, kinds ['base', 'repoStatic'], path modes ['High', 'Low', 'Mid'], branching 0, right-only True
    * from `Low`: `Low:base(B=1)`
    * from `Mid`: `Mid:base(B=1)`
    * from `High`: `High:repoStatic(B=1,preJ)->[Mid@1]; Mid:base(B=1)`
* cover `Mid_L`: λ = 1, budget 1, admissible ['Mid', 'High'], flags {'Low': '-----', 'Mid': 'j--dd', 'High': '-r---'}, kinds ['base', 'repoStatic'], path modes ['High', 'Mid'], branching 0, right-only True
    * from `Mid`: `Mid:base(B=1)`
    * from `High`: `High:repoStatic(B=1,preJ)->[Mid@1]; Mid:base(B=1)`
* cover `High_L`: λ = 1, budget 1, admissible ['High'], flags {'Low': 'j----', 'Mid': 'j--dd', 'High': 'j----'}, kinds ['base'], path modes ['High'], branching 0, right-only False
    * from `High`: `High:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Low: 1 conjunct(s); L.Mid: 1 conjunct(s); L.High: 1 conjunct(s); R.Low: 1 conjunct(s); R.Mid: 1 conjunct(s); R.High: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.High: x <= 22.45 kind=closure entry=weakening route=diB; R.High: x <= 22.45 kind=closure entry=weakening route=diB) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

## 10. Re-running

    RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/suite_v2/*/input.txt   # 39 CERTIFIED
    scripts/suite_v2_matrix.py --md /tmp/suite_v2.md --json /tmp/suite_v2.json
    scripts/suite_v2_matrix.py --only acc_tune_modes,rover_patrol_zones  # a subset
    scripts/domain_widening.py --jobs 6 --md /tmp/widen.md --json /tmp/widen.json
    scripts/domain_widening.py benchmarks/suite_v2/arm_plateau_crit/input.txt   # one file
    RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --emit-cuts benchmarks/suite_v2/arm_plateau_crit/input.txt c
                                                                 # the legacy literal `c` and the extended `cX`

The matrix script needs the `relcert` binary (`lake build relcert`) and Z3 on the path;
it takes about four minutes for the whole suite (seven tool runs per benchmark). The
widening script runs `relcert` once per (side, variable, direction) group plus the base
and the all-widened file (about 750 runs, 25 minutes at `--jobs 6`). Without
`RELCERT_IMPLIED_CUT=1` the six M6+ members (`arm_plateau_*` ×3,
`charger_fast_setpoints`, `platoon_delay_band`, `platoon_delay_profiles`) are DECLINED;
everything else certifies either way.

## 11. Not done here

* The Lean mechanization of `suite_v2` (instances, pins, coverage constants, the
  `--run-verdicts` rows): a separate task. It needs two generalizations of the lift the
  tool side now exercises: the O1 case split of the extended cut certificate
  (`EvolStrengtheningX`: membership / weakening / rational / Z3 entries — §7, and
  `docs/PAPER-MAPPING.md` §2c) and per-mode evolve domains (`UniformEvol.lean`, the
  handoff runner's `uniformEvolveR`). Until then the kernel column still reads
  `suite_uniform`, and `relcert --check-quick benchmarks/suite_uniform/*/input.txt`
  is unchanged.
* The L6 domain-corner incompleteness (met by the dropped `heater_cycle`).
* The Lean lift of the linear-form chain (§7 L7; `docs/PAPER-MAPPING.md` §2c: the
  linear-shape and derived-shape lemmas and the SEQUENTIAL composition the `given` field
  records).
* (Resolved in pass 4, §13.6: the flagged `story3_rollover_ladder_rung_b` and the
  load-bearing acceleration caps of the three lag rungs.)
* The two kept-replaceable files (`match_multi_rate`, `rover3tier_rung12`) and the 19
  kept files carry no `# scenario:` line; the script maps their kind.
* `benchmarks/suite_uniform/arm_chain_rung3`, `arm_fidelity_low` and `arm_fidelity_mid`, read by the Lean
  pins, close their Hold phase with the same kind of evolve cap the domain audit removed
  from `suite_v2` (`θ_L ≤ 0.65 ≤ 0.6 + tol`, `docs/PAPER-MAPPING.md` §2c); not touched
  here (`suite_uniform` must stay byte-identical).
* The paper's Table 1 / §6 rewrite from §8.

## 12. Regression record for `suite_uniform`

### Pass 3 (the linear-form chain; binaries of `cd3248b` and `049991c`)

* Default path byte-identical: `--emit-cuts`, `--emit-cover` and `RELCERT_DEBUG=1 relcert`
  for all 41 `suite_uniform` inputs (stdout with the benchmark-name prefix and the
  millisecond field masked, the complete stderr), each diffed against the emissions of
  the pre-change binary (the pass-2 tree, before `Checker/EvolStrengtheningX.lean` and
  `Trusted/OracleAPI.lean` were touched): no difference in any of the 246 files, with
  both the `cd3248b` and the `049991c` binary. 40 CERTIFIED, 1 DECLINED
  (`shield_unreachable`).
* `lake build`: exit 0, `Build completed successfully (8977 jobs)`; `lake build relcert
  relcert-test`: `Build completed successfully (17695 jobs)`. `git status` shows no
  change under `RelCertifier/Instances/`, `Proofs/` or `Verdicts/`.
* `relcert --check-quick benchmarks/suite_uniform/*/input.txt`: `[suite] 40 certified,
  1 declined, 0 error(s) — matches the declared suite`; `[coverage] watertank: 6/6
  hypotheses discharged`, `cut probes: 97/97`, `modal: 504/504`, `handoff: 191/191`,
  `non-connection: 2/2`, `pruned edges: 1/1`; `suite: PASS`, `verdicts: PASS`,
  `QUICK CHECKS PASSED  (the kernel check is `lake build` — see --help)`, exit 0.
* `BENCH_PATHS=<manifest of the 41> relcert-test`: `ok   all 40 IR literals match their
  files`, `ALL PASS`, exit 0.
* `relcert --run-verdicts`: `ALL MODAL HYPOTHESES DISCHARGED`, the six coverage lines as
  above, `ALL HYPOTHESES DISCHARGED`, exit 0.

### Pass 2 (binary of `7c5a11c`)

The widened channel is off by default, and the default path was checked to be the old
one, byte for byte, before anything else was run:

* `--emit-cuts` for all 41 `suite_uniform` inputs, `--emit-cover` for all 41, and
  `RELCERT_DEBUG=1 relcert` for all 41 (stdout with the millisecond field masked, and
  the complete stderr), each diffed against the same emission from the `main` binary
  (`f6ed5c9`): no difference in any of the 164 files. 40 CERTIFIED, 1 DECLINED
  (`shield_unreachable`), as declared.
* `lake build`: exit 0, 8977 jobs (warm; the new module
  `Checker/EvolStrengtheningX.lean` and `Trusted/OracleAPI.lean`'s dependents
  `Proofs/Flow/FaceBridge`, `Instances/WatertankViability`, `Trusted/ViabilityEmit`,
  `Main`, `Test` re-elaborated; `Checker/EvolStrengthening.lean` untouched, so no
  instance, pin or coverage constant was rebuilt or changed — `git status` shows no
  change under `RelCertifier/Instances/`, `Proofs/` or `Verdicts/`).
* `relcert --check-quick benchmarks/suite_uniform/*/input.txt`: `[suite] 40 certified,
  1 declined, 0 error(s) — matches the declared suite`; `[coverage] watertank: 6/6`,
  `cut probes: 97/97`, `modal: 504/504`, `handoff: 191/191`, `non-connection: 2/2`,
  `pruned edges: 1/1`; `suite: PASS`, `verdicts: PASS`, `QUICK CHECKS PASSED`, exit 0.
* `BENCH_PATHS=<manifest> relcert-test`: `ALL PASS` (bare — the two Z3-determinism
  checks ran; 40 IR literals match their files), exit 0.
* `relcert --run-verdicts`: `ALL MODAL HYPOTHESES DISCHARGED`, the six coverage lines
  as above, `ALL HYPOTHESES DISCHARGED`, exit 0.

## 13. The domain audit (pass 3, 2026-10-08)

**The rule (user).** An evolve domain states the PHYSICAL limits of the plant. It must
never be narrowed to a reachable-set estimate so that the certificate closes. A bound a
certificate stands on is therefore a physical limit the dynamics genuinely need, a
forward-invariant floor the model justifies, or a finding.

**The test** (`scripts/domain_widening.py`). For every `suite_v2` file, every evolve
bound is grouped by (side, variable, direction); each group is widened in EVERY mode of
its side by half the variable's range in that mode (a one-sided bound takes the range of
the same variable on the other side, and is skipped if that is one-sided too), and the
file is re-run (`RELCERT_IMPLIED_CUT=1`). DECLINED or ERROR marks the group
LOAD-BEARING. Then all groups are widened at once. 39 files, 742 runs.

### 13.1 Results (generated)

| benchmark | base | all widened | load-bearing evolve bounds (widened by half the range: verdict) | skipped (one-sided) |
|---|---|---|---|---|
| `acc_spoof_cruise` | CERTIFIED | CERTIFIED | none | none |
| `acc_spoof_lag` | CERTIFIED | CERTIFIED | none | none |
| `acc_spoof_modes` | CERTIFIED | CERTIFIED | none | none |
| `acc_tune_gain` | CERTIFIED | CERTIFIED | none | none |
| `acc_tune_lag` | CERTIFIED | CERTIFIED | none | none |
| `acc_tune_modes` | CERTIFIED | CERTIFIED | none | none |
| `arm_plateau_crit` | CERTIFIED | CERTIFIED | none | none |
| `arm_plateau_lowgain` | CERTIFIED | CERTIFIED | none | none |
| `arm_plateau_slow` | CERTIFIED | CERTIFIED | none | none |
| `charger_fast_setpoints` | CERTIFIED | CERTIFIED | none | none |
| `charger_fast_tapers` | CERTIFIED | CERTIFIED | none | none |
| `match_multi_rate` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo` |
| `platoon_delay_band` | CERTIFIED | CERTIFIED | none | none |
| `platoon_delay_profiles` | CERTIFIED | DECLINED | none | none |
| `quad_light_airframe_20` | CERTIFIED | CERTIFIED | none | none |
| `quad_light_airframe_40` | CERTIFIED | CERTIFIED | none | none |
| `quad_light_lag` | CERTIFIED | CERTIFIED | none | none |
| `refinement_ladder_rover_rung1_2to3` | CERTIFIED | DECLINED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `refinement_ladder_rover_rung2_3to6` | CERTIFIED | DECLINED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `refinement_ladder_rover_rung2_6dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `refinement_ladder_rover_rung2b_6dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `refinement_ladder_rover_rung2c_6dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `refinement_ladder_rover_rung3_6to8` | CERTIFIED | DECLINED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `refinement_ladder_rover_rung4_8to12` | CERTIFIED | DECLINED | none | none |
| `rover3tier_rung12` | CERTIFIED | CERTIFIED | none | none |
| `rover_dof_terrain_rung1` | CERTIFIED | DECLINED | none | none |
| `rover_dof_terrain_rung2` | CERTIFIED | DECLINED | none | none |
| `rover_dof_terrain_rung3` | CERTIFIED | DECLINED | none | none |
| `rover_dof_terrain_rung3_8d` | CERTIFIED | DECLINED | none | none |
| `rover_patrol_refine` | CERTIFIED | CERTIFIED | none | none |
| `rover_patrol_zones` | CERTIFIED | CERTIFIED | none | none |
| `story1_attdist_rung_a_6to8` | CERTIFIED | DECLINED | `L.psi.lo` (-0.6->-1.2: DECLINED); `L.theta_p.lo` (-0.6->-1.2: ERROR) | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story1_attdist_rung_b_12dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story2_lateral_rung_a_8dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story2_lateral_rung_b_12dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story3_rollover_base_12dof` | CERTIFIED | DECLINED | none | none |
| `story3_rollover_ladder_rung_a` | CERTIFIED | DECLINED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story3_rollover_ladder_rung_b` | CERTIFIED | DECLINED | `R.psi.hi` (0.15->0.475: DECLINED); `R.theta_p.hi` (0.15->0.475: DECLINED) | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `watertank` | CERTIFIED | CERTIFIED | none | none |

(Pass-3 run; the rows of the four files changed in pass 4 — `acc_spoof_lag`, `acc_tune_lag`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b` — are the pass-4 re-run, §13.6; the whole-suite pass-4 re-run is §14.) Totals of the pass-3 run: 39 files; **23** certify with every bound widened at once; **5** have a
load-bearing group; **11** pass every single-group widening but fail the all-at-once
one. Classification:

* **Expected — forward-invariant floors:** `story1_attdist_rung_a_6to8`, `L.psi.lo`,
  `L.theta_p.lo` (−0.6). The left attitude is a cascade `ψ' = ω_ψ − ψ, ω_ψ' = −ω_ψ`: on
  `ψ = −0.6` with `ω_ψ ≥ −0.6`, `ψ' ≥ 0`, so the box is forward-invariant. (The
  `L.theta_p.lo` run is ERROR, the 120 s time budget, not DECLINED.)
* **Repaired (§13.2):** the three arm rungs pass every widening and the all-at-once one.
* **Flagged (§13.3), resolved in pass 4 (§13.6 A1):** `story3_rollover_ladder_rung_b`, `L.psi.lo`, `L.theta_p.lo`: not
  forward-invariant, and the claim needs them. Its `R.theta_p.lo/hi` ERRORs are the
  time budget, not a decline: STEEP_L certifies and one MODER_L query does not return
  within 120 s (`R.psi` with the same widening certifies in 5 s); the right attitude is
  `θ_p' = −θ_p`, a contraction toward 0, so `[−0.5, 0.15]` is forward-invariant. A Z3
  budget finding, not a domain one.
* **FINDING — load-bearing acceleration caps of the three lag rungs (resolved in pass 4 by
  the remodel of §13.6 A2; the paragraph below is the pass-3 record):**
  `acc_spoof_lag` (`a ≤ 10`), `acc_tune_lag` (`a ≤ 6`), `rover_patrol_refine`
  (`a ≤ 1`), all `L.a.hi`, DECLINED. The headers declare them as the powertrain / motor
  acceleration envelope, a physical actuator limit; but the deployed lag `a' = 2 (a_cmd
  − a)` is unsaturated and `a_cmd` exceeds the cap at low speed (`a_cmd = 15 − 0.625 v
  > 10` for `v < 8`; `22.5 − 0.75 v > 6` for `v < 22`; FAST `1.5 − 1.25 v > 1` for
  `v < 0.4`), so the cap is not forward-invariant on the declared domain, and the claim
  needs it (in `acc_spoof_lag` at λ = 5/4 the row's boundary derivative is
  `0.625 a_L − 7.5`, which needs `a_L ≤ 12`). The `(v, a)` pairs are UNDERDAMPED
  (`b² − 4a` = 4 − 5, 4 − 6, 4 − 10), so the linear-form chain has nothing to offer.
  Needs a decision: accept the caps as actuator saturation (and say so in the headers)
  or remodel the lag with a saturated command. Not changed here.
* **Joint-only (11), bisected by pairs** (a scratch bisection over the script's own
  groups: the pairs that DECLINE, and the complement certifying):
  * `L.v.lo` with `R.v.lo` — the speed floor `v ≥ 0` on BOTH sides: the 8 terrain /
    position ladder rungs among the 11 and `story3_rollover_base_12dof`,
    `story3_rollover_ladder_rung_a` (widening only that pair DECLINES; widening every
    other group CERTIFIES, except in `rung4_8to12`). Physical (no reversing) and
    forward-invariant (`v' = 3 (c − v)` with `c > 0` in every mode).
  * `refinement_ladder_rover_rung4_8to12` also: the right attitude bounds
    `R.psi.lo/hi` with `R.theta_p.lo/hi` (4 pairs of 1081). The right attitude is the
    cascade `ψ' = ω − ψ, ω' = −ω` with `|ω| ≤ 0.6`, so `[−0.6, 0.6]` is
    forward-invariant; widened to ±1.2 rad together, the speed factor `1 − 0.5 ψ² −
    0.3 θ_p²` turns negative, outside the model's range of validity.
  * `platoon_delay_profiles`: `L.g.hi` with `R.g.hi` (the 60 m gap cap on both
    sides). Forward-invariant (every admissible mode contracts toward 30 m; BRAKE, which
    opens the gap, is pruned and not an admissible start) and the physical range at
    re-engagement from which the 4 m tolerance is derived (the header: an assertive
    reference re-engaging from 60 m outruns the gentle deployed follower by up to 4 m).
* **Skipped (one-sided on both sides):** the odometer floors `s ≥ 0`; forward-invariant
  (`s' ≥ 0` wherever `v ≥ 0`).

Nothing else is load-bearing.

### 13.2 Repair A — the arm family on physical domains

Before: `arm_plateau_pd` (`k_p = k_d = 1`, underdamped), `arm_plateau_slow` (half torque,
`k_p = k_d = 0.5`, underdamped), `arm_plateau_crit` (`k_p = 1, k_d = 2`), all with the
left domain `θ ≤ 0.65, v ∈ [−0.45, 0.45]` — a reachable-set envelope that CLOSED the Hold
phase (`0.65 ≤ 0.6 + 0.15`). After: `θ ∈ [0, 1.2]`, `v ∈ [−1, 1]` on every left mode,
critically / over-damped loops only, the claim re-set to what the linear-form chain
derives (§4.6, §7 L7):

| benchmark | gains | chain (Accelerate) | derived bound | claim | default | NO_CUT | NO_IMPLIED_CUT | NO_LINEAR_CUT | widening |
|---|---|---|---|---|---|---|---|---|---|
| `arm_plateau_crit` | 1, 2 | `v + (θ − 0.5) ≤ 0.355` (linear-shape) | `θ ≤ 0.855` (derived-shape) | `θ_L ≤ θ_R + 0.255` | CERTIFIED | DECLINED | DECLINED | DECLINED | passes (all-widened CERTIFIED) |
| `arm_plateau_slow` | 1, 2.5 | `v + 2 (θ − 0.5) ≤ 0.355`, `v + 0.5 (θ − 0.5) ≤ 0.355` | `θ ≤ 0.6775` | `θ_L ≤ θ_R + 0.0775` | CERTIFIED | DECLINED | DECLINED | DECLINED | passes |
| `arm_plateau_lowgain` (new) | 0.5, 1.5 | `v + (θ − 0.5) ≤ 0.355`, `v + 0.5 (θ − 0.5) ≤ 0.355` | `θ ≤ 0.855` | `θ_L ≤ θ_R + 0.255` | CERTIFIED | DECLINED | DECLINED | DECLINED | passes |

(default = `RELCERT_IMPLIED_CUT=1`; without the switch all three are DECLINED.) The next
slack down (0.25 / 0.075 / 0.25) is DECLINED for each. The underdamped `arm_plateau_pd`
is removed and the underdamped half-torque `_slow` is replaced by the over-damped worn
joint; an underdamped loop has no rational decoupling form (`[lin-skip] … no positive
rational root`) and was never certified without the cap. No duplicates (normalized hash,
§8).

### 13.3 Repair B — `story3_rollover_ladder_rung_b`: does not close; flagged (pass 3; resolved in pass 4, §13.6)

The left attitude `ψ' = ω_ψ, ω_ψ' = −ψ − 2 ω_ψ` (and `θ_p` alike) is critically damped,
`q = ω_ψ + ψ`, `q' = −q`, so the chain would give `ψ ≥ −0.5` from `q ≥ −0.5` — but it
needs an ENTRY constant for `q`, and the guards are the terrain zones in `s` only:

    [lin-skip] STEEP: pair (psi, omega_psi) with 1 root(s) but the guard bounds neither side of (psi, omega_psi) — no O1 constant

Widening the left floors to −1 (the family's validity range): `[STEEP_L λ=1 #comps=3]
STEEP=fail MODER=fail FLAT=fail`, the same at λ = 27/20, then ERROR (time budget). This
is not a tool gap: at `ψ_L = −0.95, ω_ψL = 0.232, ψ_R = −0.5` (the energy row at its
0.25 level) the row's derivative is `−0.522 + 0.668 λ > 0` for every λ ≥ 1, so the claim
NEEDS a floor on `ψ_L`, and from `ψ = −0.5, ω_ψ = −0.5` the loop reaches `ψ = −0.607`
(t = 0.5 s), so −0.5 is not invariant. The file is kept with its original domains and a
`DOMAIN-AUDIT FLAG` header. Tested, NOT installed (it changes the guards): left
attitude domains `[−1, 1]` plus the entry condition `ψ, ω_ψ, θ_p, ω_θ ≥ −0.25` in every
left guard CERTIFIES (746 ms) with `[cut-x] L.STEEP: (omega_psi + (1 * (psi - 0))) >=
-0.5 kind=linear-form entry=rational route=linear-shape` and `psi >= -0.5
kind=derived-bound entry=rational route=derived-shape` (all three left modes, both
attitude channels). Decision for the user: accept an attitude entry condition, or keep
the flag.

### 13.4 Drops

`charger_bias_estimator`, `charger_fast_thermal`, `heater_cycle` — dropped: per-mode band
domains encode event-triggered switching, which the user chose not to claim. Their
pass-2 records: §4.3 / §4.7 history, §6, §7 L5 / L6, and `git show 63bd64a:benchmarks/
suite_v2/<name>/input.txt`.

### 13.5 Matrix before / after

| mechanism | pass 2 (42) | pass 3 (39) |
|---|---|---|
| M1 | 19 | 18 (−`charger_fast_thermal`) |
| M2 | 29 | 26 (−3 dropped, −`arm_plateau_pd`, +`arm_plateau_lowgain`) |
| M3 | 6 | 6 |
| M4 | 15 | 13 (−`charger_bias_estimator`, −`charger_fast_thermal`) |
| M5 | 6 | 6 |
| M6 | 19 | 19 (−`arm_plateau_pd`, +`arm_plateau_lowgain`) |
| M6+ | 2 | 6 (+arm ×3; +`platoon_delay_profiles`, whose physical gap floor 0 m, `63bd64a`, makes the implied atoms `g ≥ 30` / `g ≥ 29` load-bearing) |
| M6L | — | 3 (arm ×3) |
| per-mode domains | 3 | 0 |

### 13.6 Pass 4 repairs (user decisions A1, A2; 2026-10-08)

**A1 — `story3_rollover_ladder_rung_b`, installed.** Left attitude domains `ψ, ω_ψ, θ_p,
ω_θ ∈ [−1, 1]` (the small-angle model's validity range; before: `[−0.5, 0.5]`) and the
GUARD entry condition `ψ, ω_ψ, θ_p, ω_θ ≥ −0.25` on every left terrain-zone switch (and
on the first zone): the deployed controller switches zones only with a settled attitude
— a controller-design condition, not a domain restriction. Dynamics and rows unchanged;
the header's `DOMAIN-AUDIT FLAG` is replaced by the resolution note. Measured: CERTIFIED
(705–760 ms), λ = 1 on all three left modes; kept chain per left mode `ω_ψ + ψ ≥ −0.5`,
`ω_θ + θ_p ≥ −0.5` (linear-form, O1 rational, O2 linear-shape) and `ψ ≥ −0.5`, `θ_p ≥
−0.5` (derived-bound, O2 derived-shape); `RELCERT_NO_CUT=1` DECLINED (2516 ms),
`RELCERT_NO_IMPLIED_CUT=1` DECLINED (2586 ms), `RELCERT_NO_LINEAR_CUT=1` DECLINED
(2727 ms), `RELCERT_NO_PRUNE=1` CERTIFIED (nothing pruned); `--handoff` 5/5 unsat. New
cells: M6, M6+, M6L (with M5 as before). Widening: every LEFT group certifies (the
derived floor replaces the declared one); load-bearing are `R.psi.hi`, `R.theta_p.hi`
(0.15 → 0.475: DECLINED) — FORWARD-INVARIANT: the reference attitude is `ψ' = −ψ`,
`θ_p' = −θ_p`, so on `ψ = 0.15` the field points inward (stated in the header).

**A2 — the three lag rungs remodeled; the acceleration caps are no longer load-bearing.**
For a speed loop `a_cmd = K (c − v)` realized through a first-order lag `a' = b (a_cmd −
a)` (`b = 1/τ`) the `(v, a)` pair is `v'' + b v' + K b (v − c) = 0`: non-oscillatory iff
`b ≥ 4K`. The pass-3 lag `τ = 0.5 s` (`b = 2`) was underdamped in all three (`b² − 4Kb =
4 − 5, 4 − 6, 4 − 10`), so `a` overshot and the unsaturated `a_cmd` exceeded any fixed
cap at low speed. The linear-form chain needs RATIONAL roots of `r² − b r + K b = 0`:

| benchmark | K | lag τ (b) | char. polynomial | roots | engagement guard (new) | physical domain on `a` | chain atoms kept (left) | claim (row) | next step tighter | λ, budget |
|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | 0.625 | 0.4 s (2.5) — slowest non-oscillatory; τ = 0.25 s gives `s² + 4s + 2.5`, roots `−2 ± √1.5`, irrational | `(s + 1.25)²` | 1.25 (critical) | `23 ≤ v ≤ 30`, `|a| ≤ 2` | `[−10, 10]` (1 g) | `a + 1.25 (v − 24) ∈ [−3.25, 9.5]`; `v ∈ [21.4, 31.6]` | `a_L + 2.5 v_L ≤ 2.5 v_R − 5.5` (`w_L ≤ v_R − 2.2`, `w = v + 0.4 a`) | −5.75 DECLINED (domain ±10 and ±100 alike) | 5/2, 5 |
| `acc_tune_lag` | 0.75 | 0.25 s (4) | `(s + 1)(s + 3)` | 1, 3 (over-damped) | `25 ≤ v ≤ 30`, `|a| ≤ 2` | `[−10, 10]` | `a + (v − 30) ∈ [−7, 2]`, `a + 3 (v − 30) ∈ [−17, 2]`; `v ∈ [23, 32]` | `a_L + 4 v_L ≤ 4 v_R + 2` (`w_L ≤ v_R + 0.5`, `w = v + 0.25 a`) | 1.75 DECLINED (±10 and ±100 alike) | 2, 4 |
| `rover_patrol_refine` | 1.25 | 0.2 s (5); τ = 0.25 s (b = 4) still oscillates | `(s + 2.5)²` | 2.5 (critical) | zone hand-over with `|a| ≤ 0.5` | `[−2, 2]` (0.2 g traction) | per zone `a + 2.5 (v − c)`: SLOW `[−0.95, 0.8]`, ECO `[−1.55, 0.95]`, BRISK `[−1.95, 1.05]`, FAST `[−2.75, 1.25]`; `v ≤ 0.8 / 1.1 / 1.3`, `v ≥ 0.1` | `a_L + 5 v_L ≤ 5 v_R − 0.25` (`w_L ≤ v_R − 0.05`) + zone margins | −0.5 DECLINED (FAST_L; ±2 and ±100 alike) | 7/4, 4 (FAST 5/2, 5) |

The bound on `a` the claim needs is DERIVED inside the chain (`a ≤ K_q − r (v − c)` on the
kept `q ≤ K_q`), so the `a`-domain is a stated physical limit that no certificate stands
on: all three pass the widening test with every bound widened at once (§13.1).
Counter-runs (matrix, §9): `RELCERT_NO_CUT=1`, `RELCERT_NO_IMPLIED_CUT=1`,
`RELCERT_NO_LINEAR_CUT=1` DECLINE all three (new cells M6, M6+, M6L). Costs, recorded:
(i) the two ACC rungs lose M4 — DISENGAGE is still declared and pruned, but the derived
left floor (`v_L ≥ 21.4`, resp. `≥ 23`) and the tight row make the `CRUISE_L/DISENGAGE_R`
pairing region empty, so `RELCERT_NO_PRUNE=1` CERTIFIES (finding 9 of §5, now caused by
a derived bound); (ii) `rover_patrol_refine` loses M3 — at its tight slack the SLOW/SLOW
joint segment fails and the SLOW window repositions instead of branching (at slack +0.5
it branches; that looser claim is not made). The engagement guards are controller-design
conditions written in the headers (ACC engages between the floor and the set speed with
no hard pedal input; the rover's planner hands over with a settled motor current).

## 14. Pass 4 (2026-10-08): branching and mode-dependent variants (B), the rigid-body family (C)

### 14.1 Task B — replacements, each a superset of the replaced cells

The target was about 10 benchmarks each for M3 (branching) and M5 (mode-dependent rows),
from 6 / 6 (M3 fell to 5 when `rover_patrol_refine` was re-set to its tight claim, §13.6).
Every new benchmark REPLACES a weaker member of its own family whose cells it contains, so
the families read as towers and the count stays put:

| new | replaces (cells) | story (one line) | proven cells (counter-runs, matrix §9) |
|---|---|---|---|
| `acc_spoof_limp` | `acc_spoof_cruise` (M1 M2 M4) | spoofed ACC whose plausibility monitor latches a limp-home loop (22 m/s, gain 0.3) vs the selectable-set-speed reference | M1 (CRUISE λ = 5/4) M2 M3 (branch 2 in both windows) M4 (NO_PRUNE DECLINED) M5 (rows CRUISE `+9`, LIMP `+12`, each tightest; handoff 3/3 unsat) M6 (NO_CUT DECLINED) |
| `acc_tune_limp` | `acc_tune_gain` (M1 M2 M4) | retuned ACC whose ECU latches a limp-home map (25 m/s, gain 0.3) vs the selectable-response reference | M1 (λ = 3/2) M2 M3 M4 M5 (CRUISE `|·| ≤ 2`, LIMP `v_R ≤ v_L + 6.5`; 3/3 unsat) M6 |
| `quad_light_profiles` | `quad_light_airframe_40` (M1 M2 M4) | 40 %-lighter quadrotor vs an autopilot with selectable climb-thrust profiles (90 / 100 / 110 %) and a limiter | M1 (λ = 5/2, polynomial) M2 M3 M4 |
| `arm_plateau_profiles` | `arm_plateau_lowgain` (M2 M6 M6+ M6L) | detuned over-damped arm vs a reference whose planner picks a fast or a gentle final approach | M2 M3 M6 M6+ M6L |
| `platoon_delay_linkloss` | `platoon_delay_band` (M2 M4 M6 M6+) | delayed-link follower that latches a radar-only gap keeper on V2V link loss, range-proportional tolerance | M2 M4 M5 (7/7 unsat, domain-conditioned) M6 M6+ |

Pattern found (recorded as design finding 12): a GENUINE mode-dependent row needs a switch
along which the row loosens. A fault-LATCHED degraded mode (limp-home, radar-only) gives it
naturally: the degraded loop settles lower or slower, its tightest row is strictly looser
than the nominal mode's, and there is no switch back. Where the tighter row is the later
mode (ACC launch → cruise) the handoff fails, and a scheduled row cannot rescue it because
guards do not end a residence (§6). The tried-and-dropped variants of this pass are in §6.
All five pass the widening test with every bound widened at once; no duplicate and no
tolerance-only variant (normalized and tolerance-masked hashes, §8).

