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
(§14). Pass 5 (2026-10-09, §15): claim tolerances chosen so that the fallback / branching
mechanism is exercised on `acc_tune_lag` and `rover_patrol_refine` (tight bounds kept as
header remarks); `acc_spoof_lag` and `charger_fast_tapers` keep their claims (measured
trade-offs); the open user decisions recorded as resolved. Suite size stays 42. Pass 6
(2026-10-09, §16): four 6-D files that exercise branching / pruning / mode-dependent rows
(`sat3w_detumble_weak`, `sat3w_detumble_phases`: a three-wheel gyrostat, polynomial;
`platoon3_linkloss`, `platoon3_profiles`: a three-follower CACC string, linear) added;
`acc_spoof_modes`, `acc_tune_modes` dropped (cells strict subsets of the limp files);
**suite size 44**, 44 / 44 CERTIFIED under the default solver settings. Pass 7
(2026-10-09, §17): the tool's default Z3 resource limit raised from 8 000 000 to
64 000 000 and its default query budget from 5 000 to 20 000 (the only tool changes;
`suite_uniform` byte-identical); the 6-D gyrostat rungs restated at their ANALYTIC
tolerances (`sat3w_detumble_phases` back on the 4-D constants), the three-follower
string on the stretch grid, `sat3w_detumble_nominal` added; L8 resolved (§7);
**suite size 45**, 45 / 45 CERTIFIED under the new defaults. Pass 8 (2026-10-09, §18):
`watertank` redesigned as the paper's running example (set-point pumps, sensor offset 3,
tampered Low pump; certified by joint segments only), and the tool's static
(zero-duration) reposition REMOVED from the certifier and the checker; still **45 / 45
CERTIFIED**. Pass 8 is the one pass that touches the Lean side and `suite_uniform`'s
results (six `suite_uniform` benchmarks are declined after the removal, §18.3); before it,
`benchmarks/suite_uniform/` and every Lean instance, pin and coverage constant were
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
| ACC under sensor spoofing / retune | `acc_spoof_limp`, `acc_spoof_lag`, `acc_tune_limp`, `acc_tune_lag` (pass 4: `_limp` replace `acc_spoof_cruise`, `acc_tune_gain`; pass 6: `acc_spoof_modes`, `acc_tune_modes` dropped) | sensor-attack, degraded-controller, model-refinement ×2 (the `_lag` rungs) | 1, 2 |
| Quadrotor climb, lighter airframe | `quad_light_airframe_20`, `quad_light_profiles` (pass 4, replaces `quad_light_airframe_40`), `quad_light_lag` | model-refinement (plant mismatch, polynomial drag) | 1, 2 |
| Battery charger | `charger_fast_setpoints`, `charger_fast_tapers` | degraded-controller ×2 | 1 |
| Platoon follower, delayed link | `platoon_delay_linkloss` (pass 4, replaces `platoon_delay_band`), `platoon_delay_profiles` | sensor-attack (stale link) | 1 |
| Rover patrol (zones) | `rover_patrol_zones`, `rover_patrol_refine` (+ kept `rover3tier_rung12`, `match_multi_rate`) | degraded-actuator, model-refinement | 2, 3 |
| Arm, leading reference | `arm_plateau_crit`, `arm_plateau_slow`, `arm_plateau_profiles` (pass 4, replaces `arm_plateau_lowgain`) | model-refinement, degraded-actuator, degraded-controller | 2 / 1 |

(The table above is the pass-3 list with the pass-4 replacements marked; the
rigid-body detumbling family — `sat_detumble_nominal`, `sat_detumble_weak`,
`sat_detumble_phases`, dim 4, polynomial — is new in pass 4, §14.2.) **Pass-4 suite: 42
benchmarks, 42 / 42 CERTIFIED.** Every non-kept benchmark exercises at least two of M1–M6
non-vacuously (§3; `quad_light_lag` exercises exactly two). Totals (§8, after pass 5,
§15): M1 18, M2 29, M3 11, M4 15, M5 10, M6 25, M6+ 9, M6L 6; no file declares per-mode
domains. (Pass 4: M3 10, M4 14, M6 26, M6+ 10, M6L 7.) **Pass 6 (§16): 44 benchmarks,
44 / 44 CERTIFIED; M1 16, M2 31, M3 11, M4 17, M5 12, M6 28, M6+ 11, M6L 8** — the
three-wheel gyrostat (`sat3w_*`, dim 6, polynomial) joins the rigid-body family and the
three-follower CACC string (`platoon3_*`, dim 6, linear) is a new family. **Pass 7
(§17): 45 benchmarks, 45 / 45 CERTIFIED; M1 16, M2 32, M3 11, M4 18, M5 12, M6 28, M6+
11, M6L 8** (+`sat3w_detumble_nominal`: M2 M4; no other cell changed). **Pass 8
(§18): 45 benchmarks, 45 / 45 CERTIFIED; M1 17, M2 33, M3 12, M4 19, M5 12, M6 29, M6+
12, M6L 8** (the redesigned `watertank` exercises M1 M2 M3 M4 M6 M6+, where the old one
exercised none non-vacuously; no other benchmark's cells changed).

## 2. Method — how a cell is earned

`scripts/suite_v2_matrix.py` runs every `benchmarks/suite_v2/<name>/input.txt`:

1. `RELCERT_DEBUG=1 relcert <input>` — verdict and wall time; the `[prune]`,
   `[admissible]`, `[cut]` lines.
2. `relcert --emit-cover <input> x` — the emitted cover: per left mode the λ, the
   budget `⌈λ εL / εR⌉`, the flag row of every right mode (`jointOK, dynPre, dynPost`; until 2026-10-09 also
   the static `repoPre, repoPost`, §18) and the admissible starts. The script then REPLAYS the verified
   checker's structural cover (`decideCovered`, `RelCertifier/Checker/Checker.lean`,
   over `buildCoverGraph` of `Checker/CoverEmit.lean`: nodes = flag rows with any
   certificate, edges = the file's declared successors minus the pruned ones, the
   sentinel for an uncertified target) from every admissible start, in the checker's
   alternative order (base, joint step, dynamic reposition; the static reposition was
   removed on 2026-10-09, §18), and
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
(e.g. `match_multi_rate` keeps its band cuts but certifies without them);
a benchmark whose fallback is pruned but which would certify anyway is printed `M4
vacuous` (one is: `rover_patrol_zones`, §5 finding 9).

## 3. Feature matrix (generated)

| benchmark | verdict (ms) | M1 λ≠1 | M2 multi-step | M3 branch | M4 prune | M5 mode-dep | M6 cut | M6+ widened cut | M6L linear-form chain | M7 scenario; dim; invariant; domains |
|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | CERTIFIED (170) | yes: CRUISE λ=5/2 (affine dynamics) | yes: CRUISE B=5 via CRUISE | no (max non-self successors at a joint step = 0) | vacuous: pruned CRUISE->DISENGAGE but NO_PRUNE=CERTIFIED | no (rows identical; handoff vacuous) | yes: L.CRUISE: 4 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE:... | yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entr... | yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entr... | model-refinement; dim 2; linear |
| `acc_spoof_limp` | CERTIFIED (291) | yes: CRUISE λ=5/4 (affine dynamics) | yes: CRUISE B=3 via ECO/NORMAL/SPORT, LIMP B=2 via ECO/NORMAL/SPORT | yes: CRUISE branch=2, LIMP branch=2 | yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO... | yes: 3/3 handoffs unsat, rows differ | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `acc_tune_lag` | CERTIFIED (83) | yes: CRUISE λ=5/4 (affine dynamics) | yes: CRUISE B=3 via CRUISE | no (max non-self successors at a joint step = 0) | yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 6 conjunct(s); R.CRUISE: 2 conjunct(s... | vacuous: widened atoms kept (L.CRUISE: (a + (1 * (v - 30))) <= 2 ki... | vacuous: linear-form atoms kept (L.CRUISE: (a + (1 * (v - 30))) <= ... | model-refinement; dim 2; linear |
| `acc_tune_limp` | CERTIFIED (333) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=3 via COMFORT/NORMAL/SPORT, LIMP B=2 via COMFORT/NORM... | yes: CRUISE branch=2, LIMP branch=2 | yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE... | yes: 3/3 handoffs unsat, rows differ | yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 co... | vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure en... | no (no linear-form atom kept) | degraded-controller; dim 1; conjunctive |
| `arm_plateau_crit` | CERTIFIED (177) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/ApproachB/ApproachC/Hold, Brake B... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.Accelerate: 4 conjunct(s); L.Brake: 2 conjunct(s); R.Approac... | yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=di... | yes: L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-f... | model-refinement; dim 2+-1; linear |
| `arm_plateau_profiles` | CERTIFIED (125) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/ApproachB/ApproachCfast/ApproachC... | yes: Accelerate branch=2, Brake branch=2 | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.Approac... | yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=di... | yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear... | degraded-controller; dim 2+-1; linear |
| `arm_plateau_slow` | CERTIFIED (174) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/ApproachC/Hold +RO, Brake B=2 via... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.Approac... | yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=di... | yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear... | degraded-actuator; dim 2+-1; linear |
| `charger_fast_setpoints` | CERTIFIED (196) | no (λ=1 everywhere) | yes: BULK B=2 via ABSORB/FULL +RO, ABSORB B=2 via ABSORB/FULL +RO, ... | no (max non-self successors at a joint step = 1) | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conj... | yes: L.BULK: x <= 90.0 kind=implied-contraction entry=rational rout... | no (no linear-form atom kept) | degraded-controller; dim 1; linear |
| `charger_fast_tapers` | CERTIFIED (222) | no (λ=1 everywhere) | yes: BULK B=2 via FULL +RO, ABSORB B=2 via ABSORB_FAST/ABSORB_SLOW/... | yes: ABSORB branch=2 | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conj... | vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contra... | no (no linear-form atom kept) | degraded-controller; dim 1; linear |
| `match_multi_rate` | CERTIFIED (298) | yes: FAST λ=3, MEDIUM λ=2 (affine dynamics) | yes: FAST B=3 via DRIVE, MEDIUM B=2 via DRIVE | no (max non-self successors at a joint step = 0) | yes: pruned DRIVE->STALL; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.FAST: 2 conjunct(s); L.MEDIUM: 2 conjunct(s);... | vacuous: widened atoms kept (L.FAST: v <= 1.0 kind=implied-contract... | no (no linear-form atom kept) | model-refinement; dim 2; linear |
| `platoon3_linkloss` | CERTIFIED (2159) | no (λ=1 everywhere) | yes: FOLLOW B=2 via FOLLOW, LOST B=2 via FOLLOW | no (max non-self successors at a joint step = 0) | yes: pruned FOLLOW->BRAKE1, FOLLOW->BRAKE2, FOLLOW->BRAKE3; NO_PRUN... | yes: 3/3 handoffs unsat, rows differ | yes: L.FOLLOW: 24 conjunct(s); L.LOST: 24 conjunct(s); R.FOLLOW: 24... | yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entr... | yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entr... | sensor-attack; dim 6; conjunctive |
| `platoon3_profiles` | CERTIFIED (2227) | no (λ=1 everywhere) | yes: FOLLOW B=2 via CLOSE/FAR/NORMAL | yes: FOLLOW branch=2 | yes: pruned NORMAL->BRAKE1, NORMAL->BRAKE2, NORMAL->BRAKE3, CLOSE->... | no (rows identical; handoff vacuous) | yes: L.FOLLOW: 24 conjunct(s); R.NORMAL: 24 conjunct(s); R.CLOSE: 2... | yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entr... | yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entr... | sensor-attack; dim 6; conjunctive |
| `platoon_delay_linkloss` | CERTIFIED (263) | no (λ=1 everywhere) | yes: FOLLOW B=2 via CATCH/FOLLOW, CATCH B=2 via CATCH/FOLLOW, LOST ... | no (max non-self successors at a joint step = 1) | yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED | yes: 7/7 handoffs unsat, rows differ | yes: L.FOLLOW: 2 conjunct(s); L.CATCH: 1 conjunct(s); L.LOST: 2 con... | yes: L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; ... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `platoon_delay_profiles` | CERTIFIED (267) | no (λ=1 everywhere) | yes: FOLLOW B=2 via ASSERTIVE/FOLLOW/GENTLE, GENTLE B=2 via ASSERTI... | yes: FOLLOW branch=2, GENTLE branch=2 | yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.FOLLOW: 2 conjunct(s); L.GENTLE: 1 conjunct(s); R.FOLLOW: 2 ... | yes: L.GENTLE: g >= 29.0 kind=implied-contraction entry=rational ro... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |
| `quad_light_airframe_20` | CERTIFIED (219) | yes: CLIMB λ=7/4 (polynomial dynamics) | yes: CLIMB B=4 via CLIMB | no (max non-self successors at a joint step = 0) | yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s);... | vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contracti... | no (no linear-form atom kept) | model-refinement; dim 1; conjunctive |
| `quad_light_lag` | CERTIFIED (129) | yes: CLIMB λ=7/4 (polynomial dynamics) | yes: CLIMB B=4 via CLIMB | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 2 conjunct(s))... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 2; linear |
| `quad_light_profiles` | CERTIFIED (497) | yes: CLIMB λ=5/2 (polynomial dynamics) | yes: CLIMB B=5 via ECO/NORMAL/SPORT | yes: CLIMB branch=2 | yes: pruned NORMAL->LIMIT, ECO->LIMIT, SPORT->LIMIT; NO_PRUNE=DECLI... | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 1 conjunct(s); R.NORMAL: 2 conjunct(s)... | vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contracti... | no (no linear-form atom kept) | model-refinement; dim 1; conjunctive |
| `refinement_ladder_rover_rung1_2to3` | CERTIFIED (256) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3+-1; conjunctive |
| `refinement_ladder_rover_rung2_3to6` | CERTIFIED (714) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `refinement_ladder_rover_rung2_6dof` | CERTIFIED (221) | yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polyno... | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 4; linear |
| `refinement_ladder_rover_rung2b_6dof` | CERTIFIED (216) | yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polyno... | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; linear |
| `refinement_ladder_rover_rung2c_6dof` | CERTIFIED (1368) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `refinement_ladder_rover_rung3_6to8` | CERTIFIED (3079) | yes: STEEP λ=9/4, MODER λ=9/4, FLAT λ=9/4 (polynomial dynamics) | yes: STEEP B=3 via FLAT/MODER/STEEP, MODER B=3 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; quadratic |
| `refinement_ladder_rover_rung4_8to12` | CERTIFIED (971) | yes: STEEP λ=17/10, MODER λ=17/10, FLAT λ=17/10 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `rover3tier_rung12` | CERTIFIED (230) | yes: ACCEL λ=7/4 (affine dynamics) | yes: ACCEL B=6 via ACCEL/COAST, COAST B=4 via ACCEL/COAST | no (max non-self successors at a joint step = 1) | no (nothing pruned) | yes: 4/4 handoffs unsat, rows differ | vacuous: cuts kept (R.ACCEL: 1 conjunct(s); R.COAST: 1 conjunct(s))... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive+linear |
| `rover_dof_terrain_rung1` | CERTIFIED (242) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 3; conjunctive |
| `rover_dof_terrain_rung2` | CERTIFIED (318) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 6; conjunctive |
| `rover_dof_terrain_rung3` | CERTIFIED (317) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `rover_dof_terrain_rung3_8d` | CERTIFIED (325) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; conjunctive |
| `rover_patrol_refine` | CERTIFIED (1562) | yes: SLOW λ=9/4, MEDIUM_ECO λ=9/4, MEDIUM_BRISK λ=9/4, FAST λ=9/4 (... | yes: SLOW B=5 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=5... | yes: SLOW branch=2 | no (nothing pruned) | yes: 10/10 handoffs unsat, rows differ | yes: L.SLOW: 5 conjunct(s); L.MEDIUM_ECO: 5 conjunct(s); L.MEDIUM_B... | yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry... | yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry... | model-refinement; dim 3; conjunctive |
| `rover_patrol_zones` | CERTIFIED (319) | no (λ=1 everywhere) | yes: SLOW B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=2... | yes: SLOW branch=2 | vacuous: pruned SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL... | yes: 10/10 handoffs unsat, rows differ | yes: L.SLOW: 3 conjunct(s); L.MEDIUM_ECO: 3 conjunct(s); L.MEDIUM_B... | vacuous: widened atoms kept (R.STALL: v <= 0.2 kind=closure entry=w... | no (no linear-form atom kept) | degraded-actuator; dim 2; conjunctive |
| `sat3w_detumble_nominal` | CERTIFIED (960) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE | no (max non-self successors at a joint step = 0) | yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.DETUMBLE: 1 conjun... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 6; quadratic |
| `sat3w_detumble_phases` | CERTIFIED (11049) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE, FINE B=2 via DETUMBLE | no (max non-self successors at a joint step = 0) | yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED | yes: 3/3 handoffs unsat, rows differ | yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: ... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 6; quadratic |
| `sat3w_detumble_weak` | CERTIFIED (11776) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via ECONOMY/NOMINAL/SURVIVAL | yes: DETUMBLE branch=2 | yes: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE; NO_PRUNE=... | no (rows identical; handoff vacuous) | yes: L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunct(s); R.ECONOMY... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | degraded-actuator; dim 6; quadratic |
| `sat_detumble_nominal` | CERTIFIED (893) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE | no (max non-self successors at a joint step = 0) | yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.DETUMBLE: 1 conjun... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 4; quadratic |
| `sat_detumble_phases` | CERTIFIED (5406) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via DETUMBLE, FINE B=2 via DETUMBLE | no (max non-self successors at a joint step = 0) | yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED | yes: 3/3 handoffs unsat, rows differ | yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: ... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | model-refinement; dim 4; quadratic |
| `sat_detumble_weak` | CERTIFIED (12129) | no (λ=1 everywhere) | yes: DETUMBLE B=2 via ECONOMY/NOMINAL/SURVIVAL | yes: DETUMBLE branch=2 | yes: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE; NO_PRUNE=... | no (rows identical; handoff vacuous) | yes: L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunct(s); R.ECONOMY... | vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2)... | no (no linear-form atom kept) | degraded-actuator; dim 4; quadratic |
| `story1_attdist_rung_a_6to8` | CERTIFIED (21702) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; conjunctive |
| `story1_attdist_rung_b_12dof` | CERTIFIED (426) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `story2_lateral_rung_a_8dof` | CERTIFIED (1106) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 8; conjunctive |
| `story2_lateral_rung_b_12dof` | CERTIFIED (1488) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; conjunctive |
| `story3_rollover_base_12dof` | CERTIFIED (1197) | yes: STEEP λ=5/4, MODER λ=5/4, FLAT λ=5/4 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; quadratic |
| `story3_rollover_ladder_rung_a` | CERTIFIED (878) | yes: STEEP λ=27/20, MODER λ=27/20, FLAT λ=27/20 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | no (no linear-form atom kept) | model-refinement; dim 12; quadratic |
| `story3_rollover_ladder_rung_b` | CERTIFIED (673) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | yes: L.STEEP: 5 conjunct(s); L.MODER: 5 conjunct(s); L.FLAT: 5 conj... | yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-for... | yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-for... | model-refinement; dim 12; quadratic |
| `watertank` | CERTIFIED (743) | yes: Low λ=2, Mid λ=2 (affine dynamics) | yes: Low B=2 via Low/MidBoost/MidEco, Mid B=2 via High/MidBoost/Mid... | yes: Low branch=2, Mid branch=2 | yes: pruned Low->PumpOff; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.High: 1 conjunct... | yes: L.Low: x <= 15.5 kind=implied-contraction entry=rational route... | no (no linear-form atom kept) | sensor-attack; dim 1; conjunctive |

## 4. The families — stories, parameters, measured covers

Each file's header states the story, the units, the parameters, the claim and the
measured cover; this section summarizes the design and what each member adds.

### 4.1 ACC under sensor spoofing / retune (4; 6 until pass 6)

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
* (`acc_spoof_modes` — the spoofed CRUISE loop alone against the selectable ECO 27 /
  NORMAL 30 / SPORT 33 reference, rows `v_L ≤ v_R ∧ v_R ≤ v_L + 9.5`, M1 M2 M3 M4 — was
  DROPPED in pass 6 (§16.3): its cells are a strict subset of `acc_spoof_limp`'s.)
* `acc_spoof_lag` — refinement of the spoofed vehicle with the powertrain lag, remodeled
  in pass 4 (§13.6): lag time constant 0.4 s (`v' = a, a' = 2.5 (a_cmd − a)`, critically
  damped, double root 1.25), engagement `23 ≤ v ≤ 30`, `|a| ≤ 2`, physical domain
  `|a| ≤ 10` (1 g). The chain `q = a + 1.25 (v − 24) ∈ [−3.25, 9.5]`, `v ∈ [21.4, 31.6]`
  DERIVES the acceleration bound; row = the lifted functional `a_L + 2.5 v_L ≤ 2.5 v_R −
  5.5` (`w = v + 0.4 a`, `w' = a_cmd`), the tightest slack on the 0.25 grid (−5.75
  DECLINED); λ = 5/2, budget 5. DISENGAGE still pruned but no longer load-bearing (the
  derived floor empties the pairing). Pass 5 (§15): the fallback is exercised only from
  slack +3.5 on, where λ = 1 and the chain is not needed (cells M2 M4 only), so the
  tight claim is KEPT. (M1 M2 M6 M6+ M6L)
* (`acc_tune_gain`, the single-reference tune rung, M1 M2 M4, was REPLACED in pass 4 by
  `acc_tune_limp`, whose cells are a superset.)
* `acc_tune_limp` (pass 4) — the tune plus a fault-latched limp-home map (`LIMP: v' = 0.3
  (25 − v)`, entered at 22..30 m/s) against the COMFORT/NORMAL/SPORT reference; rows
  `|v_L − v_R| ≤ 2` (CRUISE; 1.5 DECLINED) and `v_L ≤ v_R + 2 ∧ v_R ≤ v_L + 6.5` (LIMP;
  6.0 DECLINED); λ = 3/2 (CRUISE, budget 3) and 1 (LIMP, budget 2); branching 2; band
  cuts load-bearing; DISENGAGE ×3 pruned. (M1 M2 M3 M4 M5 M6)
* (`acc_tune_modes` — the tuned CRUISE loop alone against the selectable COMFORT 0.4 /
  NORMAL 0.5 / SPORT 0.6 reference, rows `|v_L − v_R| ≤ 2`, M1 M2 M3 M4 M6 — was DROPPED
  in pass 6 (§16.3): its cells are a strict subset of `acc_tune_limp`'s.)
* `acc_tune_lag` — the tune with the powertrain lag, remodeled in pass 4 (§13.6): lag
  0.25 s (`a' = 4 (a_cmd − a)`, over-damped, roots 1 and 3), engagement `25 ≤ v ≤ 30`,
  `|a| ≤ 2`, domain `|a| ≤ 10`; chain `q_1 = a + (v − 30) ∈ [−7, 2]`, `q_3 = a + 3 (v −
  30) ∈ [−17, 2]`, `v ∈ [23, 32]`; row (pass 5, §15) `a_L + 4 v_L ≤ 4 v_R + 16` (`w_L ≤
  v_R + 4`), the tolerance CHOSEN so that the fallback is exercised: the smallest slack
  on the 0.25 grid at which the derived floor `w_L ≥ 24` meets the DISENGAGE region `v_R
  < 20` (15.75: NO_PRUNE CERTIFIED); λ = 5/4, budget 3; DISENGAGE pruned and
  load-bearing (NO_PRUNE DECLINED); the chain is kept but not load-bearing at this slack.
  Tight bound (pass 4, remark): `+ 2` (`w_L ≤ v_R + 0.5`; 1.75 DECLINED), λ = 2, chain
  load-bearing, no M4. (M1 M2 M4)

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
  ABSORB_FAST both cover (branching 2). Row `x_L ≤ x_R + 5`, the tolerance CHOSEN so
  that the fallback is exercised (pass 5, §15: at 4.95 NO_PRUNE CERTIFIES); tight bound
  (remark) `x_L ≤ x_R + 1` (0.95 DECLINED), where M4 is lost. (M2 M3 M4 M6)
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
  `q = a + 2.5 (v − c)`; rows (pass 5, §15) = `a_L + 5 v_L ≤ 5 v_R + 0.35` (`w_L ≤ v_R +
  0.07`) plus the zone margins, the tolerance CHOSEN so that the branching is exercised:
  the smallest slack on the 0.05 grid at which the SLOW window takes a joint step through
  both MEDIUM profiles (+0.30: no branch), and the chain stays load-bearing (at +0.5 it
  branches too but NO_IMPLIED_CUT and NO_LINEAR_CUT certify); λ = 9/4, budget 5, in every
  window; 10 handoffs unsat. Tight bound (pass 4, remark): `− 0.25` (`w_L ≤ v_R − 0.05`;
  −0.5 DECLINED), no branching. (M1 M2 M3 M5 M6 M6+ M6L)
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
cells measured like the rest (except `watertank`, redesigned in pass 8 as the paper's
running example, §18; it now exercises M1 M2 M3 M4 M6 M6+). Four of them exercise no
mechanism of M1–M6 non-vacuously (`refinement_ladder_rover_rung2_3to6`, `rung2c_6dof`,
`story2_lateral_*` ×2) and `story1_*` exercise only M5 — they are kept by the user's rule and reported as measured.

### 4.9 Pass-6 / pass-7 lifts at 6 D (5) — details in §16, §17

* `sat3w_detumble_nominal`, `sat3w_detumble_weak`, `sat3w_detumble_phases` (rigid-body
  family): the gyrostat of §14.2 with THREE reaction wheels, state `(w1, w2, w3, h1, h2,
  h3)`; `E' = −2 k E` still holds through the cancellation of the gyroscopic and
  wheel-coupling cubic terms. Nominal (pass 7): exact `E_L = E_R`, stretch grid
  `λ ∈ [1, 6]` (M2 M4). Weak: 80 % wheel torque vs the NOMINAL / ECONOMY / SURVIVAL
  profiles, row at the analytic `d* = 0.2` (pass 6: 0.205). Phases: DETUMBLE exact, FINE
  (capture envelope `E ≤ 0.2`, gain 0.3, the 4-D constants) row at the analytic
  `d* = 0.08` (pass 6: envelope 0.3, gain 0.35, row 0.095). (M2 M3 M4 M6; M2 M4 M5 M6)
* `platoon3_linkloss`, `platoon3_profiles` (new family "Platoon string, three
  followers"): leader at constant speed plus three CACC followers, (gap, closing rate)
  per link, over-damped links with rational roots 0.25 / 0.5; rows are boxes on
  relational decoupling forms followed by stratified gap bounds; per-follower AEB
  fallbacks pruned through the L7 chain. Link loss on the lead link latches a 35 m
  radar-only stand-off (M2 M4 M5 M6 M6+ M6L); CLOSE / NORMAL / FAR gap profiles (M2 M3 M4
  M6 M6+ M6L). Both on the stretch grid `λ ∈ [1, 6]` since pass 7.

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

12. **Mode-dependent rows need a switch along which the row loosens** (pass 4, §14.1). A
   fault-LATCHED degraded mode (limp-home, radar-only after a link loss, fine pointing at
   a lower gain) gives one naturally: the degraded loop settles lower or slower, its
   tightest row is strictly looser than the nominal mode's, and there is no switch back.
   Where the tighter row belongs to the LATER mode (ACC launch → cruise) the handoff
   fails, and a row scheduled on the left state cannot rescue it unless it stays valid for
   the whole residence (guards are entry conditions); a range-proportional tolerance that
   is valid throughout and coincides with the earlier row on the later mode's guard does
   (`platoon_delay_linkloss`).

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
| rigid-body nominal with the default stretch grid (pass 4) | `sat_detumble_nominal` with λ ∈ [1, 6] | CERTIFIED with pruning, but `RELCERT_NO_PRUNE=1` returns ERROR (`inconclusive Z3 verdict`, 77 s): the joint DETUMBLE segment is `incon` at λ = 3/2, 7/4, 3, 13/4, … (the exact-equality energy rows at a non-unit stretch) | the claim is stated synchronous, λ ∈ [1, 1] (§7 L8); then NO_PRUNE DECLINES. Pass 7 (§17.2): under the new defaults the grid NO_PRUNE run ends in the 40 s time budget instead (no `unknown`); still λ = 1 |
| rigid-body rungs at the analytic tolerance (pass 4) | `sat_detumble_weak` at `d* = 0.2`, `sat_detumble_phases` at `d* = 0.08` | ERROR (`inconclusive Z3 verdict on a candidate route`): at `d*` the boundary is tangent and the cubic route-C query returns `unknown`; 0.205 / 0.085 CERTIFY, 0.15 / 0.07 DECLINE | claims at the smallest certifying slack on the 0.005 grid (§7 L8). Pass 7 (§17.2): the queries need 60–71 M work units and 15–17 s, above the 10 s timeout; claims kept; the 6-D lifts state `d*` |
| `sat_detumble_fast` (pass 4): deployed torquers upsized, `k_L = 0.625`, exact energy rows | built and run | CERTIFIED at λ = 5/4, budget 3 (M1 polynomial, M2) | not added (suite size; the family's three rungs cover nominal, degraded and refined) |
| `acc_spoof_modes`, `acc_tune_modes` (pass 6, Task 3) | in the suite since pass 1 | their matrix cells are strict subsets of the limp-home files that extend them (`acc_spoof_modes` M1 M2 M3 M4 ⊂ `acc_spoof_limp` M1 M2 M3 M4 M5 M6; `acc_tune_modes` M1 M2 M3 M4 M6 ⊂ `acc_tune_limp` M1 M2 M3 M4 M5 M6; same CRUISE loop and reference, the limp files add the latched mode) | **dropped (pass 6)**: redundant 1-D rows; header cross-references in `acc_spoof_limp`, `acc_tune_limp`, `acc_spoof_lag`, `acc_tune_lag` re-pointed (the loops are now defined in the limp headers) |

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

* **L8 — RESOLVED (pass 7, §17).** Not a Z3 limitation: the `unknown` verdicts came from
  the tool's own solver limits (the session's `rlimit`, raised 8 M → 64 M; for the 4-D
  rungs the 10 s per-query timeout), so the 6-D rungs now state their analytic tolerances.

Observed, not a limitation: the one-sided left-leads-right rows and the checked cuts
let the certifier certify every mixed-profile and cross-zone pairing it needed; all 39
inputs certify in under 0.6 s except the 6–12-dof ladders (`story1_attdist_rung_a_6to8`
≈ 20 s, `story3_rollover_ladder_rung_b` ≈ 5 s, the others ≤ 3 s).

## 8. Totals and the proposed Table-1 grouping (generated)

| mechanism | benchmarks (non-vacuous) | count |
|---|---|---|
| M1 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_tune_lag`, `acc_tune_limp`, `match_multi_rate`, `quad_light_airframe_20`, `quad_light_lag`, `quad_light_profiles`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover3tier_rung12`, `rover_patrol_refine`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a`, `watertank` | 17 |
| M2 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_tune_lag`, `acc_tune_limp`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `charger_fast_setpoints`, `charger_fast_tapers`, `match_multi_rate`, `platoon3_linkloss`, `platoon3_profiles`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `quad_light_airframe_20`, `quad_light_lag`, `quad_light_profiles`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover3tier_rung12`, `rover_patrol_refine`, `rover_patrol_zones`, `sat3w_detumble_nominal`, `sat3w_detumble_phases`, `sat3w_detumble_weak`, `sat_detumble_nominal`, `sat_detumble_phases`, `sat_detumble_weak`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a`, `watertank` | 33 |
| M3 | `acc_spoof_limp`, `acc_tune_limp`, `arm_plateau_profiles`, `charger_fast_tapers`, `platoon3_profiles`, `platoon_delay_profiles`, `quad_light_profiles`, `rover_patrol_refine`, `rover_patrol_zones`, `sat3w_detumble_weak`, `sat_detumble_weak`, `watertank` | 12 |
| M4 | `acc_spoof_limp`, `acc_tune_lag`, `acc_tune_limp`, `charger_fast_setpoints`, `charger_fast_tapers`, `match_multi_rate`, `platoon3_linkloss`, `platoon3_profiles`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `quad_light_airframe_20`, `quad_light_profiles`, `sat3w_detumble_nominal`, `sat3w_detumble_phases`, `sat3w_detumble_weak`, `sat_detumble_nominal`, `sat_detumble_phases`, `sat_detumble_weak`, `watertank` | 19 |
| M5 | `acc_spoof_limp`, `acc_tune_limp`, `platoon3_linkloss`, `platoon_delay_linkloss`, `rover3tier_rung12`, `rover_patrol_refine`, `rover_patrol_zones`, `sat3w_detumble_phases`, `sat_detumble_phases`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof`, `story3_rollover_ladder_rung_b` | 12 |
| M6 | `acc_spoof_lag`, `acc_spoof_limp`, `acc_tune_limp`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `charger_fast_setpoints`, `charger_fast_tapers`, `platoon3_linkloss`, `platoon3_profiles`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `refinement_ladder_rover_rung1_2to3`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover_dof_terrain_rung1`, `rover_dof_terrain_rung2`, `rover_dof_terrain_rung3`, `rover_dof_terrain_rung3_8d`, `rover_patrol_refine`, `rover_patrol_zones`, `sat3w_detumble_phases`, `sat3w_detumble_weak`, `sat_detumble_phases`, `sat_detumble_weak`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a`, `story3_rollover_ladder_rung_b`, `watertank` | 29 |
| M6+ | `acc_spoof_lag`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `charger_fast_setpoints`, `platoon3_linkloss`, `platoon3_profiles`, `platoon_delay_linkloss`, `platoon_delay_profiles`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b`, `watertank` | 12 |
| M6L | `acc_spoof_lag`, `arm_plateau_crit`, `arm_plateau_profiles`, `arm_plateau_slow`, `platoon3_linkloss`, `platoon3_profiles`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b` | 8 |
| per-mode domains |  | 0 |

| group | count | dim (L/R) | invariant forms | dynamics | discrete structure (modes L/R; pruned fallbacks; mode-dep. rows; cuts; widened cuts; linear-form chains; per-mode domains) |
|---|---|---|---|---|---|
| ACC under sensor spoofing / retune | 4 | 1, 2 | conjunctive, linear | affine | modes 1-2 / 2-4; 3 with a pruned fallback; 2 mode-dependent; 3 cut-reliant; 1 widened-cut-reliant; 1 linear-form-reliant; 0 per-mode domains |
| Quadrotor climb, lighter airframe | 3 | 1, 2 | conjunctive, linear | polynomial | modes 1-1 / 1-4; 2 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Battery charger | 2 | 1 | linear | affine | modes 3-3 / 4-5; 2 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Platoon follower, delayed link | 2 | 1 | conjunctive | affine | modes 2-3 / 3-4; 2 with a pruned fallback; 1 mode-dependent; 2 cut-reliant; 2 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Platoon string, three followers | 2 | 6 | conjunctive | affine | modes 1-2 / 4-6; 2 with a pruned fallback; 1 mode-dependent; 2 cut-reliant; 2 widened-cut-reliant; 2 linear-form-reliant; 0 per-mode domains |
| Rover patrol (zones) | 4 | 2, 3 | conjunctive, conjunctive+linear, linear | affine | modes 2-4 / 2-5; 1 with a pruned fallback; 3 mode-dependent; 2 cut-reliant; 1 widened-cut-reliant; 1 linear-form-reliant; 0 per-mode domains |
| Arm, leading reference | 3 | 2/1 | linear | affine | modes 2-2 / 4-5; 0 with a pruned fallback; 0 mode-dependent; 3 cut-reliant; 3 widened-cut-reliant; 3 linear-form-reliant; 0 per-mode domains |
| Rigid-body detumbling (polynomial) | 6 | 4, 6 | quadratic | polynomial | modes 1-2 / 2-4; 6 with a pruned fallback; 2 mode-dependent; 4 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Terrain/position ladder | 11 | 3/2, 3, 4, 6, 8, 12 | conjunctive, linear, quadratic | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 7 cut-reliant; 0 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| Story ladders | 7 | 8, 12 | conjunctive, quadratic | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 3 mode-dependent; 3 cut-reliant; 1 widened-cut-reliant; 1 linear-form-reliant; 0 per-mode domains |
| Watertank | 1 | 1 | conjunctive | affine | modes 3-3 / 5-5; 1 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 1 widened-cut-reliant; 0 linear-form-reliant; 0 per-mode domains |
| **total** | **45** | | | | |

Duplicate check: no two benchmarks normalize to the same model; no two benchmarks differ only in tolerance constants (rows' numerals masked)

## 9. Per-benchmark run records (generated)

### `acc_spoof_lag`

* family: ACC under sensor spoofing / retune; scenario: model-refinement; dims L/R 2/2; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `c6dd3244026b`
* `relcert`: **CERTIFIED** (170 ms); `[prune] acc_spoof_lag: [CRUISE->DISENGAGE]`; NO_PRUNE: **CERTIFIED** (191 ms); NO_CUT: **DECLINED** (322 ms); NO_IMPLIED_CUT: **DECLINED** (358 ms); NO_LINEAR_CUT: **DECLINED** (361 ms); domains: uniform
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
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (91 ms)
* cover `CRUISE_L`: λ = 5/2, budget 5, admissible ['CRUISE'], flags {'CRUISE': 'j--', 'DISENGAGE': 'j--'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=5)->[CRUISE@4, CRUISE@4]; CRUISE:joint(B=4)->[CRUISE@3, CRUISE@3]; CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/2 (affine dynamics); **M2** yes: CRUISE B=5 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** vacuous: pruned CRUISE->DISENGAGE but NO_PRUNE=CERTIFIED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.CRUISE: 4 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1.25 * (v - 24))) >= -3.25 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 31.6 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) <= 9.5]; L.CRUISE: v >= 21.4 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) >= -3.25]; R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape; NO_IMPLIED=DECLINED; **M6L** yes: L.CRUISE: (a + (1.25 * (v - 24))) <= 9.5 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1.25 * (v - 24))) >= -3.25 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 31.6 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) <= 9.5]; L.CRUISE: v >= 21.4 kind=derived-bound entry=rational route=derived-shape given=[(a + (1.25 * (v - 24))) >= -3.25]; NO_LINEAR=DECLINED

### `acc_spoof_limp`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `900d3e553813`
* `relcert`: **CERTIFIED** (291 ms); `[prune] acc_spoof_limp: [NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1178 ms); NO_CUT: **DECLINED** (1167 ms); NO_IMPLIED_CUT: **CERTIFIED** (278 ms); NO_LINEAR_CUT: **CERTIFIED** (278 ms); domains: uniform
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
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (92 ms)
* cover `CRUISE_L`: λ = 5/4, budget 3, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j--', 'ECO': 'j--', 'SPORT': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1); ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]`
    * from `ECO`: `ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; SPORT:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; ECO:base(B=1)`
* cover `LIMP_L`: λ = 1, budget 2, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j--', 'ECO': 'j--', 'SPORT': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1)`
    * from `ECO`: `ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/4 (affine dynamics); **M2** yes: CRUISE B=3 via ECO/NORMAL/SPORT, LIMP B=2 via ECO/NORMAL/SPORT; **M3** yes: CRUISE branch=2, LIMP branch=2; **M4** yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.ECO: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB; R.NORMAL: v <= 40.0 kind=closure entry=weakening route=shape; R.ECO: v <= 40.0 kind=closure entry=weakening route=shape; R.SPORT: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `acc_tune_lag`

* family: ACC under sensor spoofing / retune; scenario: model-refinement; dims L/R 2/2; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `c6109b9b9468`
* `relcert`: **CERTIFIED** (83 ms); `[prune] acc_tune_lag: [CRUISE->DISENGAGE]`; NO_PRUNE: **DECLINED** (336 ms); NO_CUT: **CERTIFIED** (114 ms); NO_IMPLIED_CUT: **CERTIFIED** (148 ms); NO_LINEAR_CUT: **CERTIFIED** (157 ms); domains: uniform
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
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (93 ms)
* cover `CRUISE_L`: λ = 5/4, budget 3, admissible ['CRUISE'], flags {'CRUISE': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/4 (affine dynamics); **M2** yes: CRUISE B=3 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 6 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.CRUISE: (a + (1 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1 * (v - 30))) >= -7 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) >= -17 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 32 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) <= 2]; L.CRUISE: v >= 23 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) >= -7]; R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** vacuous: linear-form atoms kept (L.CRUISE: (a + (1 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (1 * (v - 30))) >= -7 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; L.CRUISE: (a + (3 * (v - 30))) >= -17 kind=linear-form entry=rational route=linear-shape; L.CRUISE: v <= 32 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) <= 2]; L.CRUISE: v >= 23 kind=derived-bound entry=rational route=derived-shape given=[(a + (1 * (v - 30))) >= -7]) but NO_LINEAR=CERTIFIED

### `acc_tune_limp`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `68a8a66b01d8`
* `relcert`: **CERTIFIED** (333 ms); `[prune] acc_tune_limp: [NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1072 ms); NO_CUT: **DECLINED** (1011 ms); NO_IMPLIED_CUT: **CERTIFIED** (255 ms); NO_LINEAR_CUT: **CERTIFIED** (342 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] L.LIMP: 2 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.COMFORT: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [NORMAL, COMFORT, SPORT]`
* `[admissible] LIMP_L: [NORMAL, COMFORT, SPORT]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (35 ms)
* cover `CRUISE_L`: λ = 3/2, budget 3, admissible ['NORMAL', 'COMFORT', 'SPORT'], flags {'NORMAL': 'j--', 'COMFORT': 'j--', 'SPORT': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['COMFORT', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, COMFORT@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:base(B=1); SPORT:base(B=1); COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]`
    * from `COMFORT`: `COMFORT:joint(B=3)->[COMFORT@2, COMFORT@2, NORMAL@2]; COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; COMFORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; SPORT:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; COMFORT:base(B=1)`
* cover `LIMP_L`: λ = 1, budget 2, admissible ['NORMAL', 'COMFORT', 'SPORT'], flags {'NORMAL': 'j--', 'COMFORT': 'j--', 'SPORT': 'j--', 'DISENGAGE': '---'}, kinds ['base', 'joint'], path modes ['COMFORT', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, COMFORT@1, SPORT@1]; NORMAL:base(B=1); COMFORT:base(B=1); SPORT:base(B=1)`
    * from `COMFORT`: `COMFORT:joint(B=2)->[COMFORT@1, COMFORT@1, NORMAL@1]; COMFORT:base(B=1); NORMAL:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=3 via COMFORT/NORMAL/SPORT, LIMP B=2 via COMFORT/NORMAL/SPORT; **M3** yes: CRUISE branch=2, LIMP branch=2; **M4** yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.CRUISE: 2 conjunct(s); L.LIMP: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.COMFORT: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `arm_plateau_crit`

* family: Arm, leading reference; scenario: model-refinement; dims L/R 2/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `90ef24b3b08e`
* `relcert`: **CERTIFIED** (177 ms); `[prune] arm_plateau_crit: []`; NO_PRUNE: **CERTIFIED** (176 ms); NO_CUT: **DECLINED** (407 ms); NO_IMPLIED_CUT: **DECLINED** (443 ms); NO_LINEAR_CUT: **DECLINED** (371 ms); domains: uniform
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
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (22 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'jdd', 'ApproachB': 'jdd', 'ApproachC': 'jdd', 'Hold': 'jdd'}, kinds ['base', 'joint'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only False
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': '-dd', 'ApproachB': 'jdd', 'ApproachC': 'jdd', 'Hold': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:repoDyn(B=2,preJ)->[ApproachB@2]; ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/ApproachB/ApproachC/Hold, Brake B=2 via ApproachB/ApproachC/Hold +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.Accelerate: 4 conjunct(s); L.Brake: 2 conjunct(s); R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachC: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB; L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** yes: L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; NO_LINEAR=DECLINED

### `arm_plateau_profiles`

* family: Arm, leading reference; scenario: degraded-controller; dims L/R 2/1; modes L/R 2/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `a1d06af51c8d`
* `relcert`: **CERTIFIED** (125 ms); `[prune] arm_plateau_profiles: []`; NO_PRUNE: **CERTIFIED** (185 ms); NO_CUT: **DECLINED** (449 ms); NO_IMPLIED_CUT: **DECLINED** (540 ms); NO_LINEAR_CUT: **DECLINED** (423 ms); domains: uniform
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
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (90 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], flags {'ApproachA': 'jdd', 'ApproachB': 'jdd', 'ApproachCfast': 'jdd', 'ApproachCslow': 'jdd', 'Hold': 'jdd'}, kinds ['base', 'joint'], path modes ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], branching 2, right-only False
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachCfast@1, ApproachCslow@1, ApproachB@1]; ApproachB:base(B=1); ApproachCfast:base(B=1); ApproachCslow:base(B=1)`
    * from `ApproachCfast`: `ApproachCfast:joint(B=2)->[ApproachCfast@1, Hold@1, ApproachCfast@1]; ApproachCfast:base(B=1); Hold:base(B=1)`
    * from `ApproachCslow`: `ApproachCslow:joint(B=2)->[ApproachCslow@1, Hold@1, ApproachCslow@1]; ApproachCslow:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], flags {'ApproachA': 'jdd', 'ApproachB': 'jdd', 'ApproachCfast': 'jdd', 'ApproachCslow': 'jdd', 'Hold': 'jdd'}, kinds ['base', 'joint'], path modes ['ApproachA', 'ApproachB', 'ApproachCfast', 'ApproachCslow', 'Hold'], branching 2, right-only False
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:base(B=1)`
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachCfast@1, ApproachCslow@1, ApproachB@1]; ApproachB:base(B=1); ApproachCfast:base(B=1); ApproachCslow:base(B=1)`
    * from `ApproachCfast`: `ApproachCfast:joint(B=2)->[ApproachCfast@1, Hold@1, ApproachCfast@1]; ApproachCfast:base(B=1); Hold:base(B=1)`
    * from `ApproachCslow`: `ApproachCslow:joint(B=2)->[ApproachCslow@1, Hold@1, ApproachCslow@1]; ApproachCslow:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/ApproachB/ApproachCfast/ApproachCslow/Hold, Brake B=2 via ApproachA/ApproachB/ApproachCfast/ApproachCslow/Hold; **M3** yes: Accelerate branch=2, Brake branch=2; **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachCfast: 1 conjunct(s); R.ApproachCslow: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB; L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.1775 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.1775]; R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (1 * (theta - 0.5))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (1 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.1775 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (1 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.855 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.1775]; NO_LINEAR=DECLINED

### `arm_plateau_slow`

* family: Arm, leading reference; scenario: degraded-actuator; dims L/R 2/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `19259816447b`
* `relcert`: **CERTIFIED** (174 ms); `[prune] arm_plateau_slow: []`; NO_PRUNE: **CERTIFIED** (133 ms); NO_CUT: **DECLINED** (409 ms); NO_IMPLIED_CUT: **DECLINED** (426 ms); NO_LINEAR_CUT: **DECLINED** (355 ms); domains: uniform
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
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (83 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'jdd', 'ApproachB': '-dd', 'ApproachC': 'jdd', 'Hold': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:base(B=1)`
    * from `ApproachB`: `ApproachB:repoDyn(B=2,preJ)->[ApproachC@2]; ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'jdd', 'ApproachB': 'jdd', 'ApproachC': 'jdd', 'Hold': 'jdd'}, kinds ['base', 'joint'], path modes ['ApproachB', 'ApproachC', 'Hold'], branching 1, right-only False
    * from `ApproachB`: `ApproachB:joint(B=2)->[ApproachB@1, ApproachC@1, ApproachB@1]; ApproachB:base(B=1); ApproachC:base(B=1)`
    * from `ApproachC`: `ApproachC:joint(B=2)->[ApproachC@1, Hold@1, ApproachC@1]; ApproachC:base(B=1); Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/ApproachC/Hold +RO, Brake B=2 via ApproachB/ApproachC/Hold; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.Accelerate: 6 conjunct(s); L.Brake: 3 conjunct(s); R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachC: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB; L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) >= -1 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (2 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.08875 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.08875]; R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** yes: L.Accelerate: (v + (0.5 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (0.5 * (theta - 0.5))) >= -0.25 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Accelerate: (v + (2 * (theta - 0.5))) >= -1 kind=linear-form entry=rational route=linear-shape; L.Accelerate: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (2 * (theta - 0.5))) <= 0.355]; L.Brake: (v + (0.5 * (theta - 0.5))) <= 0.08875 kind=linear-form entry=rational route=linear-shape; L.Brake: (v + (2 * (theta - 0.5))) <= 0.355 kind=linear-form entry=rational route=linear-shape; L.Brake: theta <= 0.6775 kind=derived-bound entry=rational route=derived-shape given=[(v + (0.5 * (theta - 0.5))) <= 0.08875]; NO_LINEAR=DECLINED

### `charger_fast_setpoints`

* family: Battery charger; scenario: degraded-controller; dims L/R 1/1; modes L/R 3/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `a4fc327fbdea`
* `relcert`: **CERTIFIED** (196 ms); `[prune] charger_fast_setpoints: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (464 ms); NO_CUT: **DECLINED** (496 ms); NO_IMPLIED_CUT: **DECLINED** (514 ms); NO_LINEAR_CUT: **CERTIFIED** (187 ms); domains: uniform
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
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (79 ms)
* cover `BULK_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB', 'FULL'], flags {'BULK': '-dd', 'ABSORB': 'jdd', 'FULL': 'jdd', 'FAULT': '---'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only True
    * from `BULK`: `BULK:repoDyn(B=2,preJ)->[ABSORB@2]; ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `ABSORB_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB', 'FULL'], flags {'BULK': '-dd', 'ABSORB': 'jdd', 'FULL': 'jdd', 'FAULT': 'j--'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only True
    * from `BULK`: `BULK:repoDyn(B=2,preJ)->[ABSORB@2]; ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FULL_L`: λ = 1, budget 2, admissible ['ABSORB', 'FULL'], flags {'BULK': 'jdd', 'ABSORB': 'jdd', 'FULL': 'jdd', 'FAULT': 'j--'}, kinds ['base', 'joint'], path modes ['ABSORB', 'FULL'], branching 1, right-only False
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: BULK B=2 via ABSORB/FULL +RO, ABSORB B=2 via ABSORB/FULL +RO, FULL B=2 via ABSORB/FULL; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape; R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `charger_fast_tapers`

* family: Battery charger; scenario: degraded-controller; dims L/R 1/1; modes L/R 3/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `956f8ffbe687`
* `relcert`: **CERTIFIED** (222 ms); `[prune] charger_fast_tapers: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (550 ms); NO_CUT: **DECLINED** (552 ms); NO_IMPLIED_CUT: **CERTIFIED** (193 ms); NO_LINEAR_CUT: **CERTIFIED** (224 ms); domains: uniform
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
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (95 ms)
* cover `BULK_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'BULK': '-dd', 'ABSORB_SLOW': '-dd', 'ABSORB_FAST': '-dd', 'FULL': 'jdd', 'FAULT': '---'}, kinds ['base', 'joint', 'repoDyn'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FULL'], branching 0, right-only True
    * from `BULK`: `BULK:repoDyn(B=2,preJ)->[ABSORB_SLOW@2, ABSORB_FAST@2]; ABSORB_SLOW:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1); ABSORB_FAST:repoDyn(B=2,preJ)->[FULL@2]`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:repoDyn(B=2,preJ)->[FULL@2]; FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `ABSORB_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'BULK': 'jdd', 'ABSORB_SLOW': 'jdd', 'ABSORB_FAST': 'jdd', 'FULL': 'jdd', 'FAULT': 'j--'}, kinds ['base', 'joint'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'BULK', 'FULL'], branching 2, right-only False
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB_SLOW@1, ABSORB_FAST@1, BULK@1]; BULK:base(B=1); ABSORB_SLOW:base(B=1); ABSORB_FAST:base(B=1)`
    * from `ABSORB_SLOW`: `ABSORB_SLOW:joint(B=2)->[ABSORB_SLOW@1, FULL@1, ABSORB_SLOW@1]; ABSORB_SLOW:base(B=1); FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FULL_L`: λ = 1, budget 2, admissible ['ABSORB_SLOW', 'ABSORB_FAST', 'FULL'], flags {'BULK': 'jdd', 'ABSORB_SLOW': 'jdd', 'ABSORB_FAST': 'jdd', 'FULL': 'jdd', 'FAULT': 'j--'}, kinds ['base', 'joint'], path modes ['ABSORB_FAST', 'ABSORB_SLOW', 'FULL'], branching 1, right-only False
    * from `ABSORB_SLOW`: `ABSORB_SLOW:joint(B=2)->[ABSORB_SLOW@1, FULL@1, ABSORB_SLOW@1]; ABSORB_SLOW:base(B=1); FULL:base(B=1)`
    * from `ABSORB_FAST`: `ABSORB_FAST:joint(B=2)->[ABSORB_FAST@1, FULL@1, ABSORB_FAST@1]; ABSORB_FAST:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: BULK B=2 via FULL +RO, ABSORB B=2 via ABSORB_FAST/ABSORB_SLOW/BULK/FULL, FULL B=2 via ABSORB_FAST/ABSORB_SLOW/FULL; **M3** yes: ABSORB branch=2; **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB_SLOW: 2 conjunct(s); R.ABSORB_FAST: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_SLOW: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_FAST: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `match_multi_rate`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 2/2; modes L/R 4/2; εL/εR 0.3/0.3; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `8ea18edaad94`
* `relcert`: **CERTIFIED** (298 ms); `[prune] match_multi_rate: [DRIVE->STALL]`; NO_PRUNE: **DECLINED** (347 ms); NO_CUT: **CERTIFIED** (277 ms); NO_IMPLIED_CUT: **CERTIFIED** (284 ms); NO_LINEAR_CUT: **CERTIFIED** (311 ms); domains: uniform
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
* `--handoff`: 8/8 checked, 8 passed, failing -, VACUOUS (identical rows) (30 ms)
* cover `FAST_L`: λ = 3, budget 3, admissible ['DRIVE'], flags {'DRIVE': 'jdd', 'STALL': '---'}, kinds ['base', 'joint'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:joint(B=3)->[DRIVE@2, DRIVE@2]; DRIVE:joint(B=2)->[DRIVE@1, DRIVE@1]; DRIVE:base(B=1)`
* cover `MEDIUM_L`: λ = 2, budget 2, admissible ['DRIVE'], flags {'DRIVE': 'jdd', 'STALL': 'j--'}, kinds ['base', 'joint'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:joint(B=2)->[DRIVE@1, DRIVE@1]; DRIVE:base(B=1)`
* cover `SLOW_L`: λ = 1, budget 1, admissible ['DRIVE'], flags {'DRIVE': 'jdd', 'STALL': 'j--'}, kinds ['base'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:base(B=1)`
* cover `RESET_L`: λ = 1, budget 1, admissible ['DRIVE'], flags {'DRIVE': 'jdd', 'STALL': '---'}, kinds ['base'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:base(B=1)`
* cells: **M1** yes: FAST λ=3, MEDIUM λ=2 (affine dynamics); **M2** yes: FAST B=3 via DRIVE, MEDIUM B=2 via DRIVE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned DRIVE->STALL; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.FAST: 2 conjunct(s); L.MEDIUM: 2 conjunct(s); L.SLOW: 2 conjunct(s); L.RESET: 2 conjunct(s); R.DRIVE: 2 conjunct(s); R.STALL: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.FAST: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.MEDIUM: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.SLOW: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.RESET: v <= 1.0 kind=closure entry=weakening route=shape; L.RESET: v >= 0.1 kind=implied-contraction entry=rational route=shape; R.STALL: v <= 0.2 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `platoon3_linkloss`

* family: Platoon string, three followers; scenario: sensor-attack; dims L/R 6/6; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `eeb34fa84a9e`
* `relcert`: **CERTIFIED** (2159 ms); `[prune] platoon3_linkloss: [FOLLOW->BRAKE1, FOLLOW->BRAKE2, FOLLOW->BRAKE3]`; NO_PRUNE: **DECLINED** (11706 ms); NO_CUT: **DECLINED** (7847 ms); NO_IMPLIED_CUT: **DECLINED** (7952 ms); NO_LINEAR_CUT: **DECLINED** (8028 ms); domains: uniform
* `[cut] L.FOLLOW: 24 conjunct(s)`
* `[cut] L.LOST: 24 conjunct(s)`
* `[cut] R.FOLLOW: 24 conjunct(s)`
* `[cut-x] L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r1 + (0.25 * (g1 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r1 + (0.5 * (g1 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r1 + (0.5 * (g1 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) <= 2]`
* `[cut-x] L.FOLLOW: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) >= -2]`
* `[cut-x] L.FOLLOW: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) <= 3]`
* `[cut-x] L.FOLLOW: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) >= -3]`
* `[cut-x] L.FOLLOW: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]`
* `[cut-x] L.FOLLOW: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]`
* `[cut-x] L.FOLLOW: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]`
* `[cut-x] L.FOLLOW: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]`
* `[cut-x] L.FOLLOW: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]`
* `[cut-x] L.FOLLOW: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]`
* `[cut-x] L.FOLLOW: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]`
* `[cut-x] L.FOLLOW: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]`
* `[cut-x] L.LOST: (r1 + (0.25 * (g1 - 35))) <= 0.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r1 + (0.25 * (g1 - 35))) >= -3.5 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r1 + (0.5 * (g1 - 35))) <= 0 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r1 + (0.5 * (g1 - 35))) >= -6 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.LOST: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 35))) <= 0.5]`
* `[cut-x] L.LOST: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 35))) >= -3.5]`
* `[cut-x] L.LOST: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 35))) <= 0]`
* `[cut-x] L.LOST: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 35))) >= -6]`
* `[cut-x] L.LOST: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]`
* `[cut-x] L.LOST: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]`
* `[cut-x] L.LOST: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]`
* `[cut-x] L.LOST: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]`
* `[cut-x] L.LOST: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]`
* `[cut-x] L.LOST: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]`
* `[cut-x] L.LOST: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]`
* `[cut-x] L.LOST: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]`
* `[cut-x] R.FOLLOW: (r1 + (0.25 * (g1 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r1 + (0.25 * (g1 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r1 + (0.5 * (g1 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r1 + (0.5 * (g1 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r2 + (0.25 * (g2 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r2 + (0.25 * (g2 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r2 + (0.5 * (g2 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r2 + (0.5 * (g2 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r3 + (0.25 * (g3 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r3 + (0.25 * (g3 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r3 + (0.5 * (g3 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: (r3 + (0.5 * (g3 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FOLLOW: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) <= 2]`
* `[cut-x] R.FOLLOW: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) >= -2]`
* `[cut-x] R.FOLLOW: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) <= 3]`
* `[cut-x] R.FOLLOW: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) >= -3]`
* `[cut-x] R.FOLLOW: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) <= 2]`
* `[cut-x] R.FOLLOW: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) >= -2]`
* `[cut-x] R.FOLLOW: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) <= 3]`
* `[cut-x] R.FOLLOW: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) >= -3]`
* `[cut-x] R.FOLLOW: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) <= 2]`
* `[cut-x] R.FOLLOW: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) >= -2]`
* `[cut-x] R.FOLLOW: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) <= 3]`
* `[cut-x] R.FOLLOW: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) >= -3]`
* `[admissible] FOLLOW_L: [FOLLOW]`
* `[admissible] LOST_L: [FOLLOW]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (84 ms)
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['FOLLOW'], flags {'FOLLOW': 'j--', 'BRAKE1': '---', 'BRAKE2': '---', 'BRAKE3': '---'}, kinds ['base', 'joint'], path modes ['FOLLOW'], branching 0, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, FOLLOW@1]; FOLLOW:base(B=1)`
* cover `LOST_L`: λ = 1, budget 2, admissible ['FOLLOW'], flags {'FOLLOW': 'j--', 'BRAKE1': '---', 'BRAKE2': '---', 'BRAKE3': '---'}, kinds ['base', 'joint'], path modes ['FOLLOW'], branching 0, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, FOLLOW@1]; FOLLOW:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via FOLLOW, LOST B=2 via FOLLOW; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned FOLLOW->BRAKE1, FOLLOW->BRAKE2, FOLLOW->BRAKE3; NO_PRUNE=DECLINED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.FOLLOW: 24 conjunct(s); L.LOST: 24 conjunct(s); R.FOLLOW: 24 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.25 * (g1 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) <= 2]; L.FOLLOW: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) >= -2]; L.FOLLOW: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) <= 3]; L.FOLLOW: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) >= -3]; L.FOLLOW: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]; L.FOLLOW: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]; L.FOLLOW: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]; L.FOLLOW: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]; L.FOLLOW: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]; L.FOLLOW: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]; L.FOLLOW: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]; L.FOLLOW: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]; L.LOST: (r1 + (0.25 * (g1 - 35))) <= 0.5 kind=linear-form entry=rational route=linear-shape; L.LOST: (r1 + (0.25 * (g1 - 35))) >= -3.5 kind=linear-form entry=rational route=linear-shape; L.LOST: (r1 + (0.5 * (g1 - 35))) <= 0 kind=linear-form entry=rational route=linear-shape; L.LOST: (r1 + (0.5 * (g1 - 35))) >= -6 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.LOST: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 35))) <= 0.5]; L.LOST: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 35))) >= -3.5]; L.LOST: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 35))) <= 0]; L.LOST: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 35))) >= -6]; L.LOST: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]; L.LOST: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]; L.LOST: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]; L.LOST: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]; L.LOST: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]; L.LOST: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]; L.LOST: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]; L.LOST: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]; R.FOLLOW: (r1 + (0.25 * (g1 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r1 + (0.25 * (g1 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r1 + (0.5 * (g1 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r1 + (0.5 * (g1 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.25 * (g2 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.25 * (g2 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.5 * (g2 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.5 * (g2 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.25 * (g3 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.25 * (g3 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.5 * (g3 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.5 * (g3 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) <= 2]; R.FOLLOW: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) >= -2]; R.FOLLOW: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) <= 3]; R.FOLLOW: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) >= -3]; R.FOLLOW: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) <= 2]; R.FOLLOW: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) >= -2]; R.FOLLOW: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) <= 3]; R.FOLLOW: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) >= -3]; R.FOLLOW: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) <= 2]; R.FOLLOW: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) >= -2]; R.FOLLOW: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) <= 3]; R.FOLLOW: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) >= -3]; NO_IMPLIED=DECLINED; **M6L** yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.25 * (g1 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) <= 2]; L.FOLLOW: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) >= -2]; L.FOLLOW: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) <= 3]; L.FOLLOW: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) >= -3]; L.FOLLOW: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]; L.FOLLOW: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]; L.FOLLOW: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]; L.FOLLOW: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]; L.FOLLOW: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]; L.FOLLOW: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]; L.FOLLOW: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]; L.FOLLOW: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]; L.LOST: (r1 + (0.25 * (g1 - 35))) <= 0.5 kind=linear-form entry=rational route=linear-shape; L.LOST: (r1 + (0.25 * (g1 - 35))) >= -3.5 kind=linear-form entry=rational route=linear-shape; L.LOST: (r1 + (0.5 * (g1 - 35))) <= 0 kind=linear-form entry=rational route=linear-shape; L.LOST: (r1 + (0.5 * (g1 - 35))) >= -6 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.LOST: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.LOST: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.LOST: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 35))) <= 0.5]; L.LOST: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 35))) >= -3.5]; L.LOST: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 35))) <= 0]; L.LOST: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 35))) >= -6]; L.LOST: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]; L.LOST: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]; L.LOST: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]; L.LOST: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]; L.LOST: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]; L.LOST: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]; L.LOST: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]; L.LOST: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]; R.FOLLOW: (r1 + (0.25 * (g1 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r1 + (0.25 * (g1 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r1 + (0.5 * (g1 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r1 + (0.5 * (g1 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.25 * (g2 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.25 * (g2 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.5 * (g2 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r2 + (0.5 * (g2 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.25 * (g3 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.25 * (g3 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.5 * (g3 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: (r3 + (0.5 * (g3 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FOLLOW: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) <= 2]; R.FOLLOW: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) >= -2]; R.FOLLOW: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) <= 3]; R.FOLLOW: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) >= -3]; R.FOLLOW: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) <= 2]; R.FOLLOW: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) >= -2]; R.FOLLOW: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) <= 3]; R.FOLLOW: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) >= -3]; R.FOLLOW: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) <= 2]; R.FOLLOW: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) >= -2]; R.FOLLOW: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) <= 3]; R.FOLLOW: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) >= -3]; NO_LINEAR=DECLINED

### `platoon3_profiles`

* family: Platoon string, three followers; scenario: sensor-attack; dims L/R 6/6; modes L/R 1/6; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `fcf76a121d4b`
* `relcert`: **CERTIFIED** (2227 ms); `[prune] platoon3_profiles: [NORMAL->BRAKE1, NORMAL->BRAKE2, NORMAL->BRAKE3, CLOSE->BRAKE1, CLOSE->BRAKE2, CLOSE->BRAKE3, FAR->BRAKE1, FAR->BRAKE2, FAR->BRAKE3]`; NO_PRUNE: **DECLINED** (29404 ms); NO_CUT: **DECLINED** (18040 ms); NO_IMPLIED_CUT: **DECLINED** (18026 ms); NO_LINEAR_CUT: **DECLINED** (18204 ms); domains: uniform
* `[cut] L.FOLLOW: 24 conjunct(s)`
* `[cut] R.NORMAL: 24 conjunct(s)`
* `[cut] R.CLOSE: 24 conjunct(s)`
* `[cut] R.FAR: 24 conjunct(s)`
* `[cut-x] L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r1 + (0.25 * (g1 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r1 + (0.5 * (g1 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r1 + (0.5 * (g1 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] L.FOLLOW: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) <= 2]`
* `[cut-x] L.FOLLOW: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) >= -2]`
* `[cut-x] L.FOLLOW: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) <= 3]`
* `[cut-x] L.FOLLOW: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) >= -3]`
* `[cut-x] L.FOLLOW: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]`
* `[cut-x] L.FOLLOW: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]`
* `[cut-x] L.FOLLOW: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]`
* `[cut-x] L.FOLLOW: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]`
* `[cut-x] L.FOLLOW: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]`
* `[cut-x] L.FOLLOW: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]`
* `[cut-x] L.FOLLOW: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]`
* `[cut-x] L.FOLLOW: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]`
* `[cut-x] R.NORMAL: (r1 + (0.25 * (g1 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r1 + (0.25 * (g1 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r1 + (0.5 * (g1 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r1 + (0.5 * (g1 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r2 + (0.25 * (g2 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r2 + (0.25 * (g2 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r2 + (0.5 * (g2 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r2 + (0.5 * (g2 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r3 + (0.25 * (g3 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r3 + (0.25 * (g3 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r3 + (0.5 * (g3 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: (r3 + (0.5 * (g3 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.NORMAL: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) <= 2]`
* `[cut-x] R.NORMAL: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) >= -2]`
* `[cut-x] R.NORMAL: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) <= 3]`
* `[cut-x] R.NORMAL: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) >= -3]`
* `[cut-x] R.NORMAL: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) <= 2]`
* `[cut-x] R.NORMAL: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) >= -2]`
* `[cut-x] R.NORMAL: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) <= 3]`
* `[cut-x] R.NORMAL: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) >= -3]`
* `[cut-x] R.NORMAL: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) <= 2]`
* `[cut-x] R.NORMAL: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) >= -2]`
* `[cut-x] R.NORMAL: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) <= 3]`
* `[cut-x] R.NORMAL: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) >= -3]`
* `[cut-x] R.CLOSE: (r1 + (0.25 * (g1 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r1 + (0.25 * (g1 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r1 + (0.5 * (g1 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r1 + (0.5 * (g1 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r2 + (0.25 * (g2 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r2 + (0.25 * (g2 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r2 + (0.5 * (g2 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r2 + (0.5 * (g2 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r3 + (0.25 * (g3 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r3 + (0.25 * (g3 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r3 + (0.5 * (g3 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: (r3 + (0.5 * (g3 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.CLOSE: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 28))) <= 2]`
* `[cut-x] R.CLOSE: g1 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 28))) >= -2]`
* `[cut-x] R.CLOSE: g1 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 28))) <= 3]`
* `[cut-x] R.CLOSE: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 28))) >= -3]`
* `[cut-x] R.CLOSE: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 28))) <= 2]`
* `[cut-x] R.CLOSE: g2 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 28))) >= -2]`
* `[cut-x] R.CLOSE: g2 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 28))) <= 3]`
* `[cut-x] R.CLOSE: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 28))) >= -3]`
* `[cut-x] R.CLOSE: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 28))) <= 2]`
* `[cut-x] R.CLOSE: g3 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 28))) >= -2]`
* `[cut-x] R.CLOSE: g3 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 28))) <= 3]`
* `[cut-x] R.CLOSE: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 28))) >= -3]`
* `[cut-x] R.FAR: (r1 + (0.25 * (g1 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r1 + (0.25 * (g1 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r1 + (0.5 * (g1 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r1 + (0.5 * (g1 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r2 + (0.25 * (g2 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r2 + (0.25 * (g2 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r2 + (0.5 * (g2 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r2 + (0.5 * (g2 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r3 + (0.25 * (g3 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r3 + (0.25 * (g3 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r3 + (0.5 * (g3 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: (r3 + (0.5 * (g3 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape`
* `[cut-x] R.FAR: g1 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 32))) <= 2]`
* `[cut-x] R.FAR: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 32))) >= -2]`
* `[cut-x] R.FAR: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 32))) <= 3]`
* `[cut-x] R.FAR: g1 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 32))) >= -3]`
* `[cut-x] R.FAR: g2 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 32))) <= 2]`
* `[cut-x] R.FAR: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 32))) >= -2]`
* `[cut-x] R.FAR: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 32))) <= 3]`
* `[cut-x] R.FAR: g2 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 32))) >= -3]`
* `[cut-x] R.FAR: g3 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 32))) <= 2]`
* `[cut-x] R.FAR: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 32))) >= -2]`
* `[cut-x] R.FAR: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 32))) <= 3]`
* `[cut-x] R.FAR: g3 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 32))) >= -3]`
* `[admissible] FOLLOW_L: [NORMAL, CLOSE, FAR]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (88 ms)
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['NORMAL', 'CLOSE', 'FAR'], flags {'NORMAL': 'j--', 'CLOSE': 'j--', 'FAR': 'j--', 'BRAKE1': '---', 'BRAKE2': '---', 'BRAKE3': '---'}, kinds ['base', 'joint'], path modes ['CLOSE', 'FAR', 'NORMAL'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, CLOSE@1, FAR@1]; NORMAL:base(B=1); CLOSE:base(B=1); FAR:base(B=1)`
    * from `CLOSE`: `CLOSE:joint(B=2)->[CLOSE@1, CLOSE@1, NORMAL@1]; CLOSE:base(B=1); NORMAL:base(B=1)`
    * from `FAR`: `FAR:joint(B=2)->[FAR@1, FAR@1, NORMAL@1]; FAR:base(B=1); NORMAL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via CLOSE/FAR/NORMAL; **M3** yes: FOLLOW branch=2; **M4** yes: pruned NORMAL->BRAKE1, NORMAL->BRAKE2, NORMAL->BRAKE3, CLOSE->BRAKE1, CLOSE->BRAKE2, CLOSE->BRAKE3, FAR->BRAKE1, FAR->BRAKE2, FAR->BRAKE3; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.FOLLOW: 24 conjunct(s); R.NORMAL: 24 conjunct(s); R.CLOSE: 24 conjunct(s); R.FAR: 24 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.25 * (g1 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) <= 2]; L.FOLLOW: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) >= -2]; L.FOLLOW: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) <= 3]; L.FOLLOW: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) >= -3]; L.FOLLOW: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]; L.FOLLOW: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]; L.FOLLOW: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]; L.FOLLOW: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]; L.FOLLOW: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]; L.FOLLOW: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]; L.FOLLOW: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]; L.FOLLOW: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]; R.NORMAL: (r1 + (0.25 * (g1 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r1 + (0.25 * (g1 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r1 + (0.5 * (g1 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r1 + (0.5 * (g1 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.25 * (g2 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.25 * (g2 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.5 * (g2 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.5 * (g2 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.25 * (g3 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.25 * (g3 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.5 * (g3 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.5 * (g3 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) <= 2]; R.NORMAL: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) >= -2]; R.NORMAL: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) <= 3]; R.NORMAL: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) >= -3]; R.NORMAL: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) <= 2]; R.NORMAL: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) >= -2]; R.NORMAL: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) <= 3]; R.NORMAL: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) >= -3]; R.NORMAL: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) <= 2]; R.NORMAL: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) >= -2]; R.NORMAL: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) <= 3]; R.NORMAL: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) >= -3]; R.CLOSE: (r1 + (0.25 * (g1 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r1 + (0.25 * (g1 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r1 + (0.5 * (g1 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r1 + (0.5 * (g1 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.25 * (g2 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.25 * (g2 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.5 * (g2 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.5 * (g2 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.25 * (g3 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.25 * (g3 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.5 * (g3 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.5 * (g3 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 28))) <= 2]; R.CLOSE: g1 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 28))) >= -2]; R.CLOSE: g1 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 28))) <= 3]; R.CLOSE: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 28))) >= -3]; R.CLOSE: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 28))) <= 2]; R.CLOSE: g2 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 28))) >= -2]; R.CLOSE: g2 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 28))) <= 3]; R.CLOSE: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 28))) >= -3]; R.CLOSE: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 28))) <= 2]; R.CLOSE: g3 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 28))) >= -2]; R.CLOSE: g3 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 28))) <= 3]; R.CLOSE: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 28))) >= -3]; R.FAR: (r1 + (0.25 * (g1 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r1 + (0.25 * (g1 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r1 + (0.5 * (g1 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r1 + (0.5 * (g1 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.25 * (g2 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.25 * (g2 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.5 * (g2 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.5 * (g2 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.25 * (g3 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.25 * (g3 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.5 * (g3 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.5 * (g3 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FAR: g1 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 32))) <= 2]; R.FAR: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 32))) >= -2]; R.FAR: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 32))) <= 3]; R.FAR: g1 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 32))) >= -3]; R.FAR: g2 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 32))) <= 2]; R.FAR: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 32))) >= -2]; R.FAR: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 32))) <= 3]; R.FAR: g2 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 32))) >= -3]; R.FAR: g3 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 32))) <= 2]; R.FAR: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 32))) >= -2]; R.FAR: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 32))) <= 3]; R.FAR: g3 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 32))) >= -3]; NO_IMPLIED=DECLINED; **M6L** yes: L.FOLLOW: (r1 + (0.25 * (g1 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.25 * (g1 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r1 + (0.5 * (g1 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.25 * (g2 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r2 + (0.5 * (g2 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) <= 2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.25 * (g3 - 29))) >= -2 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) <= 3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: (r3 + (0.5 * (g3 - 29))) >= -3 kind=linear-form entry=rational route=linear-shape; L.FOLLOW: g1 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) <= 2]; L.FOLLOW: g1 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 29))) >= -2]; L.FOLLOW: g1 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) <= 3]; L.FOLLOW: g1 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 29))) >= -3]; L.FOLLOW: g2 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) <= 2]; L.FOLLOW: g2 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 29))) >= -2]; L.FOLLOW: g2 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) <= 3]; L.FOLLOW: g2 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 29))) >= -3]; L.FOLLOW: g3 <= 37 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) <= 2]; L.FOLLOW: g3 >= 21 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 29))) >= -2]; L.FOLLOW: g3 <= 35 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) <= 3]; L.FOLLOW: g3 >= 23 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 29))) >= -3]; R.NORMAL: (r1 + (0.25 * (g1 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r1 + (0.25 * (g1 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r1 + (0.5 * (g1 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r1 + (0.5 * (g1 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.25 * (g2 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.25 * (g2 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.5 * (g2 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r2 + (0.5 * (g2 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.25 * (g3 - 30))) <= 2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.25 * (g3 - 30))) >= -2 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.5 * (g3 - 30))) <= 3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: (r3 + (0.5 * (g3 - 30))) >= -3 kind=linear-form entry=rational route=linear-shape; R.NORMAL: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) <= 2]; R.NORMAL: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 30))) >= -2]; R.NORMAL: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) <= 3]; R.NORMAL: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 30))) >= -3]; R.NORMAL: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) <= 2]; R.NORMAL: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 30))) >= -2]; R.NORMAL: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) <= 3]; R.NORMAL: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 30))) >= -3]; R.NORMAL: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) <= 2]; R.NORMAL: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 30))) >= -2]; R.NORMAL: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) <= 3]; R.NORMAL: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 30))) >= -3]; R.CLOSE: (r1 + (0.25 * (g1 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r1 + (0.25 * (g1 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r1 + (0.5 * (g1 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r1 + (0.5 * (g1 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.25 * (g2 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.25 * (g2 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.5 * (g2 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r2 + (0.5 * (g2 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.25 * (g3 - 28))) <= 2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.25 * (g3 - 28))) >= -2 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.5 * (g3 - 28))) <= 3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: (r3 + (0.5 * (g3 - 28))) >= -3 kind=linear-form entry=rational route=linear-shape; R.CLOSE: g1 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 28))) <= 2]; R.CLOSE: g1 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 28))) >= -2]; R.CLOSE: g1 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 28))) <= 3]; R.CLOSE: g1 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 28))) >= -3]; R.CLOSE: g2 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 28))) <= 2]; R.CLOSE: g2 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 28))) >= -2]; R.CLOSE: g2 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 28))) <= 3]; R.CLOSE: g2 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 28))) >= -3]; R.CLOSE: g3 <= 36 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 28))) <= 2]; R.CLOSE: g3 >= 20 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 28))) >= -2]; R.CLOSE: g3 <= 34 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 28))) <= 3]; R.CLOSE: g3 >= 22 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 28))) >= -3]; R.FAR: (r1 + (0.25 * (g1 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r1 + (0.25 * (g1 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r1 + (0.5 * (g1 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r1 + (0.5 * (g1 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.25 * (g2 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.25 * (g2 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.5 * (g2 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r2 + (0.5 * (g2 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.25 * (g3 - 32))) <= 2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.25 * (g3 - 32))) >= -2 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.5 * (g3 - 32))) <= 3 kind=linear-form entry=rational route=linear-shape; R.FAR: (r3 + (0.5 * (g3 - 32))) >= -3 kind=linear-form entry=rational route=linear-shape; R.FAR: g1 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 32))) <= 2]; R.FAR: g1 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.25 * (g1 - 32))) >= -2]; R.FAR: g1 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 32))) <= 3]; R.FAR: g1 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r1 + (0.5 * (g1 - 32))) >= -3]; R.FAR: g2 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 32))) <= 2]; R.FAR: g2 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.25 * (g2 - 32))) >= -2]; R.FAR: g2 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 32))) <= 3]; R.FAR: g2 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r2 + (0.5 * (g2 - 32))) >= -3]; R.FAR: g3 <= 40 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 32))) <= 2]; R.FAR: g3 >= 24 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.25 * (g3 - 32))) >= -2]; R.FAR: g3 <= 38 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 32))) <= 3]; R.FAR: g3 >= 26 kind=derived-bound entry=rational route=derived-shape given=[(r3 + (0.5 * (g3 - 32))) >= -3]; NO_LINEAR=DECLINED

### `platoon_delay_linkloss`

* family: Platoon follower, delayed link; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/3; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `547981de689a`
* `relcert`: **CERTIFIED** (263 ms); `[prune] platoon_delay_linkloss: [FOLLOW->BRAKE]`; NO_PRUNE: **DECLINED** (952 ms); NO_CUT: **DECLINED** (802 ms); NO_IMPLIED_CUT: **DECLINED** (772 ms); NO_LINEAR_CUT: **CERTIFIED** (220 ms); domains: uniform
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
* `--handoff`: 7/7 checked, 7 passed, failing -, non-vacuous (79 ms)
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j--', 'CATCH': 'j--', 'BRAKE': '---'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cover `CATCH_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j--', 'CATCH': 'j--', 'BRAKE': '---'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cover `LOST_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j--', 'CATCH': 'j--', 'BRAKE': '---'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via CATCH/FOLLOW, CATCH B=2 via CATCH/FOLLOW, LOST B=2 via CATCH/FOLLOW; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED; **M5** yes: 7/7 handoffs unsat, rows differ; **M6** yes: L.FOLLOW: 2 conjunct(s); L.CATCH: 1 conjunct(s); L.LOST: 2 conjunct(s); R.FOLLOW: 2 conjunct(s); R.CATCH: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; L.CATCH: g >= 29.0 kind=implied-contraction entry=rational route=shape; R.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; R.CATCH: g >= 30.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `platoon_delay_profiles`

* family: Platoon follower, delayed link; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `4a4d185cf637`
* `relcert`: **CERTIFIED** (267 ms); `[prune] platoon_delay_profiles: [FOLLOW->BRAKE]`; NO_PRUNE: **DECLINED** (1197 ms); NO_CUT: **DECLINED** (1041 ms); NO_IMPLIED_CUT: **DECLINED** (1067 ms); NO_LINEAR_CUT: **CERTIFIED** (262 ms); domains: uniform
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
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['FOLLOW', 'GENTLE', 'ASSERTIVE'], flags {'FOLLOW': 'j--', 'GENTLE': 'j--', 'ASSERTIVE': 'j--', 'BRAKE': '---'}, kinds ['base', 'joint'], path modes ['ASSERTIVE', 'FOLLOW', 'GENTLE'], branching 2, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, GENTLE@1, ASSERTIVE@1, FOLLOW@1]; FOLLOW:base(B=1); GENTLE:base(B=1); ASSERTIVE:base(B=1)`
    * from `GENTLE`: `GENTLE:joint(B=2)->[GENTLE@1, FOLLOW@1, GENTLE@1]; GENTLE:base(B=1); FOLLOW:base(B=1)`
    * from `ASSERTIVE`: `ASSERTIVE:joint(B=2)->[ASSERTIVE@1, FOLLOW@1, ASSERTIVE@1]; ASSERTIVE:base(B=1); FOLLOW:base(B=1)`
* cover `GENTLE_L`: λ = 1, budget 2, admissible ['FOLLOW', 'GENTLE', 'ASSERTIVE'], flags {'FOLLOW': 'j--', 'GENTLE': 'j--', 'ASSERTIVE': 'j--', 'BRAKE': '---'}, kinds ['base', 'joint'], path modes ['ASSERTIVE', 'FOLLOW', 'GENTLE'], branching 2, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, GENTLE@1, ASSERTIVE@1, FOLLOW@1]; FOLLOW:base(B=1); GENTLE:base(B=1); ASSERTIVE:base(B=1)`
    * from `GENTLE`: `GENTLE:joint(B=2)->[GENTLE@1, FOLLOW@1, GENTLE@1]; GENTLE:base(B=1); FOLLOW:base(B=1)`
    * from `ASSERTIVE`: `ASSERTIVE:joint(B=2)->[ASSERTIVE@1, FOLLOW@1, ASSERTIVE@1]; ASSERTIVE:base(B=1); FOLLOW:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via ASSERTIVE/FOLLOW/GENTLE, GENTLE B=2 via ASSERTIVE/FOLLOW/GENTLE; **M3** yes: FOLLOW branch=2, GENTLE branch=2; **M4** yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.FOLLOW: 2 conjunct(s); L.GENTLE: 1 conjunct(s); R.FOLLOW: 2 conjunct(s); R.GENTLE: 1 conjunct(s); R.ASSERTIVE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.GENTLE: g >= 29.0 kind=implied-contraction entry=rational route=shape; R.GENTLE: g >= 30.0 kind=implied-contraction entry=rational route=shape; R.ASSERTIVE: g >= 30.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

### `quad_light_airframe_20`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 1/1; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9a7b144d8b09`
* `relcert`: **CERTIFIED** (219 ms); `[prune] quad_light_airframe_20: [CLIMB->LIMIT]`; NO_PRUNE: **DECLINED** (724 ms); NO_CUT: **CERTIFIED** (218 ms); NO_IMPLIED_CUT: **CERTIFIED** (158 ms); NO_LINEAR_CUT: **CERTIFIED** (164 ms); domains: uniform
* `[cut] L.CLIMB: 2 conjunct(s)`
* `[cut] R.CLIMB: 2 conjunct(s)`
* `[cut] R.LIMIT: 1 conjunct(s)`
* `[cut-x] R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (41 ms)
* cover `CLIMB_L`: λ = 7/4, budget 4, admissible ['CLIMB'], flags {'CLIMB': 'j--', 'LIMIT': '---'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=4)->[CLIMB@3, CLIMB@3]; CLIMB:joint(B=3)->[CLIMB@2, CLIMB@2]; CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=7/4 (polynomial dynamics); **M2** yes: CLIMB B=4 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s); R.LIMIT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `quad_light_lag`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 2/2; modes L/R 1/1; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `e06b31eeeac1`
* `relcert`: **CERTIFIED** (129 ms); `[prune] quad_light_lag: []`; NO_PRUNE: **CERTIFIED** (131 ms); NO_CUT: **CERTIFIED** (122 ms); NO_IMPLIED_CUT: **CERTIFIED** (130 ms); NO_LINEAR_CUT: **CERTIFIED** (125 ms); domains: uniform
* `[cut] L.CLIMB: 3 conjunct(s)`
* `[cut] R.CLIMB: 2 conjunct(s)`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (91 ms)
* cover `CLIMB_L`: λ = 7/4, budget 4, admissible ['CLIMB'], flags {'CLIMB': 'j--'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=4)->[CLIMB@3, CLIMB@3]; CLIMB:joint(B=3)->[CLIMB@2, CLIMB@2]; CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=7/4 (polynomial dynamics); **M2** yes: CLIMB B=4 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `quad_light_profiles`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 1/1; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `4449578e8cfc`
* `relcert`: **CERTIFIED** (497 ms); `[prune] quad_light_profiles: [NORMAL->LIMIT, ECO->LIMIT, SPORT->LIMIT]`; NO_PRUNE: **DECLINED** (1124 ms); NO_CUT: **CERTIFIED** (488 ms); NO_IMPLIED_CUT: **CERTIFIED** (485 ms); NO_LINEAR_CUT: **CERTIFIED** (495 ms); domains: uniform
* `[cut] L.CLIMB: 1 conjunct(s)`
* `[cut] R.NORMAL: 2 conjunct(s)`
* `[cut] R.ECO: 2 conjunct(s)`
* `[cut] R.SPORT: 2 conjunct(s)`
* `[cut] R.LIMIT: 1 conjunct(s)`
* `[cut-x] R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape`
* `[admissible] CLIMB_L: [NORMAL, ECO, SPORT]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (70 ms)
* cover `CLIMB_L`: λ = 5/2, budget 5, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j--', 'ECO': 'j--', 'SPORT': 'j--', 'LIMIT': '---'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=5)->[NORMAL@4, NORMAL@4, ECO@4, SPORT@4]; NORMAL:joint(B=4)->[NORMAL@3, NORMAL@3, ECO@3, SPORT@3]; NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1); ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; ECO:joint(B=4)->[ECO@3, ECO@3, NORMAL@3]; SPORT:joint(B=4)->[SPORT@3, SPORT@3, NORMAL@3]`
    * from `ECO`: `ECO:joint(B=5)->[ECO@4, ECO@4, NORMAL@4]; ECO:joint(B=4)->[ECO@3, ECO@3, NORMAL@3]; ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; SPORT:base(B=1); NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; NORMAL:joint(B=4)->[NORMAL@3, NORMAL@3, ECO@3, SPORT@3]; SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]`
    * from `SPORT`: `SPORT:joint(B=5)->[SPORT@4, SPORT@4, NORMAL@4]; SPORT:joint(B=4)->[SPORT@3, SPORT@3, NORMAL@3]; SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; ECO:base(B=1); NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; NORMAL:joint(B=4)->[NORMAL@3, NORMAL@3, ECO@3, SPORT@3]; ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]`
* cells: **M1** yes: CLIMB λ=5/2 (polynomial dynamics); **M2** yes: CLIMB B=5 via ECO/NORMAL/SPORT; **M3** yes: CLIMB branch=2; **M4** yes: pruned NORMAL->LIMIT, ECO->LIMIT, SPORT->LIMIT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 1 conjunct(s); R.NORMAL: 2 conjunct(s); R.ECO: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.LIMIT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung1_2to3`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 3/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `a55b07fd35ff`
* `relcert`: **CERTIFIED** (256 ms); `[prune] refinement_ladder_rover_rung1_2to3: []`; NO_PRUNE: **CERTIFIED** (259 ms); NO_CUT: **DECLINED** (820 ms); NO_IMPLIED_CUT: **CERTIFIED** (210 ms); NO_LINEAR_CUT: **CERTIFIED** (239 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (60 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2_3to6`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `1b9081f9b111`
* `relcert`: **CERTIFIED** (714 ms); `[prune] refinement_ladder_rover_rung2_3to6: []`; NO_PRUNE: **CERTIFIED** (708 ms); NO_CUT: **CERTIFIED** (560 ms); NO_IMPLIED_CUT: **CERTIFIED** (622 ms); NO_LINEAR_CUT: **CERTIFIED** (711 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (93 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 4/4; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.001, 6.0]; invariant shape linear; rows identical: True; normalized md5 `238c061085aa`
* `relcert`: **CERTIFIED** (221 ms); `[prune] refinement_ladder_rover_rung2_6dof: []`; NO_PRUNE: **CERTIFIED** (221 ms); NO_CUT: **CERTIFIED** (154 ms); NO_IMPLIED_CUT: **CERTIFIED** (96 ms); NO_LINEAR_CUT: **CERTIFIED** (224 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (87 ms)
* cover `STEEP_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2b_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.001, 6.0]; invariant shape linear; rows identical: True; normalized md5 `b1ae87a5c1db`
* `relcert`: **CERTIFIED** (216 ms); `[prune] refinement_ladder_rover_rung2b_6dof: []`; NO_PRUNE: **CERTIFIED** (209 ms); NO_CUT: **CERTIFIED** (159 ms); NO_IMPLIED_CUT: **CERTIFIED** (174 ms); NO_LINEAR_CUT: **CERTIFIED** (254 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (94 ms)
* cover `STEEP_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1001/1000, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung2c_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `724831255028`
* `relcert`: **CERTIFIED** (1368 ms); `[prune] refinement_ladder_rover_rung2c_6dof: []`; NO_PRUNE: **CERTIFIED** (1303 ms); NO_CUT: **CERTIFIED** (1254 ms); NO_IMPLIED_CUT: **CERTIFIED** (1271 ms); NO_LINEAR_CUT: **CERTIFIED** (1365 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP]`
* `[admissible] MODER_L: [MODER]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (90 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP'], flags {'STEEP': 'j--', 'MODER': '---', 'FLAT': '---'}, kinds ['base'], path modes ['STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': '---'}, kinds ['base'], path modes ['MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung3_6to8`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape quadratic; rows identical: True; normalized md5 `848946e281b6`
* `relcert`: **CERTIFIED** (3079 ms); `[prune] refinement_ladder_rover_rung3_6to8: []`; NO_PRUNE: **CERTIFIED** (3077 ms); NO_CUT: **DECLINED** (3217 ms); NO_IMPLIED_CUT: **CERTIFIED** (2978 ms); NO_LINEAR_CUT: **CERTIFIED** (3077 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (88 ms)
* cover `STEEP_L`: λ = 9/4, budget 3, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=3)->[STEEP@2, MODER@2, STEEP@2]; STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1); MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=3)->[MODER@2, FLAT@2, MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1); FLAT:joint(B=2)->[FLAT@1, FLAT@1]`
    * from `FLAT`: `FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 9/4, budget 3, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=3,preJ)->[MODER@3]; MODER:joint(B=3)->[MODER@2, FLAT@2, MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1); FLAT:joint(B=2)->[FLAT@1, FLAT@1]`
    * from `MODER`: `MODER:joint(B=3)->[MODER@2, FLAT@2, MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1); FLAT:joint(B=2)->[FLAT@1, FLAT@1]`
    * from `FLAT`: `FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 9/4, budget 3, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=3,preJ)->[FLAT@3]; FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=3)->[FLAT@2, FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=9/4, MODER λ=9/4, FLAT λ=9/4 (polynomial dynamics); **M2** yes: STEEP B=3 via FLAT/MODER/STEEP, MODER B=3 via FLAT/MODER +RO, FLAT B=3 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `refinement_ladder_rover_rung4_8to12`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9f1c06c6a52c`
* `relcert`: **CERTIFIED** (971 ms); `[prune] refinement_ladder_rover_rung4_8to12: []`; NO_PRUNE: **CERTIFIED** (949 ms); NO_CUT: **DECLINED** (1305 ms); NO_IMPLIED_CUT: **CERTIFIED** (881 ms); NO_LINEAR_CUT: **CERTIFIED** (980 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (75 ms)
* cover `STEEP_L`: λ = 17/10, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 17/10, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 17/10, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=17/10, MODER λ=17/10, FLAT λ=17/10 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover3tier_rung12`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/3; modes L/R 2/2; εL/εR 1.0/0.3; λ ∈ [1.0, 6.0]; invariant shape conjunctive+linear; rows identical: False; normalized md5 `4b65ad8433aa`
* `relcert`: **CERTIFIED** (230 ms); `[prune] rover3tier_rung12: []`; NO_PRUNE: **CERTIFIED** (231 ms); NO_CUT: **CERTIFIED** (173 ms); NO_IMPLIED_CUT: **CERTIFIED** (216 ms); NO_LINEAR_CUT: **CERTIFIED** (233 ms); domains: uniform
* `[cut] R.ACCEL: 1 conjunct(s)`
* `[cut] R.COAST: 1 conjunct(s)`
* `[admissible] ACCEL_L: [ACCEL, COAST]`
* `[admissible] COAST_L: [ACCEL, COAST]`
* `--handoff`: 4/4 checked, 4 passed, failing -, non-vacuous (86 ms)
* cover `ACCEL_L`: λ = 7/4, budget 6, admissible ['ACCEL', 'COAST'], flags {'ACCEL': 'jdd', 'COAST': 'jdd'}, kinds ['base', 'joint'], path modes ['ACCEL', 'COAST'], branching 1, right-only False
    * from `ACCEL`: `ACCEL:joint(B=6)->[ACCEL@5, COAST@5, ACCEL@5]; ACCEL:joint(B=5)->[ACCEL@4, COAST@4, ACCEL@4]; ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:base(B=1); COAST:base(B=1); COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=5)->[COAST@4, ACCEL@4, COAST@4]`
    * from `COAST`: `COAST:joint(B=6)->[COAST@5, ACCEL@5, COAST@5]; COAST:joint(B=5)->[COAST@4, ACCEL@4, COAST@4]; COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:base(B=1); ACCEL:base(B=1); ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=5)->[ACCEL@4, COAST@4, ACCEL@4]`
* cover `COAST_L`: λ = 1, budget 4, admissible ['ACCEL', 'COAST'], flags {'ACCEL': 'jdd', 'COAST': 'jdd'}, kinds ['base', 'joint'], path modes ['ACCEL', 'COAST'], branching 1, right-only False
    * from `ACCEL`: `ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:base(B=1); COAST:base(B=1); COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]`
    * from `COAST`: `COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:base(B=1); ACCEL:base(B=1); ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]`
* cells: **M1** yes: ACCEL λ=7/4 (affine dynamics); **M2** yes: ACCEL B=6 via ACCEL/COAST, COAST B=4 via ACCEL/COAST; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** yes: 4/4 handoffs unsat, rows differ; **M6** vacuous: cuts kept (R.ACCEL: 1 conjunct(s); R.COAST: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung1`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 3/3; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `0b323c73c8d9`
* `relcert`: **CERTIFIED** (242 ms); `[prune] rover_dof_terrain_rung1: []`; NO_PRUNE: **CERTIFIED** (267 ms); NO_CUT: **DECLINED** (854 ms); NO_IMPLIED_CUT: **CERTIFIED** (220 ms); NO_LINEAR_CUT: **CERTIFIED** (261 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (93 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung2`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `05e0216a07ff`
* `relcert`: **CERTIFIED** (318 ms); `[prune] rover_dof_terrain_rung2: []`; NO_PRUNE: **CERTIFIED** (301 ms); NO_CUT: **DECLINED** (958 ms); NO_IMPLIED_CUT: **CERTIFIED** (187 ms); NO_LINEAR_CUT: **CERTIFIED** (319 ms); domains: uniform
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
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung3`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `8d149b9ca736`
* `relcert`: **CERTIFIED** (317 ms); `[prune] rover_dof_terrain_rung3: []`; NO_PRUNE: **CERTIFIED** (266 ms); NO_CUT: **DECLINED** (1171 ms); NO_IMPLIED_CUT: **CERTIFIED** (227 ms); NO_LINEAR_CUT: **CERTIFIED** (331 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (47 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_dof_terrain_rung3_8d`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `675e7eb3a84a`
* `relcert`: **CERTIFIED** (325 ms); `[prune] rover_dof_terrain_rung3_8d: []`; NO_PRUNE: **CERTIFIED** (298 ms); NO_CUT: **DECLINED** (1112 ms); NO_IMPLIED_CUT: **CERTIFIED** (225 ms); NO_LINEAR_CUT: **CERTIFIED** (361 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (92 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=1,preJ)->[MODER@1]; MODER:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=1,preJ)->[FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `rover_patrol_refine`

* **2026-10-10 (§19.1):** the odometer wall `s ≤ 100` removed from every evolve domain on both sides (a blocking constraint, not a physical limit). Re-measured: CERTIFIED (1517 ms); NO_PRUNE CERTIFIED, NO_CUT / NO_IMPLIED_CUT / NO_LINEAR_CUT DECLINED; `--handoff` 10/10; cells M1 M2 M3 M5 M6 M6+ M6L unchanged; widening: no load-bearing bound. Covers and cuts byte-identical; the records below predate the change.
* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/3; modes L/R 4/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `f3bdf93f8f88`
* `relcert`: **CERTIFIED** (1562 ms); `[prune] rover_patrol_refine: []`; NO_PRUNE: **CERTIFIED** (1622 ms); NO_CUT: **DECLINED** (1207 ms); NO_IMPLIED_CUT: **DECLINED** (2537 ms); NO_LINEAR_CUT: **DECLINED** (2512 ms); domains: uniform
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
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (105 ms)
* cover `SLOW_L`: λ = 9/4, budget 5, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': 'jdd', 'MEDIUM_ECO': 'jdd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'jdd'}, kinds ['base', 'joint'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 2, right-only False
    * from `SLOW`: `SLOW:joint(B=5)->[SLOW@4, MEDIUM_ECO@4, MEDIUM_BRISK@4, SLOW@4]; SLOW:joint(B=4)->[SLOW@3, MEDIUM_ECO@3, MEDIUM_BRISK@3, SLOW@3]; SLOW:joint(B=3)->[SLOW@2, MEDIUM_ECO@2, MEDIUM_BRISK@2, SLOW@2]; SLOW:joint(B=2)->[SLOW@1, MEDIUM_ECO@1, MEDIUM_BRISK@1, SLOW@1]; SLOW:base(B=1); MEDIUM_ECO:base(B=1); MEDIUM_BRISK:base(B=1); MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; FAST:base(B=1); MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]`
    * from `FAST`: `FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_ECO_L`: λ = 9/4, budget 5, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': 'jdd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=5,preJ)->[MEDIUM_ECO@5, MEDIUM_BRISK@5]; MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]`
    * from `FAST`: `FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_BRISK_L`: λ = 9/4, budget 5, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': '-dd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=5,preJ)->[MEDIUM_ECO@5, MEDIUM_BRISK@5]; MEDIUM_ECO:repoDyn(B=5,preJ)->[FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1); MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=5,preJ)->[FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]`
    * from `FAST`: `FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `FAST_L`: λ = 9/4, budget 5, admissible ['MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': '-dd', 'MEDIUM_BRISK': '-dd', 'FAST': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO'], branching 0, right-only True
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=5,preJ)->[FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:repoDyn(B=5,preJ)->[FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cells: **M1** yes: SLOW λ=9/4, MEDIUM_ECO λ=9/4, MEDIUM_BRISK λ=9/4, FAST λ=9/4 (affine dynamics); **M2** yes: SLOW B=5 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=5 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, MEDIUM_BRISK B=5 via FAST/MEDIUM_BRISK +RO, FAST B=5 via FAST +RO; **M3** yes: SLOW branch=2; **M4** no (nothing pruned); **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.SLOW: 5 conjunct(s); L.MEDIUM_ECO: 5 conjunct(s); L.MEDIUM_BRISK: 5 conjunct(s); L.FAST: 4 conjunct(s); R.SLOW: 3 conjunct(s); R.MEDIUM_ECO: 3 conjunct(s); R.MEDIUM_BRISK: 3 conjunct(s); R.FAST: 3 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry=rational route=linear-shape; L.SLOW: (a + (2.5 * (v - 0.48))) >= -0.95 kind=linear-form entry=rational route=linear-shape; L.SLOW: v <= 0.8 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) <= 0.8]; L.SLOW: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) >= -0.95]; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) <= 0.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) >= -1.55 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: v <= 1.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) <= 0.95]; L.MEDIUM_ECO: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) >= -1.55]; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) <= 1.05 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) >= -1.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: v <= 1.3 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) <= 1.05]; L.MEDIUM_BRISK: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) >= -1.95]; L.FAST: (a + (2.5 * (v - 1.2))) <= 1.25 kind=linear-form entry=rational route=linear-shape; L.FAST: (a + (2.5 * (v - 1.2))) >= -2.75 kind=linear-form entry=rational route=linear-shape; L.FAST: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 1.2))) >= -2.75]; NO_IMPLIED=DECLINED; **M6L** yes: L.SLOW: (a + (2.5 * (v - 0.48))) <= 0.8 kind=linear-form entry=rational route=linear-shape; L.SLOW: (a + (2.5 * (v - 0.48))) >= -0.95 kind=linear-form entry=rational route=linear-shape; L.SLOW: v <= 0.8 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) <= 0.8]; L.SLOW: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.48))) >= -0.95]; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) <= 0.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: (a + (2.5 * (v - 0.72))) >= -1.55 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_ECO: v <= 1.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) <= 0.95]; L.MEDIUM_ECO: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.72))) >= -1.55]; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) <= 1.05 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: (a + (2.5 * (v - 0.88))) >= -1.95 kind=linear-form entry=rational route=linear-shape; L.MEDIUM_BRISK: v <= 1.3 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) <= 1.05]; L.MEDIUM_BRISK: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 0.88))) >= -1.95]; L.FAST: (a + (2.5 * (v - 1.2))) <= 1.25 kind=linear-form entry=rational route=linear-shape; L.FAST: (a + (2.5 * (v - 1.2))) >= -2.75 kind=linear-form entry=rational route=linear-shape; L.FAST: v >= 0.1 kind=derived-bound entry=rational route=derived-shape given=[(a + (2.5 * (v - 1.2))) >= -2.75]; NO_LINEAR=DECLINED

### `rover_patrol_zones`

* **2026-10-10 (§19.1):** the odometer wall `s ≤ 100` removed from every evolve domain on both sides (a blocking constraint, not a physical limit). Re-measured: CERTIFIED (390 ms); NO_PRUNE CERTIFIED, NO_CUT DECLINED, NO_IMPLIED_CUT / NO_LINEAR_CUT CERTIFIED; `--handoff` 10/10; cells M2 M3 M5 M6 unchanged; widening: no load-bearing bound. Covers and cuts byte-identical; the records below predate the change.
* family: Rover patrol (zones); scenario: degraded-actuator; dims L/R 2/2; modes L/R 4/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `088224fb0842`
* `relcert`: **CERTIFIED** (319 ms); `[prune] rover_patrol_zones: [SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL, FAST->STALL]`; NO_PRUNE: **CERTIFIED** (382 ms); NO_CUT: **DECLINED** (1159 ms); NO_IMPLIED_CUT: **CERTIFIED** (373 ms); NO_LINEAR_CUT: **CERTIFIED** (392 ms); domains: uniform
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
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (99 ms)
* cover `SLOW_L`: λ = 1, budget 2, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': 'jdd', 'MEDIUM_ECO': 'jdd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'jdd', 'STALL': 'j--'}, kinds ['base', 'joint'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 2, right-only False
    * from `SLOW`: `SLOW:joint(B=2)->[SLOW@1, MEDIUM_ECO@1, MEDIUM_BRISK@1, SLOW@1]; SLOW:base(B=1); MEDIUM_ECO:base(B=1); MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_ECO_L`: λ = 1, budget 2, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': 'jdd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'jdd', 'STALL': 'j--'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=2,preJ)->[MEDIUM_ECO@2, MEDIUM_BRISK@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_BRISK_L`: λ = 1, budget 2, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': '-dd', 'MEDIUM_BRISK': 'jdd', 'FAST': 'jdd', 'STALL': 'j--'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=2,preJ)->[MEDIUM_ECO@2, MEDIUM_BRISK@2]; MEDIUM_ECO:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1); MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `FAST_L`: λ = 1, budget 2, admissible ['MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '-dd', 'MEDIUM_ECO': '-dd', 'MEDIUM_BRISK': '-dd', 'FAST': 'jdd', 'STALL': 'j--'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO'], branching 0, right-only True
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:repoDyn(B=2,preJ)->[FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: SLOW B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, MEDIUM_BRISK B=2 via FAST/MEDIUM_BRISK +RO, FAST B=2 via FAST +RO; **M3** yes: SLOW branch=2; **M4** vacuous: pruned SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL, FAST->STALL but NO_PRUNE=CERTIFIED; **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.SLOW: 3 conjunct(s); L.MEDIUM_ECO: 3 conjunct(s); L.MEDIUM_BRISK: 3 conjunct(s); L.FAST: 3 conjunct(s); R.SLOW: 3 conjunct(s); R.MEDIUM_ECO: 3 conjunct(s); R.MEDIUM_BRISK: 3 conjunct(s); R.FAST: 3 conjunct(s); R.STALL: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.STALL: v <= 0.2 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat3w_detumble_nominal`

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 6/6; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape quadratic; rows identical: True; normalized md5 `15fa00d81959`
* `relcert`: **CERTIFIED** (960 ms); `[prune] sat3w_detumble_nominal: [DETUMBLE->SAFE]`; NO_PRUNE: **DECLINED** (14439 ms); NO_CUT: **CERTIFIED** (940 ms); NO_IMPLIED_CUT: **CERTIFIED** (919 ms); NO_LINEAR_CUT: **CERTIFIED** (916 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (17 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE'], flags {'DETUMBLE': 'j--', 'SAFE': '-dd'}, kinds ['base', 'joint'], path modes ['DETUMBLE'], branching 0, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1]; DETUMBLE:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.SAFE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat3w_detumble_phases`

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 6/6; modes L/R 2/2; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: False; normalized md5 `a867cf0e315d`
* `relcert`: **CERTIFIED** (11049 ms); `[prune] sat3w_detumble_phases: [DETUMBLE->SAFE]`; NO_PRUNE: **DECLINED** (953 ms); NO_CUT: **DECLINED** (1876 ms); NO_IMPLIED_CUT: **CERTIFIED** (11190 ms); NO_LINEAR_CUT: **CERTIFIED** (11208 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] L.FINE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE]`
* `[admissible] FINE_L: [DETUMBLE]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (775 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE'], flags {'DETUMBLE': 'j--', 'SAFE': '-dd'}, kinds ['base', 'joint'], path modes ['DETUMBLE'], branching 0, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1]; DETUMBLE:base(B=1)`
* cover `FINE_L`: λ = 1, budget 2, admissible ['DETUMBLE'], flags {'DETUMBLE': 'j--', 'SAFE': 'jdd'}, kinds ['base', 'joint'], path modes ['DETUMBLE'], branching 0, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1]; DETUMBLE:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE, FINE B=2 via DETUMBLE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat3w_detumble_weak`

* family: Rigid-body detumbling (polynomial); scenario: degraded-actuator; dims L/R 6/6; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `9aabd998b0d7`
* `relcert`: **CERTIFIED** (11776 ms); `[prune] sat3w_detumble_weak: [NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE]`; NO_PRUNE: **DECLINED** (11864 ms); NO_CUT: **DECLINED** (2462 ms); NO_IMPLIED_CUT: **CERTIFIED** (11825 ms); NO_LINEAR_CUT: **CERTIFIED** (11881 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] R.NOMINAL: 1 conjunct(s)`
* `[cut] R.ECONOMY: 1 conjunct(s)`
* `[cut] R.SURVIVAL: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [NOMINAL, ECONOMY, SURVIVAL]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (86 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['NOMINAL', 'ECONOMY', 'SURVIVAL'], flags {'NOMINAL': 'j--', 'ECONOMY': 'j--', 'SURVIVAL': 'j--', 'SAFE': '-dd'}, kinds ['base', 'joint'], path modes ['ECONOMY', 'NOMINAL', 'SURVIVAL'], branching 2, right-only False
    * from `NOMINAL`: `NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:base(B=1); SURVIVAL:base(B=1)`
    * from `ECONOMY`: `ECONOMY:joint(B=2)->[ECONOMY@1, ECONOMY@1, NOMINAL@1]; ECONOMY:base(B=1); NOMINAL:base(B=1)`
    * from `SURVIVAL`: `SURVIVAL:joint(B=2)->[SURVIVAL@1, SURVIVAL@1, NOMINAL@1]; SURVIVAL:base(B=1); NOMINAL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via ECONOMY/NOMINAL/SURVIVAL; **M3** yes: DETUMBLE branch=2; **M4** yes: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunct(s); R.ECONOMY: 1 conjunct(s); R.SURVIVAL: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat_detumble_nominal`

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 4/4; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `477dd8b85d3b`
* `relcert`: **CERTIFIED** (893 ms); `[prune] sat_detumble_nominal: [DETUMBLE->SAFE]`; NO_PRUNE: **DECLINED** (871 ms); NO_CUT: **CERTIFIED** (919 ms); NO_IMPLIED_CUT: **CERTIFIED** (898 ms); NO_LINEAR_CUT: **CERTIFIED** (942 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (87 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE'], flags {'DETUMBLE': 'j--', 'SAFE': '-dd'}, kinds ['base', 'joint'], path modes ['DETUMBLE'], branching 0, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1]; DETUMBLE:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.DETUMBLE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.SAFE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat_detumble_phases`

* family: Rigid-body detumbling (polynomial); scenario: model-refinement; dims L/R 4/4; modes L/R 2/2; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: False; normalized md5 `83a2563381e9`
* `relcert`: **CERTIFIED** (5406 ms); `[prune] sat_detumble_phases: [DETUMBLE->SAFE]`; NO_PRUNE: **DECLINED** (899 ms); NO_CUT: **DECLINED** (3880 ms); NO_IMPLIED_CUT: **CERTIFIED** (5347 ms); NO_LINEAR_CUT: **CERTIFIED** (5358 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] L.FINE: 1 conjunct(s)`
* `[cut] R.DETUMBLE: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [DETUMBLE]`
* `[admissible] FINE_L: [DETUMBLE]`
* `--handoff`: 3/3 checked, 3 passed, failing -, non-vacuous (785 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['DETUMBLE'], flags {'DETUMBLE': 'j--', 'SAFE': '-dd'}, kinds ['base', 'joint'], path modes ['DETUMBLE'], branching 0, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1]; DETUMBLE:base(B=1)`
* cover `FINE_L`: λ = 1, budget 2, admissible ['DETUMBLE'], flags {'DETUMBLE': 'j--', 'SAFE': 'jdd'}, kinds ['base', 'joint'], path modes ['DETUMBLE'], branching 0, right-only False
    * from `DETUMBLE`: `DETUMBLE:joint(B=2)->[DETUMBLE@1, DETUMBLE@1]; DETUMBLE:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via DETUMBLE, FINE B=2 via DETUMBLE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned DETUMBLE->SAFE; NO_PRUNE=DECLINED; **M5** yes: 3/3 handoffs unsat, rows differ; **M6** yes: L.DETUMBLE: 1 conjunct(s); L.FINE: 1 conjunct(s); R.DETUMBLE: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `sat_detumble_weak`

* family: Rigid-body detumbling (polynomial); scenario: degraded-actuator; dims L/R 4/4; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 1.0]; invariant shape quadratic; rows identical: True; normalized md5 `403efd551ba5`
* `relcert`: **CERTIFIED** (12129 ms); `[prune] sat_detumble_weak: [NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE]`; NO_PRUNE: **DECLINED** (12210 ms); NO_CUT: **DECLINED** (8675 ms); NO_IMPLIED_CUT: **CERTIFIED** (12185 ms); NO_LINEAR_CUT: **CERTIFIED** (12250 ms); domains: uniform
* `[cut] L.DETUMBLE: 1 conjunct(s)`
* `[cut] R.NOMINAL: 1 conjunct(s)`
* `[cut] R.ECONOMY: 1 conjunct(s)`
* `[cut] R.SURVIVAL: 1 conjunct(s)`
* `[cut] R.SAFE: 1 conjunct(s)`
* `[cut-x] R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen`
* `[admissible] DETUMBLE_L: [NOMINAL, ECONOMY, SURVIVAL]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (85 ms)
* cover `DETUMBLE_L`: λ = 1, budget 2, admissible ['NOMINAL', 'ECONOMY', 'SURVIVAL'], flags {'NOMINAL': 'j--', 'ECONOMY': 'j--', 'SURVIVAL': 'j--', 'SAFE': '-dd'}, kinds ['base', 'joint'], path modes ['ECONOMY', 'NOMINAL', 'SURVIVAL'], branching 2, right-only False
    * from `NOMINAL`: `NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]; NOMINAL:base(B=1); ECONOMY:base(B=1); SURVIVAL:base(B=1)`
    * from `ECONOMY`: `ECONOMY:joint(B=2)->[ECONOMY@1, ECONOMY@1, NOMINAL@1]; ECONOMY:base(B=1); NOMINAL:base(B=1)`
    * from `SURVIVAL`: `SURVIVAL:joint(B=2)->[SURVIVAL@1, SURVIVAL@1, NOMINAL@1]; SURVIVAL:base(B=1); NOMINAL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: DETUMBLE B=2 via ECONOMY/NOMINAL/SURVIVAL; **M3** yes: DETUMBLE branch=2; **M4** yes: pruned NOMINAL->SAFE, ECONOMY->SAFE, SURVIVAL->SAFE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.DETUMBLE: 1 conjunct(s); R.NOMINAL: 1 conjunct(s); R.ECONOMY: 1 conjunct(s); R.SURVIVAL: 1 conjunct(s); R.SAFE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.SAFE: ((((w1 * w1) * 2) + ((w2 * w2) * 4)) + ((w3 * w3) * 5)) >= 1.0 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED; **M6L** no (no linear-form atom kept)

### `story1_attdist_rung_a_6to8`

* family: Story ladders; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `34c422712676`
* `relcert`: **CERTIFIED** (21702 ms); `[prune] story1_attdist_rung_a_6to8: []`; NO_PRUNE: **CERTIFIED** (21717 ms); NO_CUT: **CERTIFIED** (1637 ms); NO_IMPLIED_CUT: **CERTIFIED** (21557 ms); NO_LINEAR_CUT: **CERTIFIED** (21711 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (83 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story1_attdist_rung_b_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: False; normalized md5 `d5633710e2d8`
* `relcert`: **CERTIFIED** (426 ms); `[prune] story1_attdist_rung_b_12dof: []`; NO_PRUNE: **CERTIFIED** (404 ms); NO_CUT: **CERTIFIED** (343 ms); NO_IMPLIED_CUT: **CERTIFIED** (370 ms); NO_LINEAR_CUT: **CERTIFIED** (447 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (47 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story2_lateral_rung_a_8dof`

* family: Story ladders; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `cb0ec6031104`
* `relcert`: **CERTIFIED** (1106 ms); `[prune] story2_lateral_rung_a_8dof: []`; NO_PRUNE: **CERTIFIED** (1155 ms); NO_CUT: **CERTIFIED** (1003 ms); NO_IMPLIED_CUT: **CERTIFIED** (1036 ms); NO_LINEAR_CUT: **CERTIFIED** (1157 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (92 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story2_lateral_rung_b_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `5e62b7ea6ff9`
* `relcert`: **CERTIFIED** (1488 ms); `[prune] story2_lateral_rung_b_12dof: []`; NO_PRUNE: **CERTIFIED** (1515 ms); NO_CUT: **CERTIFIED** (1259 ms); NO_IMPLIED_CUT: **CERTIFIED** (1329 ms); NO_LINEAR_CUT: **CERTIFIED** (1529 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (41 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '---', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '---', 'MODER': '---', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story3_rollover_base_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape quadratic; rows identical: True; normalized md5 `cf68fbeeef5c`
* `relcert`: **CERTIFIED** (1197 ms); `[prune] story3_rollover_base_12dof: []`; NO_PRUNE: **CERTIFIED** (1257 ms); NO_CUT: **DECLINED** (3078 ms); NO_IMPLIED_CUT: **CERTIFIED** (1134 ms); NO_LINEAR_CUT: **CERTIFIED** (1200 ms); domains: uniform
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
* cover `STEEP_L`: λ = 5/4, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 5/4, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 5/4, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=5/4, MODER λ=5/4, FLAT λ=5/4 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story3_rollover_ladder_rung_a`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape quadratic; rows identical: True; normalized md5 `af17da3f1b89`
* `relcert`: **CERTIFIED** (878 ms); `[prune] story3_rollover_ladder_rung_a: []`; NO_PRUNE: **CERTIFIED** (896 ms); NO_CUT: **DECLINED** (2406 ms); NO_IMPLIED_CUT: **CERTIFIED** (767 ms); NO_LINEAR_CUT: **CERTIFIED** (887 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (25 ms)
* cover `STEEP_L`: λ = 27/20, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'jdd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only False
    * from `STEEP`: `STEEP:joint(B=2)->[STEEP@1, MODER@1, STEEP@1]; STEEP:base(B=1); MODER:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `MODER_L`: λ = 27/20, budget 2, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': 'jdd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER', 'STEEP'], branching 1, right-only True
    * from `STEEP`: `STEEP:repoDyn(B=2,preJ)->[MODER@2]; MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `MODER`: `MODER:joint(B=2)->[MODER@1, FLAT@1, MODER@1]; MODER:base(B=1); FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cover `FLAT_L`: λ = 27/20, budget 2, admissible ['MODER', 'FLAT'], flags {'STEEP': '-dd', 'MODER': '-dd', 'FLAT': 'jdd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FLAT', 'MODER'], branching 0, right-only True
    * from `MODER`: `MODER:repoDyn(B=2,preJ)->[FLAT@2]; FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
    * from `FLAT`: `FLAT:joint(B=2)->[FLAT@1, FLAT@1]; FLAT:base(B=1)`
* cells: **M1** yes: STEEP λ=27/20, MODER λ=27/20, FLAT λ=27/20 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept); **M6L** no (no linear-form atom kept)

### `story3_rollover_ladder_rung_b`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape quadratic; rows identical: False; normalized md5 `afd0663422a6`
* `relcert`: **CERTIFIED** (673 ms); `[prune] story3_rollover_ladder_rung_b: []`; NO_PRUNE: **CERTIFIED** (732 ms); NO_CUT: **DECLINED** (2603 ms); NO_IMPLIED_CUT: **DECLINED** (2551 ms); NO_LINEAR_CUT: **DECLINED** (2639 ms); domains: uniform
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
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (38 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j--', 'MODER': 'j--', 'FLAT': 'j--'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** yes: L.STEEP: 5 conjunct(s); L.MODER: 5 conjunct(s); L.FLAT: 5 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.STEEP: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.MODER: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.MODER: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.FLAT: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.FLAT: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; NO_IMPLIED=DECLINED; **M6L** yes: L.STEEP: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.STEEP: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.STEEP: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.MODER: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.MODER: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.MODER: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; L.FLAT: (omega_psi + (1 * (psi - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: (omega_theta + (1 * (theta_p - 0))) >= -0.5 kind=linear-form entry=rational route=linear-shape; L.FLAT: psi >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_psi + (1 * (psi - 0))) >= -0.5]; L.FLAT: theta_p >= -0.5 kind=derived-bound entry=rational route=derived-shape given=[(omega_theta + (1 * (theta_p - 0))) >= -0.5]; NO_LINEAR=DECLINED

### `watertank`

* family: Watertank; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/5; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `094c7ee69d35`
* `relcert`: **CERTIFIED** (743 ms); `[prune] watertank: [Low->PumpOff]`; NO_PRUNE: **DECLINED** (1121 ms); NO_CUT: **DECLINED** (1241 ms); NO_IMPLIED_CUT: **DECLINED** (1288 ms); NO_LINEAR_CUT: **CERTIFIED** (705 ms); domains: uniform
* `[cut] L.Low: 2 conjunct(s)`
* `[cut] L.Mid: 2 conjunct(s)`
* `[cut] L.High: 1 conjunct(s)`
* `[cut] R.Low: 2 conjunct(s)`
* `[cut] R.MidEco: 2 conjunct(s)`
* `[cut] R.MidBoost: 2 conjunct(s)`
* `[cut] R.High: 1 conjunct(s)`
* `[cut] R.PumpOff: 1 conjunct(s)`
* `[cut-x] L.Low: x <= 15.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.Mid: x <= 20.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.Low: x <= 12.5 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.MidEco: x <= 17.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.MidBoost: x <= 17.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.PumpOff: x <= 2.0 kind=closure entry=weakening route=frozen`
* `[admissible] Low_L: [Low, MidEco, MidBoost]`
* `[admissible] Mid_L: [MidEco, MidBoost, High]`
* `[admissible] High_L: [High]`
* `--handoff`: 6/6 checked, 6 passed, failing -, VACUOUS (identical rows) (81 ms)
* cover `Low_L`: λ = 2, budget 2, admissible ['Low', 'MidEco', 'MidBoost'], flags {'Low': 'j--', 'MidEco': 'j--', 'MidBoost': 'j--', 'High': 'jd-', 'PumpOff': '-dd'}, kinds ['base', 'joint'], path modes ['High', 'Low', 'MidBoost', 'MidEco'], branching 2, right-only False
    * from `Low`: `Low:joint(B=2)->[Low@1, Low@1, MidEco@1, MidBoost@1]; Low:base(B=1); MidEco:base(B=1); MidBoost:base(B=1)`
    * from `MidEco`: `MidEco:joint(B=2)->[MidEco@1, MidEco@1, MidBoost@1, High@1]; MidEco:base(B=1); MidBoost:base(B=1); High:base(B=1)`
    * from `MidBoost`: `MidBoost:joint(B=2)->[MidBoost@1, MidBoost@1, MidEco@1, High@1]; MidBoost:base(B=1); MidEco:base(B=1); High:base(B=1)`
* cover `Mid_L`: λ = 2, budget 2, admissible ['MidEco', 'MidBoost', 'High'], flags {'Low': '---', 'MidEco': 'j--', 'MidBoost': 'j--', 'High': 'j--', 'PumpOff': 'jdd'}, kinds ['base', 'joint'], path modes ['High', 'MidBoost', 'MidEco'], branching 2, right-only False
    * from `MidEco`: `MidEco:joint(B=2)->[MidEco@1, MidEco@1, MidBoost@1, High@1]; MidEco:base(B=1); MidBoost:base(B=1); High:base(B=1)`
    * from `MidBoost`: `MidBoost:joint(B=2)->[MidBoost@1, MidBoost@1, MidEco@1, High@1]; MidBoost:base(B=1); MidEco:base(B=1); High:base(B=1)`
    * from `High`: `High:joint(B=2)->[High@1, High@1, MidEco@1, MidBoost@1]; High:base(B=1); MidEco:base(B=1); MidBoost:base(B=1)`
* cover `High_L`: λ = 1, budget 1, admissible ['High'], flags {'Low': 'jdd', 'MidEco': 'jdd', 'MidBoost': 'jdd', 'High': 'j--', 'PumpOff': 'jdd'}, kinds ['base'], path modes ['High'], branching 0, right-only False
    * from `High`: `High:base(B=1)`
* cells: **M1** yes: Low λ=2, Mid λ=2 (affine dynamics); **M2** yes: Low B=2 via Low/MidBoost/MidEco, Mid B=2 via High/MidBoost/MidEco; **M3** yes: Low branch=2, Mid branch=2; **M4** yes: pruned Low->PumpOff; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.Low: 2 conjunct(s); L.Mid: 2 conjunct(s); L.High: 1 conjunct(s); R.Low: 2 conjunct(s); R.MidEco: 2 conjunct(s); R.MidBoost: 2 conjunct(s); R.High: 1 conjunct(s); R.PumpOff: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.Low: x <= 15.5 kind=implied-contraction entry=rational route=shape; L.Mid: x <= 20.0 kind=closure entry=weakening route=shape; R.Low: x <= 12.5 kind=implied-contraction entry=rational route=shape; R.MidEco: x <= 17.0 kind=closure entry=weakening route=shape; R.MidBoost: x <= 17.0 kind=closure entry=weakening route=shape; R.PumpOff: x <= 2.0 kind=closure entry=weakening route=frozen; NO_IMPLIED=DECLINED; **M6L** no (no linear-form atom kept)

## 10. Re-running

    RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/suite_v2/*/input.txt   # 45 CERTIFIED
    scripts/suite_v2_matrix.py --md /tmp/suite_v2.md --json /tmp/suite_v2.json
    scripts/suite_v2_matrix.py --z3time --md /tmp/suite_v2.md   # + Z3 time / route shapes (§14.3)
    scripts/suite_v2_matrix.py --only acc_tune_limp,rover_patrol_zones  # a subset
    scripts/domain_widening.py --jobs 6 --md /tmp/widen.md --json /tmp/widen.json
    scripts/domain_widening.py benchmarks/suite_v2/arm_plateau_crit/input.txt   # one file
    RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --emit-cuts benchmarks/suite_v2/arm_plateau_crit/input.txt c
                                                                 # the legacy literal `c` and the extended `cX`

Solver defaults (pass 7): `RELCERT_Z3_RLIMIT` 64 000 000 (was 8 000 000),
`RELCERT_MAX_QUERIES` 20 000 (was 5 000), `RELCERT_Z3_TIMEOUT` 10 000 ms and
`RELCERT_TIME_BUDGET_MS` 40 000 unchanged; every number in §17 and the generated
sections is under these defaults, with nothing else running (the heaviest 6-D queries
take 6.5–8.3 s against the 10 s timeout, so a loaded or slower machine can turn the two
`sat3w_*` tangent runs into ERROR; never into a verdict).
The matrix script needs the `relcert` binary (`lake build relcert`) and Z3 on the path;
it takes about four minutes for the whole suite (seven tool runs per benchmark; pass 6
with `--z3time` and the 6-D polynomial files: about 30 minutes; pass 7, 45 files with
`--z3time`: 14 minutes). The
widening script runs `relcert` once per (side, variable, direction) group plus the base
and the all-widened file (about 750 runs, 25 minutes at `--jobs 6`). Without
`RELCERT_IMPLIED_CUT=1` the twelve M6+ members of §8 are DECLINED (measured in pass 8:
`acc_spoof_lag`, `arm_plateau_*` ×3, `charger_fast_setpoints`, `platoon3_*` ×2,
`platoon_delay_*` ×2, `rover_patrol_refine`, `story3_rollover_ladder_rung_b`,
`watertank`); everything else certifies either way. (Pass 2 listed six; the list grew
with the later passes.)

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
* The Lean mechanization of the pass-4 files: the five replacements and the rigid-body
  family (quadratic energy rows and a quadratic non-connection guard) are tool-side only.

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

(Pass-3 run, kept as the record; the rows of the four files changed in pass 4 were updated, and the whole-suite pass-4 re-run is §14.4.) Totals of the pass-3 run: 39 files; **23** certify with every bound widened at once; **5** have a
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

**Pass 5 update (2026-10-09, §15).** The costs (i) and (ii) were re-examined by stepping
the claim slack looser. `acc_tune_lag`: claim now `a_L + 4 v_L ≤ 4 v_R + 16` (`w_L ≤ v_R +
4`, M4 recovered, the chain no longer load-bearing); `rover_patrol_refine`: rows now `a_L +
5 v_L ≤ 5 v_R + 0.35` (`w_L ≤ v_R + 0.07`, M3 recovered, the chain still load-bearing);
`acc_spoof_lag`: tight claim kept (M4 only from +3.5, where M1 is also lost). The table
above is the pass-4 (tight) record; the tight bounds are kept as remarks in the headers.

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

### 14.2 Task C — the rigid-body detumbling family (polynomial, dimension 4)

`sat_detumble_nominal`, `sat_detumble_weak`, `sat_detumble_phases`: a microsatellite with
inertia `diag(2, 4, 5)` kg m² and a z-axis reaction wheel (state `w1, w2, w3, h` per side),
Euler's equations of a gyrostat with rate-damping torquers and the wheel absorbing the
z-rate. The couplings `w2 w3, w3 w1, w1 w2, w2 h, w1 h` are genuine bilinear terms; they do
no work, so the body energy `E = 2 w1² + 4 w2² + 5 w3²` obeys `E' = −2 k E` — but only
through the cancellation of the cubic terms, which every flow query on the quadratic
energy rows must establish in nonlinear real arithmetic. The reference is the decoupled
design model (`w_i' = −k w_i`). Physical domains `|w_i| ≤ 1` rad/s (gyro range), `|h| ≤
2` N m s (wheel capacity), never load-bearing (widening: all three certify with every bound
widened at once). The FALLBACK is of a new shape: the design model's FDIR `SAFE` mode on
the ENERGY threshold `E > 1` (quadratic strict guard; actuators off, energy conserved,
sink), pruned by the non-connection certificate (source: no entry state has `E > 1`;
barrier: on `E = 1` the field gives `E' = −E < 0`, again a cubic cancellation).

| rung | deployed | claim (derived) | next step | λ, budget | cells (counter-runs) | Z3: queries, ms (proxied run), max query ms | UNSAT flow queries by route (joint + reposition, both sides) / one-sided |
|---|---|---|---|---|---|---|---|
| `sat_detumble_nominal` (nominal) | full gyrostat, `k = 0.5` | `E_L = E_R` (both inequalities, tolerance 0; exact) | — (exact) | 1 (λ ∈ [1, 1], synchronous; §7 L8), 2 | M2, M4 (NO_PRUNE DECLINED); NO_CUT CERTIFIED | 41, 1651, 760 | A 10, C 1 / energy cut O2 B/L 1, B/R 2 (cut + barrier), A/R 1 |
| `sat_detumble_weak` (degraded: 80 % actuators, `k_L = 0.4`; reference profiles NOMINAL 0.5 / ECONOMY 0.45 / SURVIVAL 0.42) | `E_R ≤ E_L ∧ E_L ≤ E_R + 0.205`; analytic `d* = 1 − k_L/k_R = 0.2` | 0.2 ERROR (tangent, Z3 unknown), 0.15 DECLINED | 1, 2 | M2, M3 (branch 2), M4, M6 (NO_CUT DECLINED: the quadratic engagement cut `E ≤ 1`) | 88, 12319, 3109 | A 13, B 3, C 3 / B/L 1, B/R 6, A/R 3 |
| `sat_detumble_phases` (refined: DETUMBLE `k = 0.5` → FINE `k = 0.3` at `E ≤ 0.2`) | DETUMBLE `E_L = E_R`; FINE `E_R ≤ E_L ∧ E_L ≤ E_R + 0.085`; analytic `d* = 0.2 (1 − 0.3/0.5) = 0.08` | 0.08 ERROR, 0.07 DECLINED | 1, 2 (both phases) | M2, M4, M5 (3/3 handoffs unsat), M6 (FINE cut `E ≤ 0.2`) | 68, 6596, 3025 | A 19, B 2, C 2 / B/L 2, B/R 2, A/R 1 |

"Route" is read off the logged SMT of a proxied run (`scripts/z3_timing_proxy.py`, the
matrix's `--z3time`): A = `dom ∧ ġ > 0` (whole-domain; also the right-only dynamic
reposition queries), B = `dom ∧ g = 0 ∧ ġ ≥ 0` (boundary), C = `dom ∧ g ≥ 0 ∧ ġ > 0`
(superlevel); the checker tries A, B, C per component and stops at the first `unsat`.
All three routes are used by the family's certificates; the heaviest single queries
(≈ 3 s) are the route-A/C queries of the weak and phase rungs. The `sat_detumble_fast`
variant (M1 at λ = 5/4) certified and was not added (§6).

### 14.3 Timing — full-suite run (Task D; feeds the paper's §6 cost paragraph)

One run of `scripts/suite_v2_matrix.py --z3time` on the final 42 files (Z3 4.15.1, warm
persistent session, `RELCERT_IMPLIED_CUT=1`, nothing else running; the domain-widening run
started after it). "tool ms" is `relcert`'s own reported time of the plain run; "wall s" the
process wall time of that run (start-up included). The Z3 columns come from ONE EXTRA run
through `scripts/z3_timing_proxy.py` (`RELCERT_Z3` = the proxy, which forwards to the same
Z3 binary and stamps each query from its `(check-sat)` to the sentinel echo): number of
queries, the summed and the largest per-query Z3 time. The proxied times include the pipe
hop (about 1 ms per query; it is why a few rows show Z3 ms slightly above tool ms); Z3
dominates every run. "UNSAT queries by shape" classifies each definitive `unsat` by the
asserted formula's last conjunct: A `ġ > 0`, B `g = 0 ∧ ġ ≥ 0`, C `g ≥ 0 ∧ ġ > 0`, with
`/L`, `/R` for one-sided queries (cut O2, non-connection, reposition regions);
"A-or-static" = an A-shaped query whose term has degree ≤ 1 (affine Lie derivatives and
static region queries cannot be told apart from the text); "other" = entry / handoff-like
shapes.

| benchmark | dim L/R | verdict | tool ms (relcert's own) | wall s (process) | Z3 queries | Z3 ms (sum) | Z3 max ms | UNSAT queries by shape |
|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | 2/2 | CERTIFIED | 131 | 0.33 | 63 | 217 | 94 | A-or-static/L 2, A-or-static/R 1, B 7, B/R 1, C 1, other 1 |
| `acc_spoof_limp` | 1/1 | CERTIFIED | 251 | 0.46 | 145 | 247 | 25 | A-or-static/R 7, B 19, B/L 2, B/R 3, C 1, other 2 |
| `acc_spoof_modes` | 1/1 | CERTIFIED | 212 | 0.46 | 92 | 234 | 84 | A-or-static/R 5, B 13, B/L 2, B/R 3, other 1 |
| `acc_tune_lag` | 2/2 | CERTIFIED | 137 | 0.3 | 39 | 120 | 46 | A-or-static/L 2, A-or-static/R 1, B 1, B/R 1, other 1 |
| `acc_tune_limp` | 1/1 | CERTIFIED | 373 | 0.58 | 175 | 367 | 90 | A-or-static/R 7, B 19, B/R 3, C 5, other 2 |
| `acc_tune_modes` | 1/1 | CERTIFIED | 294 | 0.54 | 122 | 210 | 20 | A-or-static/R 5, B 13, B/R 3, C 4, other 1 |
| `arm_plateau_crit` | 2/1 | CERTIFIED | 215 | 0.46 | 82 | 218 | 93 | A-or-static 6, A-or-static/- 16, A-or-static/L 3, B 4, B/L 1, B/R 3, C 2 |
| `arm_plateau_profiles` | 2/1 | CERTIFIED | 226 | 0.47 | 97 | 243 | 97 | A-or-static 7, A-or-static/- 20, A-or-static/L 4, B 6, B/L 1, B/R 4, C 2 |
| `arm_plateau_slow` | 2/1 | CERTIFIED | 140 | 0.4 | 81 | 160 | 40 | A-or-static 5, A-or-static/- 16, A-or-static/L 5, B 1, B/L 1, B/R 3, C 3, other 1 |
| `charger_fast_setpoints` | 1/1 | CERTIFIED | 234 | 0.47 | 106 | 258 | 99 | A-or-static 7, A-or-static/- 7, A-or-static/L 2, A-or-static/R 17, B 6, B/R 1, other 4 |
| `charger_fast_tapers` | 1/1 | CERTIFIED | 279 | 0.53 | 131 | 270 | 84 | A-or-static 8, A-or-static/- 7, A-or-static/L 2, A-or-static/R 25, B 7, B/R 1, other 4 |
| `match_multi_rate` | 2/2 | CERTIFIED | 317 | 0.45 | 151 | 342 | 92 | A-or-static 1, A-or-static/L 4, A-or-static/R 9, B 6, B/R 1, C 3, other 4 |
| `platoon_delay_linkloss` | 1/1 | CERTIFIED | 286 | 0.53 | 142 | 287 | 73 | A-or-static/- 4, A-or-static/L 4, A-or-static/R 8, B 12, B/L 3, B/R 3, other 3 |
| `platoon_delay_profiles` | 1/1 | CERTIFIED | 253 | 0.47 | 131 | 277 | 78 | A-or-static/- 4, A-or-static/L 2, A-or-static/R 11, B 12, B/L 2, B/R 4, other 2 |
| `quad_light_airframe_20` | 1/1 | CERTIFIED | 237 | 0.45 | 90 | 246 | 93 | A-or-static 2, A-or-static/R 4, B 9, B/L 2, B/R 4, other 1 |
| `quad_light_lag` | 2/2 | CERTIFIED | 96 | 0.33 | 22 | 64 | 21 | B 1, B/L 1, B/R 2 |
| `quad_light_profiles` | 1/1 | CERTIFIED | 463 | 0.62 | 253 | 447 | 41 | A-or-static 2, A-or-static/R 6, B 34, B/L 1, B/R 10, other 1 |
| `refinement_ladder_rover_rung1_2to3` | 3/2 | CERTIFIED | 260 | 0.38 | 137 | 202 | 17 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `refinement_ladder_rover_rung2_3to6` | 6/6 | CERTIFIED | 676 | 0.84 | 329 | 716 | 97 | A 15, A/L 3, A/R 21, B 3, C 12, other 3 |
| `refinement_ladder_rover_rung2_6dof` | 4/4 | CERTIFIED | 249 | 0.5 | 106 | 246 | 76 | A 24, A-or-static 1, A-or-static/R 3, A/L 3 |
| `refinement_ladder_rover_rung2b_6dof` | 6/6 | CERTIFIED | 258 | 0.5 | 118 | 294 | 98 | A 24, A-or-static 1, A-or-static/R 3, A/L 3 |
| `refinement_ladder_rover_rung2c_6dof` | 6/6 | CERTIFIED | 1343 | 1.59 | 619 | 1326 | 97 | A 33, A/L 3, A/R 21, B 6, C 21, other 6 |
| `refinement_ladder_rover_rung3_6to8` | 8/8 | CERTIFIED | 2878 | 3.09 | 959 | 2860 | 51 | A 66, A/L 3, A/R 39, B 18, C 36, other 1 |
| `refinement_ladder_rover_rung4_8to12` | 12/12 | CERTIFIED | 940 | 1.08 | 301 | 974 | 73 | A 6, A/L 3, A/R 39, B 9, C 9, other 1 |
| `rover3tier_rung12` | 3/3 | CERTIFIED | 213 | 0.45 | 91 | 267 | 98 | A 12, A-or-static 1, A-or-static/R 4, B 2, B/R 2 |
| `rover_dof_terrain_rung1` | 3/3 | CERTIFIED | 301 | 0.51 | 139 | 293 | 88 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung2` | 6/6 | CERTIFIED | 357 | 0.6 | 163 | 291 | 33 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung3` | 12/12 | CERTIFIED | 357 | 0.57 | 157 | 366 | 82 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung3_8d` | 8/8 | CERTIFIED | 347 | 0.53 | 169 | 378 | 93 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_patrol_refine` | 3/3 | CERTIFIED | 1700 | 1.84 | 797 | 1673 | 50 | A 32, A-or-static 10, A-or-static/L 11, A-or-static/R 36, B 44, other 1 |
| `rover_patrol_zones` | 2/2 | CERTIFIED | 379 | 0.63 | 278 | 466 | 96 | A-or-static 14, A-or-static/L 4, A-or-static/R 80, B 14, B/R 4, other 5 |
| `sat_detumble_nominal` | 4/4 | CERTIFIED | 1608 | 1.81 | 41 | 1651 | 760 | A 10, A/R 1, B/L 1, B/R 2, C 1, other 1 |
| `sat_detumble_phases` | 4/4 | CERTIFIED | 6521 | 6.74 | 68 | 6596 | 3025 | A 19, A/R 1, B 2, B/L 2, B/R 2, C 2, other 2 |
| `sat_detumble_weak` | 4/4 | CERTIFIED | 12302 | 12.56 | 88 | 12319 | 3109 | A 13, A/R 3, B 3, B/L 1, B/R 6, C 3, other 1 |
| `story1_attdist_rung_a_6to8` | 8/8 | CERTIFIED | 20549 | 20.78 | 192 | 20414 | 4959 | A/L 3, A/R 3, B 20, C 1 |
| `story1_attdist_rung_b_12dof` | 12/12 | CERTIFIED | 497 | 0.73 | 158 | 490 | 99 | A 18, A/L 3, A/R 3, B 2, C 1 |
| `story2_lateral_rung_a_8dof` | 8/8 | CERTIFIED | 1146 | 1.38 | 518 | 1127 | 88 | A 24, A/L 3, A/R 21, B 12, C 21, other 3 |
| `story2_lateral_rung_b_12dof` | 12/12 | CERTIFIED | 1494 | 1.75 | 610 | 1459 | 96 | A 24, A/L 3, A/R 21, B 21, C 21, other 3 |
| `story3_rollover_base_12dof` | 12/12 | CERTIFIED | 1255 | 1.48 | 466 | 1220 | 95 | A 78, A/L 3, A/R 39, B 42, C 6, other/L 1 |
| `story3_rollover_ladder_rung_a` | 12/12 | CERTIFIED | 900 | 1.15 | 320 | 812 | 27 | A 42, A/L 3, A/R 39, B 6, C 6, other/L 1 |
| `story3_rollover_ladder_rung_b` | 12/12 | CERTIFIED | 688 | 0.91 | 212 | 690 | 49 | A-or-static/L 6, A/L 3, A/R 3, B 20, C 1 |
| `watertank` | 1/1 | CERTIFIED | 194 | 0.45 | 84 | 139 | 16 | A-or-static 3, A-or-static/R 6, B 6, B/L 3, B/R 3, other 3 |
| **total** | | | **61182** | | | **61108** | | |

Pass 5 (§15): the rows of `acc_tune_lag` and `rover_patrol_refine` (claims changed) are
re-measured from the pass-5 run of `scripts/suite_v2_matrix.py --z3time` (before: 199 ms,
53 queries; 1264 ms, 648 queries); the other rows and the total are the pass-4 run. The
pass-5 run as a whole: 42 / 42 CERTIFIED, 62.4 s tool time in total (Z3 62.6 s).

Pass 6 (§16.4): the four new 6-D files' rows (tool ms / Z3 queries / Z3 ms / max ms):
`sat3w_detumble_weak` 9068 / 88 / 8967 / 2956, `sat3w_detumble_phases` 11668 / 71 / 11651 /
3271, `platoon3_linkloss` 2254 / 715 / 2194 / 50, `platoon3_profiles` 2363 / 754 / 2340 / 57;
`acc_spoof_modes` and `acc_tune_modes` dropped. The pass-6 run as a whole (44 files):
88.3 s tool time in total (Z3 87.7 s); the full pass-6 table is §16.4.

Pass 7 (§17; new defaults `RELCERT_Z3_RLIMIT` 64 000 000, `RELCERT_MAX_QUERIES` 20 000):
the rows of the changed and new files (tool ms / wall s / Z3 queries / Z3 ms / max ms):
`sat3w_detumble_nominal` (new) 1629 / 1.88 / 41 / 1577 / 777, `sat3w_detumble_weak`
11982 / 12.19 / 89 / 12115 / 6514, `sat3w_detumble_phases` 12173 / 12.44 / 69 / 12315 /
8280, `platoon3_linkloss` 2156 / 2.41 / 715 / 2129 / 95, `platoon3_profiles` 2271 / 2.53 /
754 / 2224 / 86 (the plain runs of the platoon files find their cover at λ = 1 and do not
search the grid further). The pass-7 run as a whole (45 files): 92.8 s tool time in total
(Z3 93.5 s); the full table is §17.6.

Summary: 42 / 42 CERTIFIED in 61.2 s of tool time in total (sum of the per-benchmark
`relcert` times); 37 benchmarks under 1.6 s each; the long ones are
`story1_attdist_rung_a_6to8` (20.5 s, one query of 5.0 s), `sat_detumble_weak` (12.3 s),
`sat_detumble_phases` (6.5 s), `refinement_ladder_rover_rung3_6to8` (2.9 s). The
polynomial rigid-body rungs have FEW but HEAVY queries (41–88 queries, up to 3.1 s each);
the 12-dof ladders have many light ones (300–960 queries, ≤ 100 ms each).

### 14.4 Domain-widening re-run on the whole suite (Task D)

`scripts/domain_widening.py --jobs 6` over the final 42 files (796 runs):

| benchmark | base | all widened | load-bearing evolve bounds (widened by half the range: verdict) | skipped (one-sided) |
|---|---|---|---|---|
| `acc_spoof_lag` | CERTIFIED | CERTIFIED | none | none |
| `acc_spoof_limp` | CERTIFIED | CERTIFIED | none | none |
| `acc_spoof_modes` | CERTIFIED | CERTIFIED | none | none |
| `acc_tune_lag` | CERTIFIED | CERTIFIED | none | none |
| `acc_tune_limp` | CERTIFIED | CERTIFIED | none | none |
| `acc_tune_modes` | CERTIFIED | CERTIFIED | none | none |
| `arm_plateau_crit` | CERTIFIED | CERTIFIED | none | none |
| `arm_plateau_profiles` | CERTIFIED | CERTIFIED | none | none |
| `arm_plateau_slow` | CERTIFIED | CERTIFIED | none | none |
| `charger_fast_setpoints` | CERTIFIED | CERTIFIED | none | none |
| `charger_fast_tapers` | CERTIFIED | CERTIFIED | none | none |
| `match_multi_rate` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo` |
| `platoon_delay_linkloss` | CERTIFIED | CERTIFIED | none | none |
| `platoon_delay_profiles` | CERTIFIED | DECLINED | none | none |
| `quad_light_airframe_20` | CERTIFIED | CERTIFIED | none | none |
| `quad_light_lag` | CERTIFIED | CERTIFIED | none | none |
| `quad_light_profiles` | CERTIFIED | CERTIFIED | none | none |
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
| `sat_detumble_nominal` | CERTIFIED | CERTIFIED | none | none |
| `sat_detumble_phases` | CERTIFIED | CERTIFIED | none | none |
| `sat_detumble_weak` | CERTIFIED | CERTIFIED | none | none |
| `story1_attdist_rung_a_6to8` | CERTIFIED | DECLINED | `L.psi.lo` (-0.6->-1.2: DECLINED); `L.theta_p.lo` (-0.6->-1.2: ERROR) | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story1_attdist_rung_b_12dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story2_lateral_rung_a_8dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story2_lateral_rung_b_12dof` | CERTIFIED | CERTIFIED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story3_rollover_base_12dof` | CERTIFIED | DECLINED | none | none |
| `story3_rollover_ladder_rung_a` | CERTIFIED | DECLINED | none | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `story3_rollover_ladder_rung_b` | CERTIFIED | DECLINED | `R.psi.hi` (0.15->0.475: DECLINED); `R.theta_p.hi` (0.15->0.475: DECLINED) | `L.s.lo`, `L.s.lo`, `L.s.lo`, `R.s.lo`, `R.s.lo`, `R.s.lo` |
| `watertank` | CERTIFIED | CERTIFIED | none | none |

Totals: 42 files; **29** certify with every bound widened at once; **2** have a
load-bearing group; **11** pass every single-group widening but fail the all-at-once one.
Classification of every load-bearing bound (nothing is classified "forcing"):

* **Forward-invariant (stated in the header):** `story1_attdist_rung_a_6to8` `L.psi.lo`,
  `L.theta_p.lo` (−0.6; the cascade `ψ' = ω_ψ − ψ, ω_ψ' = −ω_ψ` with `ω_ψ ≥ −0.6`; the
  `θ_p` run is ERROR = the 600 s budget, not a decline); `story3_rollover_ladder_rung_b`
  `R.psi.hi`, `R.theta_p.hi` (0.15; the reference attitude `ψ' = −ψ` contracts to 0, every
  face of the box inflows; §13.6 A1).
* **Joint-only (11), unchanged files, bisected in pass 3 (§13.1):** the speed floors
  `L.v.lo` with `R.v.lo` (`v ≥ 0`, forward-invariant: `v' = 3 (c − v)`, `c > 0`) in the 8
  terrain / position rungs and `story3_rollover_base_12dof`,
  `story3_rollover_ladder_rung_a`; the right attitude pairs of
  `refinement_ladder_rover_rung4_8to12` (forward-invariant cascade); `L.g.hi` with
  `R.g.hi` in `platoon_delay_profiles` (60 m gap cap, forward-invariant for every
  admissible mode, the radar range).
* **Stated physical limits that no certificate needs:** every domain bound of the 21 pass-4
  non-kept files (ACC `|a| ≤ 10`, rover `|a| ≤ 2`, gyro `|w_i| ≤ 1`, wheel `|h| ≤ 2`, …):
  all of them certify with every bound widened at once.
* **Skipped (one-sided on both sides):** the odometer floors `s ≥ 0` (forward-invariant).

### 14.5 Matrix before / after pass 4

| mechanism | pass 3 (39) | pass 4 (42) | change |
|---|---|---|---|
| M1 | 18 | 18 | −`acc_spoof_cruise`, −`acc_tune_gain`, −`quad_light_airframe_40` (replaced); +`acc_spoof_limp`, +`acc_tune_limp`, +`quad_light_profiles` |
| M2 | 26 | 29 | +3 rigid-body rungs |
| M3 | 6 | **10** | −`rover_patrol_refine` (tight claim, §13.6); +`acc_spoof_limp`, `acc_tune_limp`, `quad_light_profiles`, `arm_plateau_profiles`, `sat_detumble_weak` |
| M4 | 13 | 14 | −`acc_spoof_lag`, −`acc_tune_lag` (pairing emptied by the derived floor, §13.6); +3 rigid-body rungs (energy-threshold fallback); replacements keep theirs |
| M5 | 6 | **10** | +`acc_spoof_limp`, `acc_tune_limp`, `platoon_delay_linkloss`, `sat_detumble_phases` |
| M6 | 19 | 26 | +lag rungs ×2, story3 rung_b, limp ×2, `sat_detumble_weak`, `sat_detumble_phases` |
| M6+ | 6 | 10 | +lag rungs ×3 (`acc_*_lag`, `rover_patrol_refine`), story3 rung_b |
| M6L | 3 | 7 | +lag rungs ×3, story3 rung_b |
| per-mode domains | 0 | 0 | |

Replaced in pass 4 (each by a superset of its cells, §14.1): `acc_spoof_cruise` →
`acc_spoof_limp`, `acc_tune_gain` → `acc_tune_limp`, `quad_light_airframe_40` →
`quad_light_profiles`, `arm_plateau_lowgain` → `arm_plateau_profiles`,
`platoon_delay_band` → `platoon_delay_linkloss`. Added: the three rigid-body rungs.
Dropped without replacement: none. Changed in place: `story3_rollover_ladder_rung_b`
(A1), `acc_spoof_lag`, `acc_tune_lag`, `rover_patrol_refine` (A2), header pointers in
`acc_spoof_lag`, `acc_spoof_modes`, `acc_tune_lag`, `acc_tune_modes`.
Duplicate check: no two files normalize to the same model, and no two differ only in
tolerance constants (the matrix script's new tolerance-masked hash, §8).

### 14.6 `suite_uniform` regression (pass 4)

No Lean / tool code was changed in pass 4 (only `benchmarks/suite_v2`, `scripts/` and docs),
so no emission diff was owed. As a sanity check on the final tree: `relcert --check-quick
benchmarks/suite_uniform/*/input.txt` → `[suite] 40 certified, 1 declined, 0 error(s) —
matches the declared suite`, coverage watertank 6/6, cut probes 97/97, modal 504/504,
handoff 191/191, non-connection 2/2, pruned edges 1/1, `QUICK CHECKS PASSED` (49.7 s).


## 15. Pass 5 (2026-10-09): claim tolerances for the lost cells; open decisions resolved

Only claim rows (tolerance constants), headers and this document changed; no dynamics,
domain, guard, tool or Lean file. Every run `RELCERT_IMPLIED_CUT=1` (except the
`RELCERT_NO_IMPLIED_CUT=1` counter-run), binary of `049991c`, Z3 4.15.1. The stepping
runs were made on copies of the files with only the row constant changed; the installed
files were then re-run through `scripts/suite_v2_matrix.py --z3time` (§3, §8, §9 are that
run's output) and `scripts/domain_widening.py`.

### 15.1 The lag rungs: smallest looser slack that recovers the lost cell

Goal (user decision 1): recover M4 on the two ACC lag rungs (`RELCERT_NO_PRUNE=1` must
DECLINE while the plain run CERTIFIES) and M3 on `rover_patrol_refine` (a used fork in
the emitted cover), keeping M6 / M6+ / M6L if some slack keeps both; otherwise M4 / M3
win (M1–M5 are the headline mechanisms).

| benchmark | row constant `c` | tight (pass 4) | chosen | one step tighter than chosen | why the threshold is where it is |
|---|---|---|---|---|---|
| `acc_tune_lag` | `a_L + 4 v_L ≤ 4 v_R + c` | `+2` (`w_L ≤ v_R + 0.5`; 1.75 DECLINED) | **`+16`** (`w_L ≤ v_R + 4`) | `+15.75`: CERTIFIED, NO_PRUNE CERTIFIED (also 15.9, 15.95) | under the cuts `w_L ≥ 24` (`v_L ≥ 23`, `q_1 ≥ −7`, `q_3 ≥ −17` give `a_L ≥ 4` at `v_L = 23`); the CRUISE_L/DISENGAGE_R region (`v_R < 20`) is non-empty iff `4·24 ≤ 4·20 + c` |
| `rover_patrol_refine` | `a_L + 5 v_L ≤ 5 v_R + c` (all four rows; zone margins unchanged) | `−0.25` (`w_L ≤ v_R − 0.05`; −0.5 DECLINED) | **`+0.35`** (`w_L ≤ v_R + 0.07`) | `+0.30`: CERTIFIED, no fork (max non-self successors 1) | measured (0.05 grid; on the 0.25 grid the first branching point +0.5 loses M6+ / M6L) |
| `acc_spoof_lag` | `a_L + 2.5 v_L ≤ 2.5 v_R + c` | `−5.5` (`w_L ≤ v_R − 2.2`; −5.75 DECLINED) | **`−5.5` kept** | — (M4 first at `+3.5`; `+3.25`, `+3.4`, `+3.45`: NO_PRUNE CERTIFIED) | `w_L ≥ 21.4` under the cuts; region non-empty iff `2.5·21.4 ≤ 2.5·20 + c` |

Stepping evidence (plain run / counter-runs; "cuts" = NO_CUT, NO_IMPLIED_CUT and
NO_LINEAR_CUT, which always agreed on these files):

* `acc_tune_lag`: plain CERTIFIED for every `c` from 2 to 18, DECLINED at 19 and 20.
  NO_PRUNE CERTIFIED for `c ≤ 15.95` (sampled 2.25, 2.5, 3, 4, 6, 8, 10, 12, 14, 15,
  15.5, 15.75, 15.9, 15.95), DECLINED for `c ≥ 16` (16, 16.25, 16.5, 17, 18). Cuts
  DECLINE for every sampled `c ≤ 9.75` (2–8 coarse, 8.25–9.75 at 0.25), CERTIFY for `c ≥
  10` (10, 12, 14, 15, 15.5, 15.75, 16, …, 18). λ: 2 at +2, 5/4 at 15.75–18. **No slack
  keeps M4 and the chain**: the chain stops being load-bearing at 10, M4 starts at 16.
  Chosen `+16`: cells M1 (λ = 5/4) M2 (budget 3) M4 — gained M4, lost M6 M6+ M6L.
* `rover_patrol_refine` (the matrix, which replays the emitted cover):

  | `c` | λ (all windows) | M3 (fork) | NO_CUT | NO_IMPLIED_CUT | NO_LINEAR_CUT | NO_PRUNE |
  |---|---|---|---|---|---|---|
  | −0.25 (pass 4) | 7/4 (FAST 5/2) | no (max 1) | DECLINED | DECLINED | DECLINED | CERTIFIED (nothing pruned) |
  | 0, 0.25 | 2 | no (max 1) | DECLINED | DECLINED | DECLINED | CERTIFIED |
  | 0.30 | 9/4 | no (max 1) | DECLINED | DECLINED | DECLINED | CERTIFIED |
  | **0.35**, 0.40 | 9/4 | **yes: SLOW branch 2** (MEDIUM_ECO, MEDIUM_BRISK) | DECLINED | DECLINED | DECLINED | CERTIFIED |
  | 0.45 | 5/2 | yes | DECLINED | DECLINED | DECLINED | CERTIFIED |
  | 0.5 | 5/2 | yes | DECLINED | CERTIFIED | CERTIFIED | CERTIFIED |
  | 0.75, 1.0 | 11/4 (1.0: ECO/BRISK/FAST 3) | yes | DECLINED | CERTIFIED | CERTIFIED | CERTIFIED |

  Chosen `+0.35`: cells M1 M2 M3 M5 M6 M6+ M6L — M3 gained, nothing lost. The task's
  "NO_PRUNE still declines so M4 is kept" does not apply: this rung declares no fallback
  (nothing is pruned at any slack; it never had M4).
* `acc_spoof_lag`: plain CERTIFIED from −5.5 to 5.5, DECLINED at 6, 8, 10, 15. NO_PRUNE
  CERTIFIED for `c ≤ 3.45`, DECLINED for `c ≥ 3.5` (3.5–5.5). Cuts DECLINE only at −5.5
  and −5.25; CERTIFY at −5.0 and every sampled point above (0.5 steps to 3.0, then 3.25,
  3.5). λ: 5/2 (−5.5), 7/4 (−5.25), 5/4 (−5.0, −4.0), 1 from −2.0 on (−2, 0, 2, 3.25,
  3.5–5.5). At the M4 slack +3.5 the cells would be **M2 M4 only**: M1 is lost too (λ = 1
  certifies first), so the trade is {M1 M2 M6 M6+ M6L} → {M2 M4}, one headline cell for
  another plus three M6 cells. That is outside the stated trade (M6L for M4 / M3), so the
  tight claim is KEPT and the measured alternative is written in the header as a remark;
  switching is a one-constant change (`(- (* 2.5 R_v) 5.5)` → `(+ (* 2.5 R_v) 3.5)`).

Counter-runs on the installed files (§9 records):

| benchmark | claim | plain | NO_PRUNE | NO_CUT | NO_IMPLIED_CUT | NO_LINEAR_CUT | cells |
|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | `−5.5` (unchanged) | CERTIFIED | CERTIFIED | DECLINED | DECLINED | DECLINED | M1 M2 M6 M6+ M6L |
| `acc_tune_lag` | `+16` | CERTIFIED | **DECLINED** | CERTIFIED | CERTIFIED | CERTIFIED | M1 M2 M4 |
| `rover_patrol_refine` | `+0.35` | CERTIFIED | CERTIFIED (nothing pruned) | DECLINED | DECLINED | DECLINED | M1 M2 M3 M5 M6 M6+ M6L |

Headers: `acc_tune_lag` and `rover_patrol_refine` state the claim, that the tolerance is
chosen so that the fallback (resp. branching) mechanism is exercised, the one-step-tighter
result, and the tight bound as a remark; `acc_spoof_lag` keeps its claim text and gains
the not-taken remark.

### 15.2 `charger_fast_tapers`: tolerance 5 is the fallback threshold (claim kept)

Tightening (user decision 2), rows `x_L ≤ x_R + c` in all three phases: CERTIFIED at 5,
4, 3, 2, 1.5, 1; DECLINED at 0.75, 0.5, 0.25, 0 and, refined at 0.05, at 0.95, 0.9, 0.85,
0.8. **Tightest certifiable: 1; first DECLINED step: 0.95.** But the matrix of the
tightened file (`c = 1`) is M2 M3 M6 — **M4 is lost** (NO_PRUNE CERTIFIES): the BULK
guard has `x_L ≥ 15` and FAULT has `x_R < 10`, so the BULK_L/FAULT_R pairing survives the
row only for `c ≥ 5`. Measured: NO_PRUNE CERTIFIED at 4.95, 4.9, 4.75, 4.5, 4, 3, 2, 1;
DECLINED at 5. The pass-1 tolerance 5 is exactly the smallest that exercises the
fallback. Since tightening would trade a headline cell for nothing, the claim is KEPT at
5 and the header now says so (the tolerance is chosen so that the fallback is exercised;
the tight bound 1 and its first DECLINED step 0.95 are a remark) — the same pattern as
15.1. Counter-runs of the installed file (unchanged from pass 4): NO_PRUNE DECLINED,
NO_CUT DECLINED, NO_IMPLIED_CUT CERTIFIED, NO_LINEAR_CUT CERTIFIED; cells M2 M3 M4 M6
(unchanged). At `c = 1`: NO_PRUNE CERTIFIED, NO_CUT DECLINED, NO_IMPLIED_CUT CERTIFIED,
NO_LINEAR_CUT CERTIFIED. Widening: CERTIFIED with every bound widened at once, no
load-bearing group, at `c = 5` and at `c = 1` alike.

### 15.3 Suite run, widening, matrix before / after

Suite run (a loop over all 42 `benchmarks/suite_v2/*/input.txt`, counted, not inferred):
**42 files, 42 CERTIFIED**, before and after the matrix run. Widening
(`scripts/domain_widening.py` on `acc_spoof_lag`, `acc_tune_lag`, `rover_patrol_refine`,
`charger_fast_tapers` and the tolerance-1 copy of the latter): every file CERTIFIES with
every bound widened at once; no load-bearing group (§14.4 is unchanged for them).
Duplicate and tolerance-only-variant checks: none.

| mechanism | pass 4 (42) | pass 5 (42) | change |
|---|---|---|---|
| M1 | 18 | 18 | |
| M2 | 29 | 29 | |
| M3 | 10 | **11** | +`rover_patrol_refine` |
| M4 | 14 | **15** | +`acc_tune_lag` |
| M5 | 10 | 10 | |
| M6 | 26 | 25 | −`acc_tune_lag` |
| M6+ | 10 | 9 | −`acc_tune_lag` |
| M6L | 7 | 6 | −`acc_tune_lag` |
| per-mode domains | 0 | 0 | |

Every non-kept file still exercises at least two of M1–M6 (`acc_tune_lag`: M1 M2 M4).
Table-1 grouping (§8): the ACC family now has 5 files with a load-bearing pruned fallback
(was 4), 4 cut-reliant (was 5), 1 widened-cut-reliant and 1 linear-form-reliant (were 2).
Timing rows of the two changed claims are in §14.3.

### 15.4 Decisions (user, 2026-10-09) — resolved

* **Lag rungs loosened** (A2 costs): RESOLVED — `acc_tune_lag` `+16` (M4 back),
  `rover_patrol_refine` `+0.35` (M3 back, chain kept); `acc_spoof_lag` kept tight because
  its M4 slack also loses M1 (15.1; the user may still choose `+3.5`).
* **Limp-mode pattern** (fault-latched degraded modes for genuine mode-dependent rows,
  §14.1, finding 12): ACCEPTED.
* **λ = 1 on `sat_detumble_nominal`** (synchronous exact refinement, §14.2, §7 L8):
  ACCEPTED.
* **New engagement guards** (ACC engagement band with `|a| ≤ 2`, the rover's settled
  hand-over `|a| ≤ 0.5`, the story-3 settled-attitude zone switch; controller-design
  conditions, §13.6): ACCEPTED.
* **`quad_light_lag` kept** (exercises exactly two mechanisms, M1 M2): suite stays 42.
* **`charger_fast_tapers` tightened**: RESOLVED by measurement — the tightest tolerance
  is 1 (0.95 DECLINED), but 5 is the fallback threshold, so the claim stays 5 with the
  header corrected (15.2; the user may still choose 1 at the cost of M4).

## 16. Pass 6 (2026-10-09): mid-dimensional lifts, trim, consolidation

Goal: the suite was bimodal — every file that exercises branching (M3), pruning (M4) or
mode-dependent rows (M5) was at 1–4 D, and no file at ≥ 6 D exercised branching or
pruning (the 6–12-D ladders have M5 at most). This pass adds four 6-D files (two
polynomial, two linear) that do, and drops two redundant 1-D files. No tool, Lean or
`suite_uniform` file changed; `scripts/suite_v2_matrix.py` only gained two family-prefix
lines and the new family's place in the Table-1 group order. Every run `RELCERT_IMPLIED_CUT=1` (except the `RELCERT_NO_IMPLIED_CUT=1`
counter-run), binary of `049991c`, Z3 4.15.1, DEFAULT solver settings
(`RELCERT_Z3_TIMEOUT` 10 s, `RELCERT_Z3_RLIMIT` 8 000 000) unless a line says otherwise.

### 16.1 Task 1 — the three-wheel gyrostat (6 D, polynomial)

**Model.** The single-z-wheel gyrostat of §14.2 becomes a full three-wheel gyrostat:
body rates `w = (w1, w2, w3)`, inertia `J = diag(2, 4, 5)`, wheel momenta `h = (h1, h2,
h3)` on the principal axes, state `(w1, w2, w3, h1, h2, h3)` per side. Euler's equations
with no external torque, `J w' = −w × (J w + h) − h'`, and the rate-damping wheel law
`h_i' = k J_i w_i` give `J w' = −w × (J w + h) − k J w`; componentwise

    w1' = −0.5 w2 w3 + 0.5 (w3 h2 − w2 h3) − k w1
    w2' = 0.75 w3 w1 + 0.25 (w1 h3 − w3 h1) − k w2
    w3' = −0.4 w1 w2 + 0.2 (w2 h1 − w1 h2) − k w3
    h1' = 2 k w1,  h2' = 4 k w2,  h3' = 5 k w3.

The energy `E = w · J w = 2 w1² + 4 w2² + 5 w3²` obeys `E' = −2 w · (w × H) − 2 k E =
−2 k E` because `w · (w × H) = 0` for every `H = J w + h`: the gyroscopic cubic terms
cancel (`−2 + 6 − 4 = 0` on `w1 w2 w3`) and so do the six wheel-coupling cubic terms
(`w1 w3 h2`, `w1 w2 h3`, `w2 w3 h1`, each `+2` and `−2`). The exact invariant functional is
therefore still `E` (checked by hand above and implicitly by every certifying flow query,
which Z3 can only close through this cancellation; each query has 12 real variables).
The wheels conserve `|J w + h|` (`H · H' = 0`); no magnetorquer is needed for `E' = −2kE`
and none is modeled. The design model (right) is `w_i' = −k w_i`, `h_i' = k J_i w_i`.
Domains `|w_i| ≤ 1` rad/s (gyro range), `|h_i| ≤ 2` N m s (wheel capacity); guards and the
SAFE fallback (`E > 1`) as in §14.2.

**Z3 behaviour — the binding limit is the tool's resource limit, not the timeout.**
`RELCERT_Z3_TIMEOUT=120000` changed nothing: every inconclusive query came back
`unknown` after 1–3 s, far below any timeout. The logged queries (`scripts/z3_timing_proxy.py`)
carry `(set-option :rlimit 8000000)`, the tool's deterministic per-query work bound
(`RelCertifier/Trusted/Z3.lean`, overridable by `RELCERT_Z3_RLIMIT`). Re-running the
four `unknown` queries of the first phases draft (FINE envelope `E ≤ 0.2`, `k_F = 0.3`,
row 0.1) with plain `z3` and no rlimit: **unsat in 2.4, 5.0, 2.6 and 6.1 s**. They are the
FINE_L / DETUMBLE_R segment, the upper conjunct `E_L ≤ E_R + d`, routes B (`dom ∧ cuts ∧
g = 0 ∧ ġ ≥ 0`) and C (`dom ∧ cuts ∧ g ≥ 0 ∧ ġ > 0`). Removing the wheel-capacity bounds
`|h_i| ≤ 2` from the route-B query makes it unsat in 0.4 s within the rlimit (route C
stays `unknown`; the bounds
bring `h` into the NRA projection although `h` cancels out of `ġ`); the bounds are the
stated physical domain, so this was only a diagnosis.

| file / variant | tolerance | default settings | other settings |
|---|---|---|---|
| `sat3w_detumble_weak` (`k_L = 0.4` vs 0.5 / 0.45 / 0.42) | **0.205** | **CERTIFIED** 8.8 s | |
| | 0.2 = `d*` (tangent) | ERROR (`unknown`, rlimit) 9.2 s | `RELCERT_Z3_RLIMIT=0`: **CERTIFIED** 12.2 s |
| | 0.19, 0.15 | DECLINED 5.6 s, 6.0 s | |
| phases draft, envelope 0.2, `k_F = 0.3` (the 4-D constants) | 0.085, 0.09, 0.1, 0.12, 0.15, 0.17, 0.18 | ERROR (FINE_L: `DETUMBLE=incon`) 13–17 s | rlimit 16 M, 32 M, 64 M: 0.085 **CERTIFIED** 9.2 s; rlimit 0: 0.08 = `d*` **CERTIFIED** 12.6 s |
| | 0.19, 0.2 (≈ the envelope itself) | CERTIFIED 6.9 s, 3.6 s | |
| | syntactic variants at 0.085 (guard scaled ×5, row scaled ×5, conjuncts swapped) | ERROR | |
| 5-D variant (wheels on x, y; z torquer) | 0.085 | ERROR (FINE_L `incon`) 20.7 s | |
| `sat3w_detumble_phases` (envelope **0.3**, `k_F` **0.35**) | **0.095** | **CERTIFIED** 11.5 s | |
| | 0.09 = `d*` (tangent) | ERROR 8.1 s | rlimit 0: **CERTIFIED** 12.5 s |
| | 0.085, 0.08 | DECLINED 4.1 s, 4.2 s | |

Scan for the phases rung (default settings, row at `d* + 0.005` with `d* = E_F (1 − k_F /
0.5)`): envelope `E_F` ∈ {0.2, 0.25, 0.3, 0.5} × `k_F` ∈ {0.25, 0.35, 0.4, 0.45}; CERTIFIED
at (0.25, 0.4), (0.3, 0.35), (0.3, 0.4), (0.5, 0.45), ERROR at the other twelve. The
installed point (0.3, 0.35) is the certifying one with the largest gain drop; the header
states that the constants are a solver-budget accommodation.

**L8 corrected.** The same holds for the 4-D rungs of §14.2: with `RELCERT_Z3_RLIMIT=0`
`sat_detumble_phases` at the analytic 0.08 CERTIFIES (36.7 s) and `sat_detumble_weak` at
the analytic 0.2 CERTIFIES (44.9 s). L8 ("Z3 inconclusive at tangency") is the tool's
deterministic resource limit, not an incompleteness of Z3's NRA procedure on these
queries. Files unchanged (open decision, §16.6).

**Installed (both CERTIFY under the default settings):**

| file | claim | λ, budget | cells (counter-runs) | Z3 (queries, total, max) |
|---|---|---|---|---|
| `sat3w_detumble_weak` | `E_R ≤ E_L ≤ E_R + 0.205` (`d* = 0.2`) | 1 (synchronous), 2 | M2, M3 (NOMINAL → ECONOMY, SURVIVAL), M4 (NO_PRUNE DECLINED), M6 (NO_CUT DECLINED; NO_IMPLIED_CUT, NO_LINEAR_CUT CERTIFIED) | 88, 8.97 s, 2.96 s (median query 2 ms; 3 queries over 1 s) |
| `sat3w_detumble_phases` | DETUMBLE exact; FINE `E_R ≤ E_L ≤ E_R + 0.095` (`d* = 0.09`) | 1, 2 (both phases) | M2, M4 (NO_PRUNE DECLINED), M5 (rows differ, `--handoff` 3/3 unsat), M6 (NO_CUT DECLINED) | 71, 11.65 s, 3.27 s (median 3 ms; 4 over 1 s; 2 route queries `unknown` on the first stratification pass, the component then proven on the retry with the other component in the domain, 2.3 s unsat) |

Widening: both CERTIFY with every bound widened at once; no load-bearing group. The
6-D nominal rung (`k = 0.5`, exact rows) CERTIFIED in 1.5 s and was not added (it would
add only M2 M4 and the suite would exceed 44).

### 16.2 Task 2 — the three-follower CACC string (6 D, linear)

**Model.** A lead vehicle cruising at constant speed and three automated followers;
per link `i` (follower `i` behind its predecessor) the gap `g_i` and the closing rate
`r_i = v_{i−1} − v_i`, `g_i' = r_i`; state `(g1, r1, g2, r2, g3, r3)` per side. Follower
`i` commands `a_i = a_{i−1} + kp (g_i − c) + kd r_i` (CACC; the predecessor's acceleration
over V2V as feed-forward; `a_0 = 0`), so `r_i' = −kp (g_i − c) − kd r_i` on every link.
`kp = 0.125`, `kd = 0.75`: `s² + 0.75 s + 0.125 = (s + 0.25)(s + 0.5)`, over-damped with
rational roots, so the L7 forms `p_j = r + ρ_j (g − c)` (`ρ = 0.25, 0.5`) decay
(`p_1' = −0.5 p_1`, `p_2' = −0.25 p_2`). Reference set point 30 m; the deployed acts on
a gap overstated by 1 m (40 ms-old V2V position at 25 m/s) and settles at 29 m.
Engagement (controller design): measured gaps within 4 m of 30, closing rates within
1 m/s (right `26..34`, left `25..33`). Fallback: per follower `k` an AEB mode BRAKEk below
20 m (`a_k = −4`, followers behind keep CACC; sinks). Domains `0 ≤ g_i ≤ 60` (radar
range), `|r_i| ≤ 10`. The interpretation "three vehicles" = three followers behind the
leader gives 6 D with (gap, closing rate) per link and no actuator-lag states (the
leader-plus-two-followers reading would be the same model with link 3 removed, 4 D; not
run).

**Rows: decoupling-form boxes, stratified gap bounds.** The row components are proven
one at a time, each later component using the earlier proven ones as a differential
cut (`strataDomIR`, `Trusted/Run.lean`); a gap row alone is not invariant for a
second-order loop, so every row is a box on a RELATIONAL decoupling form
`Q_j = Δr + ρ_j (Δg − s)` (Δ = L − R), which obeys `Q_j' = −ρ_{3−j} (Q_j − q*)` when both
loops have the same gains, followed by gap bounds that use the proven `Q` rows.

* `platoon3_linkloss` (left FOLLOW → LOST, latched; LOST = follower 1 radar-only with
  stand-off 35 m, the lead link's feed-forward being zero while the leader cruises):
  FOLLOW rows EXACT (`Q_j = 0` on every link: `Δg_i = −1`, `Δr_i = 0`); LOST rows: links
  2, 3 exact, link 1 `Q_j = Δr1 + ρ_j (e1 − 6) ∈ [−6 ρ_j, 0]` then `0 ≤ e1 ≤ 6` with `e1 =
  Δg1 + 1`, i.e. `g1_R − 1 ≤ g1_L ≤ g1_R + 5`. One step tighter (measured): `e1 ≤ 5.9`,
  `≤ 5.75` DECLINED; `e1 ≥ 0.25` DECLINED (handoff fails); `Q` box at `5.9 ρ_j` CERTIFIED
  but `--handoff` FOLLOW → LOST fails; without the `e1` rows DECLINED (BRAKE1 admissible
  as a LOST start).
* `platoon3_profiles` (reference CLOSE 28 / NORMAL 30 / FAR 32 m, NORMAL ↔ CLOSE / FAR):
  `Q_j = Δr_i + ρ_j e_i ∈ [−2 ρ_j, 2 ρ_j]`, then `|e_i| ≤ 2`, i.e. `g_R − 3 ≤ g_L ≤ g_R +
  1` whichever profile is selected (`[−2ρ_j, 2ρ_j]` is the tightest box containing the
  three equilibria `0, ±2ρ_j`). One step tighter: `Q` box at `1.9 ρ_j` DECLINED; `|e_i| ≤
  1.9` DECLINED.

Both claims are stated synchronous (`λ ∈ [1, 1]`: both sides run the same gains). With the
default grid `λ ∈ [1, 6]` `platoon3_profiles` CERTIFIES at λ = 1, but every counter-run and
every tighter-tolerance run ends in `ERROR [budget exceeded (query budget exceeded)]`
(≈ 17 s: the failing segments are re-tried at every point of the stretch grid) instead
of DECLINED, so no cell could be credited. (Pass 7, §17.4: with the default query
budget raised to 20 000 both files are on the grid.)

| file | λ, budget | cells (counter-runs) | Z3 (queries, total, max) |
|---|---|---|---|
| `platoon3_linkloss` | 1, 2 (FOLLOW and LOST) | M2; M4 (BRAKE1/2/3 pruned from FOLLOW by the derived floors `g_i ≥ 24`; NO_PRUNE DECLINED); M5 (rows differ, `--handoff` 3/3 unsat); M6, M6+, M6L (NO_CUT, NO_IMPLIED_CUT, NO_LINEAR_CUT DECLINE: the chain proves the non-connection; enabling) | 715, 2.19 s, 0.05 s (median 3 ms) |
| `platoon3_profiles` | 1, 2 | M2; M3 (NORMAL → CLOSE, FAR); M4 (nine edges pruned; NO_PRUNE DECLINED); M6, M6+, M6L (enabling, as above) | 754, 2.34 s, 0.06 s (median 3 ms) |

Widening: both CERTIFY with every bound widened at once; no load-bearing group.

What failed on the way (each run; the deciding trace line):

* One AEB mode with the disjunctive guard `g1 < 20 or g2 < 20 or g3 < 20`: `[prune] …
  []` and `[admissible] FOLLOW_L: [FOLLOW, BRAKE]` — DECLINED; replaced by one AEB mode
  per follower (guard `g_k < 20`), which prunes.
* LOST with the `Q` box only (no stratified `e1` rows) and the engagement box ±5 m:
  `[admissible] LOST_L: [FOLLOW, BRAKE]` (the box lets `g1_R = g1_L − Δg1` drop below
  20) — DECLINED; fixed by the `e1` rows and the ±4 m measured-gap engagement box.
* Link loss on the MIDDLE link (follower 2 loses follower 1's feed-forward), analysed
  and not run: link 2 is then forced by `a_1 = p_1 − 0.25 p_2`, which is resonant with the
  link-2 forms (same eigenvalues), and the only boxes that are invariant under that forcing
  bound the gap deviation by tens of metres (hand estimate ≈ ±40 m for a ±3 m box, ≈ ±90 m for the engagement box) — a
  vacuous claim. The lead-link loss keeps the per-link structure.

### 16.3 Task 3 — trim

`acc_spoof_modes` (M1 M2 M3 M4) and `acc_tune_modes` (M1 M2 M3 M4 M6) are DROPPED: each
is the CRUISE loop of the corresponding limp file against the same selectable reference,
and its cells are a strict subset of `acc_spoof_limp` (M1 M2 M3 M4 M5 M6) resp.
`acc_tune_limp` (M1 M2 M3 M4 M5 M6). The headers of `acc_spoof_limp`, `acc_tune_limp`
(which now define the spoofed / tuned CRUISE loop and the reference themselves),
`acc_spoof_lag` and `acc_tune_lag` no longer refer to the dropped files; §4.1 and the §6
table record the drop. The suite is exactly 44 after Tasks 1–2, so no further drop is
proposed as required; if one more 1-D file is wanted, the candidate is `quad_light_lag`
(exactly two mechanisms, M1 M2, kept by the user's pass-5 decision).

### 16.4 Task 4 — consolidation

**Suite loop** (a shell loop over every `benchmarks/suite_v2/*/input.txt`, counted, not
inferred; `RELCERT_IMPLIED_CUT=1`, default solver settings): **44 files, 44 CERTIFIED.**
The matrix run (`scripts/suite_v2_matrix.py --z3time`, §3, §8, §9 are its output)
agrees: 44 / 44 CERTIFIED; duplicate check and tolerance-only-variant check: none.

**Counter-runs of the new files** (matrix run; ms):

| file | plain | NO_PRUNE | NO_CUT | NO_IMPLIED_CUT | NO_LINEAR_CUT | `--handoff` | cells |
|---|---|---|---|---|---|---|---|
| `sat3w_detumble_weak` | CERTIFIED 9068 | **DECLINED** 8940 | **DECLINED** 2688 | CERTIFIED 10329 | CERTIFIED 9179 | vacuous (one left mode) | M2 M3 M4 M6 |
| `sat3w_detumble_phases` | CERTIFIED 11668 | **DECLINED** 1587 | **DECLINED** 2538 | CERTIFIED 12634 | CERTIFIED 11779 | 3/3 unsat, rows differ | M2 M4 M5 M6 |
| `platoon3_linkloss` | CERTIFIED 2254 | **DECLINED** 1147 | **DECLINED** 807 | **DECLINED** 984 | **DECLINED** 945 | 3/3 unsat, rows differ | M2 M4 M5 M6 M6+ M6L |
| `platoon3_profiles` | CERTIFIED 2363 | **DECLINED** 2393 | **DECLINED** 1637 | **DECLINED** 1932 | **DECLINED** 1942 | vacuous (one left mode) | M2 M3 M4 M6 M6+ M6L |

Branching (M3) is a used fork in the emitted cover: `sat3w_detumble_weak` `NOMINAL:joint(B=2)->[NOMINAL@1, NOMINAL@1, ECONOMY@1, SURVIVAL@1]`; `platoon3_profiles` from NORMAL to CLOSE and FAR (branch 2).

**Widening** (`scripts/domain_widening.py`, every new file): all four CERTIFY with every
evolve bound widened at once and have no load-bearing group (`sat3w_*`: `|w_i| ≤ 1`,
`|h_i| ≤ 2`; `platoon3_*`: `0 ≤ g_i ≤ 60`, `|r_i| ≤ 10` — stated physical limits that no
certificate needs). Nothing is classified "forcing". The four headers whose text changed
in Task 3 have unchanged models (§14.4 stands for them).

**Matrix before / after** (pass 5, 42 files → pass 6, 44 files):

| mechanism | pass 5 (42) | pass 6 (44) | change |
|---|---|---|---|
| M1 | 18 | 16 | −`acc_spoof_modes`, −`acc_tune_modes` |
| M2 | 29 | 31 | −2 dropped; +4 new |
| M3 | 11 | 11 | −2 dropped; +`sat3w_detumble_weak`, +`platoon3_profiles` |
| M4 | 15 | **17** | −2 dropped; +4 new |
| M5 | 10 | **12** | +`sat3w_detumble_phases`, +`platoon3_linkloss` |
| M6 | 25 | 28 | −`acc_tune_modes`; +4 new |
| M6+ | 9 | 11 | +`platoon3_linkloss`, +`platoon3_profiles` |
| M6L | 6 | 8 | +`platoon3_linkloss`, +`platoon3_profiles` |
| per-mode domains | 0 | 0 | |

No cell of any other file changed. Every non-kept file still exercises at least two of
M1–M6 non-vacuously.

**Dimension histogram** (files by the larger side's state dimension):

| dimension | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 12 | total |
|---|---|---|---|---|---|---|---|---|---|
| pass 5 | 11 | 8 | 4 | 4 | 0 | 4 | 4 | 7 | 42 |
| pass 6 | 9 | 8 | 4 | 4 | 0 | **8** | 4 | 7 | 44 |

**Files at ≥ 5 D that exercise branching (M3), pruning (M4) or mode-dependent rows (M5):**
before — `story1_attdist_rung_a_6to8` (8, M5), `story1_attdist_rung_b_12dof` (12, M5),
`story3_rollover_ladder_rung_b` (12, M5): none with M3 or M4. After — those three plus
`sat3w_detumble_weak` (6, M3 M4), `sat3w_detumble_phases` (6, M4 M5), `platoon3_linkloss`
(6, M4 M5), `platoon3_profiles` (6, M3 M4). The quadrant "≥ 6 D with branching or
pruning" now has four members (two polynomial, two linear).

**Timing** (pass-6 matrix run with `--z3time`; columns as §14.3): 44 / 44 CERTIFIED in 88.3 s
of tool time in total (Z3 87.7 s); 34 files under 1.6 s; the long ones are
`story1_attdist_rung_a_6to8` (21.1 s), `sat_detumble_weak` (12.8 s),
`sat3w_detumble_phases` (11.7 s), `sat3w_detumble_weak` (9.1 s), `sat_detumble_phases`
(6.7 s), `refinement_ladder_rover_rung3_6to8` (3.1 s). The 6-D linear string runs in
≈ 2.3 s with ≈ 750 light queries (≤ 60 ms each); the 6-D gyrostat in 9–12 s with 70–90
queries of which three or four take 0.8–3.3 s — the same few-but-heavy profile as the 4-D
rungs, at a similar cost.

| benchmark | dim L/R | verdict | tool ms (relcert's own) | wall s (process) | Z3 queries | Z3 ms (sum) | Z3 max ms | UNSAT queries by shape |
|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | 2/2 | CERTIFIED | 227 | 0.45 | 63 | 185 | 55 | A-or-static/L 2, A-or-static/R 1, B 7, B/R 1, C 1, other 1 |
| `acc_spoof_limp` | 1/1 | CERTIFIED | 280 | 0.53 | 145 | 286 | 51 | A-or-static/R 7, B 19, B/L 2, B/R 3, C 1, other 2 |
| `acc_tune_lag` | 2/2 | CERTIFIED | 92 | 0.3 | 39 | 86 | 18 | A-or-static/L 2, A-or-static/R 1, B 1, B/R 1, other 1 |
| `acc_tune_limp` | 1/1 | CERTIFIED | 300 | 0.49 | 175 | 305 | 20 | A-or-static/R 7, B 19, B/R 3, C 5, other 2 |
| `arm_plateau_crit` | 2/1 | CERTIFIED | 152 | 0.41 | 82 | 229 | 99 | A-or-static 6, A-or-static/- 16, A-or-static/L 3, B 4, B/L 1, B/R 3, C 2 |
| `arm_plateau_profiles` | 2/1 | CERTIFIED | 236 | 0.47 | 97 | 209 | 54 | A-or-static 7, A-or-static/- 20, A-or-static/L 4, B 6, B/L 1, B/R 4, C 2 |
| `arm_plateau_slow` | 2/1 | CERTIFIED | 207 | 0.44 | 81 | 200 | 65 | A-or-static 5, A-or-static/- 16, A-or-static/L 5, B 1, B/L 1, B/R 3, C 3, other 1 |
| `charger_fast_setpoints` | 1/1 | CERTIFIED | 214 | 0.37 | 106 | 196 | 48 | A-or-static 7, A-or-static/- 7, A-or-static/L 2, A-or-static/R 17, B 6, B/R 1, other 4 |
| `charger_fast_tapers` | 1/1 | CERTIFIED | 266 | 0.39 | 131 | 221 | 20 | A-or-static 8, A-or-static/- 7, A-or-static/L 2, A-or-static/R 25, B 7, B/R 1, other 4 |
| `match_multi_rate` | 2/2 | CERTIFIED | 324 | 0.46 | 151 | 313 | 46 | A-or-static 1, A-or-static/L 4, A-or-static/R 9, B 6, B/R 1, C 3, other 4 |
| `platoon3_linkloss` | 6/6 | CERTIFIED | 2254 | 2.39 | 715 | 2194 | 50 | A 41, A-or-static/L 24, A-or-static/R 15, B 1, B/R 3, C 42, other 6 |
| `platoon3_profiles` | 6/6 | CERTIFIED | 2363 | 2.53 | 754 | 2340 | 57 | A 9, A-or-static/L 12, A-or-static/R 45, B 43, B/R 9, C 43, other 3 |
| `platoon_delay_linkloss` | 1/1 | CERTIFIED | 311 | 0.45 | 142 | 292 | 47 | A-or-static/- 4, A-or-static/L 4, A-or-static/R 8, B 12, B/L 3, B/R 3, other 3 |
| `platoon_delay_profiles` | 1/1 | CERTIFIED | 238 | 0.39 | 131 | 300 | 52 | A-or-static/- 4, A-or-static/L 2, A-or-static/R 11, B 12, B/L 2, B/R 4, other 2 |
| `quad_light_airframe_20` | 1/1 | CERTIFIED | 220 | 0.4 | 90 | 216 | 47 | A-or-static 2, A-or-static/R 4, B 9, B/L 2, B/R 4, other 1 |
| `quad_light_lag` | 2/2 | CERTIFIED | 94 | 0.24 | 22 | 97 | 55 | B 1, B/L 1, B/R 2 |
| `quad_light_profiles` | 1/1 | CERTIFIED | 489 | 0.62 | 253 | 525 | 54 | A-or-static 2, A-or-static/R 6, B 34, B/L 1, B/R 10, other 1 |
| `refinement_ladder_rover_rung1_2to3` | 3/2 | CERTIFIED | 258 | 0.41 | 137 | 242 | 33 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `refinement_ladder_rover_rung2_3to6` | 6/6 | CERTIFIED | 791 | 0.99 | 329 | 740 | 50 | A 15, A/L 3, A/R 21, B 3, C 12, other 3 |
| `refinement_ladder_rover_rung2_6dof` | 4/4 | CERTIFIED | 234 | 0.42 | 106 | 222 | 38 | A 24, A-or-static 1, A-or-static/R 3, A/L 3 |
| `refinement_ladder_rover_rung2b_6dof` | 6/6 | CERTIFIED | 276 | 0.48 | 118 | 259 | 57 | A 24, A-or-static 1, A-or-static/R 3, A/L 3 |
| `refinement_ladder_rover_rung2c_6dof` | 6/6 | CERTIFIED | 1471 | 1.67 | 619 | 1454 | 55 | A 33, A/L 3, A/R 21, B 6, C 21, other 6 |
| `refinement_ladder_rover_rung3_6to8` | 8/8 | CERTIFIED | 3067 | 3.23 | 959 | 3048 | 32 | A 66, A/L 3, A/R 39, B 18, C 36, other 1 |
| `refinement_ladder_rover_rung4_8to12` | 12/12 | CERTIFIED | 1034 | 1.2 | 301 | 992 | 53 | A 6, A/L 3, A/R 39, B 9, C 9, other 1 |
| `rover3tier_rung12` | 3/3 | CERTIFIED | 220 | 0.37 | 91 | 221 | 51 | A 12, A-or-static 1, A-or-static/R 4, B 2, B/R 2 |
| `rover_dof_terrain_rung1` | 3/3 | CERTIFIED | 257 | 0.38 | 139 | 254 | 33 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung2` | 6/6 | CERTIFIED | 327 | 0.51 | 163 | 327 | 58 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung3` | 12/12 | CERTIFIED | 386 | 0.54 | 157 | 429 | 117 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung3_8d` | 8/8 | CERTIFIED | 347 | 0.54 | 169 | 330 | 30 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_patrol_refine` | 3/3 | CERTIFIED | 1627 | 1.8 | 797 | 1551 | 23 | A 32, A-or-static 10, A-or-static/L 11, A-or-static/R 36, B 44, other 1 |
| `rover_patrol_zones` | 2/2 | CERTIFIED | 437 | 0.63 | 278 | 429 | 44 | A-or-static 14, A-or-static/L 4, A-or-static/R 80, B 14, B/R 4, other 5 |
| `sat3w_detumble_phases` | 6/6 | CERTIFIED | 11668 | 11.88 | 71 | 11651 | 3271 | A 19, A/R 1, B 2, B/L 2, B/R 2, C 2, other 2 |
| `sat3w_detumble_weak` | 6/6 | CERTIFIED | 9068 | 9.28 | 88 | 8967 | 2956 | A 13, A/R 3, B 3, B/L 1, B/R 6, C 3, other 1 |
| `sat_detumble_nominal` | 4/4 | CERTIFIED | 1661 | 1.86 | 41 | 1681 | 784 | A 10, A/R 1, B/L 1, B/R 2, C 1, other 1 |
| `sat_detumble_phases` | 4/4 | CERTIFIED | 6694 | 6.89 | 68 | 6758 | 3114 | A 19, A/R 1, B 2, B/L 2, B/R 2, C 2, other 2 |
| `sat_detumble_weak` | 4/4 | CERTIFIED | 12790 | 12.99 | 88 | 12606 | 3227 | A 13, A/R 3, B 3, B/L 1, B/R 6, C 3, other 1 |
| `story1_attdist_rung_a_6to8` | 8/8 | CERTIFIED | 21122 | 21.32 | 192 | 20993 | 5102 | A/L 3, A/R 3, B 20, C 1 |
| `story1_attdist_rung_b_12dof` | 12/12 | CERTIFIED | 479 | 0.68 | 158 | 471 | 53 | A 18, A/L 3, A/R 3, B 2, C 1 |
| `story2_lateral_rung_a_8dof` | 8/8 | CERTIFIED | 1156 | 1.33 | 518 | 1164 | 61 | A 24, A/L 3, A/R 21, B 12, C 21, other 3 |
| `story2_lateral_rung_b_12dof` | 12/12 | CERTIFIED | 1530 | 1.73 | 610 | 1513 | 60 | A 24, A/L 3, A/R 21, B 21, C 21, other 3 |
| `story3_rollover_base_12dof` | 12/12 | CERTIFIED | 1308 | 1.48 | 466 | 1241 | 59 | A 78, A/L 3, A/R 39, B 42, C 6, other/L 1 |
| `story3_rollover_ladder_rung_a` | 12/12 | CERTIFIED | 908 | 1.07 | 320 | 1076 | 188 | A 42, A/L 3, A/R 39, B 6, C 6, other/L 1 |
| `story3_rollover_ladder_rung_b` | 12/12 | CERTIFIED | 751 | 0.94 | 212 | 695 | 21 | A-or-static/L 6, A/L 3, A/R 3, B 20, C 1 |
| `watertank` | 1/1 | CERTIFIED | 154 | 0.34 | 84 | 187 | 54 | A-or-static 3, A-or-static/R 6, B 6, B/L 3, B/R 3, other 3 |
| **total** | | | **88288** | | | **87695** | | |

### 16.5 Duplicates

The normalized-hash and tolerance-masked-hash checks of the matrix script report none
(the 6-D files differ from their 1-D / 4-D predecessors in the state vector and the
dynamics).

### 16.6 Open decisions (for the user)

(Pass 7 resolved the first two items, §17: the default limit is now 64 000 000, the
6-D rungs state the analytic tolerances, `sat3w_detumble_phases` is back on the 4-D
constants; the 4-D rungs keep 0.205 / 0.085 because their tangent queries exceed the
10 s per-query timeout.)

* **Z3 resource limit (L8).** The analytic tolerances certify with `RELCERT_Z3_RLIMIT=0`
  (4-D: 0.08 in 36.7 s and 0.2 in 44.9 s; 6-D: 0.09 in 12.5 s and 0.2 in 12.2 s; the 6-D
  phases rung with the 4-D constants `E ≤ 0.2`, `k_F = 0.3` certifies at 0.085 with
  `RELCERT_Z3_RLIMIT=16000000`). Options: keep `d* + 0.005` claims under the default limit
  (current), or adopt a larger limit for the suite runs (a run-setting change; every file
  would have to be re-run under it) and state the analytic tolerances.
* **`sat3w_detumble_phases` constants** (capture envelope 0.3, FINE gain 0.35) were chosen
  from a scan to fit the default limit; the 4-D rung's 0.2 / 0.3 need the larger limit.
* **"Three vehicles"** was read as three followers behind a leader (6 D, (gap, closing
  rate) per link, no lag states); a leader-plus-two-followers string would be 4 D.
* **Exact FOLLOW rows** in `platoon3_linkloss` (tolerance 0 up to the 1 m offset; the
  tightest certifiable, as `sat_detumble_nominal`).
* **New controller-design guards**: CACC engagement within 4 m (measured) of the set
  point and 1 m/s closing rate; the radar-only latch deferred to that box (with the
  leader cruising the lost feed-forward is zero, so holding the CACC law is physically
  the same loop); AEB floor 20 m per follower.

## 17. Pass 7 (2026-10-09): the Z3 work limit, analytic tolerances, stretch grids

User decisions of pass 6 (§16.6) implemented: raise the tool's Z3 work limit, state the
satellite claims at their analytic tolerances where that certifies, put the
three-follower string on the stretch grid, add the 6-D nominal rung. Two tool defaults
changed (§17.1, §17.4); nothing else in the tool, no Lean proof, pin, instance or
`suite_uniform` file. Every run `RELCERT_IMPLIED_CUT=1` (except the
`RELCERT_NO_IMPLIED_CUT=1` counter-run), Z3 4.15.1, the binary of `d2cb262`, the NEW
defaults, nothing else running unless a line says otherwise.

### 17.1 The resource limit: what it is, what it affects, the change

`Z3Session.check` (`RelCertifier/Trusted/Z3.lean`) sends, per query,
`(reset)`, `(set-option :timeout T)`, `(set-option :rlimit R)` (omitted when `R = 0`),
then the query script, `(check-sat)` and the sentinel echo. The query script itself is
built by the printer (`Trusted/Smt.lean`: `set-logic`, declarations, `assert`,
`check-sat`) and is what the verdict pin layer ties to the runner; the two `set-option`
lines are added by the session layer outside it. Checked:

* `rlimit` occurs in no file of the repository but `RelCertifier/Trusted/Z3.lean` (and
  this document; the two `sat3w_*` headers that quoted it in pass 6 are rewritten here);
  `set-option` occurs in no Lean file but `Trusted/Z3.lean`; no pin, query literal or
  coverage constant contains either.
* None of the 246 `suite_uniform` emissions (`--emit-cuts`, `--emit-cover`,
  `RELCERT_DEBUG=1 relcert`, 41 inputs each) contains `rlimit` or `set-option`.
* The one-shot process of `Verdicts/RunHandoff.z3Model` (documents a failing
  transition; never a verdict) sends no limit.

So the option affects exactly one thing: whether Z3 answers `unknown` on a query that
needs more work units than `R`. `unknown` is never a verdict (`probeUnsat` takes only a
definitive `unsat`; a route left `unknown` makes the run an ERROR). A wall-clock timeout
still yields ERROR: `RELCERT_Z3_TIMEOUT=500` on `sat3w_detumble_weak` gives `ERROR
[inconclusive Z3 verdict on a candidate route]`, and `RELCERT_Z3_RLIMIT=8000000`
reproduces the pass-6 ERROR at the analytic tolerance.

**The change** (commit `ca3503a`): the default `rlimit` 8 000 000 → **64 000 000**, in
`Z3Config` and in `Z3Config.discover`; the `RELCERT_Z3_RLIMIT` override is kept, `0`
still disables the limit, `RELCERT_Z3_TIMEOUT` (10 s) stays the wall-clock safety net.
Why 64 M and not 0: measured with `z3 -st` on the logged queries (no limit, no timeout),
the heaviest 6-D tangent queries need 29.3 M (`sat3w_detumble_weak`) and 33.1 M
(`sat3w_detumble_phases`, both the installed and the pass-6 constants) work units — 64 M
is about twice that and keeps the bound deterministic. The 4-D rungs' tangent queries
need 63.5 M / 71.2 M (`sat_detumble_weak` at 0.2) and 59.7 M / 61.6 M
(`sat_detumble_phases` at 0.08) and 15–17 s each in plain z3: no rlimit value helps
them under the 10 s timeout (with `RELCERT_Z3_RLIMIT=0` and the default timeout both
still end in ERROR), so the limit was not raised further.

**Regression** (the §12 procedure, binaries of `86e25c9` = before and `ca3503a` = after):

* `--emit-cuts`, `--emit-cover` and `RELCERT_DEBUG=1 relcert` for all 41 `suite_uniform`
  inputs (stdout with the benchmark-name prefix and the millisecond field masked, the
  complete stderr): **no difference in any of the 246 files**; 40 CERTIFIED,
  1 DECLINED (`shield_unreachable`).
* `lake build`: exit 0, `Build completed successfully (8977 jobs)` (14 modules
  downstream of `Trusted/Z3.lean` re-elaborated: `Trusted/OracleAPI`, `ViabilityEmit`,
  `Proofs/Flow/FaceBridge`, `Instances/WatertankViability`, `Instances/ModalBattery`,
  `Verdicts/Run`, `RunCut`, `RunNonConn`, `RunHandoff`, `RunModal`, `NonConnPins`,
  `ModalPinTable`, `ModalTablePins`, `ModalCodePins`, `CoveragePins`, `Watertank`; no
  proof or pin failed); `lake build relcert relcert-test`: `Build completed successfully
  (17695 jobs)`. No file under `Instances/`, `Proofs/`, `Verdicts/` changed.
* `relcert --check-quick benchmarks/suite_uniform/*/input.txt`: `[suite] 40 certified,
  1 declined, 0 error(s) — matches the declared suite`; `[coverage] watertank: 6/6`,
  `cut probes: 97/97`, `modal: 504/504`, `handoff: 191/191`, `non-connection: 2/2`,
  `pruned edges: 1/1`; `suite: PASS`, `verdicts: PASS`, `QUICK CHECKS PASSED`, exit 0.
* `BENCH_PATHS=<manifest of the 41> relcert-test`: `ALL PASS` (bare), exit 0.

**Wall-clock margin.** In the persistent session the heaviest 6-D queries take 6.5 s
(`sat3w_detumble_weak`) and 8.3 s (`sat3w_detumble_phases`) — about twice their
plain-z3 time — against the 10 s per-query timeout. On a slower or loaded machine those
two files can come back ERROR (never a verdict); every number here was taken with
nothing else running.

(Correction to §16.1 / §16.6: the 4-D rungs did NOT certify at their analytic
tolerances with `RELCERT_Z3_RLIMIT=0` alone in this pass — both end in ERROR under the
10 s timeout; they certify only with the timeout raised, §17.2.)

### 17.2 Task 2 — the satellite claims at the analytic tolerances

| file | claim before (pass 6) | claim now | analytic `d*` | one step tighter | plain run (tool ms / wall s) | Z3 (queries / total / max) |
|---|---|---|---|---|---|---|
| `sat3w_detumble_weak` | 0.205 | **0.2** | 0.2 | 0.195 **DECLINED** (5.9 s) | CERTIFIED 11982 / 12.19 | 89 / 12.1 s / 6.5 s |
| `sat3w_detumble_phases` | FINE 0.095 (envelope 0.3, gain 0.35) | **FINE 0.08** (envelope **0.2**, gain **0.3**: the 4-D constants restored) | 0.08 | 0.075 **DECLINED** (3.8 s) | CERTIFIED 12173 / 12.44 | 69 / 12.3 s / 8.3 s |
| `sat_detumble_weak` | 0.205 | 0.205 (kept) | 0.2 | 0.2 ERROR (44.8 s, 40 s time budget; two tangent queries `unknown` at the 10 s timeout); 0.195 DECLINED (11.5 s); 0.15 DECLINED | CERTIFIED 12640 / 12.86 | 88 / 12.6 s / 3.2 s |
| `sat_detumble_phases` | FINE 0.085 | FINE 0.085 (kept) | 0.08 | 0.08 ERROR (46.1 s, as above); 0.075 DECLINED (5.6 s); 0.07 DECLINED | CERTIFIED 6973 / 7.19 | 68 / 6.9 s / 3.1 s |

(Plain-run columns: the pass-7 matrix run; one-step-tighter times: separate runs.) The
4-D analytic tolerances CERTIFY only with the per-query timeout raised, which is not a
default change made here: `sat_detumble_phases` at 0.08 with `RELCERT_Z3_TIMEOUT=60000
RELCERT_TIME_BUDGET_MS=600000` in 36.7 s; `sat_detumble_weak` at 0.2 additionally needs a
resource limit above 71.2 M (`RELCERT_Z3_RLIMIT=0` or `128000000`: 44.7 s; with 64 M and
the 60 s timeout it is still `unknown`, 84.5 s).

Counter-runs (pass-7 matrix): no cell lost.

| file | NO_PRUNE | NO_CUT | NO_IMPLIED_CUT | NO_LINEAR_CUT | `--handoff` | cells |
|---|---|---|---|---|---|---|
| `sat3w_detumble_weak` | **DECLINED** 12504 | **DECLINED** 2678 | CERTIFIED 12854 | CERTIFIED 12356 | vacuous | M2 M3 M4 M6 |
| `sat3w_detumble_phases` | **DECLINED** 1625 | **DECLINED** 2536 | CERTIFIED 13431 | CERTIFIED 12303 | 3/3 unsat, rows differ | M2 M4 M5 M6 |
| `sat_detumble_weak` | **DECLINED** 12668 | **DECLINED** 10479 | CERTIFIED 16225 | CERTIFIED 12436 | vacuous | M2 M3 M4 M6 |
| `sat_detumble_phases` | **DECLINED** 1617 | **DECLINED** 6827 | CERTIFIED 22643 | CERTIFIED 6798 | 3/3 unsat, rows differ | M2 M4 M5 M6 |

**`sat_detumble_nominal`'s λ.** With the stretch grid `λ ∈ [1, 6]` the plain run
CERTIFIES at λ = 1 (1.7 s; no M1), but the `RELCERT_NO_PRUNE=1` counter-run ends in
`ERROR [budget exceeded (time budget exceeded)]` after 44.1 s: with SAFE owed it tries
every grid point; 203 queries, 168 of them `sat`, none `unknown` (44.3 s of Z3 time) —
the binding bound is the tool's 40 s run time budget (`RELCERT_TIME_BUDGET_MS`), not the
resource limit. With `RELCERT_TIME_BUDGET_MS=900000` it DECLINES in 89.7 s. The claim
stays synchronous (`λ ∈ [1, 1]`); the header records this.

Headers: the pass-6 "solver-budget accommodation" remarks are gone; each header states
the tolerance, the measured one-step-tighter verdict and (4-D) the measured reason the
analytic value is not stated.

### 17.3 Task 3 — `sat3w_detumble_nominal` (6 D)

The three-wheel gyrostat of §16.1 at `k = 0.5` on both sides against the decoupled
design model with SAFE; exact claim `E_L ≤ E_R ∧ E_R ≤ E_L` (the 4-D nominal's claim; no
tighter claim exists). Stretch grid `λ ∈ [1, 6]` (every counter-run is clean on it, unlike
the 4-D rung): plain CERTIFIED 1629 ms at λ = 1, budget 2 (M2; no M1); `RELCERT_NO_PRUNE=1`
**DECLINED** (14.9 s; M4: DETUMBLE → SAFE pruned); NO_CUT, NO_IMPLIED_CUT, NO_LINEAR_CUT
CERTIFIED (the envelope cut is kept but not needed: M6 vacuous); `--handoff` vacuous (one
left mode). Cells **M2 M4**, as the 4-D nominal. Z3: 41 queries, 1.6 s, max 0.8 s.
Widening: all-widened CERTIFIED, no load-bearing group.

### 17.4 Task 4 — the three-follower string on the stretch grid

Both files were stated at `λ ∈ [1, 1]` in pass 6 because the grid's counter-runs ended in
ERROR. Measured with the grid `λ ∈ [1, 6]`:

| file | run | old budget (5 000) | `RELCERT_MAX_QUERIES=50000` | queries used |
|---|---|---|---|---|
| `platoon3_linkloss` | plain / NO_PRUNE / NO_CUT / NO_LINEAR_CUT / NO_IMPLIED_CUT | CERTIFIED 2.2 s / DECLINED 12.0 s / DECLINED 8.3 s / DECLINED 8.1 s / DECLINED 7.9 s | (not needed) | 715 / 3 799 / 3 228 / – / – |
| `platoon3_profiles` | plain | CERTIFIED 2.2 s | CERTIFIED 2.4 s | 754 |
| | NO_PRUNE | ERROR `[budget exceeded (query budget exceeded)]` 16.6 s | DECLINED 28.2 s | 8 824 |
| | NO_CUT | ERROR (query budget) 11.7 s | DECLINED 17.1 s | 7 194 |
| | NO_LINEAR_CUT | ERROR (query budget) 11.7 s | DECLINED 17.6 s | 7 296 |
| | NO_IMPLIED_CUT | ERROR (query budget) 12.0 s | DECLINED 17.6 s | 7 290 |

(`RELCERT_MAX_QUERIES=200000 RELCERT_TIME_BUDGET_MS=900000` gives the same verdicts and
times for NO_PRUNE and NO_CUT: the runs finish on their own.) All counter-runs come back clean in under 30 s, so
the grid is restored on both files, and — since a suite run uses the defaults — the
default query budget is raised **5 000 → 20 000** (`RelCertifier/Trusted/OracleAPI.lean`,
`certify` and the `--emit-cover` path; commit `d2cb262`; 2.3× the largest count
measured). The budget only throws (`query budget exceeded` → ERROR), so the change cannot
alter any CERTIFIED or DECLINED result. Regression repeated exactly as §17.1: `lake
build` exit 0 (8977 jobs), `lake build relcert relcert-test` (17695 jobs); the 246
`suite_uniform` emissions of the new binary byte-identical to those of `86e25c9`;
`--check-quick`: `40 certified, 1 declined, 0 error(s)`, the six coverage lines as in
§17.1, `QUICK CHECKS PASSED`; `relcert-test`: `ALL PASS`.

Pass-7 matrix (new defaults): `platoon3_linkloss` NO_PRUNE DECLINED 11487, NO_CUT 7679,
NO_IMPLIED_CUT 7936, NO_LINEAR_CUT 7964; `platoon3_profiles` NO_PRUNE DECLINED 28226,
NO_CUT 16948, NO_IMPLIED_CUT 17219, NO_LINEAR_CUT 17208 (ms). Cells unchanged (M2 M4 M5
M6 M6+ M6L; M2 M3 M4 M6 M6+ M6L); both plain runs find the cover at λ = 1 (no M1: the
same gains on both sides). The `NO_PRUNE` run of `platoon3_profiles` (28 s) is the
closest run of the suite to the 40 s time budget.

One step tighter, re-measured on the grid (all DECLINED): `platoon3_linkloss` `e1 ≤ 5.9`
(22.0 s), `e1 ≥ 0.25` (22.1 s); the `Q` box at `5.9 ρ_j` CERTIFIES but `--handoff`
FOLLOW → LOST fails (2/3), as at λ = 1; `platoon3_profiles` `Q` box at `1.9 ρ_j`
(27.9 s), `|e_i| ≤ 1.9` (28.9 s).

### 17.5 Consolidation

**Suite loop** (shell loop over every `benchmarks/suite_v2/*/input.txt`, counted: 45
files): **45 CERTIFIED**. The matrix run (`scripts/suite_v2_matrix.py --z3time`, §3, §8,
§9 are its output) agrees: 45 / 45 CERTIFIED; duplicate check and tolerance-only-variant
check: none. For the 44 pass-6 files every plain verdict, every counter-run verdict
(NO_PRUNE, NO_CUT, NO_IMPLIED_CUT, NO_LINEAR_CUT), every `--handoff` result and every
cell is the same as in pass 6 (compared field by field on the two matrix JSONs).

**Widening** (`scripts/domain_widening.py`): `sat3w_detumble_nominal`,
`sat3w_detumble_weak`, `sat3w_detumble_phases` (`--jobs 2`), `platoon3_linkloss`,
`platoon3_profiles` (`--jobs 6`) and the three 4-D rungs whose headers changed
(`sat_detumble_*`, `--jobs 2`): all CERTIFY with every evolve bound widened at once and
have no load-bearing group.

**Matrix before / after** (pass 6, 44 files → pass 7, 45 files):

| mechanism | pass 6 (44) | pass 7 (45) | change |
|---|---|---|---|
| M1 | 16 | 16 | |
| M2 | 31 | **32** | +`sat3w_detumble_nominal` |
| M3 | 11 | 11 | |
| M4 | 17 | **18** | +`sat3w_detumble_nominal` |
| M5 | 12 | 12 | |
| M6 | 28 | 28 | |
| M6+ | 11 | 11 | |
| M6L | 8 | 8 | |
| per-mode domains | 0 | 0 | |

No cell of any other file changed (the restated tolerances and the grids keep every
cell).

**Dimension histogram** (files by the larger side's state dimension):

| dimension | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 12 | total |
|---|---|---|---|---|---|---|---|---|---|
| pass 6 | 9 | 8 | 4 | 4 | 0 | 8 | 4 | 7 | 44 |
| pass 7 | 9 | 8 | 4 | 4 | 0 | **9** | 4 | 7 | 45 |

### 17.6 Timing (pass-7 matrix run, new defaults)

45 / 45 CERTIFIED in 92.8 s of tool time in total (Z3 93.5 s); 34 files under 1.6 s; the
long ones are `story1_attdist_rung_a_6to8` (20.6 s), `sat_detumble_weak` (12.6 s),
`sat3w_detumble_phases` (12.2 s), `sat3w_detumble_weak` (12.0 s), `sat_detumble_phases`
(7.0 s), `refinement_ladder_rover_rung3_6to8` (3.1 s). Columns as §14.3.

| benchmark | dim L/R | verdict | tool ms (relcert's own) | wall s (process) | Z3 queries | Z3 ms (sum) | Z3 max ms | UNSAT queries by shape |
|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | 2/2 | CERTIFIED | 228 | 0.41 | 63 | 229 | 99 | A-or-static/L 2, A-or-static/R 1, B 7, B/R 1, C 1, other 1 |
| `acc_spoof_limp` | 1/1 | CERTIFIED | 256 | 0.45 | 145 | 308 | 71 | A-or-static/R 7, B 19, B/L 2, B/R 3, C 1, other 2 |
| `acc_tune_lag` | 2/2 | CERTIFIED | 143 | 0.39 | 39 | 135 | 58 | A-or-static/L 2, A-or-static/R 1, B 1, B/R 1, other 1 |
| `acc_tune_limp` | 1/1 | CERTIFIED | 355 | 0.58 | 175 | 370 | 78 | A-or-static/R 7, B 19, B/R 3, C 5, other 2 |
| `arm_plateau_crit` | 2/1 | CERTIFIED | 228 | 0.45 | 82 | 230 | 99 | A-or-static 6, A-or-static/- 16, A-or-static/L 3, B 4, B/L 1, B/R 3, C 2 |
| `arm_plateau_profiles` | 2/1 | CERTIFIED | 227 | 0.39 | 97 | 243 | 84 | A-or-static 7, A-or-static/- 20, A-or-static/L 4, B 6, B/L 1, B/R 4, C 2 |
| `arm_plateau_slow` | 2/1 | CERTIFIED | 211 | 0.47 | 81 | 320 | 183 | A-or-static 5, A-or-static/- 16, A-or-static/L 5, B 1, B/L 1, B/R 3, C 3, other 1 |
| `charger_fast_setpoints` | 1/1 | CERTIFIED | 260 | 0.52 | 106 | 252 | 63 | A-or-static 7, A-or-static/- 7, A-or-static/L 2, A-or-static/R 17, B 6, B/R 1, other 4 |
| `charger_fast_tapers` | 1/1 | CERTIFIED | 210 | 0.36 | 131 | 287 | 95 | A-or-static 8, A-or-static/- 7, A-or-static/L 2, A-or-static/R 25, B 7, B/R 1, other 4 |
| `match_multi_rate` | 2/2 | CERTIFIED | 368 | 0.55 | 151 | 320 | 65 | A-or-static 1, A-or-static/L 4, A-or-static/R 9, B 6, B/R 1, C 3, other 4 |
| `platoon3_linkloss` | 6/6 | CERTIFIED | 2156 | 2.41 | 715 | 2129 | 95 | A 41, A-or-static/L 24, A-or-static/R 15, B 1, B/R 3, C 42, other 6 |
| `platoon3_profiles` | 6/6 | CERTIFIED | 2271 | 2.53 | 754 | 2224 | 86 | A 9, A-or-static/L 12, A-or-static/R 45, B 43, B/R 9, C 43, other 3 |
| `platoon_delay_linkloss` | 1/1 | CERTIFIED | 317 | 0.51 | 142 | 280 | 52 | A-or-static/- 4, A-or-static/L 4, A-or-static/R 8, B 12, B/L 3, B/R 3, other 3 |
| `platoon_delay_profiles` | 1/1 | CERTIFIED | 286 | 0.46 | 131 | 301 | 93 | A-or-static/- 4, A-or-static/L 2, A-or-static/R 11, B 12, B/L 2, B/R 4, other 2 |
| `quad_light_airframe_20` | 1/1 | CERTIFIED | 234 | 0.49 | 90 | 224 | 65 | A-or-static 2, A-or-static/R 4, B 9, B/L 2, B/R 4, other 1 |
| `quad_light_lag` | 2/2 | CERTIFIED | 115 | 0.36 | 22 | 142 | 92 | B 1, B/L 1, B/R 2 |
| `quad_light_profiles` | 1/1 | CERTIFIED | 534 | 0.79 | 253 | 531 | 90 | A-or-static 2, A-or-static/R 6, B 34, B/L 1, B/R 10, other 1 |
| `refinement_ladder_rover_rung1_2to3` | 3/2 | CERTIFIED | 304 | 0.55 | 137 | 292 | 82 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `refinement_ladder_rover_rung2_3to6` | 6/6 | CERTIFIED | 755 | 1.01 | 329 | 686 | 33 | A 15, A/L 3, A/R 21, B 3, C 12, other 3 |
| `refinement_ladder_rover_rung2_6dof` | 4/4 | CERTIFIED | 285 | 0.53 | 106 | 265 | 95 | A 24, A-or-static 1, A-or-static/R 3, A/L 3 |
| `refinement_ladder_rover_rung2b_6dof` | 6/6 | CERTIFIED | 307 | 0.53 | 118 | 1293 | 1081 | A 24, A-or-static 1, A-or-static/R 3, A/L 3 |
| `refinement_ladder_rover_rung2c_6dof` | 6/6 | CERTIFIED | 1413 | 1.67 | 619 | 1364 | 67 | A 33, A/L 3, A/R 21, B 6, C 21, other 6 |
| `refinement_ladder_rover_rung3_6to8` | 8/8 | CERTIFIED | 3104 | 3.35 | 959 | 3062 | 100 | A 66, A/L 3, A/R 39, B 18, C 36, other 1 |
| `refinement_ladder_rover_rung4_8to12` | 12/12 | CERTIFIED | 972 | 1.2 | 301 | 946 | 31 | A 6, A/L 3, A/R 39, B 9, C 9, other 1 |
| `rover3tier_rung12` | 3/3 | CERTIFIED | 225 | 0.48 | 91 | 263 | 85 | A 12, A-or-static 1, A-or-static/R 4, B 2, B/R 2 |
| `rover_dof_terrain_rung1` | 3/3 | CERTIFIED | 241 | 0.49 | 139 | 240 | 29 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung2` | 6/6 | CERTIFIED | 363 | 0.61 | 163 | 318 | 47 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung3` | 12/12 | CERTIFIED | 349 | 0.56 | 157 | 341 | 49 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_dof_terrain_rung3_8d` | 8/8 | CERTIFIED | 390 | 0.64 | 169 | 362 | 70 | A 6, A-or-static/R 39, A/L 3, B 3, C 3, other 1 |
| `rover_patrol_refine` | 3/3 | CERTIFIED | 1640 | 1.86 | 797 | 1642 | 99 | A 32, A-or-static 10, A-or-static/L 11, A-or-static/R 36, B 44, other 1 |
| `rover_patrol_zones` | 2/2 | CERTIFIED | 424 | 0.61 | 278 | 486 | 98 | A-or-static 14, A-or-static/L 4, A-or-static/R 80, B 14, B/R 4, other 5 |
| `sat3w_detumble_nominal` | 6/6 | CERTIFIED | 1629 | 1.88 | 41 | 1577 | 777 | A 10, A/R 1, B/L 1, B/R 2, C 1, other 1 |
| `sat3w_detumble_phases` | 6/6 | CERTIFIED | 12173 | 12.44 | 69 | 12315 | 8280 | A 19, A/R 1, B 1, B/L 2, B/R 2, C 3, other 2 |
| `sat3w_detumble_weak` | 6/6 | CERTIFIED | 11982 | 12.19 | 89 | 12115 | 6514 | A 13, A/R 3, B 2, B/L 1, B/R 6, C 4, other 1 |
| `sat_detumble_nominal` | 4/4 | CERTIFIED | 1707 | 1.94 | 41 | 1714 | 777 | A 10, A/R 1, B/L 1, B/R 2, C 1, other 1 |
| `sat_detumble_phases` | 4/4 | CERTIFIED | 6973 | 7.19 | 68 | 6903 | 3115 | A 19, A/R 1, B 2, B/L 2, B/R 2, C 2, other 2 |
| `sat_detumble_weak` | 4/4 | CERTIFIED | 12640 | 12.86 | 88 | 12642 | 3201 | A 13, A/R 3, B 3, B/L 1, B/R 6, C 3, other 1 |
| `story1_attdist_rung_a_6to8` | 8/8 | CERTIFIED | 20577 | 20.81 | 192 | 20224 | 4913 | A/L 3, A/R 3, B 20, C 1 |
| `story1_attdist_rung_b_12dof` | 12/12 | CERTIFIED | 495 | 0.73 | 158 | 419 | 27 | A 18, A/L 3, A/R 3, B 2, C 1 |
| `story2_lateral_rung_a_8dof` | 8/8 | CERTIFIED | 1127 | 1.37 | 518 | 1122 | 94 | A 24, A/L 3, A/R 21, B 12, C 21, other 3 |
| `story2_lateral_rung_b_12dof` | 12/12 | CERTIFIED | 1401 | 1.59 | 610 | 1423 | 82 | A 24, A/L 3, A/R 21, B 21, C 21, other 3 |
| `story3_rollover_base_12dof` | 12/12 | CERTIFIED | 1214 | 1.46 | 466 | 1177 | 72 | A 78, A/L 3, A/R 39, B 42, C 6, other/L 1 |
| `story3_rollover_ladder_rung_a` | 12/12 | CERTIFIED | 852 | 1.1 | 320 | 864 | 85 | A 42, A/L 3, A/R 39, B 6, C 6, other/L 1 |
| `story3_rollover_ladder_rung_b` | 12/12 | CERTIFIED | 675 | 0.82 | 212 | 711 | 81 | A-or-static/L 6, A/L 3, A/R 3, B 20, C 1 |
| `watertank` | 1/1 | CERTIFIED | 142 | 0.29 | 84 | 216 | 84 | A-or-static 3, A-or-static/R 6, B 6, B/L 3, B/R 3, other 3 |
| **total** | | | **92758** | | | **93507** | | |


## 18. Pass 8 (2026-10-09): the redesigned watertank; the static reposition removed

Two changes. (1) `watertank` is redesigned as the paper's running example (commit
`bc5357d`, `benchmarks/suite_v2/watertank/input.txt`; the header's attack wording aligned
with the paper in this pass). (2) The certifier's **static reposition** is removed from the
tool, the verified checker and every proof (user decision, 2026-10-09;
`docs/COVER-AUDIT.md`, note of that date). Every number below: Z3 4.15.1, the `relcert`
binary built from this pass's tree, `RELCERT_IMPLIED_CUT=1` (except the
`RELCERT_NO_IMPLIED_CUT=1` counter-run), default solver settings (§10).

### 18.1 The redesigned `watertank`

A tank of capacity 25 dm; every mode a proportional pump `x' = k (c − x)`, `k = 0.3`.
Nominal (right, 5 modes): `PumpOff` (`x < 2`, a latched dry-run interlock, `x' = 0`),
`Low` (`2 ≤ x < 10`, toward 12.5), `Mid` in two pump profiles chosen on entry, `MidEco`
(gain 0.15) and `MidBoost` (gain 0.3), both toward 17 on `10 ≤ x < 17`, and `High`
(`x ≥ 17`, toward 17). Deployed (left, 3 modes): the level sensor reads 3 dm low, so every
threshold and set point is 3 dm higher in true level (`Low` `5 ≤ x < 13` toward 15.5,
`Mid` `13 ≤ x < 20` toward 20, `High` `x ≥ 20` toward 20), and the actuation attack makes
the pump aggressive: it doubles the low-fill gain to 0.6 and locks mid-fill to the boost
profile; levels whose reading is below the interlock threshold (`x_L < 5`) are outside the
model. Claim: `|x_L − x_R| ≤ 3` in every left mode (two rows, identical across modes);
evolve domain `0 ≤ x ≤ 25` in every mode on both sides; `εL = εR = 1`, λ grid `[1, 6]`.

Measured (the matrix run of §18.4 and separate runs):

* **CERTIFIED by joint segments only.** The replayed cover derivation of every left mode
  consists of base and joint steps; no reposition of either kind is on any path
  (`kinds ['base', 'joint']` for `Low_L` and `Mid_L`, `['base']` for `High_L`,
  `right-only False` everywhere, §9).
* **λ and budget.** `Low_L` and `Mid_L` certify at **λ = 2 with budget 2** (two right
  segments per left window); `High_L` at λ = 1, budget 1. `RELCERT_DEBUG=1` segment rows:
  for `Low_L` the nominal `Low` fails at λ = 1, 5/4, 3/2, 7/4 and passes first at λ = 2
  (the speed ratio of the tampered pump, gain 0.6 against 0.3).
* **Branching (M3).** A joint step from `Low` retains both `MidEco` and `MidBoost`, and
  from `MidEco`/`MidBoost`/`High` the other profiles; both profiles cover (branch = 2 in
  `Low_L` and `Mid_L`). For the deployed `Mid` the per-λ rows show **`MidEco` passing only
  at λ = 2** (fail at 1, 5/4, 3/2, 7/4) and **`MidBoost` passing at λ = 1** and every grid
  point after it: the full-gain deployed `Mid` against the half-gain `MidEco` needs the
  stretch, against `MidBoost` it does not.
* **Pruning (M4).** `[prune] watertank: [Low->PumpOff]`: the nominal `Low` flow from its
  entry `x ≥ 2` never reaches `x < 2`. `RELCERT_NO_PRUNE=1`: **DECLINED** (the `Low_L`
  segment against `PumpOff` fails at every λ).
* **Cuts (M6, M6+).** The kept atoms are the set points: deployed `Low` `x ≤ 15.5`
  (implied contraction, O1 rational, O2 shape), deployed `Mid` `x ≤ 20` (closure of the
  strict guard cap, shape), nominal `Low` `x ≤ 12.5` (implied), `MidEco`/`MidBoost`
  `x ≤ 17` (closures), `PumpOff` `x ≤ 2` (closure, frozen). `RELCERT_NO_CUT=1`
  **DECLINED**, `RELCERT_NO_IMPLIED_CUT=1` **DECLINED**, `RELCERT_NO_LINEAR_CUT=1`
  CERTIFIED (no linear-form atom is kept). Cells: **M1 M2 M3 M4 M6 M6+** (the old
  watertank exercised none non-vacuously).
* **Tolerance 3 is tight.** With both rows at 2.9 (`x[l] <= x[r] + 2.9 and x[r] <= x[l] +
  2.9` in every mode, nothing else changed): **DECLINED**.
* **Domains.** `scripts/domain_widening.py` on the file: base CERTIFIED, all-widened
  CERTIFIED, no load-bearing evolve bound. Widened by hand to `0 ≤ x ≤ 60` in every mode:
  CERTIFIED; to `−60 ≤ x ≤ 60`: CERTIFIED.
* Handoff: 6/6 unsat, vacuous (identical rows). Duplicate check: none (normalized md5
  `094c7ee69d35`).

### 18.2 The static reposition: what it was, why it is removed

The tool's cover had two right-only moves besides the joint step. The **dynamic**
reposition (`checkDynRepo`, flags `dynPre`/`dynPost`, `Covered.stepRepositionDynPre/Post`):
the right system flows alone, under its own field, for a full interval while the left is
held, and the invariant is certified along that flow (route A, whole domain); at its end
the cover demands that every declared, unpruned successor covers. This is the paper's
right-only segment, and it stays. The **static** reposition (`repoRegions`/`regionUnsat`,
flags `repoPre`/`repoPost`, `Covered.stepRepositionPre/Post`): a switch of the right system
into a declared successor in **zero time**, at the current state, chosen by the witness,
whose only obligation was that the invariant holds in the source mode's region
(`guardL ∧ guardR ∧ evolve ⟹ φ_inv`, post-j without `guardL`). Nothing checked that the
**successor's guard holds at the switch state**. For the paper's guarded nominal model a
guarded automaton cannot make that switch where the successor's guard is false, so a
certificate built on it can describe a response the modeled system does not have. The
demonic-successor argument of the 2026-07-19 audit note covers the switches the certificate
makes after a flow (joint step, dynamic reposition), not an ∃-chosen instantaneous switch.
The certificate now makes no zero-duration switch.

Removed: `RMode.region/repoPreOK/regionPost/repoPostOK`, `CoverCert(M/MC)`'s
`repoPresPre/Post` fields, the `Covered` and `RightReach(G)` constructors and every proof
case on them, `reposition_step_pres` and the region-invariant discharge lemmas, the tool's
`repoRegions`/`regionUnsat`/`repoMap` and its `[repo-pre]`/`[repo-post]` debug output
(`RELCERT_DEBUG=1` now prints `[repo-dyn-pre] … [repo-dyn-post]`). **Emitted literal:
the two static flags are DROPPED** from the emitted cover rows: `ModeFlagsE` is
`⟨name, jointOK, dynPre, dynPost⟩` (four fields, was six), every `Instances/BenchCovers*`
literal was regenerated in that form, and `scripts/suite_v2_matrix.py` parses it (the flag
strings in §9 are now three characters, `j`/`d`/`d`).

### 18.3 Casualties

* **`suite_uniform`: six benchmarks declined after static-reposition removal** —
  `arm_chain_rung1`, `arm_chain_rung2`, `arm_fidelity_low`, `robot_braking`,
  `rover3tier_M1`, `watertank` (each needed a static step on its cover path). Their input
  files are kept unchanged; their modal theorems, throughout instances, emitted covers,
  cover replays and verdict packs left the battery. Declared tally (`Coverage.expectedSuite`)
  40 certified / 1 declined → **34 / 7**; declared coverage `watertank` 6 → (phase removed),
  `modal` 504 → **486**, `handoff` 191 → **163**; `cut probes` 97, `non-connection` 2,
  `pruned edges` 1 unchanged. `ModalBattery` 52 → **46** theorems.
* Five more `suite_uniform` benchmarks carried static flags in their emitted covers
  (`arm_chain_rung3`, `arm_fidelity_mid`, `attitude_rate`,
  `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`) and still
  certify with the regenerated cover.
* **`suite_v2`:** only the old `watertank` (pass 1–7; identical up to comments to
  `suite_uniform/watertank`) needs it: its file from `3494c49` is DECLINED by this pass's
  binary. One more file had static steps on its derivation, `charger_fast_tapers`
  (`BULK_L`: `ABSORB_SLOW`/`ABSORB_FAST` → `FULL`); the same derivation is now found with
  dynamic repositions in their place, at the same λ = 1, budget 2 and cells. Every other
  §9 derivation is unchanged.

### 18.4 Regression evidence

* `RELCERT_IMPLIED_CUT=1 relcert benchmarks/suite_v2/*/input.txt` over all 45 inputs:
  **45 CERTIFIED**, 0 DECLINED, `errors=0`.
* `scripts/suite_v2_matrix.py --z3time`: 45 / 45 CERTIFIED; §3, §8, §9 regenerated from it.
  Totals before (pass 7) → after: M1 16 → **17**, M2 32 → **33**, M3 11 → **12**, M4 18 →
  **19**, M5 12, M6 28 → **29**, M6+ 11 → **12**, M6L 8; the only row that changed in §3 is
  `watertank`'s. Duplicate check: none; tolerance-only variant check: none. Timing totals:
  tool 88 394 ms, Z3 88 540 ms (pass 7: 92 758 / 93 507); taken while one Lean elaboration
  process of the battery rebuild ran on 1 of 12 cores; per-benchmark rows in the script's
  `--md` output, not reproduced here (§17.6 keeps the pass-7 table).
* `relcert --check-quick benchmarks/suite_uniform/*/input.txt`: `[suite] 34 certified, 7
  declined, 0 error(s) — matches the declared suite`; `[coverage] cut probes: 97/97`,
  `modal: 486/486`, `handoff: 163/163`, `non-connection: 2/2`, `pruned edges: 1/1`;
  `QUICK CHECKS PASSED` (before: 40 / 1, watertank 6/6, 97/97, 504/504, 191/191, 2/2, 1/1).
* Without `RELCERT_IMPLIED_CUT=1` the twelve M6+ members DECLINE, `watertank` among them
  (33 CERTIFIED, 12 DECLINED; §10).
* Cover drift: every committed emitted cover (`Instances/BenchCovers/*`, 34 leaves, and
  `Instances/BenchCoversNC/*`, 23 leaves, the latter under `RELCERT_NO_CUT=1`) is
  byte-identical to what `relcert --emit-cover` prints for its `suite_uniform` input.
* `lake build` (the removal tree, `07e4df9` + `adc86b3`): exit 0, `Build completed
  successfully (8948 jobs)`, no `sorry`; `lake build relcert relcert-test` 17661 jobs.
  `ModalBattery`: **46 theorems** (52 before), 36 with `z3_unsat_sound`, 10 with the three
  standard axioms alone, no other axiom. `BENCH_PATHS=<manifest of the 41> relcert-test`:
  `ALL PASS` (40 IR literals match their files; the IR literals of the six declined
  benchmarks are kept and still drift-checked).

## 19. Pass 9 (2026-10-10): the odometer wall removed; the satellite nonblocking regions

Two model-level findings from the Theorem 3 mechanization of the last nine suite_v2
benchmarks (`docs/PAPER-MAPPING.md` §2c; `RelCertifier/InstancesV2/Modal/`). Both concern
Assumption 1 of the paper (nonblocking: a right state inside the invariant can always flow
for the window's duration). Every number below: Z3 4.15.1, `RELCERT_IMPLIED_CUT=1` except in
the counter-runs, default solver settings (§10).

### 19.1 `rover_patrol_zones`, `rover_patrol_refine`: the track-end wall `s ≤ 100` removed

**Finding.** Both files carried `s <= 100.0` in every evolve domain on both sides. A domain
wall is a *blocking* constraint, not a physical limit of the rover: at `s_R = 100` the
reference cannot flow (its odometer would leave the domain), while a deployed rover up to
2 m behind (`s_L ≤ s_R + 2`) still moves. The modal claim with the right zone's kept cut
atoms as its region is then FALSE as modeled (found while proving it, 2026-10-09), although
the tool CERTIFIED (the covers' flow queries are posed over the domain, not over the
existence of the right run).

**Change** (benchmark rule: domains are physical limits, never restrictions to force a
match). The odometer wall is removed from both sides' evolve domains of every mode in both
files; the physical domains stay (`v ∈ [0, 1.6]` m/s, `s ≥ 0` m, and `a ∈ [−2, 2]` m/s² in
the refinement rung). The patrol continues past the last zone boundary: `FAST`'s guard
`s ≥ 50` already covers every `s` beyond the `MEDIUM` zones. Headers updated with the
rationale. No guard, ODE, row or tolerance changed.

**Evidence** (after the change; before in parentheses where it differs):

| run | `rover_patrol_zones` | `rover_patrol_refine` |
|---|---|---|
| `relcert` | CERTIFIED 390 ms (413) | CERTIFIED 1517 ms (1484) |
| `RELCERT_NO_PRUNE=1` | CERTIFIED | CERTIFIED |
| `RELCERT_NO_CUT=1` | DECLINED | DECLINED |
| `RELCERT_NO_IMPLIED_CUT=1` | CERTIFIED | DECLINED |
| `RELCERT_NO_LINEAR_CUT=1` | CERTIFIED | DECLINED |
| `--handoff` | 10/10 unsat | 10/10 unsat |
| matrix cells (`suite_v2_matrix.py --only …`) | M2 M3 M5 M6 (unchanged) | M1 M2 M3 M5 M6 M6+ M6L (unchanged) |
| `domain_widening.py` | all widened CERTIFIED, no load-bearing bound (`s.lo` one-sided, skipped) | same |

The emitted covers and cut certificates are byte-identical before and after
(`scripts/gen_v2_data.py` regenerated only the two IR leaves; `[ir-drift-v2]` 45/45).

**Theorem 3.** Both now carry the mode-keyed Theorem 3 (`RoverPatrolZones.lean`,
`RoverPatrolRefine.lean`; ten verdict packs each). The right zone runs are the explicit
solutions `v(t) = c + (v₀ − c) e^{−kt}`, `s(t) = s₀ + k c t + (v₀ − c)(1 − e^{−kt})`, which
stay in the domain from every domain state now that `s` has no upper wall. Right starts in
an earlier zone than the window's certified target reposition right-only (the zone run until
the odometer reaches the target's floor; `SLOW` in the `FAST` window via `MEDIUM_ECO`, since
`SLOW` has no edge to `FAST`), then the certified joint piece.

**Pre-existing header inaccuracy, reported, not changed:** the `rover_patrol_zones` header
lists mechanism M4 and says `RELCERT_NO_PRUNE=1` DECLINES; both before and after this pass
NO_PRUNE CERTIFIES (the matrix credits M4 as vacuous: `STALL`'s region is empty under the
row and the left floor, so no window ever needs the pruning). The matrix cells are unchanged
by this pass.

### 19.2 The satellite family: theorems on the nonblocking region (model property)

The six detumbling benchmarks (`sat_detumble_{nominal,weak,phases}`,
`sat3w_detumble_{nominal,weak,phases}`) declare the wheel-momentum band `|h| ≤ 2` (resp.
`|h_i| ≤ 2`) as a physical domain on both sides. It blocks right flows: from `h_R = 2`,
`w3_R = 0.4` (energy 0.8, inside the cut `E ≤ 1`) every right mode leaves `h ≤ 2` at once
(`h' = 5 k w3 > 0`), so the right cannot move, while a left state of the same energy and
`h_L = 0` flows and its energy decays — the modal claim with the cut atoms alone as the region
is FALSE. The benchmark files are NOT changed (the band is the wheel's real capacity). The
theorems are instead stated on the **nonblocking region**: the right region of every non-sink
mode carries, besides its kept cut atoms, the bands on the total angular momentum about each
wheel axis (`J = diag(2, 4, 5)`):

| benchmark | nonblocking conjunct (right state) |
|---|---|
| `sat_detumble_*` (one wheel on z) | `−2 ≤ h + 5 w3 ≤ 2` |
| `sat3w_detumble_*` (three wheels) | `−2 ≤ h1 + 2 w1 ≤ 2`, `−2 ≤ h2 + 4 w2 ≤ 2`, `−2 ≤ h3 + 5 w3 ≤ 2` |

Each quantity `h_i + J_i w_i` is EXACTLY conserved by every right design-model mode
(`(h_i + J_i w_i)' = J_i k w_i − J_i k w_i = 0`; the gains differ per profile, the ratio
`h_i' / w_i' = −J_i` does not), and `h_i(t)` stays between `h_i(0)` and `h_i(0) + J_i w_i(0)`,
so the conjunct is exactly what keeps the right run inside the band (existence: the explicit
solution). It is a property of the benchmark MODEL — the total momentum stays within the
wheel capacity — not a tool cut: it enters NO verdict query (the packs are the tool's own
`modalVerdX` queries, narrowed by the kept cut atoms only) and is carried through the joint
piece by a separate conservation lemma (`couple_cutX_nb`, `stayNB`). Every instance's
docstring states this.
