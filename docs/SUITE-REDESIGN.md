# Suite redesign — `benchmarks/suite_v2` (2026-10-08, branch `suite-redesign`)

Status: tool-side, landed on `suite-redesign` in two passes. Pass 1 (`1830a12`,
`910ae8e`): the suite and this document, no tool change. Pass 2 (2026-10-08, from
`7c5a11c`): the tool's cut channel widened (§7 L1, L2 — implied-contraction atoms and
closures of strict guard conjuncts, behind `RELCERT_IMPLIED_CUT=1`), L5 corrected
(per-mode evolve domains are the model class), five scenarios that pass 1 had dropped
re-tried and added, three weaker members retired; **suite size 42**.
`benchmarks/suite_uniform/` and every Lean instance, pin and coverage constant are
untouched (the Lean build reads `suite_uniform`; the regression record is §12); the Lean
mechanization of the new suite — including the lift of the two new atom kinds and of
per-mode domains — is a separate later task. Every number below was measured with
`scripts/suite_v2_matrix.py` (§2), Z3 4.15.1, the `relcert` binary of `7c5a11c`
(`RELCERT_IMPLIED_CUT=1` on every run but the implied-cut counter-run), warm persistent
session; the generated sections (§3, §8, §9) are its output verbatim.

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

21 new benchmarks in seven families replace them. **Suite size 42**: 19 kept + 2
kept-replaceable + 21 new; 42 / 42 CERTIFIED; no two files normalize to the same model.
Pass 2 replaced `charger_fast_bulk` by `charger_fast_setpoints` (the three-set-point
charger pass 1 had dropped under L1; cells a superset) and `platoon_delay_bias` by
`platoon_delay_band` (the same platoon with its original half-open band, dropped under
L2; cells a superset), retired `acc_spoof_cruise_50` (a magnitude variant of
`acc_spoof_cruise` with identical cells) and added the three per-mode-domain scenarios
pass 1 had dropped under L5: `charger_bias_estimator`, `charger_fast_thermal`,
`heater_cycle`.

| family | benchmarks | scenario kind (M7) | dims |
|---|---|---|---|
| ACC under sensor spoofing / retune | `acc_spoof_cruise`, `acc_spoof_modes`, `acc_spoof_lag`, `acc_tune_gain`, `acc_tune_modes`, `acc_tune_lag` | sensor-attack ×3, degraded-controller ×2, model-refinement ×2 (the `_lag` rungs) | 1, 2 |
| Quadrotor climb, lighter airframe | `quad_light_airframe_20`, `quad_light_airframe_40`, `quad_light_lag` | model-refinement (plant mismatch, polynomial drag) | 1, 2 |
| Battery charger | `charger_fast_setpoints`, `charger_fast_tapers`, `charger_fast_thermal` (degraded-controller: current limit raised), `charger_bias_estimator` (sensor-attack: SoC estimator bias) | degraded-controller ×3, sensor-attack | 1, 2 |
| Platoon follower, delayed link | `platoon_delay_band`, `platoon_delay_profiles` | sensor-attack (stale link) | 1 |
| Rover patrol (zones) | `rover_patrol_zones`, `rover_patrol_refine` (+ kept `rover3tier_rung12`, `match_multi_rate`) | degraded-actuator, model-refinement | 2, 3 |
| Arm, leading reference | `arm_plateau_pd`, `arm_plateau_slow`, `arm_plateau_crit` | model-refinement, degraded-actuator, degraded-controller | 2 / 1 |
| Heater cycle | `heater_cycle` | degraded-actuator (stronger element), hysteresis with per-mode domains | 1 |

Every new benchmark but `heater_cycle` exercises at least two of M1–M6 non-vacuously
(§3; the three arm rungs, `quad_light_lag` and `charger_bias_estimator` exercise exactly
two; `heater_cycle` exercises M2 and is the hysteresis / per-mode-domain exhibit) and
belongs to one scenario kind. Every mechanism is exercised by at least four benchmarks
in at least two families: M1 19 (ACC ×6, quadrotor ×3, charger, rover ×3, ladders ×6),
M2 29, M3 6 (ACC ×2, charger, platoon, rover ×2), M4 15 (ACC ×6, quadrotor ×2, charger
×4, platoon ×2, rover), M5 6 (rover ×3, stories ×3), M6 19 (arm ×3, charger ×2, platoon
×2, rover ×2, ACC, ladders ×9); the new cut kinds are load-bearing in 2 (M6+: charger,
platoon) and per-mode domains in 3 (charger ×2, heater).

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
3. `RELCERT_NO_PRUNE=1 relcert <input>`, `RELCERT_NO_CUT=1 relcert <input>` and
   `RELCERT_NO_IMPLIED_CUT=1 relcert <input>` — the counter-runs (the third: legacy
   guard-conjunct cuts only).
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
| M6+ | some mode keeps a WIDENED atom (closure / implied-contraction, §7) AND `RELCERT_NO_IMPLIED_CUT=1` DECLINES: the cuts are load-bearing only with the implied atoms |
| M7 | the scenario kind from the file's `# scenario:` line (the kept files carry none; the script maps them: ladders and stories model-refinement, watertank sensor-attack); dimension and invariant shape computed from the file; `per-mode domains` if some side's modes declare different evolve domains (the paper's Eq. 2 model, §7 L5) |

A benchmark that keeps cuts but still certifies without them is printed `M6 vacuous`
(e.g. every ACC file keeps its band floor as a cut, but only `acc_tune_modes` needs it);
a benchmark whose fallback is pruned but which would certify anyway is printed `M4
vacuous` (one is: `rover_patrol_zones`, §5 finding 9).

## 3. Feature matrix (generated)

| benchmark | verdict (ms) | M1 λ≠1 | M2 multi-step | M3 branch | M4 prune | M5 mode-dep | M6 cut | M6+ implied cut | M7 scenario; dim; invariant; domains |
|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_cruise` | CERTIFIED (105) | yes: CRUISE λ=5/4 (affine dynamics) | yes: CRUISE B=3 via CRUISE | no (max non-self successors at a joint step = 0) | yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.CRUISE: 2 conjunct(s... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | sensor-attack; dim 1; conjunctive |
| `acc_spoof_lag` | CERTIFIED (137) | yes: CRUISE λ=5/4 (affine dynamics) | yes: CRUISE B=3 via CRUISE | no (max non-self successors at a joint step = 0) | yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunc... | vacuous: widened atoms kept (R.CRUISE: v <= 40.0 kind=closure entry... | model-refinement; dim 2; linear |
| `acc_spoof_modes` | CERTIFIED (166) | yes: CRUISE λ=5/4 (affine dynamics) | yes: CRUISE B=3 via ECO/NORMAL/SPORT | yes: CRUISE branch=2 | yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO... | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | sensor-attack; dim 1; conjunctive |
| `acc_tune_gain` | CERTIFIED (175) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=3 via CRUISE | no (max non-self successors at a joint step = 0) | yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.CRUISE: 2 conjunct(s... | vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry... | degraded-controller; dim 1; conjunctive |
| `acc_tune_lag` | CERTIFIED (154) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=3 via CRUISE | no (max non-self successors at a joint step = 0) | yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunc... | vacuous: widened atoms kept (R.CRUISE: v <= 40.0 kind=closure entry... | model-refinement; dim 2; linear |
| `acc_tune_modes` | CERTIFIED (271) | yes: CRUISE λ=3/2 (affine dynamics) | yes: CRUISE B=3 via COMFORT/NORMAL/SPORT | yes: CRUISE branch=2 | yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE... | no (rows identical; handoff vacuous) | yes: L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.COMFORT: 2... | vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure en... | degraded-controller; dim 1; conjunctive |
| `arm_plateau_crit` | CERTIFIED (268) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/Hold +RO, Brake B=2 via ApproachA... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.Accelerate: 1 conjunct(s); R.ApproachA: 1 conjunct(s); R.App... | vacuous: widened atoms kept (L.Accelerate: v <= 0.355 kind=closure ... | degraded-controller; dim 2+-1; linear |
| `arm_plateau_pd` | CERTIFIED (205) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/Hold +RO, Brake B=2 via ApproachA... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.Appr... | vacuous: widened atoms kept (R.Hold: theta <= 1.15 kind=closure ent... | model-refinement; dim 2+-1; linear |
| `arm_plateau_slow` | CERTIFIED (212) | no (λ=1 everywhere) | yes: Accelerate B=2 via ApproachA/Hold +RO, Brake B=2 via ApproachA... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.Appr... | vacuous: widened atoms kept (R.Hold: theta <= 1.15 kind=closure ent... | degraded-actuator; dim 2+-1; linear |
| `charger_bias_estimator` | CERTIFIED (302) | no (λ=1 everywhere) | yes: BULK B=2 via ABSORB/BULK, ABSORB B=2 via ABSORB/BULK/FULL, FUL... | no (max non-self successors at a joint step = 1) | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s);... | vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contra... | sensor-attack; dim 1; conjunctive; per-mode domains |
| `charger_fast_setpoints` | CERTIFIED (164) | no (λ=1 everywhere) | yes: BULK B=2 via ABSORB/FULL +RO, ABSORB B=2 via ABSORB/FULL +RO, ... | no (max non-self successors at a joint step = 1) | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conj... | yes: L.BULK: x <= 90.0 kind=implied-contraction entry=rational rout... | degraded-controller; dim 1; linear |
| `charger_fast_tapers` | CERTIFIED (205) | no (λ=1 everywhere) | yes: BULK B=2 via FULL +RO, ABSORB B=2 via ABSORB_FAST/ABSORB_SLOW/... | yes: ABSORB branch=2 | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conj... | vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contra... | degraded-controller; dim 1; linear |
| `charger_fast_thermal` | CERTIFIED (528) | yes: BULK λ=5/4 (affine dynamics) | yes: BULK B=3 via ABSORB/BULK/FULL, ABSORB B=2 via ABSORB/BULK/FULL... | no (max non-self successors at a joint step = 1) | yes: pruned BULK->FAULT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s);... | vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contra... | degraded-controller; dim 2; conjunctive; per-mode domains |
| `heater_cycle` | CERTIFIED (146) | no (λ=1 everywhere) | yes: HEAT B=2 via HEAT/OFF, OFF B=2 via HEAT/OFF | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.HEAT: 1 conjunct(s); L.OFF: 1 conjunct(s); R.... | vacuous: widened atoms kept (L.HEAT: T <= 90.0 kind=implied-contrac... | degraded-actuator; dim 1; conjunctive; per-mode domains |
| `match_multi_rate` | CERTIFIED (327) | yes: FAST λ=3, MEDIUM λ=2 (affine dynamics) | yes: FAST B=3 via DRIVE, MEDIUM B=2 via DRIVE | no (max non-self successors at a joint step = 0) | yes: pruned DRIVE->STALL; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.FAST: 2 conjunct(s); L.MEDIUM: 2 conjunct(s);... | vacuous: widened atoms kept (L.FAST: v <= 1.0 kind=implied-contract... | model-refinement; dim 2; linear |
| `platoon_delay_band` | CERTIFIED (198) | no (λ=1 everywhere) | yes: FOLLOW B=2 via CATCH/FOLLOW, CATCH B=2 via CATCH/FOLLOW | no (max non-self successors at a joint step = 1) | yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.FOLLOW: 2 conjunct(s); L.CATCH: 1 conjunct(s); R.FOLLOW: 2 c... | yes: L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; ... | sensor-attack; dim 1; conjunctive |
| `platoon_delay_profiles` | CERTIFIED (215) | no (λ=1 everywhere) | yes: FOLLOW B=2 via ASSERTIVE/FOLLOW/GENTLE, GENTLE B=2 via ASSERTI... | yes: FOLLOW branch=2, GENTLE branch=2 | yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | yes: L.FOLLOW: 2 conjunct(s); L.GENTLE: 1 conjunct(s); R.FOLLOW: 2 ... | vacuous: widened atoms kept (L.GENTLE: g >= 29.0 kind=implied-contr... | sensor-attack; dim 1; conjunctive |
| `quad_light_airframe_20` | CERTIFIED (246) | yes: CLIMB λ=7/4 (polynomial dynamics) | yes: CLIMB B=4 via CLIMB | no (max non-self successors at a joint step = 0) | yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s);... | vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contracti... | model-refinement; dim 1; conjunctive |
| `quad_light_airframe_40` | CERTIFIED (285) | yes: CLIMB λ=9/4 (polynomial dynamics) | yes: CLIMB B=5 via CLIMB | no (max non-self successors at a joint step = 0) | yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s);... | vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contracti... | model-refinement; dim 1; conjunctive |
| `quad_light_lag` | CERTIFIED (112) | yes: CLIMB λ=7/4 (polynomial dynamics) | yes: CLIMB B=4 via CLIMB | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 2 conjunct(s))... | no (no widened atom kept) | model-refinement; dim 2; linear |
| `refinement_ladder_rover_rung1_2to3` | CERTIFIED (207) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 3+-1; conjunctive |
| `refinement_ladder_rover_rung2_3to6` | CERTIFIED (658) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 6; conjunctive |
| `refinement_ladder_rover_rung2_6dof` | CERTIFIED (266) | yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polyno... | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 4; linear |
| `refinement_ladder_rover_rung2b_6dof` | CERTIFIED (226) | yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polyno... | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 6; linear |
| `refinement_ladder_rover_rung2c_6dof` | CERTIFIED (1346) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 6; conjunctive |
| `refinement_ladder_rover_rung3_6to8` | CERTIFIED (2877) | yes: STEEP λ=9/4, MODER λ=9/4, FLAT λ=9/4 (polynomial dynamics) | yes: STEEP B=3 via FLAT/MODER/STEEP, MODER B=3 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conj... | no (no widened atom kept) | model-refinement; dim 8; quadratic |
| `refinement_ladder_rover_rung4_8to12` | CERTIFIED (983) | yes: STEEP λ=17/10, MODER λ=17/10, FLAT λ=17/10 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 12; conjunctive |
| `rover3tier_rung12` | CERTIFIED (247) | yes: ACCEL λ=7/4 (affine dynamics) | yes: ACCEL B=6 via ACCEL/COAST, COAST B=4 via ACCEL/COAST | no (max non-self successors at a joint step = 1) | no (nothing pruned) | yes: 4/4 handoffs unsat, rows differ | vacuous: cuts kept (R.ACCEL: 1 conjunct(s); R.COAST: 1 conjunct(s))... | no (no widened atom kept) | model-refinement; dim 3; conjunctive+linear |
| `rover_dof_terrain_rung1` | CERTIFIED (296) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 3; conjunctive |
| `rover_dof_terrain_rung2` | CERTIFIED (357) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 6; conjunctive |
| `rover_dof_terrain_rung3` | CERTIFIED (370) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 12; conjunctive |
| `rover_dof_terrain_rung3_8d` | CERTIFIED (363) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 8; conjunctive |
| `rover_patrol_refine` | CERTIFIED (2547) | yes: SLOW λ=7/2, MEDIUM_ECO λ=7/2, MEDIUM_BRISK λ=7/2, FAST λ=7/2 (... | yes: SLOW B=7 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=7... | yes: SLOW branch=2 | no (nothing pruned) | yes: 10/10 handoffs unsat, rows differ | yes: L.SLOW: 1 conjunct(s); L.MEDIUM_ECO: 1 conjunct(s); L.MEDIUM_B... | no (no widened atom kept) | model-refinement; dim 3; conjunctive |
| `rover_patrol_zones` | CERTIFIED (456) | no (λ=1 everywhere) | yes: SLOW B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=2... | yes: SLOW branch=2 | vacuous: pruned SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL... | yes: 10/10 handoffs unsat, rows differ | yes: L.SLOW: 3 conjunct(s); L.MEDIUM_ECO: 3 conjunct(s); L.MEDIUM_B... | vacuous: widened atoms kept (R.STALL: v <= 0.2 kind=closure entry=w... | degraded-actuator; dim 2; conjunctive |
| `story1_attdist_rung_a_6to8` | CERTIFIED (20200) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 8; conjunctive |
| `story1_attdist_rung_b_12dof` | CERTIFIED (418) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 12; conjunctive |
| `story2_lateral_rung_a_8dof` | CERTIFIED (1154) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 8; conjunctive |
| `story2_lateral_rung_b_12dof` | CERTIFIED (1494) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 12; conjunctive |
| `story3_rollover_base_12dof` | CERTIFIED (1228) | yes: STEEP λ=5/4, MODER λ=5/4, FLAT λ=5/4 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 12; quadratic |
| `story3_rollover_ladder_rung_a` | CERTIFIED (832) | yes: STEEP λ=27/20, MODER λ=27/20, FLAT λ=27/20 (polynomial dynamics) | yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, ... | no (max non-self successors at a joint step = 1) | no (nothing pruned) | no (rows identical; handoff vacuous) | yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conj... | no (no widened atom kept) | model-refinement; dim 12; quadratic |
| `story3_rollover_ladder_rung_b` | CERTIFIED (4860) | no (λ=1 everywhere) | no (single segment) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | yes: 5/5 handoffs unsat, rows differ | vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s);... | no (no widened atom kept) | model-refinement; dim 12; quadratic |
| `watertank` | CERTIFIED (226) | no (λ=1 everywhere) | no (single segment, RO used) | no (max non-self successors at a joint step = 0) | no (nothing pruned) | no (rows identical; handoff vacuous) | vacuous: cuts kept (L.Low: 1 conjunct(s); L.Mid: 1 conjunct(s); L.H... | vacuous: widened atoms kept (L.High: x <= 22.45 kind=closure entry=... | sensor-attack; dim 1; linear |

## 4. The families — stories, parameters, measured covers

Each file's header states the story, the units, the parameters, the claim and the
measured cover; this section summarizes the design and what each member adds.

### 4.1 ACC under sensor spoofing / retune (6)

A cruise controller with a first-order speed loop `v' = k (vset − v)`, `k = 0.5 /s`,
`vset = 30 m/s`, operating band `20 ≤ v`, physical envelope `0 ≤ v ≤ 40`. The
engage/disengage logic reads the wheel-speed sensor (floor 20 m/s), the speed loop the
fused GPS/radar ground speed. The reference (right) is the stock controller with its
declared DISENGAGE fallback below the floor (`v' = −0.5 v`, sink).

* `acc_spoof_cruise` — +25 % gain spoof on the fused speed: `v' = 0.5 (30 − 1.25 v) =
  0.625 (24 − v)`; rows `v_L ≤ v_R ∧ v_R ≤ v_L + 7`; λ = 5/4, budget 3; DISENGAGE pruned,
  not admissible (`v_L ≥ 20 ∧ v_L ≤ v_R`); NO_PRUNE DECLINED. (M1 M2 M4)
* (`acc_spoof_cruise_50`, the +50 % magnitude variant with λ = 3/2, was retired in
  pass 2: identical cells to `acc_spoof_cruise`; its slot went to `heater_cycle`.)
* `acc_spoof_modes` — the reference's driver may select the set speed ECO 27 / NORMAL
  30 / SPORT 33 at any time; rows `v_L ≤ v_R ∧ v_R ≤ v_L + 9.5`; λ = 5/4, budget 3; the
  cover from NORMAL takes a joint step whose retained successors ECO and SPORT both
  cover (branching 2); three DISENGAGE edges pruned. (M1 M2 M3 M4)
* `acc_spoof_lag` — refinement of the spoofed vehicle with the powertrain lag
  (`v' = a, a' = 2 (a_cmd − a)`), reference first-order; row = the lifted functional
  `a_L + 2 v_L ≤ 2 v_R` (`(a + 2v)' = 1.25 (24 − v)`); λ = 5/4, budget 3; DISENGAGE
  pruned, excluded by `v_L ≥ 23, a_L ≥ −5`. (M1 M2 M4)
* `acc_tune_gain` — aftermarket tune, gain 0.75 (1.5×), same set speed; rows
  `|v_L − v_R| ≤ 1`; λ = 3/2 (both boundary derivatives −0.75), budget 3; deployed band
  from 21 m/s so the floor is excluded. (M1 M2 M4)
* `acc_tune_modes` — the reference's driver selects a response gain COMFORT 0.4 /
  NORMAL 0.5 / SPORT 0.6; rows `|v_L − v_R| ≤ 2`; λ = 3/2, budget 3, branching 2;
  three edges pruned; the band bounds `20 ≤ v ≤ 36` are checked cuts the COMFORT and
  SPORT segments need: NO_CUT DECLINED. (M1 M2 M3 M4 M6)
* `acc_tune_lag` — the tune with the powertrain lag; row `a_L + 2 v_L ≤ 2 v_R + 6`
  (`(a + 2v)' = 1.5 (30 − v)`; envelope `a ∈ [−3, 6]`, so the row implies
  `v_L ≤ v_R + 4.5`: the lag costs tolerance); λ = 3/2, budget 3. (M1 M2 M4)

### 4.2 Quadrotor climb, lighter airframe (3) — polynomial dynamics

`w' = a − c w²` (climb rate, net specific thrust, drag per unit mass); reference
`a = 4, c = 1` (terminal 2 m/s), envelope `0 ≤ w ≤ 3.5`. The deployed airframe is
lighter than the reference model assumed, so `a_L = m/m_L (a + g) − g` and
`c_L = m/m_L · c` (not a pure time scaling because of `g`).

* `quad_light_airframe_20` — 20 % lighter (`a_L = 7.45, c_L = 1.25`); rows
  `w_L ≤ w_R + 1 ∧ w_R ≤ w_L + 0.5`; λ = 7/4, budget 4; climb-rate LIMITER above 3 m/s
  (`w' = −2 w`) pruned from CLIMB (drag wins at the threshold), excluded as a start by
  `w_L ≤ 2.5 ∧ w_R ≤ w_L + 0.5`. (M1 M2 M4)
* `quad_light_airframe_40` — 40 % lighter (`a_L = 9.524, c_L = 1.4`); λ = 9/4, budget
  5; limiter above 3.2 m/s. (M1 M2 M4)
* `quad_light_lag` — the 20 % airframe with the motor thrust lag `a' = 5 (7.45 − a)`;
  row = the lifted functional `a_L + 5 w_L ≤ 5 w_R + 12.45`; λ = 7/4, budget 4; no
  fallback (the functional cannot exclude a limiter as a start). (M1 M2)

### 4.3 Battery charger (4)

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
* `charger_fast_thermal` — 2-D: the cell temperature `T` heats in proportion to the
  charging current and cools toward 25 °C (`T' = 0.025 (100 − x) − 0.05 (T − 25)` in
  BULK, half the heating in ABSORB, cooling only in FULL/FAULT); deployed rates and
  heating × 1.25; rows `x_L ≤ x_R + 5 ∧ x_R ≤ x_L + 5 ∧ T_L ≤ T_R + 20`. PER-MODE
  DOMAINS: each phase's SoC band (`25 ≤ T ≤ 80`). λ = 5/4 (the BULK/BULK and
  ABSORB/ABSORB pairings need the reference 1.25× faster; the λ = 1 BULK pair fails:
  `[BULK_L λ=1] BULK=fail`), budget 3; the cross-phase pairings are static on the bands
  (`x_L ≤ 80 < x_R` in BULK_L/ABSORB_R); BULK → FAULT pruned (NO_PRUNE DECLINED); the
  phase floors are kept as cuts but the domains carry them (NO_CUT CERTIFIED). Pass 1
  dropped this scenario under one uniform envelope (§6). (M1 M2 M4; per-mode domains)
* `charger_bias_estimator` — sensor attack: the deployed charger runs the certified
  current profile but its SoC estimator reads 5 % high, so it switches phases 5 % early
  in true SoC (BULK `10 ≤ x < 75`, ABSORB `75 ≤ x < 94`, FULL `x ≥ 94`); rows
  `x_L ≤ x_R ∧ x_R ≤ x_L + 6` (never ahead of the certified profile, never more than
  6 % behind). PER-MODE DOMAINS: the phase bands. λ = 1, budget 2, crossing BULK →
  ABSORB → FULL jointly; BULK → FAULT pruned (NO_PRUNE DECLINED). The same file with one
  uniform envelope `0..100` is DECLINED (`[BULK_L λ=1] ABSORB=fail FULL=fail` and at
  every larger λ `BULK=fail`: the BULK_L/ABSORB_R pairing needs λ > 2 where BULK/BULK
  needs λ ≤ 1.08), which is the L5 point (§7). (M2 M4; per-mode domains)

### 4.4 Platoon follower, delayed link (2)

Gap `g` to a constant-speed leader, loops `g' = −k (g − 30)`: FOLLOW `k = 0.5`
(band `20 ≤ g < 40`), CATCH/GENTLE `0.6` and ASSERTIVE `0.7` (re-engagement,
`g ≥ 30`), BRAKE fallback below 20 m (`g' = +1.5`, sink); envelope `15 ≤ g ≤ 60`. The
deployed follower acts on the delayed link's 1 m gap overstatement (loops toward 29 m).

* `platoon_delay_band` — rows `g_L ≤ g_R + 1 ∧ g_R ≤ g_L + 3`; the FOLLOW band as the
  controller has it, half-open at 40 m; λ = 1, budget 2, crossing FOLLOW ↔ CATCH; the
  mixed segments need the band cap, which is now the CLOSURE `g ≤ 40` of the strict
  guard conjunct (`[cut-x] R.FOLLOW: g <= 40.0 kind=closure entry=weakening
  route=shape`; the band floor `g ≥ 20` is a guard conjunct, DI-strict): NO_CUT
  DECLINED (M6) and `RELCERT_NO_IMPLIED_CUT=1` DECLINED (M6+); FOLLOW → BRAKE pruned
  (the gentle loop opens the gap at 20 m), BRAKE excluded by `g_L ≥ 21 ∧ g_L ≤ g_R + 1`.
  (M2 M4 M6 M6+) Replaces `platoon_delay_bias` (the same scenario with the band closed
  by hand, cells M2 M4 M6).
* `platoon_delay_profiles` — two reference re-engagement profiles (closed band); the
  deployed uses the gentle one only; rows `g_L ≤ g_R + 4 ∧ g_R ≤ g_L + 3` (an assertive
  reference re-engaging from 60 m outruns the gentle deployed follower by up to 4 m; the
  1 m tolerance of `platoon_delay_band` is false for that pairing — measured, §6);
  branching 2 at FOLLOW and GENTLE. (M2 M3 M4 M6)

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
* `rover_patrol_refine` — the deployed with its motor lag (`v' = a, a' = 2 (a_cmd − a)`,
  `a ∈ [−0.5, 1]`), rows = the lifted functional `a_L + 2 v_L ≤ 2 v_R + 1` plus the
  zone margins; λ = 7/2, budget 7 (the lagged functional needs the reference run 3.5×
  faster; every smaller grid point fails some pairing); branching 2; cuts
  load-bearing. No STALL on this rung: the functional admits `a_L < 0`, so a stalled
  reference cannot be excluded as a start. (M1 M2 M3 M5 M6)
* kept: `rover3tier_rung12` (λ = 7/4 budget 6 / λ = 1 budget 4, non-nested rows),
  `match_multi_rate` (λ = 3 / 2, pruned `DRIVE → STALL`).

### 4.6 Arm, leading reference (3)

The arm tower redesigned: a PD joint tracking the step 0.5 rad from rest (modes
Accelerate / Brake, envelope `θ ≤ 0.65`), reference = a three-step leading ramp to a
plateau 0.6 rad then Hold (`θ' = 0`, guard `θ ≥ 0.6`); row `θ_L ≤ θ_R + 0.15`; εL = 2,
εR = 1 so budget 2. From an approach step the reference repositions right-only up the
ramp to Hold; Hold's frozen guard conjunct `θ_R ≥ 0.6` is the cut that puts the
invariant boundary (`θ_L ≥ 0.75`) outside the arm's envelope — NO_CUT DECLINED on all
three. No fallback: the arm starts at θ = 0 and the row is one-sided, so no reference
threshold below a floor can be excluded as a start (§6). Rungs: `_pd` (gains 1, 1,
underdamped), `_slow` (half torque: gains 0.5, 0.5), `_crit` (gains 1, 2, critically
damped). (M2+RO M6 each)

### 4.7 Heater cycle (1) — hysteresis with per-mode domains

Enclosure temperature `T`; certified controller cycles HEAT (`T' = 0.1 (90 − T)`) ↔ OFF
(`T' = 0.05 (20 − T)`) on a `55..65` hysteresis band: HEAT's domain `50 ≤ T ≤ 65`, OFF's
`55 ≤ T ≤ 70`, so each hand-over is forced at the band edge and may happen anywhere in
the band (guards `T ≤ 65` / `T ≥ 55`). Deployed: a replacement element 25 % stronger
(`0.125 (90 − T)`), same cooling and band.

* `heater_cycle` — rows `T_L ≤ T_R + 10.5 ∧ T_R ≤ T_L + 10.5`; λ = 1, budget 2, every
  window crossing HEAT ↔ OFF jointly. The claim is the band width: opposite phases are
  admissible (`HEAT_L/OFF_R` with `T_L = 55, T_R = 65`), so no two-sided bound below 10
  is true of the model; within a phase it is not implied by the domains (two heating
  units may be 15 °C apart) and the flows keep it. The 0.5 margin is the L6 incompleteness
  (§7): at exactly 10 the row's boundary meets the domain corner `(65, 55)` and is
  DECLINED. The widened channel keeps the set points `T ≤ 90` / `T ≥ 20` as implied atoms;
  they lie outside the bands and are not load-bearing. (M2; per-mode domains)

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
10. **Per-mode domains are what hysteresis and early-switching scenarios need** (pass 2,
   §7 L5): with each phase's band as its domain, cross-phase pairings become static
   (`x_L ≤ 75 < 80 ≤ x_R`) and the forced hand-over replaces the "unforced switching"
   objection of pass 1. The price is at the Lean side (the uniform-evolve discipline),
   not in the model or the tool.

## 6. Scenarios tried and dropped, and why

Each was run through the tool; the deciding trace line is quoted. "model-false" means
the ∀∃ claim is false for the model as written (the tool is right to decline);
"tool scope" means the claim is plausible but outside what the certifier's query forms
can establish (§7).

| scenario | what was tried | deciding evidence | verdict |
|---|---|---|---|
| charger, three set points (BULK toward 90, ABSORB toward 100) | `charger_fast_bulk` v1 | `[repo-dyn-pre] ABSORB_L: [ABSORB, FULL]` (BULK missing): the right-only BULK flow reverses above its set point 90, which lies inside the envelope, so route A over the whole domain is sat; `ABSORB_L` DECLINED | was tool scope (L1); **now CERTIFIED** with the implied atom `x ≤ 90` (`RELCERT_IMPLIED_CUT=1`, §7 L1) — in the suite as `charger_fast_setpoints`, replacing `charger_fast_bulk` (its cells are a superset: M2+RO M4 M6 M6+) |
| charger with the cell temperature (`charger_fast_thermal`, rows `x_L ≤ x_R + 5 ∧ T_L ≤ T_R + 6`) | 2-D refinement | `[repo-dyn-pre] BULK_L: []` — the reference cooling alone lowers `T_R` and breaks the thermal conjunct, so no reposition; jointly `BULK=fail ABSORB=fail` at λ = 1 (the `x` conjunct needs 5/4) and at 5/4 the `BULK_L/ABSORB_R` pair fails on the whole envelope | was "model-false on the whole envelope"; **now CERTIFIED with per-mode evolve domains** (each phase's SoC band is its domain, §7 L5), rows `x_L ≤ x_R + 5 ∧ x_R ≤ x_L + 5 ∧ T_L ≤ T_R + 20`, λ = 5/4 — in the suite as `charger_fast_thermal` |
| charger with a +5 % SoC estimator bias (sensor attack) | analysis of the `BULK_L/ABSORB_R` pairing | the deployed in BULK overtakes a reference in ABSORB (`x_L ≤ x_R` fails for `x_R < 90`); the model lets the deployed stay in BULK past 75 % | was "model-false (unforced switching)"; **now CERTIFIED with per-mode evolve domains** (`x_L ≤ 75` in the deployed BULK, `x_R ≥ 80` in the reference ABSORB make the pairing static), rows `x_L ≤ x_R ∧ x_R ≤ x_L + 6`; the same file with one uniform envelope is DECLINED (`[BULK_L λ=1] ABSORB=fail`, every λ) — in the suite as `charger_bias_estimator` |
| rover zones ordered SLOW → TRANSIT → APPROACH (last zone slower) | `rover_patrol_zones` v1 | `[SLOW_L λ=1 #comps=2] ... APPROACH=fail` at every λ: a reference ahead in the slow approach zone cannot keep `v_L ≤ v_R` against a deployed in SLOW; APPROACH is a sink (no reposition) | model-false; zones reordered so speeds do not decrease along the route |
| rover zones with the reference switching between the MEDIUM profiles | `rover_patrol_zones` v2 | FAST_L window DECLINED: `MEDIUM_ECO ---dd`, `MEDIUM_BRISK ---dd` are reposition-only nodes whose exits include each other, so `decideCovered` never grounds | tool semantics (the all-successors reposition rule, §7 L4); profiles selected on zone entry instead |
| platoon with a CATCH mode relaxing to 35 m, or declared FOLLOW → CATCH | analysis | the right-only CATCH flow opens the gap below its set point (`g_R ≥ 40` is not flow-invariant, so no cut keeps it); `FOLLOW_L/CATCH_R` fails on `g_R ∈ [20, 60]` | model-false as drafted: re-run in pass 2 with `RELCERT_IMPLIED_CUT=1` (CATCH toward 35 / 34, guard `g ≥ 40`), the implied atom IS kept (`[cut-x] R.CATCH: g >= 35.0 kind=implied-contraction entry=rational route=shape`) and the file is still DECLINED, `[FOLLOW_L λ=1] FOLLOW=pass CATCH=fail` — the right settles 6 m wider than the deployed loop's 29 m, outside the 3 m row; both profiles relax toward 30 and CATCH's guard is `g ≥ 30` |
| platoon with its original half-open FOLLOW band `20 ≤ g < 40` | `platoon_delay_bias` v0 | DECLINED: `[repo-pre] FOLLOW_L: [] … [repo-dyn-pre]: []` and the mixed FOLLOW/CATCH segments fail without the band cap; the strict conjunct `g < 40` was not a cut candidate | was tool scope (L2); **now CERTIFIED** with the closure `g ≤ 40` (`RELCERT_IMPLIED_CUT=1`, §7 L2) — in the suite as `platoon_delay_band`, replacing the closed-band `platoon_delay_bias` (same scenario, cells a superset: M2 M4 M6 M6+) |
| platoon, deployed with two profiles too (`d1 = 1`) | `platoon_delay_profiles` v1 | DECLINED: `ASSERTIVE_L/GENTLE_R` and `GENTLE_L/ASSERTIVE_R` violate `g_L ≤ g_R + 1` from a 60 m gap (0.1 g − 4.2 > 0 for g > 42) | model-false; deployed restricted to the gentle profile, tolerance 4 m |
| platoon with the delayed link as a lag state `m` (2-D left) | analysis | the lag conjunct `m − g ≤ d` is preserved only on a bounded `m` envelope and the right-only CATCH flow still fails | not run; `platoon_delay_band` models the latency as a bias |
| heater with a hysteresis cycle HEAT ↔ OFF and a two-sided row | analysis | `HEAT_L/OFF_R` is admissible (`T_L = 55, T_R = 62`) and uncertifiable (the left heats on the whole envelope while the right cools); a one-sided row is preserved by the fault's own cooling, so the fault would not be decisive | was "model-false under unforced switching"; **now CERTIFIED with per-mode evolve domains** at the band width plus 0.5 (`heater_cycle`, rows `|T_L − T_R| ≤ 10.5`, bands `[50, 65]` / `[55, 70]`): opposite phases are admissible, so no bound below the band width is true; at exactly the band width the DI routes fail at the domain corner (§7 L6) |
| quadrotor with altitude and a HOVER plateau (M6 for the quadrotor) | analysis | `CLIMB_L/HOVER_R` is admissible (altitude unrelated) and `w_L ≤ w_R` fails against a hovering reference; HOVER is a sink | model-false; the quadrotor family has no cut-reliant member |
| quadrotor with a degraded motor (20 % less thrust) | analysis | the deployed is slower in time, so the rows need λ ≈ 0.7 < λmin = 1 | not used (λ < 1 is nowhere in the suite; the lighter-airframe rungs give the polynomial M1) |
| arm with a drop-back fallback (M4) | analysis | the arm starts at θ = 0 and the row is one-sided (`θ_L ≤ θ_R + 0.15`); a reference threshold `θ_R < T` is admissible for every `T > −0.15` and a ceiling needs a conjunct bounding `θ_R` above, which the leading reference violates | model-false; the arm family exercises M2+RO and M6 |

## 7. Tool limitations found; fixes made

Each limitation below was met by a sensible scenario. L1 and L2 are FIXED on this branch
(2026-10-08, second pass; tool side only, the Lean lift of the new certificate is a later
pass). L3 and L4 stand as recorded. L5 was misattributed to the model class and is
corrected. L6 is new. None weakens a soundness check; all are incompleteness.

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
  are forced), all three scenarios certify (§6, §9): `charger_bias_estimator` (whose
  uniform-envelope control is DECLINED), `charger_fast_thermal` (λ = 5/4) and
  `heater_cycle` (at the band width plus the L6 margin). The matrix marks them
  `per-mode domains` (M7 column, §8 totals).
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

Observed, not a limitation: the one-sided left-leads-right rows and the checked cuts
let the certifier certify every mixed-profile and cross-zone pairing it needed; all 42
inputs certify in under 0.6 s except the 6–12-dof ladders (`story1_attdist_rung_a_6to8`
≈ 20 s, `story3_rollover_ladder_rung_b` ≈ 5 s, the others ≤ 3 s).

## 8. Totals and the proposed Table-1 grouping (generated)

| mechanism | benchmarks (non-vacuous) | count |
|---|---|---|
| M1 | `acc_spoof_cruise`, `acc_spoof_lag`, `acc_spoof_modes`, `acc_tune_gain`, `acc_tune_lag`, `acc_tune_modes`, `charger_fast_thermal`, `match_multi_rate`, `quad_light_airframe_20`, `quad_light_airframe_40`, `quad_light_lag`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover3tier_rung12`, `rover_patrol_refine`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a` | 19 |
| M2 | `acc_spoof_cruise`, `acc_spoof_lag`, `acc_spoof_modes`, `acc_tune_gain`, `acc_tune_lag`, `acc_tune_modes`, `arm_plateau_crit`, `arm_plateau_pd`, `arm_plateau_slow`, `charger_bias_estimator`, `charger_fast_setpoints`, `charger_fast_tapers`, `charger_fast_thermal`, `heater_cycle`, `match_multi_rate`, `platoon_delay_band`, `platoon_delay_profiles`, `quad_light_airframe_20`, `quad_light_airframe_40`, `quad_light_lag`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover3tier_rung12`, `rover_patrol_refine`, `rover_patrol_zones`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a` | 29 |
| M3 | `acc_spoof_modes`, `acc_tune_modes`, `charger_fast_tapers`, `platoon_delay_profiles`, `rover_patrol_refine`, `rover_patrol_zones` | 6 |
| M4 | `acc_spoof_cruise`, `acc_spoof_lag`, `acc_spoof_modes`, `acc_tune_gain`, `acc_tune_lag`, `acc_tune_modes`, `charger_bias_estimator`, `charger_fast_setpoints`, `charger_fast_tapers`, `charger_fast_thermal`, `match_multi_rate`, `platoon_delay_band`, `platoon_delay_profiles`, `quad_light_airframe_20`, `quad_light_airframe_40` | 15 |
| M5 | `rover3tier_rung12`, `rover_patrol_refine`, `rover_patrol_zones`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof`, `story3_rollover_ladder_rung_b` | 6 |
| M6 | `acc_tune_modes`, `arm_plateau_crit`, `arm_plateau_pd`, `arm_plateau_slow`, `charger_fast_setpoints`, `charger_fast_tapers`, `platoon_delay_band`, `platoon_delay_profiles`, `refinement_ladder_rover_rung1_2to3`, `refinement_ladder_rover_rung3_6to8`, `refinement_ladder_rover_rung4_8to12`, `rover_dof_terrain_rung1`, `rover_dof_terrain_rung2`, `rover_dof_terrain_rung3`, `rover_dof_terrain_rung3_8d`, `rover_patrol_refine`, `rover_patrol_zones`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a` | 19 |
| M6+ | `charger_fast_setpoints`, `platoon_delay_band` | 2 |
| per-mode domains | `charger_bias_estimator`, `charger_fast_thermal`, `heater_cycle` | 3 |

| group | count | dim (L/R) | invariant forms | dynamics | discrete structure (modes L/R; pruned fallbacks; mode-dep. rows; cuts; implied cuts; per-mode domains) |
|---|---|---|---|---|---|
| ACC under sensor spoofing / retune | 6 | 1, 2 | conjunctive, linear | affine | modes 1-1 / 2-4; 6 with a pruned fallback; 0 mode-dependent; 1 cut-reliant; 0 implied-cut-reliant; 0 per-mode domains |
| Quadrotor climb, lighter airframe | 3 | 1, 2 | conjunctive, linear | polynomial | modes 1-1 / 1-2; 2 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 implied-cut-reliant; 0 per-mode domains |
| Battery charger | 4 | 1, 2 | conjunctive, linear | affine | modes 3-3 / 4-5; 4 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 1 implied-cut-reliant; 2 per-mode domains |
| Platoon follower, delayed link | 2 | 1 | conjunctive | affine | modes 2-2 / 3-4; 2 with a pruned fallback; 0 mode-dependent; 2 cut-reliant; 1 implied-cut-reliant; 0 per-mode domains |
| Rover patrol (zones) | 4 | 2, 3 | conjunctive, conjunctive+linear, linear | affine | modes 2-4 / 2-5; 1 with a pruned fallback; 3 mode-dependent; 2 cut-reliant; 0 implied-cut-reliant; 0 per-mode domains |
| Arm, leading reference | 3 | 2/1 | linear | affine | modes 2-2 / 4-4; 0 with a pruned fallback; 0 mode-dependent; 3 cut-reliant; 0 implied-cut-reliant; 0 per-mode domains |
| Heater cycle | 1 | 1 | conjunctive | affine | modes 2-2 / 2-2; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 implied-cut-reliant; 1 per-mode domains |
| Terrain/position ladder | 11 | 3/2, 3, 4, 6, 8, 12 | conjunctive, linear, quadratic | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 7 cut-reliant; 0 implied-cut-reliant; 0 per-mode domains |
| Story ladders | 7 | 8, 12 | conjunctive, quadratic | polynomial | modes 3-3 / 3-3; 0 with a pruned fallback; 3 mode-dependent; 2 cut-reliant; 0 implied-cut-reliant; 0 per-mode domains |
| Watertank | 1 | 1 | linear | affine | modes 3-3 / 3-3; 0 with a pruned fallback; 0 mode-dependent; 0 cut-reliant; 0 implied-cut-reliant; 0 per-mode domains |
| **total** | **42** | | | | |

## 9. Per-benchmark run records (generated)

The verdict and wall time, the `[prune]` line, the three counter-runs and the domain
kind, the kept cuts (`[cut]` counts; `[cut-x]` the widened atoms with kind, O1 and O2),
the admissible starts, the handoff summary, the emitted cover per left mode (λ, budget,
flag rows `j r r d d` = jointOK, repoPre, repoPost, dynPre, dynPost) and the replayed
derivation from every admissible start (`mode:kind(B=budget[,σ])->[successor configs]`,
one line per distinct step).

Duplicate check (normalized md5, docs/SUITE-DEDUPE.md): no two benchmarks normalize to the same model

### `acc_spoof_cruise`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 1/1; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `b1c8d2c43a37`
* `relcert`: **CERTIFIED** (105 ms); `[prune] acc_spoof_cruise: [CRUISE->DISENGAGE]`; NO_PRUNE: **DECLINED** (646 ms); NO_CUT: **CERTIFIED** (170 ms); NO_IMPLIED_CUT: **CERTIFIED** (140 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] R.CRUISE: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB`
* `[cut-x] R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (20 ms)
* cover `CRUISE_L`: λ = 5/4, budget 3, admissible ['CRUISE'], flags {'CRUISE': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/4 (affine dynamics); **M2** yes: CRUISE B=3 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB; R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `acc_spoof_lag`

* family: ACC under sensor spoofing / retune; scenario: model-refinement; dims L/R 2/2; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `ebf474defcac`
* `relcert`: **CERTIFIED** (137 ms); `[prune] acc_spoof_lag: [CRUISE->DISENGAGE]`; NO_PRUNE: **DECLINED** (370 ms); NO_CUT: **CERTIFIED** (100 ms); NO_IMPLIED_CUT: **CERTIFIED** (140 ms); domains: uniform
* `[cut] R.CRUISE: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (81 ms)
* cover `CRUISE_L`: λ = 5/4, budget 3, admissible ['CRUISE'], flags {'CRUISE': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/4 (affine dynamics); **M2** yes: CRUISE B=3 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `acc_spoof_modes`

* family: ACC under sensor spoofing / retune; scenario: sensor-attack; dims L/R 1/1; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9ba6f4802d67`
* `relcert`: **CERTIFIED** (166 ms); `[prune] acc_spoof_modes: [NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1138 ms); NO_CUT: **CERTIFIED** (215 ms); NO_IMPLIED_CUT: **CERTIFIED** (159 ms); domains: uniform
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
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (63 ms)
* cover `CRUISE_L`: λ = 5/4, budget 3, admissible ['NORMAL', 'ECO', 'SPORT'], flags {'NORMAL': 'j----', 'ECO': 'j----', 'SPORT': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['ECO', 'NORMAL', 'SPORT'], branching 2, right-only False
    * from `NORMAL`: `NORMAL:joint(B=3)->[NORMAL@2, NORMAL@2, ECO@2, SPORT@2]; NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; NORMAL:base(B=1); ECO:base(B=1); SPORT:base(B=1); ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]`
    * from `ECO`: `ECO:joint(B=3)->[ECO@2, ECO@2, NORMAL@2]; ECO:joint(B=2)->[ECO@1, ECO@1, NORMAL@1]; ECO:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; SPORT:base(B=1)`
    * from `SPORT`: `SPORT:joint(B=3)->[SPORT@2, SPORT@2, NORMAL@2]; SPORT:joint(B=2)->[SPORT@1, SPORT@1, NORMAL@1]; SPORT:base(B=1); NORMAL:base(B=1); NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1, ECO@1, SPORT@1]; ECO:base(B=1)`
* cells: **M1** yes: CRUISE λ=5/4 (affine dynamics); **M2** yes: CRUISE B=3 via ECO/NORMAL/SPORT; **M3** yes: CRUISE branch=2; **M4** yes: pruned NORMAL->DISENGAGE, ECO->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.ECO: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry=weakening route=diB; R.NORMAL: v <= 40.0 kind=closure entry=weakening route=shape; R.ECO: v <= 40.0 kind=closure entry=weakening route=shape; R.SPORT: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `acc_tune_gain`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 1/1; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `e2d80c327bde`
* `relcert`: **CERTIFIED** (175 ms); `[prune] acc_tune_gain: [CRUISE->DISENGAGE]`; NO_PRUNE: **DECLINED** (614 ms); NO_CUT: **CERTIFIED** (192 ms); NO_IMPLIED_CUT: **CERTIFIED** (192 ms); domains: uniform
* `[cut] L.CRUISE: 2 conjunct(s)`
* `[cut] R.CRUISE: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] L.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (73 ms)
* cover `CRUISE_L`: λ = 3/2, budget 3, admissible ['CRUISE'], flags {'CRUISE': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=3 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CRUISE: 2 conjunct(s); R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `acc_tune_lag`

* family: ACC under sensor spoofing / retune; scenario: model-refinement; dims L/R 2/2; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `94d932b57d84`
* `relcert`: **CERTIFIED** (154 ms); `[prune] acc_tune_lag: [CRUISE->DISENGAGE]`; NO_PRUNE: **DECLINED** (359 ms); NO_CUT: **CERTIFIED** (141 ms); NO_IMPLIED_CUT: **CERTIFIED** (164 ms); domains: uniform
* `[cut] R.CRUISE: 2 conjunct(s)`
* `[cut] R.DISENGAGE: 1 conjunct(s)`
* `[cut-x] R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape`
* `[admissible] CRUISE_L: [CRUISE]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (88 ms)
* cover `CRUISE_L`: λ = 3/2, budget 3, admissible ['CRUISE'], flags {'CRUISE': 'j----', 'DISENGAGE': '-----'}, kinds ['base', 'joint'], path modes ['CRUISE'], branching 0, right-only False
    * from `CRUISE`: `CRUISE:joint(B=3)->[CRUISE@2, CRUISE@2]; CRUISE:joint(B=2)->[CRUISE@1, CRUISE@1]; CRUISE:base(B=1)`
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=3 via CRUISE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CRUISE->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (R.CRUISE: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.CRUISE: v <= 40.0 kind=closure entry=weakening route=shape; R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `acc_tune_modes`

* family: ACC under sensor spoofing / retune; scenario: degraded-controller; dims L/R 1/1; modes L/R 1/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `79594af327d8`
* `relcert`: **CERTIFIED** (271 ms); `[prune] acc_tune_modes: [NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE]`; NO_PRUNE: **DECLINED** (1157 ms); NO_CUT: **DECLINED** (1074 ms); NO_IMPLIED_CUT: **CERTIFIED** (263 ms); domains: uniform
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
* cells: **M1** yes: CRUISE λ=3/2 (affine dynamics); **M2** yes: CRUISE B=3 via COMFORT/NORMAL/SPORT; **M3** yes: CRUISE branch=2; **M4** yes: pruned NORMAL->DISENGAGE, COMFORT->DISENGAGE, SPORT->DISENGAGE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.CRUISE: 2 conjunct(s); R.NORMAL: 2 conjunct(s); R.COMFORT: 2 conjunct(s); R.SPORT: 2 conjunct(s); R.DISENGAGE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.DISENGAGE: v <= 20.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `arm_plateau_crit`

* family: Arm, leading reference; scenario: degraded-controller; dims L/R 2/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `c18aaa9e713a`
* `relcert`: **CERTIFIED** (268 ms); `[prune] arm_plateau_crit: []`; NO_PRUNE: **CERTIFIED** (215 ms); NO_CUT: **DECLINED** (298 ms); NO_IMPLIED_CUT: **CERTIFIED** (200 ms); domains: uniform
* `[cut] L.Accelerate: 1 conjunct(s)`
* `[cut] R.ApproachA: 1 conjunct(s)`
* `[cut] R.ApproachB: 1 conjunct(s)`
* `[cut] R.ApproachC: 1 conjunct(s)`
* `[cut] R.Hold: 2 conjunct(s)`
* `[cut-x] L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB`
* `[cut-x] R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen`
* `[admissible] Accelerate_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `[admissible] Brake_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (96 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': '-r-dd', 'ApproachC': '-rrdd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn', 'repoStatic'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:repoStatic(B=1,postJ)->[Hold@1]; Hold:base(B=1)`
    * from `ApproachB`: `ApproachB:repoStatic(B=2,preJ)->[ApproachC@2]; ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': '---dd', 'ApproachC': '-rrdd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn', 'repoStatic'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:repoStatic(B=1,postJ)->[Hold@1]; Hold:base(B=1)`
    * from `ApproachB`: `ApproachB:repoDyn(B=2,preJ)->[ApproachC@2]; ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/Hold +RO, Brake B=2 via ApproachA/Hold +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.Accelerate: 1 conjunct(s); R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachC: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.Accelerate: v <= 0.355 kind=closure entry=weakening route=diB; R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED

### `arm_plateau_pd`

* family: Arm, leading reference; scenario: model-refinement; dims L/R 2/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `def6b7955d37`
* `relcert`: **CERTIFIED** (205 ms); `[prune] arm_plateau_pd: []`; NO_PRUNE: **CERTIFIED** (212 ms); NO_CUT: **DECLINED** (323 ms); NO_IMPLIED_CUT: **CERTIFIED** (174 ms); domains: uniform
* `[cut] R.ApproachA: 1 conjunct(s)`
* `[cut] R.ApproachB: 1 conjunct(s)`
* `[cut] R.ApproachC: 1 conjunct(s)`
* `[cut] R.Hold: 2 conjunct(s)`
* `[cut-x] R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen`
* `[admissible] Accelerate_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `[admissible] Brake_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (52 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': '-r-dd', 'ApproachC': '-rrdd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn', 'repoStatic'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:repoStatic(B=1,postJ)->[Hold@1]; Hold:base(B=1)`
    * from `ApproachB`: `ApproachB:repoStatic(B=2,preJ)->[ApproachC@2]; ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': '---dd', 'ApproachC': '-rrdd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn', 'repoStatic'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:repoStatic(B=1,postJ)->[Hold@1]; Hold:base(B=1)`
    * from `ApproachB`: `ApproachB:repoDyn(B=2,preJ)->[ApproachC@2]; ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/Hold +RO, Brake B=2 via ApproachA/Hold +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachC: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED

### `arm_plateau_slow`

* family: Arm, leading reference; scenario: degraded-actuator; dims L/R 2/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `7dd19466c6dd`
* `relcert`: **CERTIFIED** (212 ms); `[prune] arm_plateau_slow: []`; NO_PRUNE: **CERTIFIED** (200 ms); NO_CUT: **DECLINED** (359 ms); NO_IMPLIED_CUT: **CERTIFIED** (191 ms); domains: uniform
* `[cut] R.ApproachA: 1 conjunct(s)`
* `[cut] R.ApproachB: 1 conjunct(s)`
* `[cut] R.ApproachC: 1 conjunct(s)`
* `[cut] R.Hold: 2 conjunct(s)`
* `[cut-x] R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen`
* `[admissible] Accelerate_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `[admissible] Brake_L: [ApproachA, ApproachB, ApproachC, Hold]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (54 ms)
* cover `Accelerate_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': '-r-dd', 'ApproachC': '-rrdd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn', 'repoStatic'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:repoStatic(B=1,postJ)->[Hold@1]; Hold:base(B=1)`
    * from `ApproachB`: `ApproachB:repoStatic(B=2,preJ)->[ApproachC@2]; ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cover `Brake_L`: λ = 1, budget 2, admissible ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], flags {'ApproachA': 'j--dd', 'ApproachB': '---dd', 'ApproachC': '-rrdd', 'Hold': 'jrrdd'}, kinds ['base', 'joint', 'repoDyn', 'repoStatic'], path modes ['ApproachA', 'ApproachB', 'ApproachC', 'Hold'], branching 1, right-only True
    * from `ApproachA`: `ApproachA:joint(B=2)->[ApproachA@1, ApproachB@1, ApproachA@1]; ApproachA:base(B=1); ApproachB:repoDyn(B=1,postJ)->[ApproachC@1]; ApproachC:repoStatic(B=1,postJ)->[Hold@1]; Hold:base(B=1)`
    * from `ApproachB`: `ApproachB:repoDyn(B=2,preJ)->[ApproachC@2]; ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `ApproachC`: `ApproachC:repoStatic(B=2,preJ)->[Hold@2]; Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
    * from `Hold`: `Hold:joint(B=2)->[Hold@1, Hold@1]; Hold:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: Accelerate B=2 via ApproachA/Hold +RO, Brake B=2 via ApproachA/Hold +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: R.ApproachA: 1 conjunct(s); R.ApproachB: 1 conjunct(s); R.ApproachC: 1 conjunct(s); R.Hold: 2 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.Hold: theta <= 1.15 kind=closure entry=weakening route=frozen) but NO_IMPLIED=CERTIFIED

### `charger_bias_estimator`

* family: Battery charger; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9811cf7515aa`
* `relcert`: **CERTIFIED** (302 ms); `[prune] charger_bias_estimator: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (1002 ms); NO_CUT: **CERTIFIED** (311 ms); NO_IMPLIED_CUT: **CERTIFIED** (286 ms); domains: per-mode
* `[cut] L.BULK: 2 conjunct(s)`
* `[cut] L.ABSORB: 2 conjunct(s)`
* `[cut] L.FULL: 1 conjunct(s)`
* `[cut] R.BULK: 2 conjunct(s)`
* `[cut] R.ABSORB: 2 conjunct(s)`
* `[cut] R.FULL: 1 conjunct(s)`
* `[cut] R.FAULT: 1 conjunct(s)`
* `[cut-x] L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape`
* `[admissible] BULK_L: [BULK, ABSORB]`
* `[admissible] ABSORB_L: [BULK, ABSORB, FULL]`
* `[admissible] FULL_L: [ABSORB, FULL]`
* `--handoff`: 5/5 checked, 0 passed, failing 0->1, 0->0, 1->2, 1->1, 2->2, VACUOUS (identical rows) (0 ms)
* cover `BULK_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB'], flags {'BULK': 'j----', 'ABSORB': 'j----', 'FULL': 'j--dd', 'FAULT': '-----'}, kinds ['base', 'joint'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only False
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB@1, BULK@1]; BULK:base(B=1); ABSORB:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
* cover `ABSORB_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB', 'FULL'], flags {'BULK': 'j----', 'ABSORB': 'j----', 'FULL': 'j--dd', 'FAULT': 'j----'}, kinds ['base', 'joint'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only False
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB@1, BULK@1]; BULK:base(B=1); ABSORB:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FULL_L`: λ = 1, budget 2, admissible ['ABSORB', 'FULL'], flags {'BULK': 'j--dd', 'ABSORB': 'j----', 'FULL': 'j--dd', 'FAULT': 'j----'}, kinds ['base', 'joint'], path modes ['ABSORB', 'FULL'], branching 1, right-only False
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: BULK B=2 via ABSORB/BULK, ABSORB B=2 via ABSORB/BULK/FULL, FULL B=2 via ABSORB/FULL; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `charger_fast_setpoints`

* family: Battery charger; scenario: degraded-controller; dims L/R 1/1; modes L/R 3/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `a4fc327fbdea`
* `relcert`: **CERTIFIED** (164 ms); `[prune] charger_fast_setpoints: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (470 ms); NO_CUT: **DECLINED** (507 ms); NO_IMPLIED_CUT: **DECLINED** (549 ms); domains: uniform
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
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (99 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** yes: BULK B=2 via ABSORB/FULL +RO, ABSORB B=2 via ABSORB/FULL +RO, FULL B=2 via ABSORB/FULL; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 90.0 kind=implied-contraction entry=rational route=shape; R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape; NO_IMPLIED=DECLINED

### `charger_fast_tapers`

* family: Battery charger; scenario: degraded-controller; dims L/R 1/1; modes L/R 3/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `956f8ffbe687`
* `relcert`: **CERTIFIED** (205 ms); `[prune] charger_fast_tapers: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (535 ms); NO_CUT: **DECLINED** (555 ms); NO_IMPLIED_CUT: **CERTIFIED** (256 ms); domains: uniform
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
* cells: **M1** no (λ=1 everywhere); **M2** yes: BULK B=2 via FULL +RO, ABSORB B=2 via ABSORB_FAST/ABSORB_SLOW/BULK/FULL, FULL B=2 via ABSORB_FAST/ABSORB_SLOW/FULL; **M3** yes: ABSORB branch=2; **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB_SLOW: 2 conjunct(s); R.ABSORB_FAST: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_SLOW: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB_FAST: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `charger_fast_thermal`

* family: Battery charger; scenario: degraded-controller; dims L/R 2/2; modes L/R 3/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `948a91cf0fff`
* `relcert`: **CERTIFIED** (528 ms); `[prune] charger_fast_thermal: [BULK->FAULT]`; NO_PRUNE: **DECLINED** (1756 ms); NO_CUT: **CERTIFIED** (506 ms); NO_IMPLIED_CUT: **CERTIFIED** (502 ms); domains: per-mode
* `[cut] L.BULK: 2 conjunct(s)`
* `[cut] L.ABSORB: 2 conjunct(s)`
* `[cut] L.FULL: 1 conjunct(s)`
* `[cut] R.BULK: 2 conjunct(s)`
* `[cut] R.ABSORB: 2 conjunct(s)`
* `[cut] R.FULL: 1 conjunct(s)`
* `[cut] R.FAULT: 1 conjunct(s)`
* `[cut-x] L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape`
* `[admissible] BULK_L: [BULK, ABSORB]`
* `[admissible] ABSORB_L: [BULK, ABSORB, FULL]`
* `[admissible] FULL_L: [ABSORB, FULL]`
* `--handoff`: 5/5 checked, 0 passed, failing 0->1, 0->0, 1->2, 1->1, 2->2, VACUOUS (identical rows) (0 ms)
* cover `BULK_L`: λ = 5/4, budget 3, admissible ['BULK', 'ABSORB'], flags {'BULK': 'j----', 'ABSORB': 'j----', 'FULL': 'j--dd', 'FAULT': '-----'}, kinds ['base', 'joint'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only False
    * from `BULK`: `BULK:joint(B=3)->[BULK@2, ABSORB@2, BULK@2]; BULK:joint(B=2)->[BULK@1, ABSORB@1, BULK@1]; BULK:base(B=1); ABSORB:base(B=1); ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; FULL:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=3)->[ABSORB@2, FULL@2, ABSORB@2]; ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1); FULL:joint(B=2)->[FULL@1, FULL@1]`
* cover `ABSORB_L`: λ = 1, budget 2, admissible ['BULK', 'ABSORB', 'FULL'], flags {'BULK': 'j----', 'ABSORB': 'j----', 'FULL': 'j----', 'FAULT': 'j----'}, kinds ['base', 'joint'], path modes ['ABSORB', 'BULK', 'FULL'], branching 1, right-only False
    * from `BULK`: `BULK:joint(B=2)->[BULK@1, ABSORB@1, BULK@1]; BULK:base(B=1); ABSORB:base(B=1)`
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cover `FULL_L`: λ = 1, budget 2, admissible ['ABSORB', 'FULL'], flags {'BULK': 'j--dd', 'ABSORB': 'j----', 'FULL': 'j----', 'FAULT': 'j----'}, kinds ['base', 'joint'], path modes ['ABSORB', 'FULL'], branching 1, right-only False
    * from `ABSORB`: `ABSORB:joint(B=2)->[ABSORB@1, FULL@1, ABSORB@1]; ABSORB:base(B=1); FULL:base(B=1)`
    * from `FULL`: `FULL:joint(B=2)->[FULL@1, FULL@1]; FULL:base(B=1)`
* cells: **M1** yes: BULK λ=5/4 (affine dynamics); **M2** yes: BULK B=3 via ABSORB/BULK/FULL, ABSORB B=2 via ABSORB/BULK/FULL, FULL B=2 via ABSORB/FULL; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned BULK->FAULT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.BULK: 2 conjunct(s); L.ABSORB: 2 conjunct(s); L.FULL: 1 conjunct(s); R.BULK: 2 conjunct(s); R.ABSORB: 2 conjunct(s); R.FULL: 1 conjunct(s); R.FAULT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; L.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.BULK: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.ABSORB: x <= 100.0 kind=implied-contraction entry=rational route=shape; R.FAULT: x <= 10.0 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `heater_cycle`

* family: Heater cycle; scenario: degraded-actuator; dims L/R 1/1; modes L/R 2/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `db11c540c5dd`
* `relcert`: **CERTIFIED** (146 ms); `[prune] heater_cycle: []`; NO_PRUNE: **CERTIFIED** (124 ms); NO_CUT: **CERTIFIED** (189 ms); NO_IMPLIED_CUT: **CERTIFIED** (188 ms); domains: per-mode
* `[cut] L.HEAT: 1 conjunct(s)`
* `[cut] L.OFF: 1 conjunct(s)`
* `[cut] R.HEAT: 1 conjunct(s)`
* `[cut] R.OFF: 1 conjunct(s)`
* `[cut-x] L.HEAT: T <= 90.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] L.OFF: T >= 20.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.HEAT: T <= 90.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.OFF: T >= 20.0 kind=implied-contraction entry=rational route=shape`
* `[admissible] HEAT_L: [HEAT, OFF]`
* `[admissible] OFF_L: [HEAT, OFF]`
* `--handoff`: 4/4 checked, 0 passed, failing 0->1, 0->0, 1->0, 1->1, VACUOUS (identical rows) (0 ms)
* cover `HEAT_L`: λ = 1, budget 2, admissible ['HEAT', 'OFF'], flags {'HEAT': 'j----', 'OFF': 'j----'}, kinds ['base', 'joint'], path modes ['HEAT', 'OFF'], branching 1, right-only False
    * from `HEAT`: `HEAT:joint(B=2)->[HEAT@1, OFF@1, HEAT@1]; HEAT:base(B=1); OFF:base(B=1)`
    * from `OFF`: `OFF:joint(B=2)->[OFF@1, HEAT@1, OFF@1]; OFF:base(B=1); HEAT:base(B=1)`
* cover `OFF_L`: λ = 1, budget 2, admissible ['HEAT', 'OFF'], flags {'HEAT': 'j----', 'OFF': 'j----'}, kinds ['base', 'joint'], path modes ['HEAT', 'OFF'], branching 1, right-only False
    * from `HEAT`: `HEAT:joint(B=2)->[HEAT@1, OFF@1, HEAT@1]; HEAT:base(B=1); OFF:base(B=1)`
    * from `OFF`: `OFF:joint(B=2)->[OFF@1, HEAT@1, OFF@1]; OFF:base(B=1); HEAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: HEAT B=2 via HEAT/OFF, OFF B=2 via HEAT/OFF; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.HEAT: 1 conjunct(s); L.OFF: 1 conjunct(s); R.HEAT: 1 conjunct(s); R.OFF: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.HEAT: T <= 90.0 kind=implied-contraction entry=rational route=shape; L.OFF: T >= 20.0 kind=implied-contraction entry=rational route=shape; R.HEAT: T <= 90.0 kind=implied-contraction entry=rational route=shape; R.OFF: T >= 20.0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED

### `match_multi_rate`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 2/2; modes L/R 4/2; εL/εR 0.3/0.3; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `8ea18edaad94`
* `relcert`: **CERTIFIED** (327 ms); `[prune] match_multi_rate: [DRIVE->STALL]`; NO_PRUNE: **DECLINED** (293 ms); NO_CUT: **CERTIFIED** (325 ms); NO_IMPLIED_CUT: **CERTIFIED** (291 ms); domains: uniform
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
* `--handoff`: 8/8 checked, 8 passed, failing -, VACUOUS (identical rows) (56 ms)
* cover `FAST_L`: λ = 3, budget 3, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': '-----'}, kinds ['base', 'joint'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:joint(B=3)->[DRIVE@2, DRIVE@2]; DRIVE:joint(B=2)->[DRIVE@1, DRIVE@1]; DRIVE:base(B=1)`
* cover `MEDIUM_L`: λ = 2, budget 2, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': 'j----'}, kinds ['base', 'joint'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:joint(B=2)->[DRIVE@1, DRIVE@1]; DRIVE:base(B=1)`
* cover `SLOW_L`: λ = 1, budget 1, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': 'j----'}, kinds ['base'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:base(B=1)`
* cover `RESET_L`: λ = 1, budget 1, admissible ['DRIVE'], flags {'DRIVE': 'j--dd', 'STALL': '-----'}, kinds ['base'], path modes ['DRIVE'], branching 0, right-only False
    * from `DRIVE`: `DRIVE:base(B=1)`
* cells: **M1** yes: FAST λ=3, MEDIUM λ=2 (affine dynamics); **M2** yes: FAST B=3 via DRIVE, MEDIUM B=2 via DRIVE; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned DRIVE->STALL; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.FAST: 2 conjunct(s); L.MEDIUM: 2 conjunct(s); L.SLOW: 2 conjunct(s); L.RESET: 2 conjunct(s); R.DRIVE: 2 conjunct(s); R.STALL: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.FAST: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.MEDIUM: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.SLOW: v <= 1.0 kind=implied-contraction entry=rational route=shape; L.RESET: v <= 1.0 kind=closure entry=weakening route=shape; L.RESET: v >= 0.1 kind=implied-contraction entry=rational route=shape; R.STALL: v <= 0.2 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `platoon_delay_band`

* family: Platoon follower, delayed link; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/3; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `8e29907d7c0c`
* `relcert`: **CERTIFIED** (198 ms); `[prune] platoon_delay_band: [FOLLOW->BRAKE]`; NO_PRUNE: **DECLINED** (867 ms); NO_CUT: **DECLINED** (755 ms); NO_IMPLIED_CUT: **DECLINED** (778 ms); domains: uniform
* `[cut] L.FOLLOW: 2 conjunct(s)`
* `[cut] L.CATCH: 1 conjunct(s)`
* `[cut] R.FOLLOW: 2 conjunct(s)`
* `[cut] R.CATCH: 1 conjunct(s)`
* `[cut-x] L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] L.CATCH: g >= 29.0 kind=implied-contraction entry=rational route=shape`
* `[cut-x] R.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape`
* `[cut-x] R.CATCH: g >= 30.0 kind=implied-contraction entry=rational route=shape`
* `[admissible] FOLLOW_L: [FOLLOW, CATCH]`
* `[admissible] CATCH_L: [FOLLOW, CATCH]`
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (36 ms)
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j----', 'CATCH': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cover `CATCH_L`: λ = 1, budget 2, admissible ['FOLLOW', 'CATCH'], flags {'FOLLOW': 'j----', 'CATCH': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['CATCH', 'FOLLOW'], branching 1, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, CATCH@1, FOLLOW@1]; FOLLOW:base(B=1); CATCH:base(B=1)`
    * from `CATCH`: `CATCH:joint(B=2)->[CATCH@1, FOLLOW@1, CATCH@1]; CATCH:base(B=1); FOLLOW:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via CATCH/FOLLOW, CATCH B=2 via CATCH/FOLLOW; **M3** no (max non-self successors at a joint step = 1); **M4** yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.FOLLOW: 2 conjunct(s); L.CATCH: 1 conjunct(s); R.FOLLOW: 2 conjunct(s); R.CATCH: 1 conjunct(s); NO_CUT=DECLINED; **M6+** yes: L.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; L.CATCH: g >= 29.0 kind=implied-contraction entry=rational route=shape; R.FOLLOW: g <= 40.0 kind=closure entry=weakening route=shape; R.CATCH: g >= 30.0 kind=implied-contraction entry=rational route=shape; NO_IMPLIED=DECLINED

### `platoon_delay_profiles`

* family: Platoon follower, delayed link; scenario: sensor-attack; dims L/R 1/1; modes L/R 2/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `7f9adf16040b`
* `relcert`: **CERTIFIED** (215 ms); `[prune] platoon_delay_profiles: [FOLLOW->BRAKE]`; NO_PRUNE: **DECLINED** (1130 ms); NO_CUT: **DECLINED** (926 ms); NO_IMPLIED_CUT: **CERTIFIED** (265 ms); domains: uniform
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
* `--handoff`: 4/4 checked, 4 passed, failing -, VACUOUS (identical rows) (100 ms)
* cover `FOLLOW_L`: λ = 1, budget 2, admissible ['FOLLOW', 'GENTLE', 'ASSERTIVE'], flags {'FOLLOW': 'j----', 'GENTLE': 'j----', 'ASSERTIVE': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['ASSERTIVE', 'FOLLOW', 'GENTLE'], branching 2, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, GENTLE@1, ASSERTIVE@1, FOLLOW@1]; FOLLOW:base(B=1); GENTLE:base(B=1); ASSERTIVE:base(B=1)`
    * from `GENTLE`: `GENTLE:joint(B=2)->[GENTLE@1, FOLLOW@1, GENTLE@1]; GENTLE:base(B=1); FOLLOW:base(B=1)`
    * from `ASSERTIVE`: `ASSERTIVE:joint(B=2)->[ASSERTIVE@1, FOLLOW@1, ASSERTIVE@1]; ASSERTIVE:base(B=1); FOLLOW:base(B=1)`
* cover `GENTLE_L`: λ = 1, budget 2, admissible ['FOLLOW', 'GENTLE', 'ASSERTIVE'], flags {'FOLLOW': 'j----', 'GENTLE': 'j----', 'ASSERTIVE': 'j----', 'BRAKE': '-----'}, kinds ['base', 'joint'], path modes ['ASSERTIVE', 'FOLLOW', 'GENTLE'], branching 2, right-only False
    * from `FOLLOW`: `FOLLOW:joint(B=2)->[FOLLOW@1, GENTLE@1, ASSERTIVE@1, FOLLOW@1]; FOLLOW:base(B=1); GENTLE:base(B=1); ASSERTIVE:base(B=1)`
    * from `GENTLE`: `GENTLE:joint(B=2)->[GENTLE@1, FOLLOW@1, GENTLE@1]; GENTLE:base(B=1); FOLLOW:base(B=1)`
    * from `ASSERTIVE`: `ASSERTIVE:joint(B=2)->[ASSERTIVE@1, FOLLOW@1, ASSERTIVE@1]; ASSERTIVE:base(B=1); FOLLOW:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** yes: FOLLOW B=2 via ASSERTIVE/FOLLOW/GENTLE, GENTLE B=2 via ASSERTIVE/FOLLOW/GENTLE; **M3** yes: FOLLOW branch=2, GENTLE branch=2; **M4** yes: pruned FOLLOW->BRAKE; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** yes: L.FOLLOW: 2 conjunct(s); L.GENTLE: 1 conjunct(s); R.FOLLOW: 2 conjunct(s); R.GENTLE: 1 conjunct(s); R.ASSERTIVE: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (L.GENTLE: g >= 29.0 kind=implied-contraction entry=rational route=shape; R.GENTLE: g >= 30.0 kind=implied-contraction entry=rational route=shape; R.ASSERTIVE: g >= 30.0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED

### `quad_light_airframe_20`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 1/1; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9a7b144d8b09`
* `relcert`: **CERTIFIED** (246 ms); `[prune] quad_light_airframe_20: [CLIMB->LIMIT]`; NO_PRUNE: **DECLINED** (691 ms); NO_CUT: **CERTIFIED** (162 ms); NO_IMPLIED_CUT: **CERTIFIED** (249 ms); domains: uniform
* `[cut] L.CLIMB: 2 conjunct(s)`
* `[cut] R.CLIMB: 2 conjunct(s)`
* `[cut] R.LIMIT: 1 conjunct(s)`
* `[cut-x] R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (97 ms)
* cover `CLIMB_L`: λ = 7/4, budget 4, admissible ['CLIMB'], flags {'CLIMB': 'j----', 'LIMIT': '-----'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=4)->[CLIMB@3, CLIMB@3]; CLIMB:joint(B=3)->[CLIMB@2, CLIMB@2]; CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=7/4 (polynomial dynamics); **M2** yes: CLIMB B=4 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s); R.LIMIT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED

### `quad_light_airframe_40`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 1/1; modes L/R 1/2; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `606712d64538`
* `relcert`: **CERTIFIED** (285 ms); `[prune] quad_light_airframe_40: [CLIMB->LIMIT]`; NO_PRUNE: **DECLINED** (619 ms); NO_CUT: **CERTIFIED** (283 ms); NO_IMPLIED_CUT: **CERTIFIED** (219 ms); domains: uniform
* `[cut] L.CLIMB: 2 conjunct(s)`
* `[cut] R.CLIMB: 2 conjunct(s)`
* `[cut] R.LIMIT: 1 conjunct(s)`
* `[cut-x] R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (36 ms)
* cover `CLIMB_L`: λ = 9/4, budget 5, admissible ['CLIMB'], flags {'CLIMB': 'j----', 'LIMIT': '-----'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=5)->[CLIMB@4, CLIMB@4]; CLIMB:joint(B=4)->[CLIMB@3, CLIMB@3]; CLIMB:joint(B=3)->[CLIMB@2, CLIMB@2]; CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=9/4 (polynomial dynamics); **M2** yes: CLIMB B=5 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** yes: pruned CLIMB->LIMIT; NO_PRUNE=DECLINED; **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 2 conjunct(s); R.CLIMB: 2 conjunct(s); R.LIMIT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (R.LIMIT: w >= 0 kind=implied-contraction entry=rational route=shape) but NO_IMPLIED=CERTIFIED

### `quad_light_lag`

* family: Quadrotor climb, lighter airframe; scenario: model-refinement; dims L/R 2/2; modes L/R 1/1; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape linear; rows identical: True; normalized md5 `e06b31eeeac1`
* `relcert`: **CERTIFIED** (112 ms); `[prune] quad_light_lag: []`; NO_PRUNE: **CERTIFIED** (146 ms); NO_CUT: **CERTIFIED** (123 ms); NO_IMPLIED_CUT: **CERTIFIED** (141 ms); domains: uniform
* `[cut] L.CLIMB: 3 conjunct(s)`
* `[cut] R.CLIMB: 2 conjunct(s)`
* `[admissible] CLIMB_L: [CLIMB]`
* `--handoff`: 1/1 checked, 1 passed, failing -, VACUOUS (identical rows) (94 ms)
* cover `CLIMB_L`: λ = 7/4, budget 4, admissible ['CLIMB'], flags {'CLIMB': 'j----'}, kinds ['base', 'joint'], path modes ['CLIMB'], branching 0, right-only False
    * from `CLIMB`: `CLIMB:joint(B=4)->[CLIMB@3, CLIMB@3]; CLIMB:joint(B=3)->[CLIMB@2, CLIMB@2]; CLIMB:joint(B=2)->[CLIMB@1, CLIMB@1]; CLIMB:base(B=1)`
* cells: **M1** yes: CLIMB λ=7/4 (polynomial dynamics); **M2** yes: CLIMB B=4 via CLIMB; **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.CLIMB: 3 conjunct(s); R.CLIMB: 2 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `refinement_ladder_rover_rung1_2to3`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 3/2; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `a55b07fd35ff`
* `relcert`: **CERTIFIED** (207 ms); `[prune] refinement_ladder_rover_rung1_2to3: []`; NO_PRUNE: **CERTIFIED** (214 ms); NO_CUT: **DECLINED** (856 ms); NO_IMPLIED_CUT: **CERTIFIED** (212 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (36 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `refinement_ladder_rover_rung2_3to6`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `1b9081f9b111`
* `relcert`: **CERTIFIED** (658 ms); `[prune] refinement_ladder_rover_rung2_3to6: []`; NO_PRUNE: **CERTIFIED** (717 ms); NO_CUT: **CERTIFIED** (621 ms); NO_IMPLIED_CUT: **CERTIFIED** (584 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (91 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '-----', 'MODER': '-----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `refinement_ladder_rover_rung2_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 4/4; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.001, 6.0]; invariant shape linear; rows identical: True; normalized md5 `238c061085aa`
* `relcert`: **CERTIFIED** (266 ms); `[prune] refinement_ladder_rover_rung2_6dof: []`; NO_PRUNE: **CERTIFIED** (208 ms); NO_CUT: **CERTIFIED** (161 ms); NO_IMPLIED_CUT: **CERTIFIED** (320 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (43 ms)
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
* cells: **M1** yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `refinement_ladder_rover_rung2b_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.001, 6.0]; invariant shape linear; rows identical: True; normalized md5 `b1ae87a5c1db`
* `relcert`: **CERTIFIED** (226 ms); `[prune] refinement_ladder_rover_rung2b_6dof: []`; NO_PRUNE: **CERTIFIED** (206 ms); NO_CUT: **CERTIFIED** (189 ms); NO_IMPLIED_CUT: **CERTIFIED** (228 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (96 ms)
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
* cells: **M1** yes: STEEP λ=1001/1000, MODER λ=1001/1000, FLAT λ=1001/1000 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `refinement_ladder_rover_rung2c_6dof`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `724831255028`
* `relcert`: **CERTIFIED** (1346 ms); `[prune] refinement_ladder_rover_rung2c_6dof: []`; NO_PRUNE: **CERTIFIED** (1340 ms); NO_CUT: **CERTIFIED** (1211 ms); NO_IMPLIED_CUT: **CERTIFIED** (1185 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP]`
* `[admissible] MODER_L: [MODER]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (87 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP'], flags {'STEEP': 'j----', 'MODER': '-----', 'FLAT': '-----'}, kinds ['base'], path modes ['STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER'], flags {'STEEP': '-----', 'MODER': 'j----', 'FLAT': '-----'}, kinds ['base'], path modes ['MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '-----', 'MODER': '-----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `refinement_ladder_rover_rung3_6to8`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape quadratic; rows identical: True; normalized md5 `848946e281b6`
* `relcert`: **CERTIFIED** (2877 ms); `[prune] refinement_ladder_rover_rung3_6to8: []`; NO_PRUNE: **CERTIFIED** (2930 ms); NO_CUT: **DECLINED** (3050 ms); NO_IMPLIED_CUT: **CERTIFIED** (2857 ms); domains: uniform
* `[cut] L.STEEP: 2 conjunct(s)`
* `[cut] L.MODER: 2 conjunct(s)`
* `[cut] L.FLAT: 2 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (83 ms)
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
* cells: **M1** yes: STEEP λ=9/4, MODER λ=9/4, FLAT λ=9/4 (polynomial dynamics); **M2** yes: STEEP B=3 via FLAT/MODER/STEEP, MODER B=3 via FLAT/MODER +RO, FLAT B=3 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 2 conjunct(s); L.MODER: 2 conjunct(s); L.FLAT: 2 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `refinement_ladder_rover_rung4_8to12`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `9f1c06c6a52c`
* `relcert`: **CERTIFIED** (983 ms); `[prune] refinement_ladder_rover_rung4_8to12: []`; NO_PRUNE: **CERTIFIED** (934 ms); NO_CUT: **DECLINED** (1261 ms); NO_IMPLIED_CUT: **CERTIFIED** (854 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (49 ms)
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
* cells: **M1** yes: STEEP λ=17/10, MODER λ=17/10, FLAT λ=17/10 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `rover3tier_rung12`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/3; modes L/R 2/2; εL/εR 1.0/0.3; λ ∈ [1.0, 6.0]; invariant shape conjunctive+linear; rows identical: False; normalized md5 `4b65ad8433aa`
* `relcert`: **CERTIFIED** (247 ms); `[prune] rover3tier_rung12: []`; NO_PRUNE: **CERTIFIED** (193 ms); NO_CUT: **CERTIFIED** (231 ms); NO_IMPLIED_CUT: **CERTIFIED** (167 ms); domains: uniform
* `[cut] R.ACCEL: 1 conjunct(s)`
* `[cut] R.COAST: 1 conjunct(s)`
* `[admissible] ACCEL_L: [ACCEL, COAST]`
* `[admissible] COAST_L: [ACCEL, COAST]`
* `--handoff`: 4/4 checked, 4 passed, failing -, non-vacuous (90 ms)
* cover `ACCEL_L`: λ = 7/4, budget 6, admissible ['ACCEL', 'COAST'], flags {'ACCEL': 'j--dd', 'COAST': 'j--dd'}, kinds ['base', 'joint'], path modes ['ACCEL', 'COAST'], branching 1, right-only False
    * from `ACCEL`: `ACCEL:joint(B=6)->[ACCEL@5, COAST@5, ACCEL@5]; ACCEL:joint(B=5)->[ACCEL@4, COAST@4, ACCEL@4]; ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:base(B=1); COAST:base(B=1); COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=5)->[COAST@4, ACCEL@4, COAST@4]`
    * from `COAST`: `COAST:joint(B=6)->[COAST@5, ACCEL@5, COAST@5]; COAST:joint(B=5)->[COAST@4, ACCEL@4, COAST@4]; COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:base(B=1); ACCEL:base(B=1); ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=5)->[ACCEL@4, COAST@4, ACCEL@4]`
* cover `COAST_L`: λ = 1, budget 4, admissible ['ACCEL', 'COAST'], flags {'ACCEL': 'j--dd', 'COAST': 'j--dd'}, kinds ['base', 'joint'], path modes ['ACCEL', 'COAST'], branching 1, right-only False
    * from `ACCEL`: `ACCEL:joint(B=4)->[ACCEL@3, COAST@3, ACCEL@3]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]; ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:base(B=1); COAST:base(B=1); COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]`
    * from `COAST`: `COAST:joint(B=4)->[COAST@3, ACCEL@3, COAST@3]; COAST:joint(B=3)->[COAST@2, ACCEL@2, COAST@2]; COAST:joint(B=2)->[COAST@1, ACCEL@1, COAST@1]; COAST:base(B=1); ACCEL:base(B=1); ACCEL:joint(B=2)->[ACCEL@1, COAST@1, ACCEL@1]; ACCEL:joint(B=3)->[ACCEL@2, COAST@2, ACCEL@2]`
* cells: **M1** yes: ACCEL λ=7/4 (affine dynamics); **M2** yes: ACCEL B=6 via ACCEL/COAST, COAST B=4 via ACCEL/COAST; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** yes: 4/4 handoffs unsat, rows differ; **M6** vacuous: cuts kept (R.ACCEL: 1 conjunct(s); R.COAST: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `rover_dof_terrain_rung1`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 3/3; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `0b323c73c8d9`
* `relcert`: **CERTIFIED** (296 ms); `[prune] rover_dof_terrain_rung1: []`; NO_PRUNE: **CERTIFIED** (295 ms); NO_CUT: **DECLINED** (853 ms); NO_IMPLIED_CUT: **CERTIFIED** (181 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (67 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `rover_dof_terrain_rung2`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 6/6; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `05e0216a07ff`
* `relcert`: **CERTIFIED** (357 ms); `[prune] rover_dof_terrain_rung2: []`; NO_PRUNE: **CERTIFIED** (369 ms); NO_CUT: **DECLINED** (952 ms); NO_IMPLIED_CUT: **CERTIFIED** (283 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (97 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `rover_dof_terrain_rung3`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `8d149b9ca736`
* `relcert`: **CERTIFIED** (370 ms); `[prune] rover_dof_terrain_rung3: []`; NO_PRUNE: **CERTIFIED** (302 ms); NO_CUT: **DECLINED** (1063 ms); NO_IMPLIED_CUT: **CERTIFIED** (234 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (69 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `rover_dof_terrain_rung3_8d`

* family: Terrain/position ladder; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: True; normalized md5 `675e7eb3a84a`
* `relcert`: **CERTIFIED** (363 ms); `[prune] rover_dof_terrain_rung3_8d: []`; NO_PRUNE: **CERTIFIED** (350 ms); NO_CUT: **DECLINED** (939 ms); NO_IMPLIED_CUT: **CERTIFIED** (207 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (37 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `rover_patrol_refine`

* family: Rover patrol (zones); scenario: model-refinement; dims L/R 3/3; modes L/R 4/4; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `e196ff320ae8`
* `relcert`: **CERTIFIED** (2547 ms); `[prune] rover_patrol_refine: []`; NO_PRUNE: **CERTIFIED** (2640 ms); NO_CUT: **DECLINED** (1220 ms); NO_IMPLIED_CUT: **CERTIFIED** (2610 ms); domains: uniform
* `[cut] L.SLOW: 1 conjunct(s)`
* `[cut] L.MEDIUM_ECO: 1 conjunct(s)`
* `[cut] L.MEDIUM_BRISK: 1 conjunct(s)`
* `[cut] L.FAST: 1 conjunct(s)`
* `[cut] R.SLOW: 3 conjunct(s)`
* `[cut] R.MEDIUM_ECO: 3 conjunct(s)`
* `[cut] R.MEDIUM_BRISK: 3 conjunct(s)`
* `[cut] R.FAST: 3 conjunct(s)`
* `[admissible] SLOW_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_ECO_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] MEDIUM_BRISK_L: [SLOW, MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `[admissible] FAST_L: [MEDIUM_ECO, MEDIUM_BRISK, FAST]`
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (96 ms)
* cover `SLOW_L`: λ = 7/2, budget 7, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': 'j--dd', 'MEDIUM_ECO': 'j--dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd'}, kinds ['base', 'joint'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 2, right-only False
    * from `SLOW`: `SLOW:joint(B=7)->[SLOW@6, MEDIUM_ECO@6, MEDIUM_BRISK@6, SLOW@6]; SLOW:joint(B=6)->[SLOW@5, MEDIUM_ECO@5, MEDIUM_BRISK@5, SLOW@5]; SLOW:joint(B=5)->[SLOW@4, MEDIUM_ECO@4, MEDIUM_BRISK@4, SLOW@4]; SLOW:joint(B=4)->[SLOW@3, MEDIUM_ECO@3, MEDIUM_BRISK@3, SLOW@3]; SLOW:joint(B=3)->[SLOW@2, MEDIUM_ECO@2, MEDIUM_BRISK@2, SLOW@2]; SLOW:joint(B=2)->[SLOW@1, MEDIUM_ECO@1, MEDIUM_BRISK@1, SLOW@1]; SLOW:base(B=1); MEDIUM_ECO:base(B=1); MEDIUM_BRISK:base(B=1); MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; FAST:base(B=1); MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_ECO:joint(B=6)->[MEDIUM_ECO@5, FAST@5, MEDIUM_ECO@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; MEDIUM_BRISK:joint(B=6)->[MEDIUM_BRISK@5, FAST@5, MEDIUM_BRISK@5]`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=7)->[MEDIUM_ECO@6, FAST@6, MEDIUM_ECO@6]; MEDIUM_ECO:joint(B=6)->[MEDIUM_ECO@5, FAST@5, MEDIUM_ECO@5]; MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=7)->[MEDIUM_BRISK@6, FAST@6, MEDIUM_BRISK@6]; MEDIUM_BRISK:joint(B=6)->[MEDIUM_BRISK@5, FAST@5, MEDIUM_BRISK@5]; MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]`
    * from `FAST`: `FAST:joint(B=7)->[FAST@6, FAST@6]; FAST:joint(B=6)->[FAST@5, FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_ECO_L`: λ = 7/2, budget 7, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': 'j--dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=7,preJ)->[MEDIUM_ECO@7, MEDIUM_BRISK@7]; MEDIUM_ECO:joint(B=7)->[MEDIUM_ECO@6, FAST@6, MEDIUM_ECO@6]; MEDIUM_ECO:joint(B=6)->[MEDIUM_ECO@5, FAST@5, MEDIUM_ECO@5]; MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]; MEDIUM_BRISK:joint(B=7)->[MEDIUM_BRISK@6, FAST@6, MEDIUM_BRISK@6]; MEDIUM_BRISK:joint(B=6)->[MEDIUM_BRISK@5, FAST@5, MEDIUM_BRISK@5]; MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=7)->[MEDIUM_ECO@6, FAST@6, MEDIUM_ECO@6]; MEDIUM_ECO:joint(B=6)->[MEDIUM_ECO@5, FAST@5, MEDIUM_ECO@5]; MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=7)->[MEDIUM_BRISK@6, FAST@6, MEDIUM_BRISK@6]; MEDIUM_BRISK:joint(B=6)->[MEDIUM_BRISK@5, FAST@5, MEDIUM_BRISK@5]; MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]`
    * from `FAST`: `FAST:joint(B=7)->[FAST@6, FAST@6]; FAST:joint(B=6)->[FAST@5, FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `MEDIUM_BRISK_L`: λ = 7/2, budget 7, admissible ['SLOW', 'MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': 'j--dd', 'MEDIUM_BRISK': 'j--dd', 'FAST': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO', 'SLOW'], branching 1, right-only True
    * from `SLOW`: `SLOW:repoDyn(B=7,preJ)->[MEDIUM_ECO@7, MEDIUM_BRISK@7]; MEDIUM_ECO:joint(B=7)->[MEDIUM_ECO@6, FAST@6, MEDIUM_ECO@6]; MEDIUM_ECO:joint(B=6)->[MEDIUM_ECO@5, FAST@5, MEDIUM_ECO@5]; MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]; MEDIUM_BRISK:joint(B=7)->[MEDIUM_BRISK@6, FAST@6, MEDIUM_BRISK@6]; MEDIUM_BRISK:joint(B=6)->[MEDIUM_BRISK@5, FAST@5, MEDIUM_BRISK@5]; MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1)`
    * from `MEDIUM_ECO`: `MEDIUM_ECO:joint(B=7)->[MEDIUM_ECO@6, FAST@6, MEDIUM_ECO@6]; MEDIUM_ECO:joint(B=6)->[MEDIUM_ECO@5, FAST@5, MEDIUM_ECO@5]; MEDIUM_ECO:joint(B=5)->[MEDIUM_ECO@4, FAST@4, MEDIUM_ECO@4]; MEDIUM_ECO:joint(B=4)->[MEDIUM_ECO@3, FAST@3, MEDIUM_ECO@3]; MEDIUM_ECO:joint(B=3)->[MEDIUM_ECO@2, FAST@2, MEDIUM_ECO@2]; MEDIUM_ECO:joint(B=2)->[MEDIUM_ECO@1, FAST@1, MEDIUM_ECO@1]; MEDIUM_ECO:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:joint(B=7)->[MEDIUM_BRISK@6, FAST@6, MEDIUM_BRISK@6]; MEDIUM_BRISK:joint(B=6)->[MEDIUM_BRISK@5, FAST@5, MEDIUM_BRISK@5]; MEDIUM_BRISK:joint(B=5)->[MEDIUM_BRISK@4, FAST@4, MEDIUM_BRISK@4]; MEDIUM_BRISK:joint(B=4)->[MEDIUM_BRISK@3, FAST@3, MEDIUM_BRISK@3]; MEDIUM_BRISK:joint(B=3)->[MEDIUM_BRISK@2, FAST@2, MEDIUM_BRISK@2]; MEDIUM_BRISK:joint(B=2)->[MEDIUM_BRISK@1, FAST@1, MEDIUM_BRISK@1]; MEDIUM_BRISK:base(B=1); FAST:base(B=1); FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=6)->[FAST@5, FAST@5]`
    * from `FAST`: `FAST:joint(B=7)->[FAST@6, FAST@6]; FAST:joint(B=6)->[FAST@5, FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cover `FAST_L`: λ = 7/2, budget 7, admissible ['MEDIUM_ECO', 'MEDIUM_BRISK', 'FAST'], flags {'SLOW': '---dd', 'MEDIUM_ECO': '---dd', 'MEDIUM_BRISK': '---dd', 'FAST': 'j--dd'}, kinds ['base', 'joint', 'repoDyn'], path modes ['FAST', 'MEDIUM_BRISK', 'MEDIUM_ECO'], branching 0, right-only True
    * from `MEDIUM_ECO`: `MEDIUM_ECO:repoDyn(B=7,preJ)->[FAST@7]; FAST:joint(B=7)->[FAST@6, FAST@6]; FAST:joint(B=6)->[FAST@5, FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `MEDIUM_BRISK`: `MEDIUM_BRISK:repoDyn(B=7,preJ)->[FAST@7]; FAST:joint(B=7)->[FAST@6, FAST@6]; FAST:joint(B=6)->[FAST@5, FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
    * from `FAST`: `FAST:joint(B=7)->[FAST@6, FAST@6]; FAST:joint(B=6)->[FAST@5, FAST@5]; FAST:joint(B=5)->[FAST@4, FAST@4]; FAST:joint(B=4)->[FAST@3, FAST@3]; FAST:joint(B=3)->[FAST@2, FAST@2]; FAST:joint(B=2)->[FAST@1, FAST@1]; FAST:base(B=1)`
* cells: **M1** yes: SLOW λ=7/2, MEDIUM_ECO λ=7/2, MEDIUM_BRISK λ=7/2, FAST λ=7/2 (affine dynamics); **M2** yes: SLOW B=7 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=7 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, MEDIUM_BRISK B=7 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, FAST B=7 via FAST +RO; **M3** yes: SLOW branch=2; **M4** no (nothing pruned); **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.SLOW: 1 conjunct(s); L.MEDIUM_ECO: 1 conjunct(s); L.MEDIUM_BRISK: 1 conjunct(s); L.FAST: 1 conjunct(s); R.SLOW: 3 conjunct(s); R.MEDIUM_ECO: 3 conjunct(s); R.MEDIUM_BRISK: 3 conjunct(s); R.FAST: 3 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `rover_patrol_zones`

* family: Rover patrol (zones); scenario: degraded-actuator; dims L/R 2/2; modes L/R 4/5; εL/εR 2.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `088224fb0842`
* `relcert`: **CERTIFIED** (456 ms); `[prune] rover_patrol_zones: [SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL, FAST->STALL]`; NO_PRUNE: **CERTIFIED** (429 ms); NO_CUT: **DECLINED** (1156 ms); NO_IMPLIED_CUT: **CERTIFIED** (413 ms); domains: uniform
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
* `--handoff`: 10/10 checked, 10 passed, failing -, non-vacuous (88 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** yes: SLOW B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO/SLOW, MEDIUM_ECO B=2 via FAST/MEDIUM_BRISK/MEDIUM_ECO +RO, MEDIUM_BRISK B=2 via FAST/MEDIUM_BRISK +RO, FAST B=2 via FAST +RO; **M3** yes: SLOW branch=2; **M4** vacuous: pruned SLOW->STALL, MEDIUM_ECO->STALL, MEDIUM_BRISK->STALL, FAST->STALL but NO_PRUNE=CERTIFIED; **M5** yes: 10/10 handoffs unsat, rows differ; **M6** yes: L.SLOW: 3 conjunct(s); L.MEDIUM_ECO: 3 conjunct(s); L.MEDIUM_BRISK: 3 conjunct(s); L.FAST: 3 conjunct(s); R.SLOW: 3 conjunct(s); R.MEDIUM_ECO: 3 conjunct(s); R.MEDIUM_BRISK: 3 conjunct(s); R.FAST: 3 conjunct(s); R.STALL: 1 conjunct(s); NO_CUT=DECLINED; **M6+** vacuous: widened atoms kept (R.STALL: v <= 0.2 kind=closure entry=weakening route=shape) but NO_IMPLIED=CERTIFIED

### `story1_attdist_rung_a_6to8`

* family: Story ladders; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape conjunctive; rows identical: False; normalized md5 `34c422712676`
* `relcert`: **CERTIFIED** (20200 ms); `[prune] story1_attdist_rung_a_6to8: []`; NO_PRUNE: **CERTIFIED** (20659 ms); NO_CUT: **CERTIFIED** (1621 ms); NO_IMPLIED_CUT: **CERTIFIED** (20115 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (16 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `story1_attdist_rung_b_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: False; normalized md5 `d5633710e2d8`
* `relcert`: **CERTIFIED** (418 ms); `[prune] story1_attdist_rung_b_12dof: []`; NO_PRUNE: **CERTIFIED** (460 ms); NO_CUT: **CERTIFIED** (387 ms); NO_IMPLIED_CUT: **CERTIFIED** (373 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (86 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `story2_lateral_rung_a_8dof`

* family: Story ladders; scenario: model-refinement; dims L/R 8/8; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `cb0ec6031104`
* `relcert`: **CERTIFIED** (1154 ms); `[prune] story2_lateral_rung_a_8dof: []`; NO_PRUNE: **CERTIFIED** (1090 ms); NO_CUT: **CERTIFIED** (919 ms); NO_IMPLIED_CUT: **CERTIFIED** (1025 ms); domains: uniform
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `story2_lateral_rung_b_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape conjunctive; rows identical: True; normalized md5 `5e62b7ea6ff9`
* `relcert`: **CERTIFIED** (1494 ms); `[prune] story2_lateral_rung_b_12dof: []`; NO_PRUNE: **CERTIFIED** (1491 ms); NO_CUT: **CERTIFIED** (1240 ms); NO_IMPLIED_CUT: **CERTIFIED** (1305 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [MODER, FLAT]`
* `[admissible] FLAT_L: [FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (88 ms)
* cover `STEEP_L`: λ = 1, budget 1, admissible ['STEEP', 'MODER', 'FLAT'], flags {'STEEP': 'j----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER', 'STEEP'], branching 0, right-only False
    * from `STEEP`: `STEEP:base(B=1)`
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `MODER_L`: λ = 1, budget 1, admissible ['MODER', 'FLAT'], flags {'STEEP': '-----', 'MODER': 'j----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT', 'MODER'], branching 0, right-only False
    * from `MODER`: `MODER:base(B=1)`
    * from `FLAT`: `FLAT:base(B=1)`
* cover `FLAT_L`: λ = 1, budget 1, admissible ['FLAT'], flags {'STEEP': '-----', 'MODER': '-----', 'FLAT': 'j----'}, kinds ['base'], path modes ['FLAT'], branching 0, right-only False
    * from `FLAT`: `FLAT:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `story3_rollover_base_12dof`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 6.0]; invariant shape quadratic; rows identical: True; normalized md5 `cf68fbeeef5c`
* `relcert`: **CERTIFIED** (1228 ms); `[prune] story3_rollover_base_12dof: []`; NO_PRUNE: **CERTIFIED** (1167 ms); NO_CUT: **DECLINED** (2872 ms); NO_IMPLIED_CUT: **CERTIFIED** (1164 ms); domains: uniform
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
* cells: **M1** yes: STEEP λ=5/4, MODER λ=5/4, FLAT λ=5/4 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `story3_rollover_ladder_rung_a`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape quadratic; rows identical: True; normalized md5 `af17da3f1b89`
* `relcert`: **CERTIFIED** (832 ms); `[prune] story3_rollover_ladder_rung_a: []`; NO_PRUNE: **CERTIFIED** (827 ms); NO_CUT: **DECLINED** (2295 ms); NO_IMPLIED_CUT: **CERTIFIED** (790 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 2 conjunct(s)`
* `[cut] R.MODER: 2 conjunct(s)`
* `[cut] R.FLAT: 2 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, VACUOUS (identical rows) (18 ms)
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
* cells: **M1** yes: STEEP λ=27/20, MODER λ=27/20, FLAT λ=27/20 (polynomial dynamics); **M2** yes: STEEP B=2 via FLAT/MODER/STEEP, MODER B=2 via FLAT/MODER +RO, FLAT B=2 via FLAT +RO; **M3** no (max non-self successors at a joint step = 1); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** yes: L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 2 conjunct(s); R.MODER: 2 conjunct(s); R.FLAT: 2 conjunct(s); NO_CUT=DECLINED; **M6+** no (no widened atom kept)

### `story3_rollover_ladder_rung_b`

* family: Story ladders; scenario: model-refinement; dims L/R 12/12; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 8.0]; invariant shape quadratic; rows identical: False; normalized md5 `b61f93e310af`
* `relcert`: **CERTIFIED** (4860 ms); `[prune] story3_rollover_ladder_rung_b: []`; NO_PRUNE: **CERTIFIED** (4891 ms); NO_CUT: **CERTIFIED** (2850 ms); NO_IMPLIED_CUT: **CERTIFIED** (4803 ms); domains: uniform
* `[cut] L.STEEP: 1 conjunct(s)`
* `[cut] L.MODER: 1 conjunct(s)`
* `[cut] L.FLAT: 1 conjunct(s)`
* `[cut] R.STEEP: 1 conjunct(s)`
* `[cut] R.MODER: 1 conjunct(s)`
* `[cut] R.FLAT: 1 conjunct(s)`
* `[admissible] STEEP_L: [STEEP, MODER, FLAT]`
* `[admissible] MODER_L: [STEEP, MODER, FLAT]`
* `[admissible] FLAT_L: [STEEP, MODER, FLAT]`
* `--handoff`: 5/5 checked, 5 passed, failing -, non-vacuous (85 ms)
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
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** yes: 5/5 handoffs unsat, rows differ; **M6** vacuous: cuts kept (L.STEEP: 1 conjunct(s); L.MODER: 1 conjunct(s); L.FLAT: 1 conjunct(s); R.STEEP: 1 conjunct(s); R.MODER: 1 conjunct(s); R.FLAT: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** no (no widened atom kept)

### `watertank`

* family: Watertank; scenario: sensor-attack; dims L/R 1/1; modes L/R 3/3; εL/εR 1.0/1.0; λ ∈ [1.0, 10.0]; invariant shape linear; rows identical: True; normalized md5 `a301828a2f41`
* `relcert`: **CERTIFIED** (226 ms); `[prune] watertank: []`; NO_PRUNE: **CERTIFIED** (228 ms); NO_CUT: **CERTIFIED** (194 ms); NO_IMPLIED_CUT: **CERTIFIED** (206 ms); domains: uniform
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
* `--handoff`: 6/6 checked, 6 passed, failing -, VACUOUS (identical rows) (93 ms)
* cover `Low_L`: λ = 1, budget 1, admissible ['Low', 'Mid', 'High'], flags {'Low': 'j----', 'Mid': 'jr-dd', 'High': '-r---'}, kinds ['base', 'repoStatic'], path modes ['High', 'Low', 'Mid'], branching 0, right-only True
    * from `Low`: `Low:base(B=1)`
    * from `Mid`: `Mid:base(B=1)`
    * from `High`: `High:repoStatic(B=1,preJ)->[Mid@1]; Mid:base(B=1)`
* cover `Mid_L`: λ = 1, budget 1, admissible ['Mid', 'High'], flags {'Low': '-----', 'Mid': 'j--dd', 'High': '-r---'}, kinds ['base', 'repoStatic'], path modes ['High', 'Mid'], branching 0, right-only True
    * from `Mid`: `Mid:base(B=1)`
    * from `High`: `High:repoStatic(B=1,preJ)->[Mid@1]; Mid:base(B=1)`
* cover `High_L`: λ = 1, budget 1, admissible ['High'], flags {'Low': 'j----', 'Mid': 'j--dd', 'High': 'j----'}, kinds ['base'], path modes ['High'], branching 0, right-only False
    * from `High`: `High:base(B=1)`
* cells: **M1** no (λ=1 everywhere); **M2** no (single segment, RO used); **M3** no (max non-self successors at a joint step = 0); **M4** no (nothing pruned); **M5** no (rows identical; handoff vacuous); **M6** vacuous: cuts kept (L.Low: 1 conjunct(s); L.Mid: 1 conjunct(s); L.High: 1 conjunct(s); R.Low: 1 conjunct(s); R.Mid: 1 conjunct(s); R.High: 1 conjunct(s)) but NO_CUT=CERTIFIED; **M6+** vacuous: widened atoms kept (L.High: x <= 22.45 kind=closure entry=weakening route=diB; R.High: x <= 22.45 kind=closure entry=weakening route=diB) but NO_IMPLIED=CERTIFIED

## 10. Re-running

    RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/suite_v2/*/input.txt   # 42 CERTIFIED
    scripts/suite_v2_matrix.py --md /tmp/suite_v2.md --json /tmp/suite_v2.json
    scripts/suite_v2_matrix.py --only acc_tune_modes,rover_patrol_zones  # a subset
    RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --emit-cuts benchmarks/suite_v2/charger_fast_setpoints/input.txt c
                                                                 # the legacy literal `c` and the extended `cX`

The script needs the `relcert` binary (`lake build relcert`) and Z3 on the path; it
takes about four minutes for the whole suite (six tool runs per benchmark). Without
`RELCERT_IMPLIED_CUT=1`, `charger_fast_setpoints` and `platoon_delay_band` are
DECLINED (the M6+ members); everything else certifies either way.

## 11. Not done here

* The Lean mechanization of `suite_v2` (instances, pins, coverage constants, the
  `--run-verdicts` rows): a separate task. It needs two generalizations of the lift the
  tool side now exercises: the O1 case split of the extended cut certificate
  (`EvolStrengtheningX`: membership / weakening / rational / Z3 entries — §7, and
  `docs/PAPER-MAPPING.md` §2c) and per-mode evolve domains (`UniformEvol.lean`, the
  handoff runner's `uniformEvolveR`). Until then the kernel column still reads
  `suite_uniform`, and `relcert --check-quick benchmarks/suite_uniform/*/input.txt`
  is unchanged.
* The L6 domain-corner incompleteness (`heater_cycle` at exactly the band width).
* The two kept-replaceable files (`match_multi_rate`, `rover3tier_rung12`) and the 19
  kept files carry no `# scenario:` line; the script maps their kind.
* The paper's Table 1 / §6 rewrite from §8.

## 12. Regression record for `suite_uniform` (pass 2, binary of `7c5a11c`)

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
