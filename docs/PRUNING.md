# Non-connection pruning — the suite exhibit (2026-10-08, branch `pruning-suite`)

Status: landed 2026-10-08. One benchmark (`match_multi_rate`) exercises the paper's
Section 4.3 device for real; thirteen candidates were tried by runs and dropped, each for
a reason recorded in §3. Tool: `RELCERT_NO_PRUNE=1` switch, right-only variables in the
lowering, a shared query builder, a fifth verdict phase with declared counts. Lean: the
modal theorem over the enlarged automaton, the pruned edge's Theorem 2 instance, both
in `ModalBattery` (52 theorems).

## 1. What the device is, and what the tool does

Paper Section 4.3 (Theorem 2, non-connection certificate): a declared right edge
`mR → mSuc` may be dropped from the cover's all-successors obligation when the
successor's guard is a single strict threshold `{g > 0}` on one variable and two Z3
checks are both `unsat`:

| check | query (`Trusted/NonConnQuery.lean`) | meaning |
|---|---|---|
| source | `guard_mR ∧ evolve_mR ∧ cut_mR ∧ g > 0` | no entry state of the source mode is on the far side of the threshold |
| barrier | `evolve_mR ∧ cut_mR ∧ g = 0 ∧ Lie_R g ≥ 0` | on the threshold, the source mode's right flow (left frozen, λ = 1) moves `g` strictly down |

`cut_mR` is the source mode's checked cut (`OracleAPI.checkedCut`). The tool
(`OracleAPI.nonConnPrune`, now a thin caller of the shared builder) prunes only when
both verdicts are definitive `unsat`; anything else keeps the edge. Soundness is
`Checker/NonConn.lean` `nonconn_sound` (dL-lean `DI_strict`): from every source state,
no state the flow reaches satisfies the guard. The pruned edges are part of the emitted
certificate (`CoverEmitE.pruned`), the kernel replay (`BenchCoverReplay`, `decide`)
drops them from `retainedSucc`, and the structural graph gives an unpruned edge to an
uncertified mode the out-of-range sentinel, so an uncertified declared successor fails
the cover unless pruned.

Before this branch no emitted cover had a pruned edge: `RELCERT_DEBUG=1` printed
`[prune] <name>: []` for all 40 benchmarks, and the one exhibit, `shield_unreachable`,
did not even lower (its right side declares a variable `w` the left lacks).

## 2. Design rules for a modified benchmark (all five must hold; §3 shows the runs)

(a) **Additive only.** One right mode (an emergency / fallback sink with a short
physical story in the file header), one edge from an existing right mode to it. No
existing mode's dynamics, guard, evolve, successor list (beyond the appended successor),
epsilon, λ range or invariant row changes. The new mode is a RIGHT mode, so the
(left-keyed) invariant rows are untouched.

(b) **Prunable threshold.** The new mode's guard is a single strict threshold on one
variable, FEASIBLE inside the source's evolve domain, with no source-guard state on its
far side and the source flow moving the variable strictly away from it. A zero
derivative does not prune (route B is strict); a flow toward the threshold does not
prune. Use the far side: a drop-back threshold below a monotone-increasing variable,
or a threshold beyond a contraction set point.

(c) **Uncertifiable if entered.** The new mode breaks the invariant flow-wise and is a
sink (self-loop only), so the cover genuinely fails without pruning.

(d) **Reached.** The cover must pass through the source mode with budget remaining
(budget ≥ 2 at a joint step), otherwise the new edge is never an obligation and pruning
never fires. Verified with `RELCERT_DEBUG=1`.

(e) **Reproducible.** `RELCERT_NO_PRUNE=1 relcert <input>` DECLINED, `relcert <input>`
CERTIFIED with the pruned edge printed (`[prune] <name>: [src->tgt]`, stderr).

**(f) The obstacle the runs surfaced — admissible initial modes.** The paper (Section
4.3, and `OracleAPI.admissible`) requires every ADMISSIBLE initial right mode to cover:
`q₀` is admissible for `m_L` when `guard_{m_L} ∧ guard_{q₀} ∧ φ_inv` is satisfiable.
An emergency mode whose threshold region is compatible with some left guard under the
invariant is therefore an admissible START, and a sink that is uncertifiable (c) cannot
cover from the start — pruning its incoming edge changes nothing about that
obligation, and the benchmark declines with or without pruning. So a modified
benchmark also needs: **the emergency guard is excluded by `guard_{m_L} ∧ φ_inv` for
every left mode.** With the suite's one-sided invariants `x_L ≤ x_R + d` (every row of
every benchmark bounds a right variable from BELOW given the left), only a threshold
`x_R < T` with `T ≤ min_{m_L} (lower bound of x_L in guard_{m_L}) − d` is excluded,
and (b) needs `T` above the right evolve floor. That is satisfiable only where the
invariant offset is `0` and the left guards keep the variable strictly above the right
evolve floor: `match_multi_rate` (`v_L ≤ v_R`, every left guard `v_L ≥ 0.2`, right
evolve `v ≥ 0`). Everywhere else the emergency mode is admissible (`[admissible]`
lines in §3) or no feasible far-side threshold exists.

## 3. Candidates, decided by runs

Each candidate was run as a scratch copy (repo files untouched except the one adopted)
with the emergency mode appended and the edge declared, `RELCERT_DEBUG=1`, with and
without `RELCERT_NO_PRUNE=1`. `[prune]` is the tool's line; `[admissible]` the
admissible initial right modes of the first left window.

| benchmark | source → new mode (guard; ode) | cover budget at source | pruned? | admissible start? | pruning ON | pruning OFF | verdict on the candidate |
|---|---|---|---|---|---|---|---|
| **`match_multi_rate`** | `DRIVE → STALL` (`v < 0.2`; `v' = −2v, s' = v`) | FAST 3, MEDIUM 2 | yes `[DRIVE->STALL]` | no (`[DRIVE]` at every window) | **CERTIFIED** | **DECLINED** | **adopted** |
| `watertank` | `Mid → EmergencyDrain` (`x < 5`; `x' = −3`) | 1 at every window | yes `[Mid->EmergencyDrain]` | yes (`Low_L: [Low, Mid, High, EmergencyDrain]`) | DECLINED | DECLINED | dropped: (d) single-segment covers, and (f) |
| `rover3tier_M1` | `COAST → OVERSPEED` (`v > 0.9`; `v' = −3`) | 4 | yes | yes | ERROR (time budget) | DECLINED | dropped: (f) |
| `arm_chain_rung1` | `Return → FAULT` (`θ > 0.95`; `θ' = −0.5`) | 3, 2 | yes | yes | DECLINED | DECLINED | dropped: (f) (`θ_L ≤ θ_R + 0.4`, `θ_L ≥ 0` allows any `θ_R ≥ −0.4`) |
| `arm_chain_rung2` | `Return → FAULT` (same) | 2, 2 | yes | yes | DECLINED | DECLINED | dropped: (f) |
| `arm_fidelity_low` | `Return → FAULT` (same) | 5 | yes | yes | DECLINED | DECLINED | dropped: (f) |
| `endurance_gain_M1` | `FLAT → OVERSPEED` (`v > 0.75`; `v' = −2`) | 2, 2, 3 | yes | yes (`s` is unbounded in the row) | DECLINED | ERROR (time budget) | dropped: (f) |
| `endurance_orderlift_1to2` | `FLAT → OVERSPEED` (`v > 0.75`) | 4 | yes | yes | DECLINED | ERROR (time budget) | dropped: (f) |
| `endurance_orderlift_2to3` | `FLAT → OVERSPEED` (`v > 0.8`) | 2, 2, 3 | yes | yes | DECLINED | ERROR (time budget) | dropped: (f) |
| `rover3tier_rung12` | `ACCEL → STALL` (`v < 0.25`; `v' = −2`) | 6, 4 | yes | yes (`a_L` unbounded in the ACCEL row's functional) | ERROR (time budget) | ERROR (time budget) | dropped: (f) |
| `rover_terrain_M1` | `SMOOTH → OVERSPEED` (`v > 1.3`; `v' = −3`) | 2, 2, 3 | yes | yes (`s` unbounded) | DECLINED | ERROR (time budget) | dropped: (f) |
| `rover_tier_r1` | `Cruise → STALL` (`v < 0.28`; `v' = −2`) | 5 | yes | yes | CERTIFIED | CERTIFIED | dropped: (c) fails — the row `s_L ≤ s_R + 0.5` is preserved by ANY right mode at λ ≥ 5.6 (`s' = v ≥ 0.25`), so STALL is jointly certifiable |
| `attitude_rate` | `TRACK → OVERRATE` (`p > 1.18`; `p' = −3`) | 2 | yes | yes | DECLINED | DECLINED | dropped: (f) |
| `rover_drag` | `Track → OVERSPEED` (`vx > 1.3`; `vx' = −2`) | 1 | yes | no (`vx_R − vx_L ≤ 0.05` bounds `vx_R` above) | CERTIFIED | CERTIFIED | dropped: (d) single-segment cover; pruning never fires |
| `rover3_M1`, `rover_coupled`, `rover_position` | (`Drive → BRAKE`, `vx < 0.2` tried) | 2 | — | — | — | — | dropped: (b) — no feasible far-side threshold: the right modes hold or raise `vx`, whose evolve floor `0.25` is the lowest right guard floor, and `px` is unbounded in every right guard; the tried threshold lies outside the evolve domain |

Not tried (budget 1 at every window, so (d) cannot hold): `arm_chain_rung3`,
`arm_fidelity_mid`, `robot_braking`, `rover_4d_box`, the four `rover_dof_terrain_*`,
`refinement_ladder_rover_rung1_2to3`, `rung2_3to6`, `rung2c_6dof`, `story1_*`,
`story2_*`, `story3_rollover_ladder_rung_b`. Left alone per the task (8–12 dof, rebuild
cost): `rung3_6to8`, `rung4_8to12`, `rover_attitude_cone_12dof`, `story3_rollover_base`,
`story3_rollover_ladder_rung_a`, `rung2_6dof`, `rung2b_6dof` — all of whose rows are
`v_L ≤ v_R` with a left `STEEP` guard floor `v_L ≥ 0` equal to the right evolve floor, so
(f) excludes them too.

**Count: 1 modified (`match_multi_rate`), 13 tried and dropped, 20 not applicable.**
The target of a third of the suite is not reachable under rules (a)–(e) plus the paper's
admissibility of initial modes, because the suite's invariants are one-sided
left-leads-right bounds whose left guard floors coincide with the right evolve floors.

## 4. `match_multi_rate` — the exhibit

| item | value |
|---|---|
| new mode, story | `STALL`: the reasoning rover's drive controller declares a stall fallback — if the measured speed drops below 0.2 while in `DRIVE`, the drive is cut and the wheel speed decays (`v' = −2v`) while the odometer keeps integrating (`s' = v`); sink (`next = [STALL]`) |
| edge | `DRIVE → STALL` (appended to `DRIVE`'s `next`) |
| threshold | `v < 0.2` on the right `v`; feasible in `DRIVE`'s evolve (`0 ≤ v ≤ 1.15`); `DRIVE`'s guard `0.2 ≤ v ≤ 1` has no state below it; at `v = 0.2` the `DRIVE` field is `v' = 1 − v = 0.8 > 0` (strictly away) |
| uncertifiable if entered | `v_L ≤ v_R` breaks: the left `FAST` field `v' = 3(1 − v)` rises while `STALL` decays (route A/B/C all `sat`; the tool's `[FAST_L …] STALL=fail`) |
| source check (`sourceCheck`) | `UNSAT( v_R ≥ 0.2 ∧ v_R ≤ 1 ∧ s_R ≥ 0 ∧ v_R ≥ 0 ∧ v_R ≤ 1.15 ∧ cut(v_R ≥ 0.2 ∧ v_R ≤ 1) ∧ 0.2 − v_R > 0 )` — `unsat` |
| barrier check (`barrierCheck`) | `UNSAT( s_R ≥ 0 ∧ v_R ≥ 0 ∧ v_R ≤ 1.15 ∧ cut ∧ 0.2 − v_R = 0 ∧ Lie(0.2 − v_R) = −(1 − v_R) ≥ 0 )` — `unsat` |
| admissible starts | `[DRIVE]` for all four left windows (`v_L ≥ 0.2 ∧ v_L ≤ v_R ∧ v_R < 0.2` is unsatisfiable) |
| cover (unchanged) | FAST λ = 3 budget 3, MEDIUM λ = 2 budget 2, SLOW/RESET λ = 1 budget 1, all in-place at `DRIVE`; emitted `pruned = [("DRIVE", "STALL")]`, `STALL` row all-false (not a node) |
| `RELCERT_NO_PRUNE=1` | `match_multi_rate: DECLINED` — `FAST` at budget 3 and `MEDIUM` at budget 2 owe `STALL` at the decremented budget; it is not a node (no joint, static or dynamic certificate), so the sentinel index fails `decideCovered`; no λ in `[1, 6]` gives those windows a single-segment cover (`cover = εR/εL = 1` is tried first and fails to certify at `DRIVE` for `FAST`/`MEDIUM`) |
| pruning on | `match_multi_rate: CERTIFIED`, stderr `[prune] match_multi_rate: [DRIVE->STALL]` |
| Lean, Theorem 3 | `MatchMultiRatePruned.match_multi_rate_pruned` (`Instances/MatchMultiRatePruned.lean`): `rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody GrP mv) (canonInvM gM gsM ∧ envLR ∧ mvRegionR mv regionsP 2))`, `GrP` = the two-mode automaton with the edges `DRIVE→DRIVE`, `DRIVE→STALL`, `STALL→STALL`, `regionsP DRIVE = ⊤`, `regionsP STALL = ⊥`; hypotheses the base `VerdM 0..3`; axioms std 3 + `z3_unsat_sound` |
| Lean, Theorem 2 | `MatchMultiRatePruned.match_multi_rate_nonconn`: from `VerdNC` (the two queries above, pinned to the runner by `Verdicts/NonConnPins.lean`), every state the `DRIVE` right flow reaches from a `DRIVE` entry state has `v_R ≥ 0.2` (`…_nonconn'`); axioms std 3 + `z3_unsat_sound` |
| base theorem | `MatchMultiRateModal.match_multi_rate_modal` stands unchanged over the one-mode automaton `GrM` (its `GrM` is hand-listed, not read off the IR's mode count) |
| runner | phase 5 `== non-connection ==`: `UNSAT [source] match_multi_rate DRIVE -> STALL`, `UNSAT [barrier] …`; coverage `non-connection: 2/2`, `pruned edges: 1/1` |
| settling family | `match_multi_rateM` / `faithfulSettling` / `match_multi_rate_real` WITHDRAWN: the settling transcription requires a closed guard band on every right mode (`Faithful.bandSettling`), and `STALL`'s guard is a one-sided threshold by construction; extending the settling model class is new machinery and was not done (39 `*_real` theorems remain) |

### Where the pruned edge enters the proofs, and where it does not

* **Theorem 3 (modal).** It does not enter. The witness is the base instance's response
  (in-place `DRIVE` pieces), lifted to the enlarged automaton edge by edge
  (`Proofs/Encoding/SinkExtension.lean`, `Hmulti_sink_extend`); a `∃` run never has to
  take a declared edge. What the certificate changes is the STATEMENT: the plain
  `mvValid mv 2` bookkeeping would quantify over starts in `STALL`, from which no
  response exists (the right can only decay or stand still while a left window
  accelerates), so that statement is false; the honest statement carries the mode
  region `⊥` at `STALL` — the right is never in `STALL` — which is exactly what the
  non-connection certificate licenses for the only edge into it.
* **The kernel cover replay** (`BenchCoverReplay`, `decide`) is where the pruned edge
  does its work: `retainedSucc` drops it, so `decideCovered` accepts the FAST/MEDIUM
  covers; with the edge retained the sentinel target fails. The throughput instance
  (`Throughout/match_multi_rate.lean`, regenerated, byte-identical) carries the pruned
  flag in `realGraphOf` the same way; `CoverCertM` has no `pruneSound` field — the
  structural graph's edges have `⊤` guards, so `CoverCert.pruneSound` could not be
  stated against it, and `RightReach` along an unpruned `⊤`-guarded edge into a
  non-node only reaches `refl`.
* **Theorem 2** is stated and discharged separately (`match_multi_rate_nonconn`): the
  runner's two queries, pinned, through `nonconn_of_unsat` into `nonconn_sound`. It is
  the kernel-checked content of `CoverEmitE.pruned`, not a hypothesis of Theorem 3.

## 5. `shield_unreachable`

The lowering now accepts right-only variables (`Trusted/JointVars.lean`: the joint
variable list is the left list followed by the right-only names; a right-only variable
has left derivative `0` and appears in no left formula), so the benchmark runs:

```
$ ./.lake/build/bin/relcert benchmarks/suite_uniform/shield_unreachable/input.txt
shield_unreachable: DECLINED (262ms)
$ RELCERT_NO_PRUNE=1 ./.lake/build/bin/relcert benchmarks/suite_uniform/shield_unreachable/input.txt
  [prune] shield_unreachable: disabled (RELCERT_NO_PRUNE)
shield_unreachable: DECLINED (382ms)
```

It declines either way, for two independent reasons, both visible under
`RELCERT_DEBUG=1`: (i) `[prune] shield_unreachable: []` — `Shield`'s guard
`w ≥ 4 ∧ w < 4.95` is a closed compound band, outside the strict-scalar scope of the
certificate (`nonConnPrune` keeps the edge; the tool's scope note has said so since
the beginning), so `Cruise → Shield` is never pruned and `Shield=fail` at every λ;
(ii) `Shield` is an admissible initial right mode (`w` is free in the invariant
`v_L ≤ v_R + 0.5`), so even a prunable guard would leave a start in `Shield` to cover,
which it cannot. The model is not changed; the declared suite now expects it as the
one DECLINED input (`Coverage.expectedSuite`: 40 certified, 1 declined, 0 errors). Its
`--handoff` self-loop still reports `query did not lower` (that runner is untouched —
`Trusted/Handoff.lean` is upstream of the mode-keyed proofs); it is outside the emitted
suite as before.

## 6. Tool changes

* `Trusted/JointVars.lean` (new): `PProblem.jointVars`; used by `certifyWithData`,
  the `--emit-*` doors, `--emit-cuts`, the viability emitters. The emitted suite is
  unaffected (both sides declare the same variables).
* `Trusted/NonConnQuery.lean` (new): `guardTerm`, `queries`, `cutOfAtoms`,
  `rightCutAtoms` — the two pruning queries defined once; `nonConnPrune` calls
  `queries`.
* `Trusted/OracleAPI.lean`: `RELCERT_NO_PRUNE=1` (no query issued, every edge kept);
  `[prune] <name>: [...]` printed on stderr whenever an edge is pruned, and
  `[prune] <name>: disabled (RELCERT_NO_PRUNE)` under the switch; `[admissible]`
  per-window diagnostic under `RELCERT_DEBUG=1`.
* `Verdicts/RunNonConn.lean` (new): phase 5 of `--run-verdicts` / `--check-quick`;
  `Verdicts/Coverage.lean`: `expected.prunedEdges = 1`, `expected.nonconn = 2`,
  `expectedSuite` 40/1/0; `Verdicts/CoveragePins.lean`: `derivedPruned_eq_expected`,
  `nonconn_eq_two_pruned`, `benchCoverTable_names`, `prunedEdges_declared`,
  `prunedEdges_rebuild` (all `decide`); `Verdicts/NonConnPins.lean` (new): the
  runner's rebuilt pair for `DRIVE → STALL` IS the instance's `VerdNC` pair.
* `Main.lean`: phase 5 wired, `--help` lists the switches.
* `scripts/gen_throughout.py`, `scripts/gen_cover_replay.py`: repointed at the
  per-benchmark leaves (they read the pre-X0 monoliths and would have emitted empty
  batteries).

## 7. Totals

| quantity | before | after |
|---|---|---|
| benchmarks exercising a pruned edge | 0 | 1 |
| pruned edges in emitted covers / non-connection queries in `--run-verdicts` | 0 / 0 | 1 / 2 |
| declared coverage (watertank / cut / modal / handoff / non-connection) | 6 / 97 / 504 / 191 | 6 / 97 / 504 / 191 / 2 |
| suite tally (certified / declined / errors over 41 inputs) | 40 / 0 / 1 | 40 / 1 / 0 |
| theorems in `ModalBattery` | 50 | 52 (`+ match_multi_rate_pruned`, `+ match_multi_rate_nonconn`) |
| `*_real` settling theorems / `faithfulSettling` certificates | 40 / 40 | 39 / 39 |
| evolve-box faces in `BenchViability2` | 1085 | 1088 (`STALL`: `growth0`, `growth4`, `strict`) |

## 8. Re-running

    ./.lake/build/bin/relcert benchmarks/suite_uniform/match_multi_rate/input.txt
    RELCERT_NO_PRUNE=1 ./.lake/build/bin/relcert benchmarks/suite_uniform/match_multi_rate/input.txt
    ./.lake/build/bin/relcert --run-verdicts            # phase 5: non-connection, 2/2 and 1/1
    lake build RelCertifier.Instances.ModalBattery 2>&1 | grep -A3 "depends on axioms"

The scratch experiment driver (not committed) appended one mode and one edge to a copy
of each candidate and ran both settings with `RELCERT_DEBUG=1`; the rows of §3 are its
output.

## 9. Verification (2026-10-08, branch `pruning-suite`, Z3 4.15.1, warm tree)

`lake build` (warm; the rebuild touched the `match_multi_rate` column, the `OracleAPI`
cascade — `CutComposition`, the two `…Declared` leaves, `FaceBridge`,
`WatertankViability` — the settling aggregators, the runner/pin layer and the new
leaves): `Build completed successfully (8976 jobs)`, exit 0. `lake build relcert
relcert-test`: exit 0.

`./.lake/build/bin/relcert benchmarks/suite_uniform/match_multi_rate/input.txt` and the
switch:

```
$ ./.lake/build/bin/relcert benchmarks/suite_uniform/match_multi_rate/input.txt
  [prune] match_multi_rate: [DRIVE->STALL]
z3 = /opt/homebrew/bin/z3  (warm persistent session)
match_multi_rate: CERTIFIED (254ms)
errors=0

$ RELCERT_NO_PRUNE=1 ./.lake/build/bin/relcert benchmarks/suite_uniform/match_multi_rate/input.txt
  [prune] match_multi_rate: disabled (RELCERT_NO_PRUNE)
z3 = /opt/homebrew/bin/z3  (warm persistent session)
match_multi_rate: DECLINED (252ms)
errors=0
```

`RELCERT_DEBUG=1` on the same input (excerpt): `[admissible] FAST_L: [DRIVE]` (likewise
`MEDIUM_L`, `SLOW_L`, `RESET_L`), `[FAST_L λ=1 #comps=1] DRIVE=fail STALL=fail`,
`[FAST_L λ=3 #comps=1] DRIVE=pass STALL=fail`.

`./.lake/build/bin/relcert --check-quick benchmarks/suite_uniform/*/input.txt` (head of
check 1 shows `  [prune] match_multi_rate: [DRIVE->STALL]` and
`shield_unreachable: DECLINED (282ms)`; tail):

```
errors=0
  [suite] 40 certified, 1 declined, 0 error(s) — matches the declared suite
...
HANDOFF PHASE COMPLETE (0 declared failure(s), as expected)
== non-connection : 1 pruned edge(s), two queries each ==
  UNSAT [source]  match_multi_rate DRIVE -> STALL
  UNSAT [barrier]  match_multi_rate DRIVE -> STALL
NON-CONNECTION PHASE COMPLETE (1 edge(s))
  [coverage] watertank: 6/6 hypotheses discharged
  [coverage] cut probes: 97/97 hypotheses discharged
  [coverage] modal: 504/504 hypotheses discharged
  [coverage] handoff: 191/191 hypotheses discharged
  [coverage] non-connection: 2/2 hypotheses discharged
  [coverage] pruned edges: 1/1 hypotheses discharged

  suite:    PASS
  verdicts: PASS
QUICK CHECKS PASSED  (the kernel check is `lake build` — see --help)
```

`./.lake/build/bin/relcert --run-verdicts` (tail): the same five coverage lines and
`ALL HYPOTHESES DISCHARGED`, exit 0.

`BENCH_PATHS=<manifest of the 41 inputs> ./.lake/build/bin/relcert-test`: `[ir-drift] ok
all 40 IR literals match their files` … `ok watertank: 8× identical CERTIFIED`, `ok
declined benchmark: 8× identical verdict`, final line `ALL PASS` (no skips).

`./.lake/build/bin/relcert --handoff benchmarks/suite_uniform/*/input.txt`: 192
transitions over 41 inputs, 191 unsat; `match_multi_rate` 8/8 (vacuous, unchanged); the
documented `shield_unreachable` FAIL (`handoff query did not lower`), exit 1 by design.

Axiom audit (`lake env lean RelCertifier/Instances/ModalBattery.lean | grep -A3 "depends
on axioms"`): **52 theorems, 42 with `z3_unsat_sound`, 10 standard-three**, no
`sorryAx`, no `native_decide`, no other axiom. The two new lines:

```
'RelCertifier.MatchMultiRatePruned.match_multi_rate_pruned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 z3_unsat_sound]
'RelCertifier.MatchMultiRatePruned.match_multi_rate_nonconn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 z3_unsat_sound]
```

Stub grep (`grep -rn 'sorry\|admit\b\|native_decide' --include='*.lean' RelCertifier/
| grep -v Archive`): docstring prose only.

Pin bite test: a scratch file asserting `derivedPruned = 2` or `prunedEdges = []` by
`decide` fails to compile (2 errors), so the declared counts and the edge list cannot
be re-pointed silently; the runtime phase compares `2/2` and `1/1` through the same
`checkPhase` as the other four phases.

