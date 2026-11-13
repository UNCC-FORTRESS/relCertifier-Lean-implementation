# Per-row hypothesis slicing (`RELCERT_SLICE_HOPS`)

Branch `hyp-slicing`. A flow query of a row `g` (paper Definition 5, the Lie conditions of
Lemma 2) carries, as its domain, every hypothesis established so far: the evolve boxes of both
modes, the mode facts, and the rows of the earlier certification rounds. On wide models (the
CPS-QRC probe's rung files: 32 variables, 58 rows, 65 KB per query) Z3 answers `unknown` on
the full query inside the tool's budget while a slice of it (8 variables, 11 hypotheses) is
`unsat` in a fraction of a second. The knob keeps, per row, only the hypotheses near the row.

## What the knob does

`RELCERT_SLICE_HOPS=k` (a natural number; unset = today's behaviour, the printed queries are
byte-identical to `main`'s). For every joint flow query (`OracleAPI.checkSeg`) and every
right-only flow query (`OracleAPI.checkDynRepo`), with `H` the conjuncts of the query's domain:

* the goal variables are `vars(g) ∪ vars(Lie(g))` (`goalVars`; the Lie derivative's variables
  are read with zero products dropped, so a coordinate the row does not read is not a goal
  variable through its `0 * f_i` summand);
* a *row* is a conjunct of `H` reading two or more variables, a *box* one reading at most one;
* hop 0 keeps the rows whose variables intersect the goal variables; hop `j+1` adds the rows
  sharing a variable with a row kept at hop `j`;
* the boxes of every kept variable (the goal variables, the variables of the kept rows) are
  always kept; the goal part of the query (`g`, `Lie(g)`) is untouched.

The sliced domain keeps the `and` tree of the full one and replaces each dropped conjunct by
`true` in place (`sliceDom`, `Trusted/Slice.lean`), so it is a sub-conjunction leaf by leaf.
With the knob set the tool logs one line per query on stderr:

```
[slice hops=1] joint comp#37 BRAKE->BRAKE λ=1: vars 32->9 hyps 58->12 bytes 65012->8830
```

(full and sliced variable count of the route-A query, hypothesis count of the domain, bytes of
the printed script). The same slicing is applied by the verdict runners (`--check-quick-v2`'s
modal and reposition phases, `relcert-bridge-verdicts`, the demo verdict scripts) when the knob
is set in their environment, through the same function.

Not sliced: the mode-fact (implied-cut) channel. Its O2 queries (`checkedCutX`, `probeUnsat`)
carry only the bare evolve domain of one mode and, for a derived bound, the one linear atom it
is derived from, never the rows, so there is nothing to slice there; the stay, non-connection,
admissibility, handoff, progress and coverage queries are likewise untouched.

## The mechanization

The tool's claim is that every certification is an instance of the Lean theorem, so the sliced
runner is described by the same theorems, with one change of hypothesis shape at the Z3 leaf.

* **The sliced verdict.** `Z3Unsat q` (`Trusted/Oracle.lean`, next to the axiom
  `z3_unsat_sound`): Z3 answered `unsat` on some formula implied by `q`, that is
  `∃ q', (∀ σ, q.sat σ → q'.sat σ) ∧ z3solve q' = unsat`. `Z3Unsat.of_eq` is the unsliced
  verdict (`q' = q`).
* **The monotonicity lemma.** `z3Unsat_sound : Z3Unsat q → ∀ σ, ¬ q.sat σ`
  (`Trusted/Oracle.lean`), proved from `z3_unsat_sound` alone: an `unsat` answer on the sliced
  query implies the row's original obligation. Its slicing-specific instance is
  `Z3Unsat_of_sliced` (`Trusted/Slice.lean`): `unsat` on `dom' ∧ G` with
  `dom' = sliceFlowDom k g ġ dom` gives `Z3Unsat (dom ∧ G)`, through `sliceDom_weakens`
  (a state in the full domain is in the sliced one, by induction on the `and` tree).
* **Where it enters.** The flow verdict packs assume `Z3Unsat` instead of `z3solve _ = unsat`:
  `VerdXCore` (`Proofs/Encoding/CutRespond.lean`, the joint pack), `StrataVerdS`
  (`Proofs/Flow/StratifiedBarrierStrict.lean`, the strict pack, `VerdXCoreS`), `VerdDynCore`
  (`Proofs/Encoding/ReplayDyn.lean`, the right-only pack), and the fold-shaped strata lemmas
  `strata_hcert_from_verdicts'` / `segPresAll_from_strata_verdicts'`
  (`Proofs/Flow/StratifiedBarrier.lean`). Their consumers apply `z3Unsat_sound` where they
  applied `z3_unsat_sound` and continue into `flow_cert_sound` unchanged. The record-level
  theorems `theorem3_window_of_records(_pl)` and `theorem3_keyed_of_records(_pl)` and the
  bridge instances keep their statements.
* **The pin layer.** `modalVerdXQueries`, `modalVerdXQueriesS`, `modalVerdDynXQueries`,
  `modalVerdDynXQueriesPre` (`VerdictsV2/ModalX.lean`, `ModalXStrict.lean`, `ModalDynX.lean`)
  take the knob `k : Option ℕ` and slice each component's domain with `sliceFlowDom`, the
  function `checkSeg` and `checkDynRepo` call. The pin theorems `modalVerdX_of_queries`,
  `modalVerdXS_of_queries`, `modalVerdDynX_of_queries(Pre)` prove that an `unsat` answer on
  the printed (sliced) text is the instance's `Z3Unsat` hypothesis on the full query
  (`Z3Unsat_iflowQuery_of_sliced` and the route B, C variants, `VerdictsV2/ModalX.lean`).
  `bridgeGroups k`, `bridgeGroupsS k` and `verdicts_of_groups` / `verdictsS_of_groups`
  (`Proofs/Encoding/Emitted/Run.lean`, `StrictRun.lean`) carry the knob; the per-benchmark
  pins `<b>_bridge_run {k : Option ℕ} (hrun : bridgeGroups IR n cX covM prog ce k = some gs)
  (hok : GroupsOK gs)` (generated by `scripts/gen_bridge.py`) hold for every `k`. The runners
  read the knob once (`sliceHopsFromEnv`) and pass it; with the knob unset `k = none` and
  `sliceDomOpt none` is the identity, so `bridgeGroups … none` is the old `bridgeGroups`.
* **The audit** (`InstancesV2/AxiomCheck.lean`, `docs/CERTIFICATION-CHECK.md` check 2) is
  unchanged: 16 lines, 9 at `propext`, `Classical.choice`, `Quot.sound`, 7 adding
  `z3_unsat_sound`; the battery's 78 lines (76 standard, 2 with `z3_unsat_sound`) likewise.

## The gate (this branch, 2026-11-13)

Knob unset (the regression guarantee, `docs/CERTIFICATION-CHECK.md`):

* `lake build` clean (18394 jobs, 0 errors, no `sorry`), the five executables built;
* `--check-quick-v2` on the 50 suite benchmarks: `50 certified, 0 declined, 0 error(s)`;
  modal 1421/1421, handoff 2846/2846, non-connection 32/32, pruned edges 16/16, reposition
  950/950; `[wellformed] STRICT: 181/181 right modes ok` (75 invariant, 106 exit, 0 UNKNOWN,
  0 BLOCKING); `SUITE_V2 QUICK CHECKS PASSED`;
* `ONE DOMAIN: PASS (50 benchmarks: 48 with one evolve domain, 2 kind (iii) …)`;
* the three negatives `DECLINED`, `errors=0`; `lit_hypercert_vehicle_s8` all five right modes
  `BLOCKING`, `DECLINED` under the strict switch;
* `relcert-test`: `ok   all 50 suite_v2 IR literals match their files (50 files)`, `ALL PASS`;
* `relcert-bridge-verdicts` 13677/13677, `relcert-refute-verdicts` 416/416,
  `relcert-progress-verdicts` 1009/1009;
* the axiom audit: `AxiomCheck` 16 lines (9 at the three standard axioms, 7 adding
  `z3_unsat_sound`), the battery 78 lines (76 standard, 2 with `z3_unsat_sound`), both
  textually identical to `main`'s (`daf26c8`), no `sorryAx`;
* the demo verdict scripts of check 5 (stutter, pre-landing, strict, progress) as on `main`.

The printed queries are byte-identical to `main`'s: `sliceDomOpt none` is the identity and the
runners pass `none` when the variable is unset.

Knob set:

* `RELCERT_SLICE_HOPS=0 … --check-quick-v2` on the 50 suite benchmarks: `50 certified,
  0 declined, 0 error(s)` (check 1/3, wall 944 s against 857 s unsliced, on a loaded machine);
  the strict Assumption 1 gate 181/181 as before; the re-send of `main`'s committed records
  (check 2/3) discharges modal 1414/1421 and reposition 851/950 (handoff, non-connection and
  pruned edges unchanged at 2846, 32, 16): 7 joint and 99 right-only groups of six benchmarks
  (`lit_freedm_meter` 42, `lit_drl_lane_control` 30, `lit_girard08_robot` 23,
  `syringe_relay_prearm` 6, `turbine_startup_gearratio` 4, `elevator_start_discbrake` 1) are
  `sat` on their hop-0 slice: the recorded strata order was found with the full hypothesis
  set, and the slice drops a row it needs. So `verdicts: FAIL` on `main`'s records, as
  expected: a knob-on run needs knob-on records.
* `RELCERT_SLICE_HOPS=1`: `50 certified, 0 declined` (wall 746 s); modal 1414/1421,
  reposition 875/950 (82 groups of the same six benchmarks, `lit_drl_lane_control` 30→20,
  `lit_girard08_robot` 23→9, the others as at hop 0).
* Regeneration with the knob on (`lit_freedm_meter`, the most affected):
  `RELCERT_SLICE_HOPS=0 scripts/gen_v2_data.py lit_freedm_meter` rewrites its choice,
  pre-landing and progress leaves (the cover and cut leaves are unchanged; 1386 groups against
  1826 on `main`'s records, the hop-0 run certifying fewer right-only nodes and choosing a
  smaller committed set), `scripts/gen_bridge.py lit_freedm_meter` regenerates the instance,
  `lake build RelCertifier.InstancesV2.Bridge.LitFreedmMeter` type-checks it (the pins
  `lit_freedm_meter_bridge` and `lit_freedm_meter_bridge_run` at the new records), and
  `RELCERT_BRIDGE_ONE=lit_freedm_meter RELCERT_SLICE_HOPS=0 lake env lean
  scripts/bridge_one_verdicts.lean` discharges all 1386 groups at hop 0 (and, the same
  records, all 1386 unsliced). The regenerated leaves are not committed: `main`'s records stay
  the branch's, so the unset gate above is the regression guarantee.

Under the knob a `sat` answer on a sliced query is reported like a `sat` on the full query
(`FAIL comp#i`, the component not certified in that round, the pairing `fail` if no route of a
component is `unsat` and none is inconclusive). For the full query it is inconclusive, since
the sliced query is weaker; a sliced `sat` could be escalated to the full query (another
member of the component's group, `sliceDomOpt none`), which the pin layer would absorb as a
fourth to sixth alternative. Not done here.

The probe's stalled rung files (`CPS-QRC-reduction/docs/probe-2026-11/p20-ladder/logs/slice_*`,
same command lines as `run_p20.sh`, proxy `z3sos.py`, 1 h budget, 3 s Z3 timeout):

The originals ran with a 2 h budget (`r1_lam2`: ERROR budget exceeded at 7346 s inside
`(BRAKE_L, BRAKE_R)` with three position-gap rows left, 65 Z3-unknown; `r2_lam3`: DECLINED at
5420 s, `(TURN_L, TURN_R)` incon on the dv-, roll-difference and ghost-level rows, 52
Z3-unknown). The sliced re-runs (1 h cap each, so every one ends on the budget) all run on a
machine shared with other oracle jobs (load 40 to 55 on 12 cores); the per-query slice
statistics are the robust part of the comparison.

* `slice_r2_h0` (rung 2, hop 0): 2592 queries in 1 h (original 2223 in 1.5 h), median query
  26 → 3 variables, 77 → 9 hypotheses; 28 Z3-unknown (original 52); the proxy's cache hits
  433 times (original 15). `STRAIGHT_L` passes on `STRAIGHT_R` but its `TURN_R`/`ACCEL_R`
  pairings flip from pass to fail (rows 12 to 15, 22, 34, 35, 44 to 47 and 11 to 15, 26 are
  `sat` on their hop-0 slice); `(BRAKE_L, BRAKE_R)` flips from pass to fail on the three
  position-gap rows 37 to 39 (the hop-0 slice drops the rows they need); `(BRAKE_L, TURN_R)`
  incon as before; the budget ends inside `TURN_L`, whose `TURN_R` rows 11, 20 to 23 FAIL
  as in the original.
* `slice_r2_h1` (rung 2, hop 1): 2539 queries, median 26 → 4 variables, 77 → 10 hypotheses,
  33 Z3-unknown; `(BRAKE_L, BRAKE_R)` passes again (the position-gap rows return at one hop,
  the expected pattern); `STRAIGHT_L`'s `TURN_R`/`ACCEL_R` pairings stay fail at one hop;
  `(TURN_L, TURN_R)` incon with the same five rows, the budget ending inside `TURN_L`. The
  rung-2 TURN obstacle (dv-, drollL, the ghost level) is unchanged by slicing: those rows are
  unknown on their own slice.
* `slice_r1_h0` (rung 1, hop 0): 2733 queries in 1 h (original 2189 in 2 h), median 27 → 4
  variables, 90 → 12 hypotheses, 51 Z3-unknown (original 65), cache 469 hits (original 14);
  `STRAIGHT_L` keeps `STRAIGHT_R`, loses `TURN_R` and `ACCEL_R` (pass → fail); the budget ends
  inside `(BRAKE_L, BRAKE_R)` with the original's round-1 set of 11 BRAKE rows (28 to 31, 33,
  34, 36 to 39, 47) still FAIL, so hop 0 makes no progress on the BRAKE gap rows.
* `slice_r1_h1` (rung 1, hop 1): 2636 queries, median 27 → 4 variables, 89 → 15 hypotheses,
  43 Z3-unknown; `STRAIGHT_L` as at hop 0; the budget ends inside `(BRAKE_L, BRAKE_R)` with
  six rows left FAIL in the last round (28 to 31, 33, 34): the three position-gap rows 37 to
  39 that stalled the original are proven at one hop, while 28 to 31, 33, 34 (proven by the
  original in its round 2 with the full set) are `sat` on their one-hop slice.

Reading: slicing removes most of the Z3 time per query (the unknown count drops by a third to
a half and the runs issue more queries per hour), and the rung-1 position-gap rows that
stalled the original are proven at one hop; but on this family other rows then need the far
hypotheses (rung 1 rows 28 to 34 at one hop, rung 2 BRAKE at hop 0), and the rung-2 TURN rows
(dv-, drollL, the ghost level) are unknown on any slice. The
pass → fail flips of `STRAIGHT_L`'s off-diagonal pairings are the completeness cost of
reporting a sliced `sat` as a `sat` (above); the escalation to the full query would remove it.
