# Assumption 1, verified per benchmark (`WellFormedR`)

**Status (2026-10-15, branch `theorem3-general`).** The paper's Assumption 1
(Well-Formedness) is a separately stated, kernel-checked model fact for every one of the 50
suite_v2 benchmarks: **proved for all 50**, **false for none** (the four literature benchmarks
of 2026-10-15 included; the two dRL ones and `freedm_meter` are proved directly over the bridge's automaton,
`<b>_wellFormedR_direct`, with explicit polynomial runs, `trajRs_sol`). The six satellites are proved
literally since 2026-10-15, when their conserved momentum band entered the right evolve
domain (§3, §5); until then they were proved on the band, with the literal predicate refuted. Until 2026-10-10 it was false for 9 models (refuted in the kernel with exhibited
blocking states); those nine were repaired (`docs/SUITE-REDESIGN.md` §21: the fallback sinks
re-engage or are latched with an invariant guard, the arm planner's successor sets name every
band a sampled interval can reach) and are now proved. No proof uses Z3. The tool's sufficient
check of the successor half (`relcert --wellformed`) finds every one of the 174 right modes
`ok`, and `--check-quick-v2` now runs it STRICT, against a declared count (§4). The generic-bridge
instances (`InstancesV2/Bridge/`, the paper's route to
Theorem 3) take it as a hypothesis: `theorem3_keyed_of_records`
(`Proofs/Encoding/Emitted/Keyed.lean:427`) and `theorem3_window_of_records`
(`Emitted/Window.lean:83`) take `hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg
(epsR p)`, which each generated instance discharges from the benchmark's `WellFormedR` lemma,
transported and lifted by one coordinate (§6). Assumption 1 is therefore a hypothesis of the
bridge theorems and a proved fact, never a trust item.

## 1. The paper's statement and the predicate

The paper (restated 2026-10-10): *the right model is nonblocking and complete with respect
to its declared successor relation: from every state satisfying a source-mode guard, an
evolution spanning the control interval `ε_r` exists, and every evolution of duration at most
`ε_r`, including the empty one, ends in a state satisfying the guard of at least one declared
successor mode.* Its remark: satisfied when each right mode has a self-loop whose guard
contains every state reachable within one control interval of the mode, or a successor whose
guard holds wherever the self-loop's does not.

`Proofs/Encoding/WellFormedR.lean`:

```lean
def WellFormedRModeIn (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n))
    (reg : Formula (Var n)) (ε : ℝ) (q : ℕ) : Prop :=
  ∀ m, G.modeAt q = some m →
    ∀ x, Formula.sat (guard q) x → Formula.sat m.dom x → Formula.sat reg x →
      (∃ Φ, ODESol m.sys m.dom x ε Φ) ∧
      ∀ (t : ℝ) (Φ : ℝ → State (Var n)), t ≤ ε → ODESol m.sys m.dom x t Φ →
        ∃ e ∈ G.edgesFrom q, Formula.sat (guard e.tgt) (Φ t)

def WellFormedRIn G guard reg ε : Prop := ∀ q, q < G.modes.length → WellFormedRModeIn G guard reg ε q
def WellFormedR  G guard ε     : Prop := WellFormedRIn G guard Formula.tt ε
```

* `G` is the benchmark's guarded right automaton, the graph of its Theorem 3 (`Gr`, `GrG`,
  `GrPG`): the file's modes (`rightBlock (fR q) (Term.const 1)` over the evolve domain) and
  its `next` lists (`edgeList_eq_IR` / `GrG_edges_IR`, by `decide`).
* `guard q` is the lowered right guard of mode `q` (`hostGuard vs n Side.R (mR q)`, the
  lowering every edge of `G` tests: `Gr_guards`; `wellFormedR_switchLegal` turns clause (ii)
  into a legal switch).
* `ε = epsR p`, the file's `epsilon` read as the tool reads it (`(parseRat p.R.epsilon).getD 1`),
  pinned per benchmark (`epsR_eq`).
* `ODESol sys dom x r Φ` (dL-caltiming): `Φ` solves `sys` on `[0, r]` from `x`, freezes every
  unbound variable and stays in `dom`; `t = 0` is the empty evolution.
* **The evolve-domain conjunct** `m.dom x`: the automaton's states are its evolve domain's; a
  run, even the empty one, exists only from a domain state (`ODESol.start_dom`). Without the
  conjunct clause (i) would fail at any guard state outside the domain for no dynamical
  reason (`watertank`'s `PumpOff` guard `x < 2` admits `x = −1`, outside `0 ≤ x ≤ 25`). The
  retired settling checker made the same correction (`Checker/WellFormedChecker.lean`, "THE
  BASE-SET CORRECTION").
* **Region-relative form** (style (c)): `WellFormedRIn G guard reg ε` with
  `RegionInvariant G reg` (every mode's flow keeps `reg`; a jump does not move the state).

## 2. Proof styles and generic support

* **(a) forward invariance** of the mode's guard under its own flow, then the self-loop.
* **(b) exit into a successor's guard** within one interval (the band advances into the next
  band; a threshold is crossed into the next mode's guard).
* **(c) the momentum band in the domain**: the six satellites, style (a) once the right
  evolve domain carries the conserved momentum band (the explicit solution keeps the sums
  constant, so it stays in the domain).

Generic lemmas (`WellFormedR.lean`): closed form of a linear coordinate at the run's duration
(`ODESol.linear_exact`, `linear_between`, `linear_up/down/lt/gt`), rate bounds
(`ODESol.rate_le/ge`, `mono`, `const`), one-coordinate barriers for nonlinear fields
(`ODESol.coord_le_barrier/ge_barrier`, via `DI_nonstrict_superlevel`), conserved affine
combinations (`ODESol.affine_const`), magnitude decay (`decay_sq_le`), explicit runs
(`trajJ_sol`, `exists_contract_run`, `exists_rate_run`, `const_sol`), existence from the
instances' viability route with the left held still and a time rescaling
(`exists_of_HExistSegB_zero`, `ODESol.reparam`), and the refutation lemmas
(`not_wellFormedR_of_run`: one explicit run that ends outside every successor guard;
`not_wellFormedR_of_noRun`: no run of duration `ε`). `WellFormedLadder.lean`: one theorem
(`wellFormedR_ladder`) for the 18 terrain ladders. `InstancesV2/WellFormed/Platoon3Link.lean`:
the operating range of a platoon link is kept by the reference's own flow
(`link_guard_Ronly`); the latched AEB sink's guard part is kept by its braking link
(`brake_guard_Ronly`: `g + 2r` conserved, `r` decaying); the explicit 6-D solution with any
set of braking links (`solB_sol`, inside the evolve box).

Existence (clause (i)) is always an explicit or instance-supplied run: the exponential and
linear solutions, the ladders' `LadderRun.sol` (and `runE` / `run_sol` / `drive_sol`, the
instances' explicit runs with their duration kept), the platoon link solution `solΦ` and the
sinks' `solB`, the
satellites' `flowR_exists` (the conserved sums keep the band), and for `w' = c − w²` the instances' viability route
(both faces strict, hand Lipschitz data). **No Z3 leaf** anywhere: the pinned-query discipline
was not needed.

## 3. Per benchmark

Theorems: `<ns>.<bench>_wellFormedR` (proved; for the nine repaired models also the
per-mode theorems `…_brake`, `…_limit`, `…_mode`), for the detumble family also
`<ns>.<bench>_band_invariant` (the band is kept by every mode's flow; the predicate itself is
unconditional since the momentum band `|h_i + J_i w_i| ≤ 2` entered the right evolve domains,
2026-10-15). Files: `InstancesV2/WellFormed/<B>.lean` (50, each
self-contained: right model and proof; the 19 carried-over ones moved in from `Instances/WellFormed/`
on 2026-10-22). Battery: `InstancesV2/WellFormedBattery.lean`. Tool column:
`relcert --wellformed` (§4). Z3 leaves: none for every row.

| # | benchmark | result | modes: style | tool check |
|---|---|---|---|---|
| 1 | `acc_spoof_lag` | proved | CRUISE (a), DISENGAGE (a) | both ok (invariant) |
| 2 | `acc_spoof_limp` | proved | NORMAL, ECO, SPORT (a); DISENGAGE (a) | all ok (invariant) |
| 3 | `acc_tune_lag` | proved | CRUISE (a), DISENGAGE (a) | both ok (invariant) |
| 4 | `acc_tune_limp` | proved | NORMAL, COMFORT, SPORT (a); DISENGAGE (a) | all ok (invariant) |
| 5 | `arm_plateau_crit` | proved (repaired) | ApproachA (b) → B, C or Hold; ApproachB (b) → C or Hold; ApproachC (b) → Hold; Hold (a) | A ok (exit→B,C,Hold); B ok (exit→C,Hold); C ok (exit→Hold); Hold ok (invariant) |
| 6 | `arm_plateau_profiles` | proved (repaired) | ApproachA (b) → B, Cfast or Hold; ApproachB (b) → Cfast or Hold; ApproachCfast, ApproachCslow (b) → Hold; Hold (a) | A ok (exit→B,Cslow,Hold); B ok (exit→Cslow,Hold); C's ok (exit→Hold); Hold ok (invariant) |
| 7 | `arm_plateau_slow` | proved (repaired) | as `arm_plateau_crit` | as `arm_plateau_crit` |
| 8 | `charger_fast_setpoints` | proved | BULK (b) → ABSORB; ABSORB (b) → FULL; FULL (a); FAULT (a) | BULK ok (exit→ABSORB); ABSORB ok (exit→FULL); FULL, FAULT ok (invariant) |
| 9 | `charger_fast_tapers` | proved | BULK (b) → ABSORB_SLOW (closed form at `t ≤ 1`); ABSORB_SLOW, ABSORB_FAST (b) → FULL; FULL (a); FAULT (a) | BULK ok (exit→ABSORB_FAST, same guard); ABSORB_* ok (exit→FULL); FULL, FAULT ok (invariant) |
| 10 | `match_multi_rate` | proved | DRIVE (a), STALL (a); `ε_r = 0.3` | both ok (invariant) |
| 11 | `platoon3_linkloss` | proved (repaired) | FOLLOW (a); BRAKE1–3 (a), latched (`g + 2r` conserved; explicit solution `solB`) | all ok (invariant) |
| 12 | `platoon3_profiles` | proved (repaired) | NORMAL, CLOSE, FAR (a); BRAKE1–3 (a), latched | all ok (invariant) |
| 13 | `platoon_delay_linkloss` | proved (repaired) | FOLLOW (a), CATCH (a); BRAKE (b) → FOLLOW | FOLLOW, CATCH ok (invariant); BRAKE ok (exit→FOLLOW) |
| 14 | `platoon_delay_profiles` | proved (repaired) | FOLLOW, GENTLE, ASSERTIVE (a); BRAKE (b) → FOLLOW | those ok (invariant); BRAKE ok (exit→FOLLOW) |
| 15 | `quad_light_airframe_20` | proved (repaired) | CLIMB (a) (barriers, guard `0 ≤ w ≤ 3`); LIMIT (b) → CLIMB (exponential decay) | CLIMB ok (invariant); LIMIT ok (exit→CLIMB) |
| 16 | `quad_light_lag` | proved | CLIMB (a) (barriers; viability existence) | ok (invariant) |
| 17 | `quad_light_profiles` | proved (repaired) | NORMAL, ECO, SPORT (a) (guard `0 ≤ w ≤ 3.2`); LIMIT (b) → NORMAL | those ok (invariant); LIMIT ok (exit→NORMAL) |
| 18 | `rover_ladder_2to3` | proved | STEEP (b) → MODER, MODER (b) → FLAT, FLAT (a) | STEEP ok (exit→MODER), MODER ok (exit→FLAT), FLAT ok (invariant) |
| 19 | `rover_ladder_3to6` | proved | as 18 (ladder lemma) | as 18 |
| 20 | `rover_ladder_2to4` | proved | as 18 | as 18 |
| 21 | `rover_ladder_2to6` | proved | as 18 | as 18 |
| 22 | `rover_ladder_4to6` | proved | as 18 | as 18 |
| 23 | `rover_ladder_6to8` | proved | as 18 | as 18 |
| 24 | `rover_ladder_8to12` | proved | as 18 | as 18 |
| 25 | `tank_dos_3to1` | proved | HIGH, LOW (b) (contractions to 1.3 resp. 0.7 inside `[0, 2]`, the guards `[0, 1)`, `[1, 2]` partition the tank); `ε_r = 1` | ok (exit) |
| 26 | `rover_terrain_2to3` | proved | as 18 | as 18 |
| 27 | `rover_terrain_3to6` | proved | as 18 | as 18 |
| 28 | `rover_terrain_6to12` | proved | as 18 | as 18 |
| 29 | `rover_terrain_6to8` | proved | as 18 | as 18 |
| 30 | `rover_patrol_lag` | proved | SLOW (b) → MEDIUM_ECO; MEDIUM_ECO, MEDIUM_BRISK (b) → FAST; FAST (a) | SLOW ok (exit→MEDIUM_BRISK); MEDIUM_* ok (exit→FAST); FAST ok (invariant) |
| 31 | `rover_patrol_zones` | proved | as 30; STALL (a) | as 30; STALL ok (invariant) |
| 32 | `sat3w_detumble_nominal` | proved | DETUMBLE (a) (the band in the domain keeps the explicit run); SAFE (a) | both ok (invariant) (clause (i) is not checked by the tool) |
| 33 | `sat3w_detumble_phases` | proved | as 32 | as 32 |
| 34 | `sat3w_detumble_weak` | proved | NOMINAL, ECONOMY, SURVIVAL (a) (the band in the domain keeps the explicit runs); SAFE (a) | all ok (invariant) |
| 35 | `sat_detumble_nominal` | proved | as 32 | as 32 |
| 36 | `sat_detumble_phases` | proved | as 32 | as 32 |
| 37 | `sat_detumble_weak` | proved | as 34 | as 34 |
| 38 | `rover_attitude_6to8` | proved | as 18 | as 18 |
| 39 | `rover_attitude_8to12` | proved | as 18 | as 18 |
| 40 | `rover_lateral_6to8` | proved | as 18 | as 18 |
| 41 | `rover_lateral_8to12` | proved | as 18 | as 18 |
| 42 | `rover_rollover_6to12` | proved | as 18 | as 18 |
| 43 | `rover_rollover_6to7` | proved | as 18 | as 18 |
| 44 | `rover_rollover_7to12` | proved | as 18 | as 18 |
| 45 | `watertank` | proved | Low (b) → MidEco; MidEco, MidBoost, High, PumpOff (a) | Low ok (exit→MidBoost, same guard); the others ok (invariant) |
| 47 | `drl_car_stop` | proved (direct) | Accel, Brake (b) → Coast; Coast (a); explicit run `x + v t + c t²/2` | Accel, Brake ok (exit→Coast); Coast ok (invariant) |
| 48 | `drl_lane_control` | proved (direct) | every mode (b) → CoastLAccel or CoastLBrake by the leader's speed; explicit run | all six ok (exit) |
| 49 | `vehicle_hypercert` | proved (`ChoiceVehicleHypercert.wellFormedR`) | A0 (a); the others (b) → A0 or Ap4 | A0 ok (invariant); the others ok (exit) |
| 50 | `freedm_meter` | proved (direct) | every mode (b) → GridD0R0 (guard = domain); explicit linear run | battery modes ok (exit); grid modes ok (invariant) |

Totals: proved 39, false 0, band 6 (`WellFormedBattery.wfDeclared = (39, 0, 6)`, was
`(30, 9, 6)` until the 2026-10-10 repairs;
`wf_coverage` checks in the kernel that the three name lists are a permutation of the suite's
IR table). Z3-free: 45/45. Region-relative: the 6 satellites.

### The nine repaired models (refuted until 2026-10-10; the exhibited states)

| benchmark | blocking mode (before) | state, and where one interval `ε_r = 1` took it | repair (`docs/SUITE-REDESIGN.md` §21) |
|---|---|---|---|
| `arm_plateau_{crit,profiles,slow}` | ApproachA (`0 ≤ θ ≤ 0.35`, `θ' = 0.5`), successors ApproachB `[0.35, 0.5]`, ApproachA | `θ = 0.35` → `0.85` | sampled planner: `ApproachA → [ApproachB, ApproachA, ApproachC(s), Hold]` |
| same | ApproachB (`0.35 ≤ θ ≤ 0.5`, `θ' = 0.35`), successors ApproachC(s) `[0.5, 0.6]`, ApproachB | `θ = 0.5` → `0.85` | `ApproachB → [ApproachC(s), ApproachB, Hold]` |
| `platoon_delay_{linkloss,profiles}` | BRAKE (`g < 20`, `g' = 1.5`), successors BRAKE only | `g = 19` → `20.5` | re-engagement `BRAKE → FOLLOW` (at `g ≥ 20`) |
| `platoon3_{linkloss,profiles}` | BRAKE1 (`g₁ < 20`, `g₁' = r₁`, `r₁' = 4`), successors BRAKE1 only | `g₁ = 19`, `r₁ = 0`, links 2, 3 at rest at 30 → `g₁ = 21`, `r₁ = 4` | latched AEB: `r_k' = −r_k/2`, guard `g_k < 20 ∧ 0 ≤ g_k + 2r_k < 20 ∧` the other links' operating range (invariant) |
| `quad_light_airframe_20` | LIMIT (`w > 3`, `w' = −2w`), successors LIMIT only | `w = 3.1` → `3.1 e^{−2} < 3` | `LIMIT → CLIMB`; CLIMB's guard `0 ≤ w ≤ 3` (was 2.6) |
| `quad_light_profiles` | LIMIT (`w > 3.2`) | `w = 3.3` → `3.3 e^{−2} < 3.2` | `LIMIT → NORMAL`; the climb modes' guard `0 ≤ w ≤ 3.2` (was 2.6) |
| the 6 satellites (until 2026-10-15) | DETUMBLE / NOMINAL | `w3 = 0.4`, `h = 2` (resp. `h3 = 2`), the rest 0 (energy `0.8 ≤ 1`): no run of duration 1 exists: `h + 5 w3` is conserved, so `h(1) = 4 − 2 e^{−1/2} > 2` would leave the domain `|h| ≤ 2` (clause (i)) | the right evolve domains carry the momentum band `|h_i + J_i w_i| ≤ 2` (the body's momentum within the wheels' capacity, a constant of every design-model flow; each file's `MOMENTUM BAND` paragraph) |

The sinks are pruned: the certificate never enters them, so no Theorem 3 depended on them,
and the repairs left every prune, admissible start and cover unchanged. The arm approach
bands are entered by the Theorem 3 responses, which switch at the band boundaries inside the
interval; as a sampled controller with period `ε_r` the old model violated the assumption,
the repaired one does not. The satellites' momentum band is the band their standalone Theorem 3 regions carry (`nbF`,
`docs/SUITE-REDESIGN.md` §19.2): the total angular momentum about each wheel axis,
`h_i + J_i w_i`, within the wheel's capacity, the condition under which the wheel can absorb the
body's momentum, and a constant of every design-model flow. Since 2026-10-15 it is part of the
right evolve domains (each file's header says so), the tool certifies the six with byte-identical
covers, and Assumption 1 holds literally.

## 4. The tool check (`relcert --wellformed`)

`Trusted/WellFormedCheck.lean`. Per right mode, a cheap SUFFICIENT check of clause (ii):

1. **Invariance**: the guard's comparison atoms are kept by the mode's own flow over its
   evolve domain, stratified (an atom may be conditioned only on atoms kept in earlier
   rounds): the cut channel's routes, contraction shape (`contractShapeOK`,
   `contractShapeOKX`, no Z3), frozen, DI route B `UNSAT(D ∧ I ∧ g = 0 ∧ ġ ≥ 0)`, DI route A
   `UNSAT(D ∧ I ∧ ġ > 0)`. All kept and a self-loop: `ok (invariant)`.
2. **Exit within one interval**: for each atom not kept, a rate bound `L` with
   `UNSAT(D ∧ I ∧ ġ > L)` (bisection on `k/100`); then one coverage query
   `UNSAT(D ∧ I ∧ ⋀ g ≤ L ε_r ∧ ⋀_{s ∈ next(q)} ¬guard_s)`: every end state of a run of at
   most `ε_r` is in a declared successor's guard. `ok (exit→S)`, `S` greedily minimized.
3. Otherwise `UNKNOWN`.

Only `unsat` counts. Clause (i) (a full-interval run exists) is not checked (the satellites'
`ok (invariant)` rows are about clause (ii) only; the kernel's `WellFormedR` is the full
statement). Output: `[wellformed] <bench>: q1 ok (invariant) | q2 ok (exit→q3) | q4 UNKNOWN
(N queries)` and `[wellformed] summary: …`. `--check-quick-v2` runs the same section as its
check 3/3, strict (below); until 2026-10-10 it was informational there.

**Suite_v2 result** (2026-10-10, repaired models): 45 benchmarks, 146 right modes: 83 ok
(invariant), 63 ok (exit), **0 UNKNOWN**, 2279 queries. Every mode the kernel proves is `ok`.
Before the repairs: 77 / 53 / 16 UNKNOWN in 9 benchmarks (2236 queries); the 16 UNKNOWN modes
were exactly the blocking modes of §3 (ApproachA and ApproachB of the three `arm_plateau`
files, BRAKE of the two `platoon_delay` files, BRAKE1–BRAKE3 of the two `platoon3` files,
LIMIT of the two `quad_light` files).

**The old `platoon3` model** (commit `1a3507f`, engagement-band guards `26 ≤ gᵢ ≤ 34`,
`|rᵢ| ≤ 1`, no catch-all mode; reconstructed outside the tree):
`platoon3_linkloss: FOLLOW UNKNOWN | BRAKE1 UNKNOWN | BRAKE2 UNKNOWN | BRAKE3 UNKNOWN`,
`platoon3_profiles: NORMAL UNKNOWN | CLOSE UNKNOWN | FAR UNKNOWN | BRAKE1–3 UNKNOWN`; the
repaired model's `FOLLOW` / `NORMAL` / `CLOSE` / `FAR` are `ok (invariant)`. With the switch
on, the old model's two benchmarks, CERTIFIED by the default run, are DECLINED.

**The switch** `RELCERT_WELLFORMED_STRICT=1`: a CERTIFIED benchmark with an `UNKNOWN` right
mode becomes DECLINED (a `[wellformed] STRICT` line on stderr says why). Off by default for a
single `relcert <file>` run; off, no verdict and no emission changes.

**Strict in the recipe** (2026-10-10). `--check-quick-v2` certifies the suite in the strict
mode (the switch forced on for its check 1/3) and ends with check 3/3, the `--wellformed`
report gated against declared counts: `ExpectedSuiteV2.wfModes = 174` (`VerdictsV2/RunV2.lean`; the
kernel pin `CoveragePinsV2.suiteV2_wfModes` of that count was archived with the standalone
route on 2026-10-22) and
`wfUnknown = 0`. Any `UNKNOWN` mode, or a mode count off the declared one, fails the run
(`wellformed (strict): FAIL`, exit 1). Checked negatively: with the pre-repair
`platoon_delay_linkloss` in place of the repaired one, check 1 declines it
(`44 certified, 1 declined … but the declared suite is 45/0/0`) and check 3 reports
`145/146 right modes ok … 1 UNKNOWN`: `SUITE_V2 QUICK CHECKS FAILED`, exit 1. The informational
`relcert --wellformed <files>` is unchanged.

## 5. Build and audit

```bash
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt
```

Expected: 76 axiom lines, each exactly `[propext, Classical.choice, Quot.sound]` (39
`<b>_wellFormedR`, the repaired modes' per-mode theorems, the satellites' three each, 13
generic lemmas including `Platoon3Link.brake_guard_Ronly`, `Platoon3Link.solB_sol` and
`WellFormedBattery.wf_coverage`); the summary line of §4.

## 6. The lift to the bridge dimension (2026-10-21, branch `clocked-right`)

Each `WellFormedR` lemma is stated at a fixed dimension `n0` (the pack table's `dim`, or the
state variables padded to three coordinates: the right mode variable, the left clock and the
stored left mode; the right clock, the keyed form's fourth auxiliary coordinate, is the `+ 1`
below). Since the
right automaton of the bridge is clocked (`rightAutomatonBodyC`, the right clock `(Aux, d)`;
`docs/PAPER-MAPPING.md` §9), the generated instances live at `n0 + 1` (`bridgeDimV2`,
`VerdictsV2/RunBridge.lean:74`). `Proofs/Encoding/Emitted/Lift.lean` carries the lemma across:

* `padOK p n : Bool` (`Lift.lean:108`): for every right mode `q ≤ nR p` (the out-of-range
  default included), the lowered guard and evolve domain at `n+1` are the `IForm.embed` of
  their lowering at `n`, and the dynamics pad with the new coordinate's derivative `0`
  (`dynPadOK`). Each generated instance proves `pad_ok : padOK IR n0 = true` by
  `decide +kernel`.
* `wellFormedR_lift (hpad : padOK p n = true) (h : WellFormedR (grOf p n pr) (guardR p n) ε) :
  WellFormedR (grOf p (n+1) pr) (guardR p (n+1)) ε` (`Lift.lean:292`): every solution at
  `n+1` projects to one at `n` (`odeSol_proj`) and every solution at `n` extends with the new
  coordinate constant (`odeSol_ext`), so both clauses transfer.

The order in a generated instance (`scripts/gen_bridge.py`, e.g. `InstancesV2/Bridge/Watertank.lean:53`):
transport at the lemma's dimension (`wellFormedR_transport`, or the `_direct` form), then
`wellFormedR_lift (n := n0) pad_ok`, then `WellFormedRIn.of_tt` at `reg = ⊤`. The five
hand-written `InstancesV2/Choice/General/` exhibits keep only their Assumption 1 proofs
(their Theorem-3 parts were retired on 2026-10-21, fixed at `Var 2` with no slot for the
right clock); those proofs are lifted the same way into the corresponding bridge instances.
Nothing in this file's battery or audit (§5) changes: the lift is a generic lemma at the
three standard axioms, applied inside the bridge instances.
