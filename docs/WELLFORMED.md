# Assumption 1, verified per benchmark (`WellFormedR`)

**Status (2026-10-15, branch `theorem3-general`).** The paper's Assumption 1
(Well-Formedness) is a separately stated, kernel-checked model fact for every one of the 50
suite_v2 benchmarks (2026-10-27: four moved to `benchmarks/reserve/`, below, seven more in batch I4, ten new in batch I5 and five in batch I6, and five swapped for literature case studies in batch I8): **proved for all 50**, **false for none** (the four literature benchmarks
of 2026-10-15 included; the two dRL ones, `lit_freedm_meter` and the case studies of batch I8 are proved directly over the bridge's automaton,
`<b>_wellFormedR_direct`, with explicit polynomial runs, `trajRs_sol`). The satellites are proved
literally since 2026-10-15 (§3, §5); from 2026-10-15 to 2026-10-29 their right evolve domain carried the
conserved momentum band, since 2026-10-29 (one domain per benchmark) their domain is the gyro box `|w_i| ≤ 1`
on both sides, without the band (not a first integral of the left) and without the wheel box `|h| ≤ 2` (which the
design model's flow crosses); until 2026-10-15 they were proved on the band, with the literal predicate refuted. Until 2026-10-10 it was false for 9 models (refuted in the kernel with exhibited
blocking states); those nine were repaired (`docs/SUITE-REDESIGN.md` §21: the fallback sinks
re-engage or are latched with an invariant guard, the arm planner's successor sets name every
band a sampled interval can reach) and are now proved. No proof uses Z3. The tool's sufficient
check of both clauses (`relcert --wellformed`; the nonblocking clause since 2026-10-26, before
which only the successor clause was checked) finds every one of the 176 right modes `ok` (2026-10-30), and
`--check-quick-v2` runs it STRICT, against declared counts (§4). The generic-bridge
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
* **(c) the momentum band in the domain** (2026-10-15 to 2026-10-29): the satellites, style (a) once the right
  evolve domain carried the conserved momentum band. Since 2026-10-29 the domain is the gyro box
  `|w_i| ≤ 1` only (one domain per benchmark): style (a), the explicit solution's rates decay
  (`|w_i(t)| = |w_i(0)| e^{−kt}`), `h` is unconstrained.

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
(`wellFormedR_ladder`) for the terrain ladders at the old scale (no suite benchmark uses it since
2026-10-27). `WellFormedTerrain.lean` (2026-10-26): one theorem
(`wellFormedR_terrain`) for the terrain chain (`MUD`, `GRAVEL`, `PAVED` odometer bands `[0, 5)`,
`[5, 12)`, `[12, ∞)`, an optional cap `x_c ≤ c_T` kept by a contraction) and, since 2026-10-27,
the four ladder rungs (`STEEP`, `MODER`, `FLAT` at `[0, 60)`, `[60, 140)`, `[140, ∞)`, no cap),
and the explicit runs of
affine cascades (`forcedSol`: `y' = F t − k y` by variation of constants; `intSol`) with their
comparison bounds (`forcedSol_between`, `mono_of_deriv_nonneg`). `InstancesV2/WellFormed/Platoon3Link.lean`:
the operating range of a platoon link is kept by the reference's own flow
(`link_guard_Ronly`); the latched AEB sink's guard part is kept by its braking link
(`brake_guard_Ronly`: `g + 2r` conserved, `r` decaying); the explicit 6-D solution with any
set of braking links (`solB_sol`, inside the evolve box).

Existence (clause (i)) is always an explicit or instance-supplied run: the exponential and
linear solutions, the ladders' `LadderRun.sol` (and `runE` / `run_sol` / `drive_sol`, the
instances' explicit runs with their duration kept), the platoon link solution `solΦ` and the
sinks' `solB`, the
satellites' `flowR_exists` (the decaying rates keep the gyro box), and for `w' = c − w²` the instances' viability route
(both faces strict, hand Lipschitz data). **No Z3 leaf** anywhere: the pinned-query discipline
was not needed.

## 3. Per benchmark

Theorems: `<ns>.<bench>_wellFormedR` (proved; for the nine repaired models also the
per-mode theorems `…_brake`, `…_limit`, `…_mode`), for the detumble family also
`<ns>.<bench>_band_invariant` (the band is kept by every right mode's flow, a model fact of the
design model; the predicate itself is unconditional since 2026-10-15, with the band in the right
evolve domains until 2026-10-29 and over the gyro box `|w_i| ≤ 1` alone since). Files: `InstancesV2/WellFormed/<B>.lean` (51, each
self-contained: right model and proof; the 19 carried-over ones moved in from `Instances/WellFormed/`
on 2026-10-22). Battery: `InstancesV2/WellFormedBattery.lean`. Tool column:
`relcert --wellformed` (§4). Z3 leaves: none for every row.

| # | benchmark | result | modes: style | tool check |
|---|---|---|---|---|
| 1 | `acc_spoof_lag` | proved (right period 0.1 s since 2026-10-27, batch I4) | CRUISE (a) (the lagged loop's envelope, modal coordinates `a + 2v − 60`, `3a + 2v − 60` decaying; explicit two-exponential run) | ok (invariant) |
| 2 | `acc_spoof_limp` | proved (batch 10, 2026-10-30: DISENGAGE and its edges removed, a dead mode; proof adapted) | NORMAL, ECO, SPORT (a) (closed guards `20 ≤ v ≤ 40`, set points 27 / 30 / 33 inside, `linear_between`) | all ok (invariant) |
| 3 | `acc_tune_lag` | proved (right period 0.1 s since 2026-10-27, batch I4) | CRUISE (a) (the lagged loop's envelope, modal coordinates `a + 2.5v − 75`, `a + 0.625v − 18.75` decaying; explicit two-exponential run) | ok (invariant) |
| 4 | `acc_tune_limp` | proved (right period 0.1 s since 2026-10-27, batch I4; review round 6, 2026-10-30: COMFORT and SPORT removed, proof adapted) | NORMAL (a); DISENGAGE (a) | all ok (invariant) |
| 5 | `arm_plateau_crit` | moved to `benchmarks/reserve/` 2026-10-27 (batch I4; was: proved (repaired); proof in git history) | ApproachA (b) → B, C or Hold; ApproachB (b) → C or Hold; ApproachC (b) → Hold; Hold (a) | A ok (exit→B,C,Hold); B ok (exit→C,Hold); C ok (exit→Hold); Hold ok (invariant) |
| 6 | `arm_plateau_profiles` | moved to `benchmarks/reserve/` 2026-10-27 (was: proved (repaired); proof in git history) | ApproachA (b) → B, Cfast or Hold; ApproachB (b) → Cfast or Hold; ApproachCfast, ApproachCslow (b) → Hold; Hold (a) | A ok (exit→B,Cslow,Hold); B ok (exit→Cslow,Hold); C's ok (exit→Hold); Hold ok (invariant) |
| 7 | `arm_plateau_slow` | moved to `benchmarks/reserve/` 2026-10-27 (batch I4; was: proved (repaired); proof in git history) | as `arm_plateau_crit` | as `arm_plateau_crit` |
| 8 | `charger_fast_setpoints` | moved to `benchmarks/reserve/` 2026-10-27 (batch I4; was: proved; proof in git history) | PRECHARGE (b) → BULK; BULK (b) → ABSORB; ABSORB (b) → FULL; FULL (a); FAULT (a); dimension 3 (mode-keyed) | PRECHARGE ok (exit→BULK); BULK ok (exit→ABSORB); ABSORB ok (exit→FULL); FULL, FAULT ok (invariant) |
| 9 | `charger_fast_tapers` (left the suite 2026-10-30, review round 6, `benchmarks/skipped/`; the proof went with it) | was proved (reinstalled 2026-10-27, batch I7, at the minute time scale, `ε_r = 0.006`: the round-2 proof at the new interval; in `benchmarks/reserve/` from batch I4 to batch I7); fix round 4 (2026-10-29): FAULT removed (its edges were dead), PRECHARGE from `x = 0`; proof adapted | PRECHARGE (b) → BULK; BULK (b) → ABSORB_SLOW (closed form at `t ≤ 0.006`); ABSORB_SLOW, ABSORB_FAST (b) → FULL; FULL (a); FAULT (a); dimension 3 (mode-keyed) | PRECHARGE ok (exit→BULK); BULK ok (exit→ABSORB_FAST, same guard); ABSORB_* ok (exit→FULL); FULL, FAULT ok (invariant) |
| 10 | `match_multi_rate` | replaced 2026-10-27 by `gantry_speed_zones` (row 55; was: proved; proof in git history) | DRIVE (a), STALL (a); `ε_r = 0.3` | both ok (invariant) |
| 11 | `platoon3_linkloss` | moved to `benchmarks/reserve/` 2026-10-27 (was: proved (repaired); proof in git history) | FOLLOW (a); BRAKE1–3 (a), latched (`g + 2r` conserved; explicit solution `solB`) | all ok (invariant) |
| 12 | `platoon3_profiles` | moved to `benchmarks/reserve/` 2026-10-27 (was: proved (repaired); proof in git history) | NORMAL, CLOSE, FAR (a); BRAKE1–3 (a), latched | all ok (invariant) |
| 13 | `platoon_delay_linkloss` | replaced 2026-10-27 by `platoon_linkloss` (row 51; was: proved (repaired); proof in git history) | FOLLOW (a), CATCH (a); BRAKE (b) → FOLLOW | FOLLOW, CATCH ok (invariant); BRAKE ok (exit→FOLLOW) |
| 14 | `platoon_delay_profiles` | replaced 2026-10-27 by `platoon_profiles` (row 56; was: proved (repaired); proof in git history) | FOLLOW, GENTLE, ASSERTIVE (a); BRAKE (b) → FOLLOW | those ok (invariant); BRAKE ok (exit→FOLLOW) |
| 15 | `quad_light_airframe_20` | moved to `benchmarks/reserve/` 2026-10-27 (batch I7; was: proved, redesigned 2026-10-27, repaired 2026-10-10 before; proof in git history) | CLIMB (a) (the affine pair `h' = w`, `w' = 9.81 − 4.905 w`; the explicit run `forcedSol` / `intSol` stays in the guard box `h ≥ 0`, `0 ≤ w ≤ 2`, the equilibrium `w = 2` on its face) | ok (invariant) |
| 16 | `quad_light_lag` | proved | CLIMB (a) (since 2026-10-27 the affine cascade `h' = w`, `w' = a − 4.905 w`, `a' = 10 (9.81 − a)`; the explicit run `forcedSol` / `intSol` stays in the guard box; since 2026-10-29 (one domain on both sides) the box is `h ≥ 0`, `0 ≤ w ≤ 3`, `0 ≤ a ≤ 14.715`, kept since `14.715 = 3 × 4.905`) | ok (invariant) |
| 17 | `quad_light_profiles` | proved (redesigned 2026-10-27; repaired 2026-10-10 before, proof in git history; review round 6, 2026-10-30: pilot profile switching, SPORT set point 2.5, proof adapted) | NORMAL, ECO, SPORT (a) (`h' = w`, `w' = c − 4.905 w` toward 2.0, 1.6, 2.5 (2.4 before 2026-10-30); explicit run in the guard box `h ≥ 0`, `0 ≤ w ≤ 3`); dimension 3 (mode choice, the default padding) | all ok (invariant) |
| 18 | `rover_ladder_2to3` | proved (reinstalled 2026-10-27 on the canonical rover hierarchy: right `L2`, `ψ` frozen; since 2026-10-29 the right evolve domain is the validity box of both sides, the frozen coordinates stay at their start values) | STEEP (b) → MODER, MODER (b) → FLAT, FLAT (a) (the shared three-band lemma `wellFormedR_terrain` at the route scale: odometer zones `[0, 60)`, `[60, 140)`, `[140, ∞)`, no cap, `0 ≤ s' ≤ 8`; existence: `v → c_q` by `forcedSol`, `s` its integral) | STEEP ok (exit→MODER), MODER ok (exit→FLAT), FLAT ok (invariant) |
| 19 | `rover_ladder_3to6` | proved (reinstalled 2026-10-27, right `L3`) | as 18 (existence: also `ψ` decaying) | as 18 |
| 20 | `rover_ladder_2to4` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 21 | `rover_ladder_2to6` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 22 | `airheader_dos_3to1` | moved to `benchmarks/reserve/` 2026-10-27 (was: proved; proof in git history) | NORMAL, ALARM (b) (the run ends in `0 ≤ p ≤ 9`, the three guards partition it, all declared successors; existence by the explicit exponential at the frozen demand); TRIP (a) (`p' = −g p ≤ 0` keeps `p < 5`, latched self-loop); `ε_r = 1` | NORMAL ok (exit→ALARM), ALARM ok (exit→NORMAL), TRIP ok (invariant) |
| 23 | `rover_ladder_6to8` | proved (reinstalled 2026-10-27, right `L6`) | as 18 (existence: the cascade `z → θ`, `(v, ψ) → φ`, all `→ s`, kept in the box by `forcedSol_between`) | as 18 |
| 24 | `rover_ladder_8to12` | proved (reinstalled 2026-10-27, right `L8`) | as 18 (existence: the cascade `ω_ψ → ψ`, `z → ω_θ → θ`, `(v, ω_ψ, ψ) → φ`, all `→ s`) | as 18 |
| 25 | `tank_dos_3to1` | proved (in the reserve between two commits of batch I9, back since 2026-10-28) | P2, P3, P4 (b) → the next stage, P5 (a) (since 2026-10-27 the staged pump `h' = 0.005 c − 0.001 w h`, `w' = 0.02 (22 − w)`: `w` explicit, `h` by variation of constants over the floor `w ≥ 2c`, barriers keep `0 ≤ h ≤ 2.5`; `w` rises at most 3.2 in `ε_r = 10`, one band) | P2–P4 ok (exit), P5 ok (invariant) |
| 26 | `hvac_fan_staging` | moved to `benchmarks/reserve/` 2026-10-27 (batch I8; was: proved; proof in git history) | LOW, MED, HIGH (b) (contractions to 27, 24, 21 inside `[16, 32]`; a run ends in `[16, 32]`, MED's guard, and MED follows every speed); `ε_r = 1`; dimension 3 (the default padding) | LOW ok (exit→HIGH), MED ok (invariant), HIGH ok (exit→MED) |
| 27 | `rover_terrain_2to4` | proved; fix round 4 (2026-10-29): wheel floor `w ≥ 0.05` (soil-model validity); proof adapted | MUD (b) → GRAVEL, GRAVEL (b) → PAVED, PAVED (a) (terrain-chain lemma; guards the odometer bands only; existence: `v → c_T`, `s` its integral, `w`, `zs` frozen) | MUD ok (exit→GRAVEL), GRAVEL ok (exit→PAVED), PAVED ok (invariant) |
| 28 | `rover_terrain_4to6` | proved; fix round 4 (2026-10-29): wheel and command floors `0.15 → 0.05` (at `0` the stalled rover leaves `v ≥ 0`: BLOCKING); proof adapted | as 27, cap `w ≤ c_T` kept by `w' = 3 (c_T − w)` (existence: the affine cascade `w, zs → v → s` inside the evolve box by the comparison bounds) | as 27 |
| 29 | `rover_terrain_6to12` | moved to `benchmarks/reserve/` 2026-10-30 (batch 11, displaced for letter balance; was: proved, fix round 4 floors 0.13; the proof `InstancesV2/WellFormed/RoverTerrain6to12.lean` is in git history) | - |
| 30 | `rover_patrol_lag` | left the suite 2026-10-30 (batch 10, `benchmarks/skipped/`; the proof is in git history) | - | - |
| 31 | `rover_patrol_zones` | left the suite 2026-10-27 (batch I3; a design of the same name is in `benchmarks/reserve/`; was: proved; proof in git history) | as 30; STALL (a) | as 30; STALL ok (invariant) |
| 32 | `sat3w_detumble_nominal` | moved to `benchmarks/reserve/` 2026-10-27 (batch I4; was: proved; proof in git history) | DETUMBLE (a) (the band in the domain keeps the explicit run); SAFE (a) | both ok (invariant) (both clauses, since 2026-10-26) |
| 33 | `sat3w_detumble_phases` | proved (new three-mode right model 2026-10-27, batch I4) | DETUMBLE, FINE (a) (each guard, `E ≤ 1` resp. `E ≤ 0.125`, forward invariant; since 2026-10-29 the domain is the gyro box `|w_i| ≤ 1`, which the explicit runs keep since each rate decays; until then the band in the domain kept them); SAFE (a) | all ok (invariant) |
| 34 | `sat3w_detumble_weak` | moved to `benchmarks/reserve/` 2026-10-27 (batch I4; was: proved; proof in git history) | NOMINAL, ECONOMY, SURVIVAL (a) (the band in the domain keeps the explicit runs); SAFE (a) | all ok (invariant) |
| 35 | `sat_detumble_nominal` | moved to `benchmarks/reserve/` 2026-10-27 (batch I4; was: proved; proof in git history) | as 32 | as 32 |
| 36 | `sat_detumble_phases` | proved (new three-mode right model 2026-10-27, batch I4) | as 33 | as 33 |
| 37 | `sat_detumble_weak` | proved | NOMINAL, ECONOMY, SURVIVAL (a) (the guard `E ≤ 1` forward invariant; the gyro box `|w_i| ≤ 1` kept by the decaying rates, since 2026-10-29 without the band); SAFE (a) | all ok (invariant) |
| 38 | `rover_attitude_6to8` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 39 | `rover_attitude_8to12` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 40 | `rover_lateral_6to8` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 41 | `rover_lateral_8to12` | left the suite 2026-10-27 (batch I3; a design of the same name is in `benchmarks/reserve/`; was: proved; proof in git history) | as 18 | as 18 |
| 42 | `rover_rollover_6to12` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 43 | `rover_rollover_6to7` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 44 | `rover_rollover_7to12` | left the suite 2026-10-27 (batch I3, the rover hierarchy; was: proved; proof in git history) | as 18 | as 18 |
| 45 | `watertank` | proved | Low (b) → MidEco; MidEco, MidBoost, High, PumpOff (a) | Low ok (exit→MidBoost, same guard); the others ok (invariant) |
| 47 | `lit_drl_car_stop` | skipped 2026-10-29 (literature migration, `benchmarks/skipped/`; was: proved, direct, Coast at `v ≤ 1` since 2026-10-28; proof in git history) | every mode (b) → Coast (`v ≤ 1`) or Brake (`v ≥ 1`) by the end speed; explicit run `x + v t + c t²/2` | Accel ok (exit→Coast,Brake); Coast ok (invariant); Brake ok (exit→Coast) |
| 48 | `lit_drl_lane_control` | proved (direct; follower Coast at `v_f ≤ 1` since 2026-10-28) | every mode (b) → a Coast pair (`v_f ≤ 1`) or a Brake pair (`v_f ≥ 1`), the leader's member by its speed (`v_l ≤ 9` LAccel, `v_l ≥ 1` LBrake); explicit run | all six ok (exit) |
| 49 | `lit_hypercert_vehicle` (left the suite 2026-10-28, `benchmarks/skipped/`; the proof went with it) | was proved (`V2LitHypercertVehicle.lit_hypercert_vehicle_wellFormedR`, since 2026-10-27 with the position coordinate `s ≥ 0`: the explicit run `s₀ + v₀ t + c t²/2`, `v₀ + c t` stays in the domain; before, `ChoiceLitHypercertVehicle.wellFormedR` of the velocity-only model) | every mode (b) → A0 (A0's guard is the domain's velocity range) | A0 ok (invariant); the others ok (exit) |
| 50 | `lit_freedm_meter` | proved (direct) | every mode (b) → GridD0R0 (guard = domain); explicit linear run | battery modes ok (exit); grid modes ok (invariant) |
| 51 | `platoon_linkloss` | proved (2026-10-27; `PlatoonCaccAeb`, shared with row 52); fix round 4 (2026-10-29): the start-only AEB removed, the right is the CACC alone (a); proof adapted | CACC (a) (the projected stop gap `w = g + 2r` obeys `w' = −(w − 20)/4`, so `5 ≤ w ≤ 60` is kept; existence: the explicit two-exponential run stays in the box `0 ≤ g ≤ 60`, `|r| ≤ 10`); AEB (a), latched (`w` conserved; explicit run) | both ok (invariant) |
| 52 | `platoon_latency` | moved to `benchmarks/reserve/` 2026-10-30 (batch 10; the proof is in git history; the shared `PlatoonCaccAeb` stays for `platoon_linkloss`) | - | - |
| 53 | `engine_start_highidle` | proved (2026-10-27); fix round 4 (2026-10-29): start-air supply `p` (frozen, `[0, 60]`) and `STARTER_LOW` (`p < 35`, toward 25.5, the time-out reachable from rest); proof adapted | STARTER, LIGHTOFF, SELF (b) → the next phase (contractions toward 30, 55, 62 inside `[0, 110]`; a run ends in its own band or the next); IDLE (a) (toward 62 from `n ≥ 60`); ABORT (a) (decay inside `[0, 5)`) | STARTER, LIGHTOFF, SELF ok (exit), IDLE, ABORT ok (invariant) |
| 54 | `train_ato_odometry` | proved (2026-10-27) | PL1, PL2, PL3 (a) (contractions toward 25 inside `[5, 27.08]`, guard = domain) | all ok (invariant) |
| 55 | `gantry_speed_zones` | proved (2026-10-27) | MOVE (a) (two independent axis servos toward `(0.5, 0.3)`; the explicit two-exponential run stays in the travel box, guard = domain) | ok (invariant) |
| 56 | `platoon_profiles` | proved (back in the suite 2026-10-27, batch I9, as the time-scaled design; the right model of row 51, `PlatoonCaccAeb`; in the reserve from batch I8 to I9); fix round 4 (2026-10-29): the start-only AEB removed, the right is the CACC alone (a); proof adapted | as 51 | both ok (invariant) |
| 57 | `watertank_twospeed` | proved (redesigned 2026-10-27, six right modes; review round 6, 2026-10-30: the `Fast -> PumpOff` edge removed, edge list adapted) | Fast (b) → Slow or MidEco, Slow (b) → MidEco (contractions toward 12.5); MidEco, MidBoost (a) (toward 17 from below, strictly); High (a) (toward 17 from above); PumpOff (a) (frozen below 2) | Fast ok (exit→Slow,MidBoost); Slow ok (exit→MidBoost); the other four ok (invariant) |
| 58 | `bms_chiller_undercharge` | moved to `benchmarks/reserve/` 2026-10-28 (batch I10; was: proved 2026-10-27, dimension 3, mode choice; proof in git history) | COAST, CHILL_LO, CHILL_HI: every run ends in `[0, 60]`, which COAST's guard `[0, 40]` and CHILL_HI's `[20, 60]` cover (every mode lists every mode); existence: contractions toward 50, 30, 20 | COAST ok (exit→CHILL_HI); CHILL_LO, CHILL_HI ok (invariant) |
| 59 | `canal_gate_notches` | proved (back in the suite 2026-10-29, fix round 4, for `grid_ffr_dos`; its batch-I5 proof restored, dimension 3, mode choice; in `benchmarks/reserve/` from batch I8) | N100, N75, N50, N25: every run ends in N50's guard (the whole domain `[0, 1.2]`); existence: contractions toward 1, 0.75, 0.5, 0.25 | N100, N25 ok (exit→N50); N75, N50 ok (invariant) |
| 60 | `turbine_startup_gearratio` | proved (2026-10-27); rewritten batch 10 (2026-10-30: STOP removed, REG and GUST added, gust amplitude `G ≤ 5.03` and gust clock `t`, dimension 3) | SPINUP (b) → RAMP, RAMP (b) → GEN, GEN (b) → REG (explicit exponentials, `linear_between`); REG (a) at `w ≥ 11.979`; GUST (a) by the lower barrier at 11.979 (field `1.3125 (12.1 − w) + 0.24 G > 0` below it) | SPINUP, RAMP, GEN ok (exit); REG, GUST ok (invariant) |
| 61 | `molding_pack_checkring` | proved (back from the reserve 2026-10-30, review round 6, in place of `charger_fast_tapers`; domain the 2000 bar pressure rating; in `benchmarks/reserve/` from batch I11, proved 2026-10-27, batch I5) | HOLD (b) → COOL (the clock; the nozzle pressure's approach to 500 and the cavity pressure by variation of constants, `forcedSol`, inside the rating `[0, 2000]`); COOL (a) (the clock does not fall; two decays) | HOLD ok (exit→COOL); COOL ok (invariant) |
| 62 | `fuelcell_chp_dos` | skipped 2026-10-30 (batch 11, `benchmarks/skipped/fuelcell_chp_dos/SKIPPED.md`; was: proved, dimension 3; the proof `InstancesV2/WellFormed/FuelcellChpDos.lean` is in git history) | - |
| 63 | `elevator_start_discbrake` | proved (2026-10-27, batch I5; STOP's guard carries the rest position `z + v/4 ≤ 20.5` since its installation: without it STOP is BLOCKING at `z = 20.5`, `v > 0`) | LIFT (b) → UP (the car held, the brake toward 1); UP (b) → APP (`z` grows by at most `0.17`, `b ≥ 0.95` kept); APP (b) → STOP (`z < 20.07`, `v ≤ 1.7`, so `z + v/4 < 20.495`); STOP (a) (`z + v/4` conserved, `z` does not fall); existence: explicit exponentials, `z` the integral of `v` (`intSol`) resp. its closed form in STOP | LIFT ok (exit→UP); UP ok (exit→APP); APP ok (exit→STOP); STOP ok (invariant) |
| 64 | `furnace_program_timebase` | proved (2026-10-27, batch I5) | PREHEAT (b) → HEAT, HEAT (b) → SOAK (the set point rises toward 650 resp. 870, `linear_up`); SOAK (a); existence: the set point's exponential, the load by variation of constants inside `[20, 900]` | PREHEAT ok (exit→HEAT); HEAT ok (exit→SOAK); SOAK ok (invariant) |
| 65 | `compressor_station_recycle` | moved to `benchmarks/reserve/` 2026-10-28 (batch I11; was: proved 2026-10-27, batch I5, dimension 3, mode choice; proof in git history) | LOW, MED, HIGH: every run ends in the box, MED's guard (every level lists every level); existence: two independent exponentials toward the level's equilibrium | LOW ok (exit→HIGH); MED ok (invariant); HIGH ok (exit→MED) |
| 66 | `syringe_relay_prearm` | proved (2026-10-27, batch I5) | RUN1 (b) → TAKEUP2 or RUN2; TAKEUP2 (b) → RUN2; RUN2 (b) → END (the moving volume or take-up passes its threshold, the frozen coordinates keep the guard's other atoms); END (a); existence: linear motions below 50 resp. 1.2, `C` toward its level | RUN1 ok (exit→TAKEUP2,RUN2); TAKEUP2 ok (exit→RUN2); RUN2 ok (exit→END); END ok (invariant) |
| 67 | `hydro_rejection_gatecal` | proved (2026-10-27, batch I5) | ONGRID (b) → REJECT (the speed held by the grid, the gate toward `0.85 − 20 w`); REJECT (a) (the clock does not fall; `w` by variation of constants inside `[−1, 1]`) | ONGRID ok (exit→REJECT); REJECT ok (invariant) |
| 68 | `ventilator_vc_cuffleak` | proved (2026-10-27, batch I5; review round 6, 2026-10-30: inspiratory countdown timer `s`, domain `s ≥ 0`, `V ≥ −0.4`, proof rewritten) | INSP (b) → EXP (the timer falls from `s₀ ≥ 0.01`, so it stays `≥ 0` for one period; `V` rises at 0.4; `s < 0.01` is EXP's guard); EXP (a) (the timer is frozen; `V` decays toward 0, above `min V₀ 0 ≥ −0.4`) | INSP ok (exit→EXP); EXP ok (invariant) |
| 69 | `insulin_basal_cgmloss` | skipped 2026-10-29 (literature migration, in place of `rampmeter_poll_2to1`; was: proved, batch I5, back in the suite later in batch I11 rounds; proof in git history) | every level (b) → a neighbour (the 5-minute glucose motion bound: the field of `G` lies in `[−5.6, 2.42]` on the domain, so `G` moves by less than one 30 mg/dL band in one interval); existence: `X` toward `0.2 q`, `G` by variation of constants inside `[40, 400]` | all nine ok (exit) |
| 70 | `rover_rollover_payload` | moved to `benchmarks/reserve/` 2026-10-27 (batch I8; was: proved, batch I5, dimension 12, mode choice; proof in git history) | STEEP (b) → MODER, MODER (b) → FLAT (the odometer bands `[0, 62)`, `[58, 142)`, `[138, ∞)`: `0 ≤ s' ≤ 8` on the box), FLAT (a); the back edges are never needed. Existence: the roll-slip block `(φ, ω_φ, y, ω_y)` is coupled both ways, so the run comes from Picard–Lindelöf on an enlarged box `B_δ` whose 22 faces are all strictly inflowing (`strict_faces_raw`; the field reads no `s`, no left or auxiliary coordinate, so its Lipschitz data on any ball around a `B_δ` point are those of one fixed ball), glued by `chainN`; on that run the true box is recovered coordinate by coordinate (`drive_le`, driven contractions with the forcing bounds `|ω_φ| ≤ 0.28`, `|ω_y| ≤ 0.45`) | STEEP ok (exit→MODER); MODER ok (exit→FLAT); FLAT ok (invariant) |
| 71 | `flaps_slow_approach` | proved (batch I6; back in the suite 2026-10-27, batch I9, in the reserve from batch I8 to I9) | EXT (b) → CONF2 (the flaps rise at 1 deg/s from below 15 and end below 15.1); CONF2 (a) (the flaps set); existence: `f = f₀ + r t`, `V = 150 + (V₀ − 150) exp(−((0.02 + 0.001 f₀) t + r t²/2000))` (the flap drag grows with the angle), inside `[150, V₀]` | EXT ok (exit→CONF2); CONF2 ok (invariant) |
| 72 | `tunnel_jetfan_pairout` | skipped 2026-10-29 (domain audit: `benchmarks/skipped/tunnel_jetfan_pairout/SKIPPED.md`; the proof left with it; was: proved 2026-10-27, batch I6; the first polynomial right field, `u²` and `u c`) | NORMAL (b) → FIRE (the clock; `c ≤ 100` kept: at `c ≥ 100`, `u ≥ 2.6` the airflow flushes CO faster than traffic emits it); FIRE (a) (`t ≥ 600` kept); existence: the explicit Riccati run `u = U((U + u₀)e^{2bUs} − (U − u₀)) / ((U + u₀)e^{2bUs} + (U − u₀))` between `u₀` and `U = √(a/b)`, `c` by variation of constants with the rate `u(s)/1600`, inside `[0, 900]` | NORMAL ok (exit→FIRE); FIRE ok (invariant) |
| 73 | `rampmeter_poll_2to1` | proved (batch I6; in the reserve 2026-10-27 to 2026-10-29, back in the suite in place of `insulin_basal_cgmloss` with the band 8, right model unchanged, batch-I6 proof restored) | every level (b) → a declared neighbour (the 20 s density envelope: `k` between `L + (k₀ − L)E` and `U + (k₀ − U)E`, `L = 10 + r`, `U = 27.5 + r`, `E = e^{−0.01 t} ≥ 0.8`, by two comparison lemmas); existence: `kd` held, `k1` toward `kd`, `k` by variation of constants inside `[14, 42.5]` | all six ok (exit) |
| 74 | `bottling_fill_strainer` | proved (2026-10-27, batch I6) | FILL (b) → CLOSE (`u = 1` held, `V` rises at most 1 mL in 5 ms, `V + 8u ≤ 1003`); CLOSE (a) (`V` nondecreasing, `V + 8u` conserved: the guard conjunct `V + 8u ≤ 1060` added at installation, without which CLOSE was BLOCKING at the domain top); existence: explicit (`u` frozen, resp. `u₀ e^{−25t}` and `V + 8u` constant) | FILL ok (exit→CLOSE); CLOSE ok (invariant) |
| 75 | `antenna_track_kvretune` | back in the suite 2026-10-29 (domain audit; the proof of fb55b6e restored unchanged; between: moved to `benchmarks/reserve/` 2026-10-28, batch I11; was: proved 2026-10-27, batch I6; proof in git history) | TRACK (b) → STOW (`c + 0.7 t` conserved; at `t ≥ 60`, `c ≤ 47.05 < 90`), STOW (b) → STOWED, STOWED (a); existence: `t`, `c` affine, `x` by variation of constants toward the command (`forcedSol 30`), inside `[−2, 92]` | TRACK ok (exit→STOW); STOW ok (exit→STOWED); STOWED ok (invariant) |
| 76 | `grid_ffr_dos` | skipped 2026-10-29 (fix round 4: the band did not depend on the attack; `benchmarks/skipped/grid_ffr_dos/SKIPPED.md`; was: proved, 2026-10-27, batch I7; proof in git history) | NORMAL (b) → FFR (`a = 0` frozen; on `a = 0` the three guards cover the domain: `x > −0.4`, `[−1.5, −0.4]`, `x < −1.5`); FFR (b) → TRIP or itself (the release line `x − 2a ≤ −0.4` kept by a non-strict barrier, Lie derivative `≤ 5.375 a − 6.25 d − 8.95 < 0`); TRIP (a) (`x` falls toward `−2.5`); existence: `a = 1 + (a₀ − 1) e^{−k t}` (`k = 0`, `5`), `x` by variation of constants (`forcedSol`) inside `[min x₀ (−5/7), max x₀ (5/42)]`, TRIP by `exists_contract_run` | NORMAL ok (exit→FFR); FFR, TRIP ok (invariant) |
| 77 | `lit_csf21_vehicle_thermo` | proved (2026-10-27, batch I8; direct, `_wellFormedR_direct`; Coast at `v ≤ 1` since 2026-10-28) | every mode (b) → Coast* (`v ≤ 1`) or Brk* (`v ≥ 1`) by the end speed, *Cool or *Heat by the end temperature (explicit run `d − v t − c t²/2`, `v + c t`, `temp ± t`; Acc from `v ≤ 39`, Brk from `v ≥ 1` keep `0 ≤ v ≤ 40`) | all six ok (exit) |
| 78 | `lit_csf21_vehicle_bus` | proved (2026-10-27, batch I8; direct; Coast at `v ≤ 1` since 2026-10-28) | every Cool mode (b) → CoastCoolA (`v ≤ 1`) or BrkCoolA (`v ≥ 1`), every Heat mode (b) → CoastHeatA or BrkHeatA, by the end speed; the same explicit run | CoastCoolA, CoastHeatA ok (invariant); the other ten ok (exit) |
| 79 | `lit_lz21_vehicle_position` | proved (2026-10-27, batch I8; direct) | every mode (b) → U0 (its guard `0 ≤ v ≤ 0.1` is the speed part of the domain); explicit run `x + v t + c t²/2`, `v + c t` (Um from `v ≥ 0.05`, Up from `v ≤ 0.05`) | Um ok (exit→Up), U0 ok (invariant), Up ok (exit→U0) |
| 80 | `lit_girard08_robot` | proved (2026-10-27, batch I8; direct, dimension 6; the right evolve domain is the constant atom `0.0 <= 1.0`) | every location (b) → itself or the next location (constant headings of norm 0.2: one interval moves each coordinate by at most 0.2, across at most one line of the 0.4-enlarged invariants); explicit linear run | all six ok (exit) |
| 82 | `zone_lightmass_schedule` | skipped 2026-10-29 (literature migration, `benchmarks/skipped/`; was: proved, 2026-10-28, batch I10, dimension 2; proof in git history) | COMFORT, STANDBY, ECONOMY (a): every run ends in `[5, 30]`, every level's guard (every level lists every level); existence: contractions toward 21, 19, 16 at rate 0.02 /min, `exists_contract_run` | all three ok (invariant) |
| 83 | `h2_refuel_ambientbias` | proved (2026-10-28, batch I11; from the reserve); fix round 4 (2026-10-29): the start-only ABORT removed, STAGE1 from `p = 0`; proof adapted | STAGE1, STAGE2, STAGE3, TOPOFF (b) → the next stage (contractions toward 20, 40, 60, 70.5 inside `[0, 87.5]`; a run ends in its own band or the next); COMPLETE (a) (held at `p ≥ 70`); ABORT (a) (held below 0.5); existence: the explicit exponential, `exists_contract_run` with `k = 0` for the held modes | STAGE1 ok (exit→STAGE2), STAGE2 ok (exit→STAGE3), STAGE3 ok (exit→TOPOFF), TOPOFF ok (exit→COMPLETE); COMPLETE, ABORT ok (invariant) |
| 84 | `reactor_feed_wireless` | proved (2026-10-28, batch I11; from the reserve; dimension 2) | F1 to F4: every run ends in `[15, 60] × [15, 35]`, which the four guards cover (`T < 25`, `[25, 35)`, `[35, 45]`, `T > 45`; every level lists every level); existence: `T` toward `p + 4, 8, 12, 16 ∈ [19, 51]`, `p` held (`trajRs_sol`) | F1 ok (exit→F2), F2 ok (exit→F1,F3), F3 ok (exit→F2,F4), F4 ok (exit→F3) |
| 81 | `lit_nahs25_salt_tank` | proved (2026-10-27, batch I8; direct; no evolve domain since 2026-10-28, the constant atom `0 ≤ 1` as `lit_girard08_robot`) | On (a) (every run stays `≥ 25`, `ODESol.linear_down`; explicit run `25 + (xp − 25) e^{−t/10}`); Off (a) (the constant run; the strict guard atom `xp < 25` carried exactly) | both ok (invariant) |
| 85 | `lit_gpt10_boost_converter` | proved (2026-10-29, literature migration; direct; dimension 3) | P1, P2 (a): guards and domain the constant atom `0 ≤ 1`, so every end state enables the self-loop; existence for every length from the affine field's global Lipschitz bound (`exists_odeSol_of_lipschitz`, `Proofs/Flow/LipschitzRun.lean`) | P1 ok (invariant); P2 ok (invariant) |
| 86 | `lit_csf25_salt_tank_hold` | proved (2026-10-29, literature migration; direct; dimension 3) | Inc, Dec (b): the guards `xp < 35` / `xp ≥ 35` partition the level, both declared successors of both; existence by the Lipschitz route over the whole space, the level kept between its start and the mode's set point (`ODESol.linear_between` on every prefix), inside `[0, 300]` | Inc ok (exit→Dec); Dec ok (exit→Inc) |
| 87 | `boiler_purge_vfd` | proved (2026-10-30, batch 10, new; dimension 3: purge credit `v`, pressure `p`, offset `e`) | PURGE (b) → FIRE (`v = v₀ + t/100`, `p`, `e` constant); FIRE (a) (`v` frozen at `≥ 5`; `p` the exponential approach to 10 in `[−1, 16]`) | PURGE ok (exit→FIRE); FIRE ok (invariant) |
| 88 | `autoclave_liquid_steambank` | proved (2026-10-30, batch 10, new; dimension 3: chamber `c`, load `T`, counter `t`) | HEAT (b) → EQUIL / EXPOSE (ramp `c' = 4`, load `forcedSol`), EQUIL (b) → EXPOSE, EXPOSE (b) → EXHAUST (`T ≥ min(T₀, c₀) ≥ 121` by `linear_between`), EXHAUST (a) (`t` frozen) | HEAT, EQUIL, EXPOSE ok (exit); EXHAUST ok (invariant) |
| 89 | `lit_nahs25_engine_cooling` | proved (2026-10-30, batch 11, new; direct, dimension 3; the pre-landing demo's proof `EngineCoolingPrelanding.lean` under the suite name) | Cool (b) → Heat (the linear descent `temp − t/2`, above 99.5 within a cycle from `temp ≥ 100`), Heat (b) → Cool (the linear ascent `temp + t`); every end state is in `temp ≥ 100` or `temp ≤ 100`, both modes declare both; Z3-free |
| 90 | `extruder_pe100_manualstart` | proved (2026-10-30, batch 11, new; dimension 2, as `reactor_feed_wireless`) | N1..N4 (b): explicit exponential `(p + r) + (T − p − r) e^{−t/2}`, `p` held; the recipe range `180 ≤ p ≤ 220` from the guard puts `p + r ∈ [181.33, 242]` inside `130 ≤ T ≤ 300`; the four guards partition the domain, every step declares every step; Z3-free |

Totals (the suite, 2026-10-28, batch I11): proved 47, false 0, band 3
(`WellFormedBattery.wfDeclared = (47, 0, 3)`, was `(30, 9, 6)` until the 2026-10-10 repairs;
`wf_coverage` checks in the kernel that the three name lists are a permutation of the suite's
IR table). Z3-free: 50/50. Region-relative: none since 2026-10-15 (the 3 satellites' `wfBand` list is kept for their band audit, `_band_invariant`).

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
body's momentum, and a constant of every design-model flow. From 2026-10-15 to 2026-10-29 it was part of the
right evolve domains. Since 2026-10-29 (one physical domain per benchmark, the same on both sides)
it is not: it is not a first integral of the left (the gyroscopic couplings, e.g.
`d/dt (h + 5 w3) = −2 w1 w2`), so on the left it would be a reachable-set band; the wheel box
`|h| ≤ 2` went with it (the design model's flow `h' = 5 k w3` crosses it, which is the blocking state
above); the domain is the gyro box `|w_i| ≤ 1`, the claim (energy) does not read `h`, the covers are
unchanged, and Assumption 1 holds literally on the new domain.

## 4. The tool check (`relcert --wellformed`)

`Trusted/WellFormedCheck.lean`. Per right mode, a cheap SUFFICIENT check of both clauses,
clause (ii) first:

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

Then clause (i), on a mode whose clause (ii) is shown (since 2026-10-26; until then clause (i)
was not checked). It must show that from every state of `X₀ = G ∧ D` the solution of the
mode's (polynomial) field exists on `[0, ε_r]` and stays in `D`, which is the first conjunct
of `WellFormedRModeIn` with its domain conjunct. `I` are the facts of steps 1/1b (valid along
every run inside `D` from `X₀`).

4. **The domain persists, atom by atom.** Each atom `d ≤ 0` of `D` persists past the first
   time `τ < ε_r` the solution would leave the atoms shown so far, by: (R1) contraction
   shape or frozen (exact for the unconstrained flow); (R3) `UNSAT(D ∧ I ∧ d = 0 ∧ ḋ ≥ 0)`;
   (R5) `UNSAT(P ∧ ¬(d ≤ 0))`; (R4) `UNSAT(P ∧ ḋ > 0)`; (R6, a threshold atom `x ⋈ c`)
   `UNSAT(P ∧ ḋ[x := c] > 0)`, since `ḋ − ḋ[x := c]` is a polynomial multiple of `d`; (R2,
   the interval margin) a rate bound `UNSAT(D ∧ I ∧ ḋ > L)` and `UNSAT(X₀ ∧ d + L ε_r > 0)`.
   `P` is the conjunction of the atoms shown before (sequential, never mutual); the closures
   of the guard atoms are optional candidates for `P`. DI route A over `D` is deliberately
   not a route: it speaks only of runs that stay in `D`, the thing to be shown.
5. **Or the domain polyhedron persists.** All domain atoms closed and affine: the polyhedron
   `K` of the domain atoms and the affine candidates is invariant when the field points
   inward on every face, `UNSAT(K ∧ k = 0 ∧ k̇ > 0)` per atom `k` (Nagumo / Bony–Brezis for a
   polyhedron and a locally Lipschitz field), a greatest fixpoint over the candidates. The
   satellites used it until 2026-10-29 (`h ≤ 2` under `h' = 2.5 w₃` held on its face because the
   conserved band gave `h + 5 w₃ ≤ 2`; their domain is now the gyro box), as do the `platoon3` sinks (`g₁ ≥ 0` with the guard's
   conserved `g₁ + 2 r₁ ≥ 0`) and the `rover_lateral` pairs (`y ≤ 0.5` with `y + w ≤ 0.5`).
6. **Existence.** An affine field has global solutions; otherwise every moving coordinate's
   field is bounded on `D ∧ I` (`|fᵢ| ≤ 10⁴`), so the solution cannot blow up before `ε_r`.

A domain atom no route keeps is tested for an immediate exit, `SAT(X₀ ∧ d = 0 ∧ ḋ > 0)`: a
start state leaves `D` at once, so no run of duration `ε_r > 0` exists, clause (i) is false
and the mode is **`BLOCKING (leaves d)`** (a `sat` answer only ever marks a failure).
Otherwise **`UNKNOWN (nonblocking)`**: clause (ii) shown, clause (i) not (a later exit, as in
a variant of `lit_hypercert_vehicle` whose `Am4` guard admits `v = 0.02` under `v' = −0.04`, is
`UNKNOWN`, never `ok`). An `ok` mode keeps its clause (ii) label (`invariant` / `exit→S`, the
Lean styles (a) / (b)); `ok` means both clauses.

Only `unsat` counts. Output: `[wellformed] <bench>: q1 ok (invariant) | q2 ok (exit→q3) | q4
UNKNOWN | q5 UNKNOWN (nonblocking) | q6 BLOCKING (leaves d) (N queries)` and `[wellformed]
summary: …` (with `RELCERT_DEBUG=1`, the reason of every mode not `ok` on stderr).
`--check-quick-v2` runs the same section as its check 3/3, strict (below); until 2026-10-10 it
was informational there.

**Suite_v2 result** (2026-10-30, both clauses, review round 6): 50 benchmarks, 176 right
modes: 78 ok (invariant), 98 ok (exit), **0 UNKNOWN, 0 BLOCKING** (literature migration,
2026-10-29: 181 right modes, 80 / 101, 12326 queries; batch I11,
2026-10-28: 184 right modes, 88 / 96, 12291 queries; batch I9: 180 right modes, 86 / 94, 12581 queries; batch I8: 187 right
modes, 85 / 102, 13428 queries); the per-mode labels are those of the
clause (ii) check alone (2026-10-26, 50 benchmarks: 174 right modes, 91 / 83, 10643 queries,
about 17 s). The 37
round-2 designs of the 2026-10-26 redesign pass (outside the tree): 122 right modes, 69 ok
(invariant), 53 ok (exit), 0 UNKNOWN, 0 BLOCKING, labels unchanged.

**The blocking exhibit** `benchmarks/negative_wellformed/lit_hypercert_vehicle_s8` (the round-2
variant with `s ≤ 8` in every evolve domain; self-contained, it stays after its suite benchmark was skipped on 2026-10-28): the default run CERTIFIES it, clause (ii) alone
finds all five right modes `ok`, the two-clause check finds all five `BLOCKING (leaves s <= 8.0)`
(at `s = 8`, `v > 0` the flow leaves at once), and `RELCERT_WELLFORMED_STRICT=1` DECLINES it.

**Clause (ii) on the repaired models** (2026-10-10): 45 benchmarks, 146 right modes: 83 ok
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

**The switch** `RELCERT_WELLFORMED_STRICT=1`: a CERTIFIED benchmark with an `UNKNOWN` or
`BLOCKING` right mode becomes DECLINED (a `[wellformed] STRICT` line on stderr says why). Off by default for a
single `relcert <file>` run; off, no verdict and no emission changes.

**Strict in the recipe** (2026-10-10). `--check-quick-v2` certifies the suite in the strict
mode (the switch forced on for its check 1/3) and ends with check 3/3, the `--wellformed`
report gated against declared counts: `ExpectedSuiteV2.wfModes = 176` (2026-10-30; `VerdictsV2/RunV2.lean`; the
kernel pin `CoveragePinsV2.suiteV2_wfModes` of that count was archived with the standalone
route on 2026-10-22), `wfUnknown = 0` and `wfBlocking = 0`. Any `UNKNOWN` or `BLOCKING` mode,
or a mode count off the declared one, fails the run (`wellformed (strict): FAIL`, exit 1). Checked negatively: with the pre-repair
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
`wellFormedR_lift (n := n0) pad_ok`, then `WellFormedRIn.of_tt` at `reg = ⊤`. The
hand-written `InstancesV2/Choice/General/` exhibits (two since 2026-10-27, when `lit_hypercert_vehicle`
moved to `InstancesV2/WellFormed/`) keep only their Assumption 1 proofs
(their Theorem-3 parts were retired on 2026-10-21, fixed at `Var 2` with no slot for the
right clock); those proofs are lifted the same way into the corresponding bridge instances.
Nothing in this file's battery or audit (§5) changes: the lift is a generic lemma at the
three standard axioms, applied inside the bridge instances.
