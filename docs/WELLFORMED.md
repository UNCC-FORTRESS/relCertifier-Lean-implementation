# Assumption 1, verified per benchmark (`WellFormedR`)

The paper's Assumption 1 (Well-Formedness) is a separately stated, kernel-checked model fact
for every one of the 50 suite_v2 benchmarks: **proved for all 50**, **false for none**, no proof
uses Z3. 40 are stated over the benchmark's standalone right automaton (`<ns>.<b>_wellFormedR`)
and transported onto the bridge's graph; the 10 literature benchmarks are proved directly over
the bridge's automaton (`<ns>.<b>_wellFormedR_direct`, with explicit polynomial runs,
`trajRs_sol`). The 3 satellites are proved on their declared domain, the gyro box `|w_i| ≤ 1`
(§3). The tool's sufficient check of both clauses (`relcert --wellformed`) finds every one of
the 181 right modes `ok` (75 by invariance, 106 by exit), and `--check-quick-v2` runs it
STRICT, against declared counts (§4). The generic-bridge instances (`InstancesV2/Bridge/`, the
paper's route to Theorem 3) take it as a hypothesis: `theorem3_keyed_of_records`
(`Proofs/Encoding/Emitted/Keyed.lean`) and `theorem3_window_of_records`
(`Emitted/Window.lean`) take `hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg
(epsR p)`, which each generated instance discharges from the benchmark's `WellFormedR` lemma,
transported and lifted by one coordinate (§6). Assumption 1 is therefore a hypothesis of the
bridge theorems and a proved fact, never a trust item. Former suite benchmarks (their rows,
proofs and repairs) are in the git history; `benchmarks/reserve/` and `benchmarks/skipped/`
are kept at the tag `pre-cleanup-2026-11`.

## 1. The paper's statement and the predicate

The paper: *the right model is nonblocking and complete with respect
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
* **(c) region-relative** (`WellFormedRIn` with a region kept by every right flow): no suite
  benchmark uses it. The satellites are style (a) on the gyro box `|w_i| ≤ 1`: the explicit
  solution's rates decay (`|w_i(t)| = |w_i(0)| e^{−kt}`), `h` is unconstrained.

Generic lemmas (`WellFormedR.lean`): closed form of a linear coordinate at the run's duration
(`ODESol.linear_exact`, `linear_between`, `linear_up/down/lt/gt`), rate bounds
(`ODESol.rate_le/ge`, `mono`, `const`), one-coordinate barriers for nonlinear fields
(`ODESol.coord_le_barrier/ge_barrier`, via `DI_nonstrict_superlevel`), conserved affine
combinations (`ODESol.affine_const`), magnitude decay (`decay_sq_le`), explicit runs
(`trajJ_sol`, `exists_contract_run`, `exists_rate_run`, `const_sol`), existence from the
instances' viability route with the left held still and a time rescaling
(`exists_of_HExistSegB_zero`, `ODESol.reparam`), and the refutation lemmas
(`not_wellFormedR_of_run`: one explicit run that ends outside every successor guard;
`not_wellFormedR_of_noRun`: no run of duration `ε`). `WellFormedLadder.lean`: `wellFormedR_ladder`, for terrain ladders at an older scale (no suite
benchmark uses it). `WellFormedTerrain.lean`: one theorem
(`wellFormedR_terrain`) for the terrain chain (`MUD`, `GRAVEL`, `PAVED` odometer bands `[0, 5)`,
`[5, 12)`, `[12, ∞)`, an optional cap `x_c ≤ c_T` kept by a contraction) and the four ladder rungs (`STEEP`, `MODER`, `FLAT` at `[0, 60)`, `[60, 140)`, `[140, ∞)`, no cap),
and the explicit runs of
affine cascades (`forcedSol`: `y' = F t − k y` by variation of constants; `intSol`) with their
comparison bounds (`forcedSol_between`, `mono_of_deriv_nonneg`). `WellFormedStopline.lean`: `wellFormedR_stopline`, for the four stop-line rungs.
`InstancesV2/WellFormed/PlatoonCaccAeb.lean`: the CACC follower's band and box
(`cacc_w_band`, `aeb_w_const`, `cacc_box`) and its explicit runs (`cacc_exists`, `aeb_exists`).

Existence (clause (i)) is always an explicit or instance-supplied run: the exponential and
linear solutions, the ladders' `LadderRun.sol` (and `runE` / `run_sol` / `drive_sol`, the
instances' explicit runs with their duration kept), the platoon follower's `link_sol`, the
satellites' `flowR_exists` (the decaying rates keep the gyro box), and for `w' = c − w²` the instances' viability route
(both faces strict, hand Lipschitz data). **No Z3 leaf** anywhere: the pinned-query discipline
was not needed.

## 3. Per benchmark

Theorems: `<ns>.<b>_wellFormedR` or `<ns>.<b>_wellFormedR_direct` (proved), for the 3
satellites also `<ns>.<b>_band_invariant` (the conserved momentum band is kept by every right
mode's flow, a model fact of the design model, audited beside the proofs). Files:
`InstancesV2/WellFormed/<B>.lean`, each self-contained (right model and proof; 54 files: the
50 benchmarks, the shared `PlatoonCaccAeb.lean`, and the three demo models
`EngineCoolingPrelanding`, `HoldRepositionStrict`, `StoplineFrictionMixed`). Battery:
`InstancesV2/WellFormedBattery.lean`. Tool column: the `relcert --wellformed` labels recorded
with each proof (§4 has the current suite totals). Z3 leaves: none for every row.

| # | benchmark | theorem | modes: style | tool check |
|---|---|---|---|---|
| 1 | `acc_spoof_lag` | `V2AccSpoofLag.acc_spoof_lag_wellFormedR` | CRUISE (a) (the lagged loop's envelope, modal coordinates `a + 2v − 60`, `3a + 2v − 60` decaying; explicit two-exponential run) | ok (invariant) |
| 2 | `acc_spoof_limp` | `V2AccSpoofLimp.acc_spoof_limp_wellFormedR` | NORMAL, ECO, SPORT (a) (closed guards `20 ≤ v ≤ 40`, set points 27 / 30 / 33 inside, `linear_between`) | all ok (invariant) |
| 3 | `acc_tune_limp` | `V2AccTuneLimp.acc_tune_limp_wellFormedR` | NORMAL (a); DISENGAGE (a) | all ok (invariant) |
| 4 | `antenna_track_kvretune` | `V2AntennaTrackKvretune.antenna_track_kvretune_wellFormedR` | TRACK (b) → STOW (`c + 0.7 t` conserved; at `t ≥ 60`, `c ≤ 47.05 < 90`), STOW (b) → STOWED, STOWED (a); existence: `t`, `c` affine, `x` by variation of constants toward the command (`forcedSol 30`), inside `[−2, 92]` | TRACK ok (exit→STOW); STOW ok (exit→STOWED); STOWED ok (invariant) |
| 5 | `autoclave_liquid_steambank` | `V2AutoclaveLiquidSteambank.autoclave_liquid_steambank_wellFormedR` | HEAT (b) → EQUIL / EXPOSE (ramp `c' = 4`, load `forcedSol`), EQUIL (b) → EXPOSE, EXPOSE (b) → EXHAUST (`T ≥ min(T₀, c₀) ≥ 121` by `linear_between`), EXHAUST (a) (`t` frozen) | HEAT, EQUIL, EXPOSE ok (exit); EXHAUST ok (invariant) |
| 6 | `boiler_purge_vfd` | `V2BoilerPurgeVfd.boiler_purge_vfd_wellFormedR` | PURGE (b) → FIRE (`v = v₀ + t/100`, `p`, `e` constant); FIRE (a) (`v` frozen at `≥ 5`; `p` the exponential approach to 10 in `[−1, 16]`) | PURGE ok (exit→FIRE); FIRE ok (invariant) |
| 7 | `bottling_fill_strainer` | `V2BottlingFillStrainer.bottling_fill_strainer_wellFormedR` | FILL (b) → CLOSE (`u = 1` held, `V` rises at most 1 mL in 5 ms, `V + 8u ≤ 1003`); CLOSE (a) (`V` nondecreasing, `V + 8u` conserved: the guard conjunct `V + 8u ≤ 1060` added at installation, without which CLOSE was BLOCKING at the domain top); existence: explicit (`u` frozen, resp. `u₀ e^{−25t}` and `V + 8u` constant) | FILL ok (exit→CLOSE); CLOSE ok (invariant) |
| 8 | `canal_gate_notches` | `V2CanalGateNotches.canal_gate_notches_wellFormedR` | N100, N75, N50, N25: every run ends in N50's guard (the whole domain `[0, 1.2]`); existence: contractions toward 1, 0.75, 0.5, 0.25 | N100, N25 ok (exit→N50); N75, N50 ok (invariant) |
| 9 | `elevator_start_discbrake` | `V2ElevatorStartDiscbrake.elevator_start_discbrake_wellFormedR` | LIFT (b) → UP (the car held, the brake toward 1); UP (b) → APP (`z` grows by at most `0.17`, `b ≥ 0.95` kept); APP (b) → STOP (`z < 20.07`, `v ≤ 1.7`, so `z + v/4 < 20.495`); STOP (a) (`z + v/4` conserved, `z` does not fall); existence: explicit exponentials, `z` the integral of `v` (`intSol`) resp. its closed form in STOP | LIFT ok (exit→UP); UP ok (exit→APP); APP ok (exit→STOP); STOP ok (invariant) |
| 10 | `engine_start_highidle` | `V2EngineStartHighidle.engine_start_highidle_wellFormedR` | STARTER, LIGHTOFF, SELF (b) → the next phase (contractions toward 30, 55, 62 inside `[0, 110]`; a run ends in its own band or the next); IDLE (a) (toward 62 from `n ≥ 60`); ABORT (a) (decay inside `[0, 5)`) | STARTER, LIGHTOFF, SELF ok (exit), IDLE, ABORT ok (invariant) |
| 11 | `extruder_pe100_manualstart` | `V2ExtruderPe100Manualstart.extruder_pe100_manualstart_wellFormedR` | N1..N4 (b): explicit exponential `(p + r) + (T − p − r) e^{−t/2}`, `p` held; the recipe range `180 ≤ p ≤ 220` from the guard puts `p + r ∈ [181.33, 242]` inside `130 ≤ T ≤ 300`; the four guards partition the domain, every step declares every step; Z3-free |
| 12 | `flaps_slow_approach` | `V2FlapsSlowApproach.flaps_slow_approach_wellFormedR` | EXT (b) → CONF2 (the flaps rise at 1 deg/s from below 15 and end below 15.1); CONF2 (a) (the flaps set); existence: `f = f₀ + r t`, `V = 150 + (V₀ − 150) exp(−((0.02 + 0.001 f₀) t + r t²/2000))` (the flap drag grows with the angle), inside `[150, V₀]` | EXT ok (exit→CONF2); CONF2 ok (invariant) |
| 13 | `furnace_program_timebase` | `V2FurnaceProgramTimebase.furnace_program_timebase_wellFormedR` | PREHEAT (b) → HEAT, HEAT (b) → SOAK (the set point rises toward 650 resp. 870, `linear_up`); SOAK (a); existence: the set point's exponential, the load by variation of constants inside `[20, 900]` | PREHEAT ok (exit→HEAT); HEAT ok (exit→SOAK); SOAK ok (invariant) |
| 14 | `gantry_speed_zones` | `V2GantrySpeedZones.gantry_speed_zones_wellFormedR` | MOVE (a) (two independent axis servos toward `(0.5, 0.3)`; the explicit two-exponential run stays in the travel box, guard = domain) | ok (invariant) |
| 15 | `h2_refuel_ambientbias` | `V2H2RefuelAmbientbias.h2_refuel_ambientbias_wellFormedR` | STAGE1, STAGE2, STAGE3, TOPOFF (b) → the next stage (contractions toward 20, 40, 60, 70.5 inside `[0, 87.5]`; a run ends in its own band or the next); COMPLETE (a) (held at `p ≥ 70`); ABORT (a) (held below 0.5); existence: the explicit exponential, `exists_contract_run` with `k = 0` for the held modes | STAGE1 ok (exit→STAGE2), STAGE2 ok (exit→STAGE3), STAGE3 ok (exit→TOPOFF), TOPOFF ok (exit→COMPLETE); COMPLETE, ABORT ok (invariant) |
| 16 | `hydro_rejection_gatecal` | `V2HydroRejectionGatecal.hydro_rejection_gatecal_wellFormedR` | ONGRID (b) → REJECT (the speed held by the grid, the gate toward `0.85 − 20 w`); REJECT (a) (the clock does not fall; `w` by variation of constants inside `[−1, 1]`) | ONGRID ok (exit→REJECT); REJECT ok (invariant) |
| 17 | `lit_csf21_vehicle_bus` | `V2LitCsf21VehicleBus.lit_csf21_vehicle_bus_wellFormedR_direct` | every Cool mode (b) → CoastCoolA (`v ≤ 1`) or BrkCoolA (`v ≥ 1`), every Heat mode (b) → CoastHeatA or BrkHeatA, by the end speed; the same explicit run | CoastCoolA, CoastHeatA ok (invariant); the other ten ok (exit) |
| 18 | `lit_csf21_vehicle_thermo` | `V2LitCsf21VehicleThermo.lit_csf21_vehicle_thermo_wellFormedR_direct` | every mode (b) → Coast* (`v ≤ 1`) or Brk* (`v ≥ 1`) by the end speed, *Cool or *Heat by the end temperature (explicit run `d − v t − c t²/2`, `v + c t`, `temp ± t`; Acc from `v ≤ 39`, Brk from `v ≥ 1` keep `0 ≤ v ≤ 40`) | all six ok (exit) |
| 19 | `lit_csf25_salt_tank_hold` | `V2LitCsf25SaltTankHold.lit_csf25_salt_tank_hold_wellFormedR_direct` | Inc, Dec (b): the guards `xp < 35` / `xp ≥ 35` partition the level, both declared successors of both; existence by the Lipschitz route over the whole space, the level kept between its start and the mode's set point (`ODESol.linear_between` on every prefix), inside `[0, 300]` | Inc ok (exit→Dec); Dec ok (exit→Inc) |
| 20 | `lit_drl_lane_control` | `V2LitDrlLaneControl.lit_drl_lane_control_wellFormedR_direct` | every mode (b) → a Coast pair (`v_f ≤ 1`) or a Brake pair (`v_f ≥ 1`), the leader's member by its speed (`v_l ≤ 9` LAccel, `v_l ≥ 1` LBrake); explicit run | all six ok (exit) |
| 21 | `lit_freedm_meter` | `V2LitFreedmMeter.lit_freedm_meter_wellFormedR_direct` | every mode (b) → GridD0R0 (guard = domain); explicit linear run | battery modes ok (exit); grid modes ok (invariant) |
| 22 | `lit_girard08_robot` | `V2LitGirard08Robot.lit_girard08_robot_wellFormedR_direct` | every location (b) → itself or the next location (constant headings of norm 0.2: one interval moves each coordinate by at most 0.2, across at most one line of the 0.4-enlarged invariants); explicit linear run | all six ok (exit) |
| 23 | `lit_gpt10_boost_converter` | `V2LitGpt10BoostConverter.lit_gpt10_boost_converter_wellFormedR_direct` | P1, P2 (a): guards and domain the constant atom `0 ≤ 1`, so every end state enables the self-loop; existence for every length from the affine field's global Lipschitz bound (`exists_odeSol_of_lipschitz`, `Proofs/Flow/LipschitzRun.lean`) | P1 ok (invariant); P2 ok (invariant) |
| 24 | `lit_lz21_vehicle_position` | `V2LitLz21VehiclePosition.lit_lz21_vehicle_position_wellFormedR_direct` | every mode (b) → U0 (its guard `0 ≤ v ≤ 0.1` is the speed part of the domain); explicit run `x + v t + c t²/2`, `v + c t` (Um from `v ≥ 0.05`, Up from `v ≤ 0.05`) | Um ok (exit→Up), U0 ok (invariant), Up ok (exit→U0) |
| 25 | `lit_nahs25_engine_cooling` | `V2LitNahs25EngineCooling.lit_nahs25_engine_cooling_wellFormedR_direct` | Cool (b) → Heat (the linear descent `temp − t/2`, above 99.5 within a cycle from `temp ≥ 100`), Heat (b) → Cool (the linear ascent `temp + t`); every end state is in `temp ≥ 100` or `temp ≤ 100`, both modes declare both; Z3-free |
| 26 | `lit_nahs25_salt_tank` | `V2LitNahs25SaltTank.lit_nahs25_salt_tank_wellFormedR_direct` | On (a) (every run stays `≥ 25`, `ODESol.linear_down`; explicit run `25 + (xp − 25) e^{−t/10}`); Off (a) (the constant run; the strict guard atom `xp < 25` carried exactly) | both ok (invariant) |
| 27 | `molding_pack_checkring` | `V2MoldingPackCheckring.molding_pack_checkring_wellFormedR` | HOLD (b) → COOL (the clock; the nozzle pressure's approach to 500 and the cavity pressure by variation of constants, `forcedSol`, inside the rating `[0, 2000]`); COOL (a) (the clock does not fall; two decays) | HOLD ok (exit→COOL); COOL ok (invariant) |
| 28 | `platoon_profiles` | `V2PlatoonProfiles.platoon_profiles_wellFormedR` | as 51 | both ok (invariant) |
| 29 | `quad_light_lag` | `V2QuadLightLag.quad_light_lag_wellFormedR` | CLIMB (a) (the affine cascade `h' = w`, `w' = a − 4.905 w`, `a' = 10 (9.81 − a)`; the explicit run `forcedSol` / `intSol` stays in the guard box; (one domain on both sides) the box is `h ≥ 0`, `0 ≤ w ≤ 3`, `0 ≤ a ≤ 14.715`, kept since `14.715 = 3 × 4.905`) | ok (invariant) |
| 30 | `quad_light_profiles` | `V2QuadLightProfiles.quad_light_profiles_wellFormedR` | NORMAL, ECO, SPORT (a) (`h' = w`, `w' = c − 4.905 w` toward 2.0, 1.6, 2.5 (2.4 before 2026-10-30); explicit run in the guard box `h ≥ 0`, `0 ≤ w ≤ 3`); dimension 3 (mode choice, the default padding) | all ok (invariant) |
| 31 | `rampmeter_poll_2to1` | `V2RampmeterPoll2to1.rampmeter_poll_2to1_wellFormedR` | every level (b) → a declared neighbour (the 20 s density envelope: `k` between `L + (k₀ − L)E` and `U + (k₀ − U)E`, `L = 10 + r`, `U = 27.5 + r`, `E = e^{−0.01 t} ≥ 0.8`, by two comparison lemmas); existence: `kd` held, `k1` toward `kd`, `k` by variation of constants inside `[14, 42.5]` | all six ok (exit) |
| 32 | `reactor_feed_wireless` | `V2ReactorFeedWireless.reactor_feed_wireless_wellFormedR` | F1 to F4: every run ends in `[15, 60] × [15, 35]`, which the four guards cover (`T < 25`, `[25, 35)`, `[35, 45]`, `T > 45`; every level lists every level); existence: `T` toward `p + 4, 8, 12, 16 ∈ [19, 51]`, `p` held (`trajRs_sol`) | F1 ok (exit→F2), F2 ok (exit→F1,F3), F3 ok (exit→F2,F4), F4 ok (exit→F3) |
| 33 | `rover_ladder_2to3` | `RoverLadder2to3Guarded.rover_ladder_2to3_wellFormedR` | STEEP (b) → MODER, MODER (b) → FLAT, FLAT (a) (the shared three-band lemma `wellFormedR_terrain` at the route scale: odometer zones `[0, 60)`, `[60, 140)`, `[140, ∞)`, no cap, `0 ≤ s' ≤ 8`; existence: `v → c_q` by `forcedSol`, `s` its integral) | STEEP ok (exit→MODER), MODER ok (exit→FLAT), FLAT ok (invariant) |
| 34 | `rover_ladder_3to6` | `RoverLadder3to6Guarded.rover_ladder_3to6_wellFormedR` | as 18 (existence: also `ψ` decaying) | as 18 |
| 35 | `rover_ladder_6to8` | `RoverLadder6to8Guarded.rover_ladder_6to8_wellFormedR` | as 18 (existence: the cascade `z → θ`, `(v, ψ) → φ`, all `→ s`, kept in the box by `forcedSol_between`) | as 18 |
| 36 | `rover_ladder_8to12` | `RoverLadder8to12Guarded.rover_ladder_8to12_wellFormedR` | as 18 (existence: the cascade `ω_ψ → ψ`, `z → ω_θ → θ`, `(v, ω_ψ, ψ) → φ`, all `→ s`) | as 18 |
| 37 | `sat3w_detumble_phases` | `V2Sat3wDetumblePhases.sat3w_detumble_phases_wellFormedR` | DETUMBLE, FINE (a) (each guard, `E ≤ 1` resp. `E ≤ 0.125`, forward invariant; the domain is the gyro box `|w_i| ≤ 1`, which the explicit runs keep since each rate decays; until then the band in the domain kept them); SAFE (a) | all ok (invariant) |
| 38 | `sat_detumble_phases` | `V2SatDetumblePhases.sat_detumble_phases_wellFormedR` | as 33 | as 33 |
| 39 | `sat_detumble_weak` | `V2SatDetumbleWeak.sat_detumble_weak_wellFormedR` | NOMINAL, ECONOMY, SURVIVAL (a) (the guard `E ≤ 1` forward invariant; the gyro box `|w_i| ≤ 1` kept by the decaying rates, without the band); SAFE (a) | all ok (invariant) |
| 40 | `stopline_drag` | `StoplineDrag.stopline_drag_wellFormedR` | as 91 (existence: `c` by `forcedSol` toward 0 or 2.7, then `b` by `forcedSol` forced by `20 c`, inside `[0, 3]`) |
| 41 | `stopline_friction` | `StoplineFriction.stopline_friction_wellFormedR` | as 91 (existence: `b` by `forcedSol` toward 0 or 3 inside `[0, 3]`, `v` integrates `−b`) |
| 42 | `stopline_lag` | `StoplineLag.stopline_lag_wellFormedR` | CRUISE (b) → CRUISE/BRAKE, BRAKE (b) → BRAKE/STOP, STOP (a) (the shared stop-line lemma `wellFormedR_stopline`, `Proofs/Encoding/WellFormedStopline.lean`: CRUISE keeps `v` and moves `p` forward, BRAKE keeps `p ≥ 100` and ends at `v ≥ 0.35` or `v ≤ 0.35`, STOP frozen); existence: `v` held or `v₀ − 3t ≥ 0.05`, `intSol` for `p`; Z3-free |
| 43 | `stopline_tyre` | `StoplineTyre.stopline_tyre_wellFormedR` | as 91 (existence: `b` toward 0 or 2.7) |
| 44 | `syringe_relay_prearm` | `V2SyringeRelayPrearm.syringe_relay_prearm_wellFormedR` | RUN1 (b) → TAKEUP2 or RUN2; TAKEUP2 (b) → RUN2; RUN2 (b) → END (the moving volume or take-up passes its threshold, the frozen coordinates keep the guard's other atoms); END (a); existence: linear motions below 50 resp. 1.2, `C` toward its level | RUN1 ok (exit→TAKEUP2,RUN2); TAKEUP2 ok (exit→RUN2); RUN2 ok (exit→END); END ok (invariant) |
| 45 | `tank_dos_3to1` | `V2TankDos3to1.tank_dos_3to1_wellFormedR` | P2, P3, P4 (b) → the next stage, P5 (a) (the staged pump `h' = 0.005 c − 0.001 w h`, `w' = 0.02 (22 − w)`: `w` explicit, `h` by variation of constants over the floor `w ≥ 2c`, barriers keep `0 ≤ h ≤ 2.5`; `w` rises at most 3.2 in `ε_r = 10`, one band) | P2–P4 ok (exit), P5 ok (invariant) |
| 46 | `train_ato_odometry` | `V2TrainAtoOdometry.train_ato_odometry_wellFormedR` | PL1, PL2, PL3 (a) (contractions toward 25 inside `[5, 27.08]`, guard = domain) | all ok (invariant) |
| 47 | `turbine_startup_gearratio` | `V2TurbineStartupGearratio.turbine_startup_gearratio_wellFormedR` | SPINUP (b) → RAMP, RAMP (b) → GEN, GEN (b) → REG (explicit exponentials, `linear_between`); REG (a) at `w ≥ 11.979`; GUST (a) by the lower barrier at 11.979 (field `1.3125 (12.1 − w) + 0.24 G > 0` below it) | SPINUP, RAMP, GEN ok (exit); REG, GUST ok (invariant) |
| 48 | `ventilator_vc_cuffleak` | `V2VentilatorVcCuffleak.ventilator_vc_cuffleak_wellFormedR` | INSP (b) → EXP (the timer falls from `s₀ ≥ 0.01`, so it stays `≥ 0` for one period; `V` rises at 0.4; `s < 0.01` is EXP's guard); EXP (a) (the timer is frozen; `V` decays toward 0, above `min V₀ 0 ≥ −0.4`) | INSP ok (exit→EXP); EXP ok (invariant) |
| 49 | `watertank` | `V2Watertank.watertank_wellFormedR` | Low (b) → MidEco; MidEco, MidBoost, High, PumpOff (a) | Low ok (exit→MidBoost, same guard); the others ok (invariant) |
| 50 | `watertank_twospeed` | `V2WatertankTwospeed.watertank_twospeed_wellFormedR` | Fast (b) → Slow or MidEco, Slow (b) → MidEco (contractions toward 12.5); MidEco, MidBoost (a) (toward 17 from below, strictly); High (a) (toward 17 from above); PumpOff (a) (frozen below 2) | Fast ok (exit→Slow,MidBoost); Slow ok (exit→MidBoost); the other four ok (invariant) |

Totals: proved 47, false 0, band 3 (`WellFormedBattery.wfDeclared = (47, 0, 3)`; the 3 band
entries are the satellites, proved unconditionally, whose `wfBand` list is kept for their band
audit). `wf_coverage` checks in the kernel that the three name lists are a permutation of the
suite's IR table. Z3-free: 50/50. Region-relative: none.

The satellites' momentum band, the total angular momentum about each wheel axis `h_i + J_i w_i`
within the wheel's capacity, is a constant of every design-model flow (`_band_invariant`). It is
not part of the evolve domain: it is not a first integral of the left (the gyroscopic couplings,
e.g. `d/dt (h + 5 w3) = −2 w1 w2`), so on the left it would be a reachable-set band. The domain
is the gyro box `|w_i| ≤ 1`, the claim (energy) does not read `h`, and Assumption 1 holds
literally on it.

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

Then clause (i), on a mode whose clause (ii) is shown. It must show that from every state of `X₀ = G ∧ D` the solution of the
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
   polyhedron and a locally Lipschitz field), a greatest fixpoint over the candidates.
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
`--check-quick-v2` runs the same section as its check 3/3, strict (below).

**Suite_v2 result**: 50 benchmarks, 181 right modes: 75 ok (invariant), 106 ok (exit),
**0 UNKNOWN, 0 BLOCKING** (`ExpectedSuiteV2.wfModes = 181`, `VerdictsV2/RunV2.lean`).

**The blocking exhibit** `benchmarks/negative_wellformed/lit_hypercert_vehicle_s8` (a right model
with `s ≤ 8` in every evolve domain; self-contained): the default run CERTIFIES it, clause (ii)
alone finds all five right modes `ok`, the two-clause check finds all five `BLOCKING (leaves s <=
8.0)` (at `s = 8`, `v > 0` the flow leaves at once), and `RELCERT_WELLFORMED_STRICT=1` DECLINES it.

**The switch** `RELCERT_WELLFORMED_STRICT=1`: a CERTIFIED benchmark with an `UNKNOWN` or
`BLOCKING` right mode becomes DECLINED (a `[wellformed] STRICT` line on stderr says why). Off by default for a
single `relcert <file>` run; off, no verdict and no emission changes.

**Strict in the recipe.** `--check-quick-v2` certifies the suite in the strict mode (the switch
forced on for its check 1/3) and ends with check 3/3, the `--wellformed` report gated against
declared counts: `ExpectedSuiteV2.wfModes = 181`, `wfUnknown = 0` and `wfBlocking = 0`
(`VerdictsV2/RunV2.lean`). Any `UNKNOWN` or `BLOCKING` mode, or a mode count off the declared
one, fails the run (`wellformed (strict): FAIL`, exit 1). The informational
`relcert --wellformed <files>` is unchanged.

## 5. Build and audit

```bash
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt
```

Expected: 78 axiom lines. The battery prints 67 of its own, each exactly `[propext,
Classical.choice, Quot.sound]`: the 50 right models (40 `<b>_wellFormedR`, 10
`<b>_wellFormedR_direct`), the 3 satellites' `<b>_band_invariant`, and 14 generic lemmas
(`wellFormedR_terrain`, `wellFormedR_stopline`, `wellFormedR_switchLegal`,
`not_wellFormedR_of_run`, `not_wellFormedR_of_noRun`, `exists_contract_run`,
`exists_rate_run`, `exists_of_HExistSegB_zero`, `ODESol.coord_le_barrier`,
`ODESol.affine_const`, `PlatoonCaccAeb.cacc_w_band`, `PlatoonCaccAeb.aeb_w_const`,
`PlatoonCaccAeb.cacc_box`, `WellFormedBattery.wf_coverage`). `lake` also replays the 11 lines of
`Proofs/Soundness/CutLiftX.lean`'s own audit, 2 of which add `z3_unsat_sound` (the lift of the
mode facts, not an Assumption 1 proof): 76 lines at the three standard axioms, 2 with
`z3_unsat_sound`. The summary line of §4.

## 6. The lift to the bridge dimension

Each `WellFormedR` lemma is stated at a fixed dimension `n0` (the pack table's `dim`, or the
state variables padded to three coordinates: the right mode variable, the left clock and the
stored left mode; the right clock, the keyed form's fourth auxiliary coordinate, is the `+ 1`
below). Since the
right automaton of the bridge is clocked (`rightAutomatonBodyC`, the right clock `(Aux, d)`;
`docs/PAPER-MAPPING.md` §9), the generated instances live at `n0 + 1` (`bridgeDimV2`,
`VerdictsV2/RunBridge.lean`). `Proofs/Encoding/Emitted/Lift.lean` carries the lemma across:

* `padOK p n : Bool` (`Lift.lean`): for every right mode `q ≤ nR p` (the out-of-range
  default included), the lowered guard and evolve domain at `n+1` are the `IForm.embed` of
  their lowering at `n`, and the dynamics pad with the new coordinate's derivative `0`
  (`dynPadOK`). Each generated instance proves `pad_ok : padOK IR n0 = true` by
  `decide +kernel`.
* `wellFormedR_lift (hpad : padOK p n = true) (h : WellFormedR (grOf p n pr) (guardR p n) ε) :
  WellFormedR (grOf p (n+1) pr) (guardR p (n+1)) ε` (`Lift.lean`): every solution at
  `n+1` projects to one at `n` (`odeSol_proj`) and every solution at `n` extends with the new
  coordinate constant (`odeSol_ext`), so both clauses transfer.

The order in a generated instance (`scripts/gen_bridge.py`, e.g. `InstancesV2/Bridge/Watertank.lean`):
transport at the lemma's dimension (`wellFormedR_transport`, or the `_direct` form), then
`wellFormedR_lift (n := n0) pad_ok`, then `WellFormedRIn.of_tt` at `reg = ⊤`. The two
hand-written `InstancesV2/Choice/General/` exhibits keep only their Assumption 1 proofs; those proofs are lifted the same way into the corresponding bridge instances.
Nothing in this file's battery or audit (§5) changes: the lift is a generic lemma at the
three standard axioms, applied inside the bridge instances.
