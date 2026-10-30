# Benchmark suite: `suite_v2`

`suite_v2/<name>/input.txt` is the complete specification of one benchmark: the left
(ideal) and right (implementation) hybrid automata, the relational invariant (one row per
left mode) and the time-stretch range. **50 benchmarks.** With the widened cut channel on
(`RELCERT_IMPLIED_CUT=1`, as every suite_v2 run sets it) the tool CERTIFIES all 50, and
every one carries a kernel-checked Theorem 3 (the paper's Soundness of Synthesis) with the paper's left program over the
guard-gated right automaton, at the mode-consistent region (`RelCertifier/InstancesV2/Bridge/`;
check recipe: `docs/CERTIFICATION-CHECK.md`). Without the widened channel 6 of them
DECLINE (the rows marked *widened cuts* below; measured 2026-10-30, `docs/paper-numbers/matrix.log`). Near-duplicates and weak benchmarks are kept
outside the suite in `benchmarks/reserve/` (inputs, headers and verdicts only; `reserve/README.md`).

**Assumption 1 of each right model** (the paper's Well-Formedness: from every guard state a
full control interval of flow exists, and every evolution of at most `ε_r` ends in a declared
successor's guard) is verified per file (`WellFormedR`, `docs/WELLFORMED.md`): it holds for
all 50 literally (the 3 satellite files on the gyro box `|w_i| <= 1` alone since 2026-10-29, when
every benchmark got one physical evolve domain, the same on both sides: `scripts/check_one_domain.py`).
Nine files had a blocking mode until 2026-10-10 and were repaired (`docs/SUITE-REDESIGN.md`
§21; each header says how and why; `arm_plateau_{crit,profiles,slow}` and
`platoon3_{linkloss,profiles}` are in `benchmarks/reserve/` since 2026-10-27, and `platoon_delay_{linkloss,profiles}` were
replaced by the redesigned `platoon_linkloss` and `platoon_profiles`, the latter in the reserve since batch I8): `arm_plateau_{crit,profiles,slow}` (the ApproachA /
ApproachB bands are narrower than one control interval of their own rate: the sampled
planner's successor sets now name every band a sample can find), `platoon_delay_{linkloss,
profiles}` (the sink `BRAKE` left its guard: it now re-engages `FOLLOW`),
`platoon3_{linkloss,profiles}` (the sinks `BRAKE1`–`BRAKE3`: now latched, speed-matching, with
an invariant guard) and `quad_light_{airframe_20,profiles}` (the sink `LIMIT`: it handed back to
the climb controller, whose operating range reached the limiter threshold; both were redesigned
on 2026-10-27 with the altitude coordinate and no limiter mode).
`relcert --wellformed <input.txt>…` runs the tool's sufficient check per right mode (every one
of the 176 is `ok`, 2026-10-30); `--check-quick-v2` runs it strict and fails on any `UNKNOWN` or `BLOCKING`.

The suite's design, the per-family rationale, the domain audit (every evolve bound is a
physical limit of the plant; `scripts/domain_widening.py` re-runs the tool with every bound
widened) and the mechanism matrix (which certifier mechanism each benchmark actually
needs, read off counter-runs; `scripts/suite_v2_matrix.py`) are in
`docs/SUITE-REDESIGN.md`. Each file written for this suite states in its header the
physical story, the units, the measured cover and the mechanisms it exercises
(`# scenario:` and `# mechanisms:` lines).

## Batch 11, 2026-10-30: the pre-landing key in the suite, a P carrier, used and needed letters

`docs/BATCH11-2026-10-30.md`:
* Merged `origin/prelanding` (the opt-in `prelanding = true`, `docs/PRELANDING.md`).
* In: `lit_nahs25_engine_cooling` (NAHS 2025 engine cooling, the source's forward distance 0.3, tight; letter R through the pre-landing right-only certificate; the genuine Cool guard closed to `temp >= 100`, disclosed) for `fuelcell_chp_dos` (to `skipped/`); `extruder_pe100_manualstart` (M B P I, tight 18.61) for `rover_terrain_6to12` (to the reserve, valid, displaced for letter balance).
* Letters: Table 1 lists the mechanisms the certificate USES and marks those it NEEDS (rule below, `scripts/suite_v2_letters.py`). Needed S 19 M 21 R 8 B 9 P 2 D 13 I 17 X 14; used S 19 M 21 R 8 B 9 P 3 D 13 I 21 X 14. Literature files 10.

## Batch 10, 2026-10-30: letter rules, restored letters, two replacements

`docs/BATCH10-2026-10-30.md`, review `docs/BENCHMARK-REVIEW-2026-10-30-r10.md`:
* Letter rules: stretch 0 (stutter) is credited under S (the former letter W is folded into S); M is the cover shape again (matrix M2: a left mode's cover with budget >= 2 and a joint step; the round-6 refinement that also required a right mode change on the replayed path is reverted). Information only: `RELCERT_SINGLE_STEP=1` (single-step covers, budget 1) and the per-file verdict in `docs/paper-numbers/letters.md`.
* Models changed so that letters removed by the round-6 row fixes come from ordinary operation: `h2_refuel_ambientbias` (a drawn-down cascade bank: STAGE3DRAWN, TOPOFFEARLY; looser top rows restored; R back), `acc_spoof_limp` (immediate gradient-check latch at the attack onset speed; LIMP entry up to 40 m/s; dead DISENGAGE removed; X back), `turbine_startup_gearratio` (IEC 61400-1 extreme operating gust, REG and GUST modes, dead STOP removed; D back, X new, the artifact P gone). `rover_terrain_2to4`: no honest S M (the auxiliary row now admits the rest start); letters I.
* Replaced: `platoon_latency` (to the reserve) by `boiler_purge_vfd` (R D), `rover_patrol_lag` (to `skipped/`) by `autoclave_liquid_steambank` (S R D). `pack_coldcharge_broadcast` was designed for the `fuelcell_chp_dos` slot and withdrawn after review round 10 (`skipped/pack_coldcharge_broadcast/SKIPPED.md`).
* Letters S 18 M 15 R 5 W 1 B 10 P 3 D 10 I 18 X 13 -> S 19 M 21 R 7 B 9 P 2 D 13 I 18 X 15.

## Review round 6, 2026-10-30: one skip and refill, five right models changed

Verified HIGH findings of `docs/BENCHMARK-REVIEW-2026-10-30-r6.md` (section "Verified HIGH findings and actions"; commit `bd7c608`):
* `charger_fast_tapers` to `skipped/` (the claim does not depend on its cause; `skipped/charger_fast_tapers/SKIPPED.md`); `molding_pack_checkring` in from the reserve (2000 bar rating domain, letter D; Assumption 1 in `MoldingPackCheckring.lean`, mode-keyed bridge).
* Right models changed, Assumption 1 proofs adapted: `acc_tune_limp` (COMFORT and SPORT removed), `quad_light_profiles` (profile switching, SPORT set point 2.5), `ventilator_vc_cuffleak` (inspiratory countdown timer `s`; domain `s >= 0`, `V >= -0.4`), `fuelcell_chp_dos` (physical domain, design inlet range in the guards), `watertank_twospeed` (`Fast -> PumpOff` removed).
* Row and start fixes: `turbine_startup_gearratio` uniform rows (window form, no longer mode-keyed), `h2_refuel_ambientbias` rows `p_R >= 58`, `acc_spoof_limp` ceiling 28.6, `rover_terrain_2to4` real-time form; header fixes on eight files.
* Letter rule M also needs the replayed path of a multi-step cover to change right mode (a single-mode right, or a witness that stays in one mode, gives one continuous right run). Letters S 20 M 24 R 7 W 1 B 12 P 4 D 11 I 17 X 15 -> S 18 M 15 R 5 W 1 B 10 P 3 D 10 I 18 X 13 (`docs/paper-numbers/letters.md`).
* Checks: `--check-quick-v2` 50 certified, modal 1185/1185, handoff 2831/2831, non-connection 38/38, pruned 19/19, reposition 70/70, strict gate 176/176 (78 invariant, 98 exit); bridge 7375/7375; progress 162/162; refute 227/227 (81 instances); ONE DOMAIN PASS.

## Literature round 3, 2026-10-29: the stale-reading tank, the robot in physical coordinates

* `lit_csf25_salt_tank_hold`: the held decision is now the STALE reading of the source's DoS (the payload skip keeps
  the reading of the last fresh sample, at 4), answered by the genuine state of that reading (the paper's mid_a
  pairing, Fig. 10) re-timed by 1/3. Rows: the paper's offset 2.1 plus slope 1.25 (1.24 declines; the paper's 1.3),
  5.85 lb at the end of the hold (the paper's 6, exact worst case 5.47); the envelope psi_b (34.5, 37.1) restated
  for a stale reading as moving edges of one re-timed genuine cycle (rates 0.655 and 0.1, tight). Letters S D I
  (unchanged).
* `lit_girard08_robot`: the robot in the source's physical coordinates (y1, y1', w), Eqs. (6)-(7) as printed (the
  error coordinates of before were an exact change of variables kept for run time: about 4 s, now about 57 s).
  Level 0.16 = precision 0.4 still tight (0.159999 declines); cause tests unchanged; letters X (unchanged).
* Not installed: the NAHS 2025 engine cooling (no row set certifies with a meaningful value, also with
  repositioning on: the right-only check is whole-domain and the constant-rate flows push one atom of every band
  the wrong way; `docs/OVERNIGHT-2026-10-29.md`, "Literature round 3"). No removal; suite 50 (41 designed, 9 from
  the literature). Checks: `--check-quick-v2` 50 certified, modal 1162/1162, handoff 2827/2827, non-connection
  44/44, pruned 22/22, reposition 74/74, strict gate 181/181; bridge 7437/7437; progress 194/194; refute 206/206
  (75 instances; new: `lit_csf25_salt_tank_hold` m031, the Dec envelope edge on the attacked level).

## Literature migration, 2026-10-29: two literature files in, one reserve swap

* `lit_gpt10_boost_converter` (new; Girard, Pola, Tabuada, IEEE TAC 55(1) 2010, Sec. 5.1): the boost DC-DC
  converter matched within the source's precision 2.6 by every run of its lattice abstraction (left: the
  converter pushed by a drift whose window displacement covers the eta-ball, 48 modes; right: the converter,
  committed to the abstraction's switch position by choice). Tight 2.58 (2.57 declines; computed 2.5783), linear in
  eta; M load-bearing (the Euclidean norm declines). Letters X. Replaces `lit_drl_car_stop` (to `skipped/`).
* `lit_csf25_salt_tank_hold` (new, owner-approved; Xiang et al., IEEE CSF 2025, Sec. VII): one held 3-min decision
  under a timed sensor DoS against the genuine tank re-timed by 1/3 (the paper's Props. 6 and 7); Inc slope 1.31
  (1.30 declines), growing with the hold (0 / 0.99 / 1.31 / 1.48 for 1 to 4 min). Letters S D I. Replaces
  `zone_lightmass_schedule` (to `skipped/`; r5 overall 2, the row certifies only by the domain).
* `rampmeter_poll_2to1` back from the reserve with the HCM level-of-service requirement 8 veh/mi/ln (tightest
  7.00), in place of `insulin_basal_cgmloss` (to `skipped/`; same template and letters M B).
* Not installed (measured reasons in `docs/OVERNIGHT-2026-10-29.md`): the n-room building of Girard, Goessler,
  Mouelhi (2016; n = 3 exceeds the time budget with the quantizer stand-in, the copy form has no tight value) and the
  engine cooling of NAHS 2025 (its distance compares reachable sets; the run-wise relation is false in lock step).
* Header-only fixes to six literature files from an independent audit (`docs/OVERNIGHT-2026-10-29.md`, Phase B).

Letters S 20 M 25 R 7 B 13 P 4 D 10 I 17 X 16 -> S 20 M 24 R 7 B 12 P 4 D 11 I 18 X 15. Suite 50 (41 designed, 9
from the literature). Checks: `--check-quick-v2` 50 certified, modal 1160/1160, handoff 2827/2827, non-connection
44/44, pruned 22/22, reposition 74/74, strict gate 181/181; bridge 7433/7433; progress 194/194; refute 204/204.

## Fix round 4, 2026-10-29: start-only fallbacks, rows without content, one swap

The verified items of review round 4 (`docs/BENCHMARK-REVIEW-2026-10-29-r4.md`), each tested on a
scratch copy first; the full table (finding, action, letters before / after, tight numbers) is in
`docs/OVERNIGHT-2026-10-29.md`, "Fix round 4 (2026-10-29)". Start-only fallback modes:
`engine_start_highidle` got a reachable trigger (start-air supply pressure; on low supply a start
from rest hangs below light-off and aborts at the 30 s time-out; R D I kept); the AEB of the three
platoon files, the ABORT of `h2_refuel_ambientbias` and the FAULT of `charger_fast_tapers` had no
trigger an ordinary run reaches in their models and were removed (platoon D lost in all three,
charger P lost; h2 keeps R D I). Rows without content: `rover_ladder_2to3` heading row,
`bottling_fill_strainer` row 5 (implied), the three output-only rows of `rover_terrain_6to12`
removed; `reactor_feed_wireless` band 9 -> 8 K (tight, requirement restated). Numbers:
`quad_light_lag` Psi 0.16 -> 0.45, `hydro_rejection_gatecal` 0.09 -> 0.07, `watertank` lambda_max 6 ->
2, `watertank_twospeed` lower row 2 -> 1.5; the terrain chain on the soil model's validity floors
(w >= 0.05 in 2to4 and 4to6, restoring their composition; 0.13 in 6to12 for the ramp), since a floor
of 0 makes the right model leave v >= 0 (Assumption 1 BLOCKING). Header fixes in `acc_tune_lag`,
`syringe_relay_prearm`, `sat_detumble_weak`, `ventilator_vc_cuffleak`, `rover_terrain_6to12`,
`platoon_latency`. Swap: `grid_ffr_dos` skipped (its band did not depend on the attack;
`skipped/grid_ffr_dos/SKIPPED.md`), `canal_gate_notches` back from the reserve (X). Ten Assumption 1
proofs adapted, one restored. Letters: S 20 M 26 R 7 B 13 P 6 D 13 I 17 X 15 -> S 20 M 25 R 7 B 13
P 4 D 10 I 17 X 16.
Checks (all green; one serial `lake build`, exit 0): `--check-quick-v2` 50 certified, modal
1218/1218, handoff 537/537, non-connection 42/42, pruned 21/21, reposition 74/74, strict gate
186/186; `relcert-test` ALL PASS; bridge 5180/5180; progress 194/194; refute 204/204 (74
instances); WellFormedBattery 66 lines; one domain PASS.

## One domain per benchmark, 2026-10-29

Rule (owner): one physical evolve domain per benchmark, the same text on every mode of both sides;
physical constraints only. Checked by `scripts/check_one_domain.py` (kind (iii) exception: one
physical limit in two reading scales, conversion stated in a `# Domain conversion (kind iii):`
header line). Thirteen files had more than one domain: `platoon_latency` and `rover_patrol_lag`
declare the lag coordinate on the right (frozen) with the shared box, and `rover_patrol_lag` loses
its lag envelope `0 <= a + 4 v <= 6.4`; the four `rover_ladder_*` rungs drop the right's `[0, 0]`
pins for the validity box; `rover_terrain_2to4` drops the creep floor `w >= 0.15`; `quad_light_lag`
moves from the two airframes' set points to `0 <= w <= 3`, `0 <= a <= 14.715` on both; the three
satellites drop the momentum band (a first integral of the design model, not of the gyrostat) and
the wheel box (crossed by the design model's flow) for the gyro box `|w_i| <= 1`;
`train_ato_odometry` and `turbine_startup_gearratio` are kind (iii). Every file CERTIFIES with its
rows unchanged, letters unchanged per benchmark; details in `docs/OVERNIGHT-2026-10-29.md`.

## Domain audit, 2026-10-29: four domains moved to physical limits, one benchmark skipped and refilled

Rule (owner, `docs/SUITE-REDESIGN.md` section 13): an evolve domain states a physical constraint
of the plant (a hardware limit, a sensor range, a saturation, a trip), never a closed-loop target,
set point, asymptote or reachable-set cap chosen so that the claim certifies. A domain scan of the
50 files (every two-sided evolve bound widened by 5 % and 20 % of its range, then one bound at a
time; `docs/OVERNIGHT-2026-10-29.md`, "Domain audit 2026-10-29") found nine files whose
certificate stood on a bound: four on a physical limit (class a: `acc_tune_lag`'s 1 g box, the
rover ladder's suspension travel and governed top speed) and five on a closed-loop band (class b).

| benchmark | old bound | new bound | action | letters before / after |
|---|---|---|---|---|
| `flaps_slow_approach` | `V` in [150, 185] kt (the autothrust target F and the selection speed S) | `V` in [130, 200] kt (VLS CONF 2 to the flap placard VFE CONF 2) | rows `V_R <= V_L + 25`, `V_L <= V_R + 10` (tight: 24.99, 9.99 decline; the 20 kt window holds for selections up to 190 kt) | S / S |
| `platoon_latency` | `e` in [-0.5, 0.5] m/s^2 (the jerk-reachable error band) | `e` in [-20, 20] m/s^2 (two accelerations within the 1 g tyre-road limit) | the band `abs(e_L) <= 0.5` stated as a row (tight: 0.49 declines; `abs(Delta g)` 4.00 unchanged) | D / D |
| `quad_light_profiles` | `w <= 2.4` m/s (the SPORT set point) | `w <= 3` m/s (the autopilot's climb-rate limiter) | row `w_L <= 2.4` (tight: 2.39 declines; the limiter never engages) | S M B X / S M B X |
| `turbine_startup_gearratio` | `w <= 12.705` / `12.1` rpm (the rated targets) | `w <= 13.9755` / `13.31` rpm (the overspeed trips; the deployed's is 5 % late through the stale ratio) | GEN row `w_L <= 1.05 w_R + 0.061` (tight: 0.060 declines), exact in the other phases; uniform rows decline | R P I / R P I D |
| `engine_start_highidle` | `5 <= N2`, `t <= 40` | `0 <= N2 <= 110`, `t >= 0` | domain only; Assumption 1 proof adapted | R D I / R D I |
| `tunnel_jetfan_pairout` | `u >= 2.6` m/s (the controller's minimum duty) | `u >= 0` DECLINES, no claim-side fix (`skipped/tunnel_jetfan_pairout/SKIPPED.md`) | skipped | D I / (out) |
| `antenna_track_kvretune` | (reserve) | `t >= 0`, elevation travel [-2, 92] deg (limit switches), not load-bearing | refilled from the reserve (round-1 reserve score 4), Assumption 1 proof of fb55b6e unchanged | (in) / D |
| `acc_tune_lag`, `rover_ladder_3to6`, `rover_ladder_6to8`, `rover_ladder_8to12` | physical (1 g box; suspension travel 0.15 m; governed 8 m/s) | unchanged | headers: the bound is physical and load-bearing (which one, at 5 % and 20 %) | unchanged |

Letters (measured, `docs/paper-numbers/letters.md`): S 20 M 26 R 7 B 13 P 6 D 13 I 17 X 15 (D 12 -> 13:
the tunnel's D out, the antenna's and the turbine's in; I 18 -> 17: the tunnel's I had no replacement
at reserve score 4; every other benchmark's letters unchanged). The four files on physical limits
(class a) keep their domains; their W20 widening declines by design and the headers say so.
Checks (all green; `lake build` exit 0, 9293 jobs, the five executables 18172): `--check-quick-v2` 50 certified, modal 1264/1264, handoff 544/544, non-connection 60/60, pruned 30/30, reposition 74/74, strict gate 189/189 (87 invariant, 102 exit), 0 UNKNOWN, 0 BLOCKING; `relcert-test` ALL PASS (50 literals); bridge 5283/5283 (declared count set after measuring, was 5246: the tunnel's 38 groups out, the antenna's in, the five re-emitted instances); progress 197/197; refute 260/260 (87 instances, was 73: two tunnel out, 13 antenna and three platoon in) and every refutation instance builds; WellFormedBattery 66 standard axiom lines (plus the 11 `CutLiftX` replay lines); AxiomCheck 9; both negatives DECLINED; `lit_hypercert_vehicle_s8` BLOCKING / DECLINED; `scripts/paper_numbers.sh` re-run (covers identical, letters S 20 M 26 R 7 B 13 P 6 D 13 I 17 X 15; per-benchmark letters identical to the previous run for every file but the three listed).

## Review round 3, 2026-10-29: two constant changes, four header fixes

Round 3 (`docs/BENCHMARK-REVIEW-2026-10-29-r3.md`, hash-based reviewer pairing). Verified and
applied: `acc_spoof_limp` LIMP guard `20..36` (the fault is not conditioned on speed, the same
ceiling as `acc_tune_limp`; certifies up to 40; without the choice only up to 34.50, so the file
now carries X: LIMP by the ECO -> NORMAL hop; row 1 tight -2.40 / -2.41 at the new ceiling, row 2
-0.20 / -0.21 unchanged); `acc_tune_limp` `lambda_max` pinned to 1.5 (the cover's 3/2; identical
battery and covers); headers of `gantry_speed_zones` (verdict block re-measured, tolerance 0.00
at lambda_max 3, 0.01 at 4), `tunnel_jetfan_pairout` (the floor 2.6 m/s is the normal-ventilation
minimum duty, below every admitted steady state and the critical velocity), `sat3w_detumble_phases`
(the stylized wheel gain, about 100x a microsatellite wheel; the gains / 1000 variant certifies
with the same ablations), `fuelcell_chp_dos` (one garbled sentence). The four files still at 2
(`charger_fast_tapers`, `lit_lz21_vehicle_position`, `rover_terrain_2to4`,
`turbine_startup_gearratio`) are structural objections the suite keeps and documents: the
charger's constant is the tool's and its letters R P B D cannot be replaced from the reserve, the
LZ21 source bound blocks the right model, the terrain rung keeps the stretched form as the chain's
exhibit with the real-time form stated, the turbine claim is one-sided against an existential
reference with the domain restriction disclosed as load-bearing.

Checks after round 3: `lake build` exit 0; `--check-quick-v2` 50 certified, modal 1248/1248,
handoff 541/541, non-connection 60/60, pruned 30/30, reposition 73/73, strict gate 188/188;
bridge 5246/5246; progress 197/197; refute 219/219 (73 instances); WellFormedBattery 66 lines;
`relcert-test` ALL PASS. Letters (re-run 2026-10-29): S 20, M 26, R 7, B 13, P 6, D 12, I 18, X 15
(`acc_spoof_limp` M B I -> M B I X; every other benchmark identical); 25 benchmarks certify
under `RELCERT_SYNC=1`, 15 decline without the existential choice.

## Review round 2, 2026-10-29: six model changes (three with Assumption 1 proofs rewritten), twelve header fixes

Round 2 of the overnight review (`docs/BENCHMARK-REVIEW-2026-10-29-r2.md`, new reviewer pairing;
`docs/OVERNIGHT-2026-10-29.md`). As in round 1, every claim acted on was verified first; the
refuted reviewer fixes are listed there. Changes (ablation verdicts measured before and after; no
mechanism letter lost):

* `turbine_startup_gearratio` (round-1 header had announced it): the deployed loop gains are now
  scaled by the gear error (RAMP 0.0380952, GEN 0.047619, the stock gains / 1.05) and the domains
  are the start-up's reachable speeds (left `w <= 12.705`, right `w <= 12.1`; with both at 16 the
  physics-corrected model declines under every switch, so the restriction is load-bearing and the
  header says so). Factor 1.05 certifies, 1.047 and 1.049 decline; two-sided slack on RAMP+GEN now
  6.85 (was 10.75). Assumption 1 proof: the right domain constant 16 -> 121/10, nothing else.
  Letters R P I unchanged (SYNC, NO_PRUNE, NO_REPO, NO_CUT decline).
* `tunnel_jetfan_pairout` (announced): floor `u >= 2.6` (below the critical velocity, a stated
  physical choice; it carries the NORMAL CO row through the mode fact `c <= 100`, load-bearing at
  2.54), cap 900, and FIRE rows with smoke-control content: `u_L <= u_R <= u_L + 1.42` and
  `u_L >= 3` (NORMAL strengthening 0.41). Tight: 0.41/0.40 and 1.42/1.41 (the values without the
  unary row, 0.47/1.56, are stated as such). Proof: domain pins 630 -> 900 and 3.2 -> 13/5, the
  Riccati run's bounds re-closed by the existing tactics. Letters D I unchanged (NO_CUT declines,
  uniform rows decline). `docs/WELLFORMED.md` row updated.
* `engine_start_highidle` (announced): a light-off time-out clock `t` on both sides (`t' = 1` in
  STARTER, frozen elsewhere), STARTER guarded `t < 30`, ABORT guarded `n < 25 and t >= 30`, so
  ABORT is reachable (nothing pruned any more: pruned edges 32 -> 30 over the suite); rows STARTER
  `n_L <= n_R` and `t_R <= t_L`, LIGHTOFF exact, +4 above (4.00 certifies, 3.996 declines; the low
  rows tight at 0.00; uniform +4 declines, D kept). Proof rewritten at `Var 3` (n, t, padding):
  STARTER exits on the time-out or into LIGHTOFF, ABORT is a constant run. Letters R D I unchanged.
  The old refutation witness `engine_start_highidle_m003` (a mutant of the previous model) is
  replaced by `_m008` on the new model.
* `acc_tune_limp` (RETHINK, overall 2: the LIMP ceiling 30 read as tuned): LIMP guard `20..36`
  (the fault is not conditioned on speed; the ceiling is not load-bearing: 37.50 certifies, 37.51
  declines, above the 36 cruise ceiling, by the SPORT -> NORMAL hop) and a physical DISENGAGE
  coast-down `v' = -0.1 v` (2 m/s^2 at the floor; was -0.5 v, 10 m/s^2). Letters S M B D I X
  unchanged. Proof: the DISENGAGE gain 1/2 -> 1/10.
* `acc_spoof_limp`: the same DISENGAGE field (the two files share the reference model; proof
  adapted with a per-mode gain); header: the LIMP ceiling is not load-bearing (certifies up to 40;
  without the choice up to 34.50, the ECO/limp crossover), 110 km/h certifies identically. Letters
  M B I unchanged.
* `acc_tune_lag`: the measured speed tolerance is now a row, `|v_L - v_R| <= 3.34` (3.33 declines),
  beside the exact modal rows, at the pinned stretch 2 (tau = 0.32 s is the unique lag at which the
  retune's slow root is exactly twice the stock's; at 0.30 the exact rows decline). Letters S M
  unchanged.
* Header-only fixes (ablations identical before and after): `h2_refuel_ambientbias` (ABORT a start
  only, the exact stage rows and D rest on it: without ABORT the stage rows certify at +0.01 and
  uniform +2.9 certifies, letters R I), `platoon_profiles` (AEB_L start-only, D rests on it; the
  SPORT derivative corrected to `-0.36 (g - 20) - 0.8 r`), `platoon_latency` (AEB start-only on
  both sides, without it no letter), `fuelcell_chp_dos` (the non-monotone certifying window
  [5.00, 8.00], 8.005..9.995 decline, 10 and above certify; the band around a settled reference),
  `quad_light_lag` and `quad_light_profiles` (K = 4.0 at lambda 1.24525 and K = 4.5 at 1.218 both
  certify pinned; a range certifies only when the exact ratio is a grid point; profiles rows: row 1
  to 0.00, row 2 pinned to row 3's constant, 0.8 is the requirement's radius),
  `insulin_basal_cgmloss` (the 5 min / 10 min rate figures: band-edge 17.9 / 35.8, domain maximum
  27.9 / 55.8, successors still adjacent), `rover_terrain_2to4` (matched and plan-ahead starts need
  lambda 1; slip-ahead starts need the window, worst PAVED start 2.637 = the tool's 2.64),
  `lit_lz21_vehicle_position` (the content is translation invariance for any offset; the source's
  `x <= 10` makes three right modes BLOCKING, so it stays dropped; a documented literature row),
  `rover_patrol_lag` (the one-sided claim stated as such; the reverse direction certifies only with
  the plan re-timed by at most 0.6, tight 0.75, letters S only; the two-sided band declines in every
  form), `zone_lightmass_schedule` (the tight value is 0.0303 x the largest set-point-to-bound
  distance, measured on seven ranges; 0.5 certifies for far bounds within 16.5 K of a set point;
  scenario relabelled plant-change), `rover_terrain_4to6` (sinkage drag coefficient named,
  `u` is a lagged speed command).

Checks after round 2: `lake build` exit 0; `--check-quick-v2` 50 certified, modal 1250/1250,
handoff 541/541, non-connection 60/60, pruned 30/30, reposition 73/73, strict gate 188/188;
bridge 5246/5246; progress 197/197; refute 219/219 (73 instances); WellFormedBattery 66 lines;
`relcert-test` ALL PASS. Letters (re-run 2026-10-29): S 20, M 26, R 7, B 13, P 6, D 12, I 18, X 14,
every benchmark's letters identical to the round-1 run.

## Review round 1, 2026-10-29: one refill, four model changes, thirteen header fixes

Round 1 of the overnight review (`docs/BENCHMARK-REVIEW-2026-10-29-r1.md`: five fresh reviewers,
rubric only; `docs/OVERNIGHT-2026-10-29.md` for the full log). Every reviewer claim acted on was
first verified by a tool run on a scratch variant (bisection, ablations, simulation); unverified
claims were dropped. Changes, each confirmed CERTIFIED by default and under the strict gate, with
the five ablation verdicts measured before and after (no mechanism letter lost):

* `insulin_basal_cgmloss` back from the reserve (overall 4 in the reserve scoring, M B, the
  medical domain and the chain-depth multi-cycle template): the file is the reserve's design,
  its Assumption 1 proof of commit 8c92730 builds unchanged; the suite is 50 again after the
  skip of `lit_hypercert_vehicle`. Bridge instance 445 groups (5245 over the suite and the two
  exhibits); 24 mutants, no refutation witness.
* `zone_lightmass_schedule` (POLISH, overall 3): the comfort band 16..21 as evolve domain was the
  schedule's set-point span, not a range of the zone air. Now the instrumented range 5..30 on
  both sides and the EN 15500 control-accuracy class as the requirement: rows
  `|T_L - T_R| <= 0.5` in both left modes (tight: 0.49 certifies, 0.48 declines; the inductive
  bound on 5..30 is 0.4848; the 0.152 derivation is kept as the cause-dependence paragraph).
  Right model line for line the batch I10 one, so its Assumption 1 proof is reused (restored
  from 66f22eb). Letters S M B X unchanged (SYNC and NO_CHOICE decline as before).
* `sat_detumble_weak` (RETHINK, overall 2: the left field was the right NOMINAL field scaled by
  0.8, so the witness was the left re-timed): the left DETUMBLE field is now the gyrostat
  couplings of `sat_detumble_phases` at damping 0.4 with `h' = 2 w3`; the right model is byte for
  byte unchanged. The energy identity `E_L(t) = E_R(0.8 t)` still certifies (1.97 s) while the
  states differ (RK4: `w_L(2) = (-0.046, 0.218, 0.064)` against `w_R(1.6) = (0.225, 0.135,
  0.090)`); cover identical (lambda 4/5, budget 2, hops ECONOMY/SURVIVAL -> NOMINAL), letters
  S M B X unchanged; four new refutation witnesses on the new left (71 instances, 215 groups).
* `rover_terrain_2to4` (RETHINK, overall 2: `lambda_max = 3` read as the certificate's need): the
  window is now the derived traction ratio `(mu_PAVED + r_PAVED)/3 = 2.68` rounded up to the
  grid value `lambda_max = 2.7` (2.64 certifies, 2.63 declines); the row `w[l] <= v[r]` was
  tested and certifies at lambda 1 with letter I only, so the file keeps the re-timed form and
  says so. With the 20-step grid the GRAVEL cover is now 67/50 (was 13/10), PAVED 27/10, MUD 1.
  Letters S M I unchanged.
* `h2_refuel_ambientbias` (POLISH): `lambda_max` pinned to 1.0 (every cover was at lambda 1;
  identical battery, 12/12 handoff); the top rows' 2.9 is stated as the certificate's need
  (2.899 declines, 2.4 declines; no physically sound variant certifies the 2.4 end-pressure
  shift); the duplicate verdict block and the unusable aside removed.
* Header-only fixes (models unchanged, ablations identical before and after):
  `charger_fast_tapers` (the 2 % constant is the tool's tight value, not a requirement: re-timed
  lead 0.00 simulated, certifying window [2.00, 5.00], the two residual units named, SYNC declines
  at every c up to 90), `fuelcell_chp_dos` (the 5.00 is the segment-end successor obligation;
  simulated drifts +4.30 K / -5.83 K inside the bands; the Tin range [40, 56] as a limitation of
  the certificate, wider ranges need 10.00), `engine_start_highidle` (both ABORT edges pruned,
  ABORT a start only, the exact low rows and the letter D rest on it; the time-out clock model is
  scheduled), `turbine_startup_gearratio` (stock gains not scaled by 1/1.05; the scaled variant
  certifies only with the start-up's reachable speeds as domain; STOP a start only; one-sided
  against an existential reference), `tunnel_jetfan_pairout` (the floor `u >= 3.2` is the
  certificate's forward-invariant set, load-bearing at 2.54 through the mode fact `c <= 100`; the
  FIRE row carries no smoke-control content beyond it; the floor-2.6 variant with real FIRE rows
  certifies with D I and is scheduled), `acc_spoof_lag` (row 1 re-timed only; the real-time form
  certifies at -3.95 with `w = v + a/2` on both sides, letter I), `acc_spoof_limp` (the -0.20
  intercept needs the committed choice, 1.90 without it), `platoon_linkloss` (0.6 s; the AEB
  trigger period is not load-bearing), `platoon_profiles` (`platoon_latency` is in the suite;
  SPORT rows exact with no tolerance content, real-time tolerance 4.00), `quad_light_lag` and
  `quad_light_profiles` (4.905 /s is a velocity-loop gain, PX4 default 4 /s, not drag; K = 4.0
  certifies at lambda 1.24525 with the same letters; ECO/SPORT are starts the cover leaves),
  `rover_terrain_6to12` (ramp wording, the sigma 0.25 binding constraint and the 0.028 edge),
  `sat_detumble_phases` (stylized time unit, isotropic damping as a requirement of the claim,
  magnetorquer order of magnitude, FINE as a rate-damping phase).

Checks after round 1: `lake build` exit 0; `--check-quick-v2` 50 certified, modal 1241/1241,
handoff 542/542, non-connection 64/64, pruned 32/32, reposition 73/73, strict gate 188/188;
bridge 5245/5245; progress 199/199; refute 215/215 (71 instances); WellFormedBattery 66 lines;
`relcert-test` ALL PASS. Letter totals (`docs/paper-numbers/letters.md`, re-run 2026-10-29):
S 20, M 25 -> 26, R 7, B 12 -> 13, P 6, D 12, I 18, X 14 (the insulin file's M B; every other
benchmark's letters identical to the previous run; 25 benchmarks certify under `RELCERT_SYNC=1`).

## Skipped 2026-10-28: `lit_hypercert_vehicle`

`lit_hypercert_vehicle` left the suite (50 -> 49; literature 9 -> 8) for `benchmarks/skipped/`
(input unchanged, `SKIPPED.md` with the reason, no Lean integration): the source's claim is false as
formalized (under the source's own run semantics on X = [0, 8] x [0, 0.6] the secret run that cruises
5 steps and brakes 15 rests at s = 7.5, and every velocity-close partner starts inside the secret set),
and what the file certified was a claim about a different system (the position bound dropped), not a
weakening of the source's. Rule: a literature example whose source claim is false as formalized is
skipped, not repaired. Its copy-witness content lives on in `lit_lz21_vehicle_position`. Removed with
it: its generated leaves and bridge instance, its Assumption 1 proof (`WellFormed/LitHypercertVehicle`)
and its 16 witness-less finder records; the self-contained exhibit
`negative_wellformed/lit_hypercert_vehicle_s8` stays. Counts: handoff 528 -> 503, strict gate
184 -> 179 right modes (87 invariant, 92 exit), bridge groups 4874 -> 4797 (its 77), battery 66 -> 65
axiom lines.

## Review fixes 2026-10-28: `zone_lightmass_schedule`, `charger_fast_tapers`, two literature headers

Four changes from the benchmark review of 2026-10-28 (`docs/BENCHMARK-REVIEW-2026-10-28.md`), each
verified on scratch variants before it was installed:

* `zone_lightmass_schedule` (score 2, RETHINK): the exact re-timing identity `T_L = T_R` certified
  only the rounded plant (left rate 0.04, ratio exactly 2; with the stated plant 0.04125 and
  lambda 2 it declines, and a lambda grid misses 2). Now the band form: left rate 0.04125 (the
  stated 165/80), right 0.02, lambda 2 pinned (the design ratio), the comfort band 16..21 as
  guard and domain, rows `|T_L - T_R| <= 0.152` in both left modes. Tight: 0.152 certifies, 0.15
  declines (the inductive bound `(a - lambda b) 5 / a = 0.1515`); the reachable worst case from
  equal starts is 0.057 K; with ratio 2.25 the row needs 0.56 (the bound follows the cause).
  Letters S M B X kept (SYNC, lambda 1 and NO_CHOICE decline; NO_PRUNE, NO_CUT, NO_REPO certify);
  the stray ", M6" after the choice sentence is gone (no matrix column for X).
* `charger_fast_tapers` (score 1, RETHINK): the equal-time claim was false physically (the
  deployed leads the profile by up to 7 % SoC in the CC phase) and certified only by parking the
  profile at FULL in every CC-phase pairing, so its "tightest 1.00" measured 100 - 99. Now the
  physics-corrected model (only the CC rate raised: BULK 0.125; PRECHARGE 0.2 and ABSORB 0.05
  are the profile's values) against the profile replayed at the current ratio 5/4
  (`lambda_min = lambda_max = 1.25`), one-sided rows `x_L <= x_R + 2` (PRECHARGE `x_L <= x_R`),
  FAULT row kept. Tight at c = 2 (1.9999 declines), the two residual artifacts disclosed in the
  header (c >= 2 from the re-timed FAULT/FAULT pairing, c = 1 with that row loosened to +10; the
  remaining c >= 1 the FULL pairing's asymptote-against-floor gap). BULK_L x BULK_R is now a
  genuine joint segment; repositioning serves the BULK_L lag pairings only. Letters: S gained
  (lambda 5/4), M R B P D I kept; no X before or after (NO_CHOICE certifies; a two-sided
  PRECHARGE row declines at c = 2, 5, 10, and a lambda window [1.2, 1.3] certifies at 6/5 without
  choice either). The stretch must be pinned: searched on [1, 6] the tool takes lambda 1 and
  parks at FULL again. Suite counts after the two redesigns: modal 1004 -> 1007 and reposition
  76 -> 73 (the charger's joint pairings grew and its reposition nodes shrank), bridge groups
  `charger_fast_tapers` 222 -> 225, `zone_lightmass_schedule` 26 unchanged, 4800 over the suite
  and the two exhibits; progress certificates 199 unchanged.
  Letter totals (`docs/paper-numbers/letters.md`, re-run 2026-10-28): S 19 -> 20 (the charger's
  stretch), X 15 -> 14 (the skipped file), M 25, R 7, B 12, P 6, D 12, I 18 unchanged; benchmarks
  certifying under `RELCERT_SYNC=1` 25 -> 24; without pruning 44 -> 43 and without choice 35
  (the skipped file certified under both); the pruning ablation stays at 6 declines.
* `lit_freedm_meter`: header X paragraph corrected (the witness never needs its battery: a grid
  mode with the left's net draw always exists, the source's own argument for Prop. 11; a
  grid-only right and a battery-unreachable right also certify; choice is needed because the
  matching grid mode changes per window). Input unchanged.
* `lit_lz21_vehicle_position`: header item (3) now discloses that the three-level, guard-checked
  input narrows the universally quantified secret run (and that sub-period switching adds runs),
  with the copy witness level-independent (a five-level file also certifies). Input unchanged.

## Literature faithfulness fixes (2026-10-28)

The owner asked that the nine literature benchmarks be as faithful to their sources as the
suite's format allows; a read-only audit against the fetched sources (LICS 2016 and IJCAR 2024 for
dRL, LICS 2018 for FREEDM, CSF 2021, L-CSS 2021, DEDS 2008, NAHS 2025, HyperCertificates) listed
the fixes, every one tested on a scratch copy before it was installed. Models (five files):

- `lit_drl_car_stop`, `lit_drl_lane_control`, `lit_csf21_vehicle_thermo`, `lit_csf21_vehicle_bus`: the Coast
  action that the suite adds on both sides (the one-period stand-in for the source's braking to
  rest, which Assumption 1 forbids on the right) is now enabled only at `v <= 1` (`v_f <= 1` for
  the lane follower) instead of at any speed, so the attacked or conservative car is a subset of
  the source's car plus that stand-in. Every verdict is unchanged (CERTIFIED; the same
  configurations CERTIFIED and DECLINED as before, re-measured under control, SYNC, NO_PRUNE,
  NO_CHOICE, NO_PRUNE+NO_CHOICE, SYNC+NO_CHOICE, NO_CUT, NO_IMPLIED_CUT, NO_LINEAR_CUT,
  NO_PAIR_STRETCH, NO_REPO, OPREGION, WELLFORMED_STRICT, --handoff and --wellformed strict:
  0 UNKNOWN, 0 BLOCKING); covers and choice records unchanged except `lit_drl_lane_control`'s cover;
  bridge groups `lit_csf21_vehicle_thermo` 116 -> 120, `lit_csf21_vehicle_bus` 180 -> 186, the dRL files
  unchanged. The four Assumption 1 proofs are rewritten: the exit clause now splits on the end
  speed (`v <= 1` into Coast, `v >= 1` into Brake, with the thermostat or leader case split as
  before), Z3-free at the three standard axioms.
- `lit_nahs25_salt_tank`: the evolve domain `xp >= 0`, which the source's plant lacks, is dropped
  (the constant atom `0.0 <= 1.0`, as `lit_girard08_robot`); every verdict unchanged, bridge groups
  56 -> 54, the proof's domain clause now trivial.

Headers only (IR unchanged, checked by regenerating the leaves): `lit_drl_car_stop` (LICS 2016 gives
templates; the concrete car is Prebet-Platzer Example 1 with `safeT`, `safeE` unspecified, so
`Safe` and `Safe_eps` are our instantiation; the `v >= 0` domain is load-bearing, the
Prebet-literal variant declines and is false; what is certified is dRL's Open Goal 1);
`lit_drl_lane_control` (dRL removes FM 2011's stopped branch, `Safe` is ours, the three-valued leader
variant declines, open); `lit_freedm_meter` (the source has no sampling period; why sampling at 1 is
harmless; the literal charge test also certifies); `lit_csf21_vehicle_thermo` and `lit_csf21_vehicle_bus`
(Def. 5 is symmetric, the converse direction is immediate); `lit_lz21_vehicle_position` (the position
bound is dropped for the copying witness, not because the claim fails; the source starts at
rest, ours from every equal velocity pair); `lit_girard08_robot` (the certified abstraction is more
permissive than Fig. 3); `lit_hypercert_vehicle` (the Q1 reading kept; the stale sentence on the
successor-only `--wellformed` replaced by the strict gate's BLOCKING verdict). Suite counts
after the fixes: modal 1004, handoff 528, non-connection 64, pruned 32, reposition 76, strict gate
184 (88/96) unchanged; bridge 4866 -> 4874.

## Batch I11 (2026-10-28): three swaps from the reserve scan

Third round of the owner's 2026-10-27 request, decided on the reserve scan of 2026-10-28 (every
reserve file re-measured with the branch binary; criteria: physically meaningful with a named
source where one exists, a relational property an engineer cares about, letters disclosed where they
come from the claim's form, mechanisms judged per group). Three swaps, the suite at 50 (41 own
designs, 9 from the literature): `platoon_latency` (D; the degraded-network scenario, back in the
platoon group as a plain member) for `antenna_track_kvretune` (the weakest D of the suite: its D
came only from the rule that a uniform row drops a stated requirement); `reactor_feed_wireless`
(M B P; the exothermic reactor's feed interlock under a 2 min wireless publish period, P being the
suite's scarcest letter; the thermal constants are design values, the publish period a WirelessHART
setting, the two 9 K process-safety limits stated) for `compressor_station_recycle` (a single
identity-hop X with no source); `h2_refuel_ambientbias` (R D I; a 70 MPa fill under a 10 K
ambient-sensor bias, the protocol now named: SAE J2601, 70 MPa NWP, 87.5 MPa = 125 % maximum
fueling pressure, 0.5 MPa minimum tank pressure, the end pressure read from the ambient table)
for `molding_pack_checkring` (a single D with no source for its 25 bar envelope or hold time).
Each installed with the full pipeline: `platoon_latency`'s Lean integration restored from commit
9dcda0c (the right model unchanged, cover byte-identical), new Z3-free Assumption 1 proofs
`WellFormed/H2RefuelAmbientbias.lean` (six 1-D contractions, as `EngineStartHighidle`) and
`WellFormed/ReactorFeedWireless.lean` (four exponential runs at dimension 2, as `FuelcellChpDos`),
the KEYED set (`h2_refuel_ambientbias`, `platoon_latency` in; `antenna_track_kvretune`,
`molding_pack_checkring` out), bridge instances, modal and reposition packs, refutation finder
runs (`--only`) and two matrix families. Every installed right model passes `--wellformed` strict
with 0 UNKNOWN and 0 BLOCKING. Letter totals S 19, M 24 -> 25, R 6 -> 7, B 11 -> 12, P 5 -> 6,
D 12, I 17 -> 18, X 16 -> 15; benchmarks certifying under `RELCERT_SYNC=1` 26 -> 25.

## Batch I10 (2026-10-28): one time-scaled design in, one single-letter file out

Second round of the owner's 2026-10-27 request (more Table 1 mechanisms, every benchmark physically
meaningful with a meaningful relational property). One swap: `zone_lightmass_schedule` (a building-
automation occupancy schedule, comfort / standby / economy set points as in the EN 15232 energy levels,
deployed in a lightweight prefabricated zone of half the areal heat capacity of the medium-weight zone it
was commissioned in; the light zone reproduces the reference zone's temperature trace at twice the speed:
exact rows `T_L = T_R` at `lambda = 2`, the heat-capacity ratio, budget 2; letters S M B X, with B and X
from the claim's form as the header states) replaces `bms_chiller_undercharge` (X only, certifies under
`RELCERT_SYNC=1`; in the reserve with its reason). Designed and measured in scratch first (every
configuration, `--handoff`, `--wellformed` strict; 1.9, 2.1 and 1.0 DECLINE, the exact ratio), installed
with the full Lean pipeline (Assumption 1 proof `WellFormed/ZoneLightmassSchedule.lean`, Z3-free, at
dimension 2; bridge instance; 8 refutation mutants, no witness). Tried and not adopted: a vacuum
pump-down recipe on a load lock of half the chamber volume (the same exact scaling, but the reference's
irreversible turbo start pairs with the deployed's roughing phase as an admissible start with no return
edge: DECLINED), and a second first-order time-scaled design in another domain (a mathematical twin of
the zone file; not added). Letter totals S 18 -> 19, M 23 -> 24, B 10 -> 11, R 6, P 5, D 12, I 17,
X 16; benchmarks certifying under `RELCERT_SYNC=1` 27 -> 26. The suite stays at 50 (41 designed, 9 from
the literature).

## Batch I9 (2026-10-27): more mechanisms, the multi-rate and stretch passes, two swaps

Owner request (2026-10-27): demonstrate more of the paper's Table 1 mechanisms while keeping every
benchmark physically meaningful; the earlier equal-period pass (batch I4) and the stretch pins (batch
I6) came from an over-reading ("letters must come from the cause") that the owner has dropped: a
slower deployed controller, from a lower-rate ECU, a slower network, a slower sensor or a duty cycle,
is a legitimate stated scenario, and a claim naturally stated at matched progress may carry a stretch
range taken from a stated source. Every change was designed and measured in scratch first (control,
SYNC, NO_PRUNE, NO_CHOICE, NO_PRUNE+NO_CHOICE, NO_CUT, NO_REPO, OPREGION, `--handoff`, `--wellformed`
strict, the uniform-rows test for D), installed with the full Lean pipeline, and each header states
where its period or stretch comes from and where each letter comes from. Letter totals S 12 -> 18,
M 15 -> 23, R 6, B 8 -> 10, P 5, D 12, I 17, X 16; benchmarks certifying under `RELCERT_SYNC=1`
33 -> 27 (`docs/paper-numbers/letters.md`). The suite stays at 50 (41 designed, 9 from the literature).

Multi-rate pass (the deployed side's decision period restored to twice the reference's, with the
stated reason; right models and their Assumption 1 proofs unchanged): `sat_detumble_phases` and
`sat3w_detumble_phases` (the flight mode manager evaluates the phase handover every other 1 s sensor
cycle, a two-sample debounce: X -> M I X, the FINE capture envelope being the load-bearing cut on the
second design cycle), `sat_detumble_weak` (the ADCS in its under-voltage power-saving duty cycle decides
every 2 s; with the exact re-timed claim below: I X -> S M B X), `charger_fast_tapers` (the raised-limit
firmware takes the phase decision on every other CHAdeMO request cycle, 0.72 s: R P D I -> M R B P D I)
and `platoon_linkloss` (the link-loss supervisor's two-message timeout, 0.2 s: D -> M D). Tried and
not adopted: a doubled period on the eleven equal-period D-only or X-only files (antenna, bms,
bottling, compressor, elevator, furnace, hydro, molding, syringe, tunnel, ventilator: each DECLINES),
on `engine_start_highidle` and `turbine_startup_gearratio` (M would appear, but no physical reason for a
slower start sequencer), and on the chain and ladder rungs (each rung's right is the previous rung's
left, so a period ratio would break the composition).

Stretch pass (claims naturally stated at matched progress; the stretch stated from the cause or from
a stated allowance, never searched to trigger a letter): `acc_spoof_lag` (the exact dominant-mode claim
`u_L <= u_R - 6` with `v_L <= v_R` at the stated ratio 3/2, the loop-gain factor the spoof introduces:
I -> S M; the batch-I4 real-time shortfall envelope still certifies and is quoted as a consequence),
`quad_light_profiles` (altitude conformance to the plan's NORMAL profile at the terminal-rate ratio 6/5
the mass ratio fixes, the rows of `quad_light_airframe_20`, the complete profile graph kept: X ->
S M B X), `sat_detumble_weak` (the weakened spacecraft's energy equals the NOMINAL design model's at
4/5 of its clock, the derating ratio: exact, pinned) and `rover_terrain_2to4` (the no-slip plan's speed
loop is the wheel loop's 3 /s again, the 4-DOF model with slip and sinkage removed, and the progress
claim is stated against the plan re-timed within an allowance `lambda in [1, 3]` that covers the
largest ratio the chain can need, `(mu_PAVED + r_PAVED) / 3 = 2.68`, with margin: I -> S M I; the
covers use 13/10 in GRAVEL and 27/10 in PAVED, lambda_max 2.5 DECLINES, 2.7 CERTIFIES; the terrain
chain still composes, 12-DOF <= 6-DOF <= 4-DOF in real time <= plan re-timed by at most 3, and a stop
line the plan never passes is never passed by the 12-DOF rover since the position bound is time-free).
Every exact ratio certifies at its exact value only (as `quad_light_lag`'s 6/5 and `acc_tune_lag`'s 2):
the headers state the measured decline at the neighbouring grid points. Tried and not adopted: the
exact dominant-mode rows together with the real-time shortfall envelope on `acc_spoof_lag` (DECLINED at
every stretch), a stretch range on `rover_terrain_4to6` and `rover_terrain_6to12` (their claims hold in
real time, the range is unused), and the batch-I4 band claim of `sat_detumble_weak` with a stretch
range (SYNC still certifies, 114 s).

Two swaps. `flaps_slow_approach` is back from the reserve (S: the per-mode stretch 1/2 while the flaps
move, from one of the flap drive's two hydraulic motors, and 1 once they are set; a tolerance claim on
the approach speed) and takes the place of `insulin_basal_cgmloss` (M B; the chain-depth multi-cycle
template under a 2:1 period ratio is carried by `tank_dos_3to1`, whose mode facts are load-bearing (M I),
`fuelcell_chp_dos` (M B P X) and the three satellite files; the third slowest suite file at 15 s; the
medical domain stays represented by `ventilator_vc_cuffleak` and `syringe_relay_prearm`; a first form of
this batch had moved `tank_dos_3to1` instead, which left the letter I at 16, below the frozen 17, so the
tank file stays and the insulin file goes). `platoon_profiles` is back from
the reserve as the round-A time-scaled design (SPORT = the CACC at 1.2 times its bandwidth, kp 0.18,
kd 0.9; the SPORT follower's gap and closing rate are the NORMAL follower's re-timed by 6/5, the AEB
the same function at real time; `lambda in [1, 1.2]`, the two pairings' ratios: S M D) and takes the
place of `platoon_latency` (D; the same right model and the same AEB D as `platoon_linkloss`). Both
right models are batch-I6 / batch-I2 ones with their Assumption 1 proofs (`WellFormed/FlapsSlowApproach`,
`WellFormed/PlatoonProfiles` through the shared `PlatoonCaccAeb` lemmas). The two files that left are
stored in `benchmarks/reserve/` as the suite files with one line of reason each; their Lean integration
is in git history (`platoon_latency` last at commit 9dcda0c, `insulin_basal_cgmloss` at c57ca5f).

Also in this batch: the `acc_tune_limp` header states D under the rule of 2026-10-27 (S M B D I X).

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
compressor level to track the degraded full level: mode choice; in the reserve since batch I10), `canal_gate_notches` (an
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

## Renamed 2026-10-28: the literature group

The nine case studies reproduced from published work carry the prefix `lit_` (family
"Literature" in `scripts/suite_v2_matrix.py`), with the source's venue and year where the old name
lacked it. Only names changed (directory, `name =`, header lines, derived Lean identifiers and
modules, refutation mutants and witnesses); models, invariants, certificates and proofs are
unchanged. The exhibits sharing a stem are renamed with them. Older records (git history, dated
docs) use the old names.

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

## Batch I8 (2026-10-27): five own designs swapped for case studies from published work

Owner request (2026-10-27): prefer case studies from existing work, for credibility; the literature
group of four was too thin. Five of the suite's own designs move to the reserve and five case
studies reproduced from published papers replace them; the suite stays at 50 (41 designed, 9 from
the literature). Each new header cites its source, states what the file reproduces and every
departure from it, and reports the verdicts measured on this branch. Each install with its Lean
integration (records, bridge instance, a new Z3-free Assumption 1 proof stated over the bridge's
automaton, `_wellFormedR_direct`), a refutation-finder run, the matrix family `Literature` and the
counts; each move with its Lean integration, records, refutations and counts.

First group: `lit_csf21_vehicle_thermo` (Xiang, Fulton, Chong, CSF 2021, the car with interior
temperature control: an attacker who owns the cabin-temperature reading cannot change the car's
distance and velocity; X, the genuine car commits to the attacked car's action at every window)
and `lit_csf21_vehicle_bus` (the same paper's internal-bus case study: the thermostat shares the
drive's bus, one message per cycle, twelve genuine modes by message type; X) in;
`hvac_fan_staging` and `platoon_profiles` (the two tier-2 members of the final audit: the identity
hop of template B, and a special case of `platoon_linkloss`) to the reserve. The negative exhibit
`lit_csf21_vehicle_thermo_leaky` (an air-conditioning load on the drive lets the temperature reading
reach the velocity; expected DECLINED) joins `lit_freedm_meter_leaky` in `benchmarks/negative/`.

Second group: `lit_lz21_vehicle_position` (Liu and Zamani, IEEE L-CSS 2021: approximate initial-state
opacity of a vehicle whose position an intruder observes with precision 1 m; the partner run starts
1 m ahead and copies the input; X), `lit_girard08_robot` (Girard, Julius, Pappas, DEDS 2008: a planar
robot with its dynamic tracking controller is approximately simulated, with precision 0.4 m, by its
planner's kinematic model; X; the robot written in the coordinates of the source's simulation
function; its location changes sampled, since the generic bridge takes one evolve domain per side,
`Emitted.uniformEvolve`: with the source's per-location evolve domains every verdict is the same but
no bridge instance can be stated, the header's departure (6)) and `lit_nahs25_salt_tank` (Xiang,
Lanotte, Tini, Chong, Merro, NAHS 2025: a brine tank whose salt sensor is under a bounded attack
stays within 3 lb of the genuine tank, the source's forward simulation distance; I) in;
`rover_rollover_payload` (both letters from the claim form, and a second structural difference,
the reference's transition bands), `flaps_slow_approach` (the integrator-stretch template shared
with `furnace_program_timebase` and `bottling_fill_strainer`, a weakly sourced tolerance, exact
rows dependent on the stretch grid) and `canal_gate_notches` (one of several X-only own designs;
the literature cases now show X) to the reserve.

**Relation to the running example.** The NAHS 2025 salt-tank case, now `lit_nahs25_salt_tank`, is a
related published scenario (one tank, a sensor attack of magnitude 3, the same attack magnitude as
`watertank`; its claim is the source's Def. 8 distance 0 by stutter since 2026-10-29, the band 3
of the lock-step reading before), not the source of the paper's running example
`watertank`: the plants, the attacks (a bounded reading error at every sample against a constant
3 dm offset with a tampered pump) and the mechanisms (S at stretch 0 against S M B at stretch 2)
differ (`lit_nahs25_salt_tank`'s header, "RELATION TO THE RUNNING EXAMPLE").

## Batch I7 (2026-10-27): two tier-2 members swapped for reserve designs

Owner clarification (2026-10-27): a benchmark needs a meaningful relational property; its claim
need not depend on the stated cause. Two reserve designs set aside only because their claims also
hold for other deployed behaviour replace the two tier-2 members; the suite stays at 50.
`charger_fast_tapers` (a DC fast charger whose current limit is raised 25 %, against the certified
profile with two taper options; R P D I) is back from the reserve at the minute time scale
(`epsilon = 0.006` min = 0.36 s on both sides, the rate constants per minute: a 15 -> 80 % bulk
phase of about 14.5 min; the earlier design used the hour with `epsilon = 0.0001` h), the same
letters, the tightest charging row 1.00 % as before; its header states the 2 % BMS-accuracy
requirement and that the bound also holds for other deployed charge rates. Its Assumption 1 proof
is the round-2 proof at the new interval. `quad_light_airframe_20` moved to the reserve (the
lag-free special case of `quad_light_lag`). Each move with its Lean integration, records,
refutations and counts.

Second group: `grid_ffr_dos` (an island grid's fast frequency response under a denial-of-service
attack on the FFR command link, holding each supervisor decision for 0.3 s, against the command
delivered every 0.1 s; M P: one attacked cycle against three nominal cycles, the generator trip
edges pruned by non-connection certificates) is installed from the reserve (round-A design, the
model unchanged). Its header states the FFR-loss requirement (the attacked island at most the
FFR's own frequency support, 0.1 / 0.42 = 0.238 Hz, rounded to 0.24, below the nominal one) and
that the bound also holds for a longer hold and for a deployed FFR that never activates; the
exact claim certifies without the attack and declines with it. Its Assumption 1 proof is new
(an explicit run, and a non-strict barrier for the FFR release line `x - 2a <= -0.4`).
`rampmeter_poll_2to1` moved to the reserve (the chain-depth template of `tank_dos_3to1` and
`insulin_basal_cgmloss` repeated).

## Batch I6 (2026-10-27): round C fixes and five new benchmarks

From the final audit of the suite (round C). `rover_terrain_2to4`: the plan's speed loop now runs
at the rover's fastest ground response (8 /s, the traction stiffness on pavement) instead of the
wheel loop's 3 /s, so "never ahead of the plan" holds in real time: the file certifies at
lambda 1 (`lambda_min = lambda_max = 1`; the 3 /s plan at lambda 1 DECLINES), letters S M gone,
I kept, the tightest slip threshold still 0.21; its left model is unchanged, so it is still
exactly `rover_terrain_4to6`'s right with `u`, `zh` pinned and the chain composes, now with
every step at lambda 1; its Assumption 1 proof follows the new rate. Stretch ranges pinned (every
cover already used the pinned value; verdicts and letters unchanged): `quad_light_lag` to exactly
6/5 (the terminal climb-rate ratio; [1, 2] certified only because 6/5 is a stretch-grid point),
`acc_spoof_limp`, `engine_start_highidle`, `turbine_startup_gearratio`, `rover_terrain_4to6` and
`rover_terrain_6to12` from `lambda_max = 6` to 1. `acc_spoof_limp`'s header now says that its M
and B come from the deployed monitor's 2 s debounce period and that I persists without the
spoof. `quad_light_airframe_20` is marked tier 2 in its header (the lag-free special case of
`quad_light_lag`), kept until a replacement exists.

Second group, five new benchmarks (round C designs; every header re-measured on this branch, the
letters as measured, `scripts/suite_v2_matrix.py` families added): `flaps_slow_approach` (an
airliner extending its flaps to CONF 2 with one of the flap drive's two hydraulic systems lost,
the flaps at half speed, against both systems; S, a per-mode stretch 1/2 while the flaps move with
a 20 kt speed tolerance; the header states that the flap rows need the rate ratio on the stretch
grid: 0.49 and 0.51 deg/s both DECLINE), `tunnel_jetfan_pairout` (a 1.6 km road tunnel with one of
its five jet-fan pairs out of service, through a fire alarm; D I: the CO row of normal operation is
dropped in fire mode; the design's fire-mode velocity tolerance `u_R <= u_L + 4.2` was implied by
the domains and was dropped at installation, the 3 m/s critical velocity is met by the
forward-invariant 3.2 m/s floor; I persists with all ten fans), `rampmeter_poll_2to1` (a ramp meter
on 40 s polled detector data against the 20 s local update; M B; TIER 2: the final audit
recommended the reserve, the chain-depth template of `tank_dos_3to1` and `insulin_basal_cgmloss`
again and its 10 veh/mi/ln requirement 1.0 below the 11 at which any schedule certifies; it stays
until a replacement exists), `bottling_fill_strainer` (a volumetric bottle filler with a partly
clogged product strainer, 85 % flow; S I; at installation `CLOSE`'s guard gained the
predicted-final-volume conjunct `V + (Q/25) u <= 1060` on both sides, each with its own flow: the
design's right `CLOSE` was BLOCKING at the domain top under the strict Assumption 1 gate; verdicts,
letters and the tightest 1.20 mL unchanged) and `antenna_track_kvretune` (a LEO ground-station
antenna's elevation axis retuned to a lower velocity error constant, over the end of a pass; D:
the pointing row while tracking, the slew-lag envelope during the stow slew; in the reserve since
batch I11). Each right model
has its Z3-free Assumption 1 proof (`InstancesV2/WellFormed/`; `tunnel_jetfan_pairout`'s is the
first over a polynomial right field, `u^2` and `u c`, with an explicit Riccati run), each its
bridge instance (two mode-keyed). Suite 45 -> 50.

## Batch I5 (2026-10-27): ten new benchmarks, four designs to the reserve

New (designs of rounds A, B and C; every header re-measured on this branch, the letters as
measured, `scripts/suite_v2_matrix.py` families added): `molding_pack_checkring` (an
injection-molding pack and hold phase on a machine with a worn check ring, against a new ring;
D: the hold row bounds nozzle and cavity pressure, the cooling row only the cavity; in the reserve
since batch I11),
`fuelcell_chp_dos` (a PEM fuel-cell CHP unit whose current-level selection is held for two
protocol cycles by a denial-of-service attack, against the stack maker's protocol; M B P X; its
7 K tolerance sits in a narrow non-monotone certified window, [5, 8] certifies, (8, 10) declines,
10 certifies again, and the header now gives where its 45/85 degC window and 40-56 degC return
range come from), `elevator_start_discbrake` (an elevator trip with a retrofitted fast-lifting
disc brake, against the validated drum-brake trip; R D; at installation `STOP`'s guard gained the
rest-position conjunct `z + v/4 <= 20.5` on both sides: the design's `STOP` was BLOCKING at the
overhead limit under the strict Assumption 1 gate; verdicts and letters unchanged),
`furnace_program_timebase` (a heat-treatment furnace running its validated program at 80 % rate;
S I; the stretch range [0.8, 1] is the recipe's rate window; it DECLINES without the widened cut
channel), `compressor_station_recycle` (a gas compressor station whose third unit's recycle valve
is stuck open; X, which also appears with a healthy valve as an identity hop, now said in the
header; the non-identity commitment is the fault's; in the reserve since batch I11), `syringe_relay_prearm` (a syringe-pump relay
that pre-arms the incoming syringe, against the validated relay; R D), `hydro_rejection_gatecal`
(a hydro unit with a gate transducer recalibrated 2 % low, in a load-rejection test; D),
`ventilator_vc_cuffleak` (a volume-controlled breath with an under-inflated cuff, against a
sealed cuff; D, the rows from ISO 80601-2-12's volume and PEEP accuracy) and
`insulin_basal_cgmloss` (automated basal insulin whose glucose readings arrive over a lossy
link, against every reading; M B). Each right model has its Z3-free Assumption 1 proof
(`InstancesV2/WellFormed/`), each its bridge instance (five mode-keyed). Suite 35 -> 44.

Second group: `rover_rollover_payload` (the canonical 12-DOF rover with a mast payload that
raises its centre of gravity from 0.9 m to 1.2 m, roll gradient 0.015 -> 0.02 and load-transfer
factor 4/3, against the same rover without the payload; the claim bounds the payload rover's
load-transfer ratio and its excess over the nominal's scaled by the CG ratio; the reference reads
the zone joints as 2 m transition bands with back edges, a second structural difference disclosed
in the header; X I from the claim form, present also at `h_L = h_R`, disclosed; about 20 s). Its right model
is the first with a two-way coupled block (`φ → ω_y → y → ω_φ → φ`); its Assumption 1 proof
builds the run by Picard–Lindelöf on an enlarged, strictly inflowing box and recovers the true
box coordinate by coordinate (`InstancesV2/WellFormed/RoverRolloverPayload.lean`). Suite 44 ->
45. Four designs went to `benchmarks/reserve/` without ever entering the suite:
`datacenter_crah_poll` (a near-duplicate of `tank_dos_3to1`), `reactor_feed_wireless` (a twin of
`fuelcell_chp_dos`), `rover_lateral_tirewear` (a twin of `rover_rollover_payload`, at three
decline edges) and `lng_cooldown_overspray` (the `hvac_fan_staging` pattern, its parameter at a
decline edge).

## Batch I4 (2026-10-27): equal periods, and seven files to the reserve

Installed over the suite files (the equal-period designs of the round-A pass, inputs and headers
re-measured on this branch): `acc_spoof_lag` and `acc_tune_lag` (both sides at the 0.1 s radar
cycle; each left guard is now its own loop's forward-invariant engaged envelope, so no left run
from the engagement box is cut short; letters I, resp. S M), `acc_tune_limp` (0.1 s periods;
letters S M B I X; its mode-dependent rows are expressiveness, a uniform row certifies, so no D),
`sat_detumble_phases` and `sat3w_detumble_phases` (1 s on both sides; the design model now has
both phases, `FINE` added, with the same phase logic as the full model, and the claim is exact
energy equality in both phases; letter X), `sat_detumble_weak` (1 s on both sides; both sides at
the design-model level, so the weakened gain is the one cause; letters I X).

Seven files left the suite (suite 42 -> 35) for `benchmarks/reserve/`, each stored as its
equal-period design of the round-A pass with a banner and one line of reason
(`reserve/README.md`): `charger_fast_tapers` (the claim does not depend on the current limit; a
wrong time scale), `charger_fast_setpoints` (the same cause-blind claim; a stale name),
`sat_detumble_nominal` (no letter; `sat_detumble_phases` restricted to `DETUMBLE`),
`sat3w_detumble_nominal` (no letter), `sat3w_detumble_weak` (the same numbers as
`sat_detumble_weak`), `arm_plateau_crit` and `arm_plateau_slow` (no genuinely relational claim
against the ramp planner; stored as the relational redesign, the planner fallback noted). Their
Lean leaves, Assumption 1 proofs, bridge instances and refutations are in git history (last at
commit 0a40e7d).

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
Stretch 0 (stutter, opted in with `[problem] stutter = true`, `docs/STUTTER.md`) is a special case
of stretching and is credited under S (2026-10-30; the separate letter W of 2026-10-29 is folded
into S): a cover has a stretch-0 pairing and the file without the key declines. One suite_v2 file
sets the key (`lit_nahs25_salt_tank`).
The pre-landing key (`[problem] prelanding = true`, `docs/PRELANDING.md`, 2026-10-30): a right-only
segment's flow certificate only before the landing. One suite_v2 file sets it since batch 11
(`lit_nahs25_engine_cooling`, the NAHS 2025 engine cooling system at the source's distance 0.3, the
genuine Cool guard closed to `temp >= 100`, disclosed; letter R, `RELCERT_NO_REPO=1` declines); the
same file under its demo name stays in `benchmarks/prelanding_demo/engine_cooling_prelanding`, beside
`hold_reposition_strict`, a synthetic strict-row demo of the same key (the strict component on the
closed pre-landing region).
Used and needed (2026-10-30, batch 11, owner's decision): Table 1 lists the mechanisms a certificate
USES and marks those it also NEEDS. Needed is the rule above (the file declines with the mechanism
switched off; M and B by the cover shape); used is read off the replayed derivation of the cover
found (S a stretch other than 1, stretch 0 included; M and B the cover shape; R a right-only segment
on the path; P an edge pruned out of a path mode into a live mode; D non-vacuous unsat handoffs of
differing rows; I a cut kept on the path that is load-bearing for that certificate: `NO_CUT`
declines or finds a different cover; X a committed-choice record). Both flags per file in
`docs/paper-numbers/letters.md` / `letters.json`, rules in the docstring of
`scripts/suite_v2_letters.py`, Table 1 and appendix snippets in `docs/paper-numbers/table1.tex` and
`table_per_benchmark.tex`.

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
| `acc_spoof_lag` | 2 / 2 | 1 / 1 | sensor-attack | redesigned 2026-10-26: same lag both sides; 2026-10-27: equal 0.1 s periods, the left guard its own loop's engaged envelope; batch I9: the exact dominant-mode claim at the stated ratio 3/2 (`lambda_min = lambda_max = 1.5`) |
| `acc_spoof_limp` | 1 / 1 | 2 / 4 | sensor-attack | redesigned 2026-10-27: the same two requirement rows in both modes (no longer mode-keyed), closed right guards; lambda pinned to 1 (batch I6) |
| `acc_tune_lag` | 2 / 2 | 1 / 1 | degraded-controller | redesigned 2026-10-26: same lag both sides; 2026-10-27: equal 0.1 s periods, the left guard its own loop's engaged envelope |
| `acc_tune_limp` | 1 / 1 | 2 / 2 | degraded-controller | mode-keyed, mode choice; equal 0.1 s periods since 2026-10-27; review round 6 (2026-10-30): the never-run COMFORT and SPORT right modes removed |
| `bottling_fill_strainer` | 2 / 2 | 2 / 2 | degraded-actuator | new 2026-10-27 (batch I6): stretch 17/20 in FILL (`lambda_min = 0.8`), load-bearing mode fact; `CLOSE`'s predicted-final-volume guard conjunct added at installation |
| `canal_gate_notches` | 1 / 1 | 3 / 4 | controller-refinement | back from the reserve 2026-10-29 (fix round 4, for the skipped `grid_ffr_dos`; in the reserve from batch I8): mode choice (the operating rule's notch committed at each window start) |
| `lit_csf21_vehicle_bus` | 3 / 3 | 6 / 12 | sensor-attack | literature (CSF 2021, internal bus), mode choice; new 2026-10-27 (batch I8) |
| `lit_csf21_vehicle_thermo` | 3 / 3 | 6 / 6 | sensor-attack | literature (CSF 2021), mode choice; new 2026-10-27 (batch I8); leaky counterpart in `benchmarks/negative/` |
| `lit_gpt10_boost_converter` | 2 / 2 | 48 / 2 | abstraction | literature (Girard, Pola, Tabuada, TAC 2010), mode choice; new 2026-10-29 (literature migration), in place of `lit_drl_car_stop` |
| `lit_drl_lane_control` | 3 / 3 | 6 / 6 | controller-refinement | literature (dRL), mode choice |
| `elevator_start_discbrake` | 3 / 3 | 4 / 4 | actuator-change | new 2026-10-27 (batch I5): mode-keyed (LIFT row), right-only repositioning (the reference's slower brake lift); STOP's rest-position guard conjunct added at installation |
| `engine_start_highidle` | 3 / 3 | 6 / 6 | controller-change | new 2026-10-27: mode-keyed, widened cuts; lambda pinned to 1 (batch I6); fix round 4 (2026-10-29): start-air supply p and STARTER_LOW, a reachable hung-start abort |
| `flaps_slow_approach` | 2 / 2 | 2 / 2 | degraded-actuator | back from the reserve 2026-10-27 (batch I9; new in batch I6): a per-mode stretch 1/2 while the flaps move (one hydraulic motor of two), 1 once set; 20 kt speed tolerance (S) |
| `lit_freedm_meter` | 2 / 2 | 12 / 12 | information-flow | literature (dHL, FREEDM), mode choice |
| `extruder_pe100_manualstart` | 2 / 2 | 4 / 4 | degraded-controller | new 2026-10-30 (batch 11, a design for a genuine P, `docs/BATCH11-2026-10-30.md`): a single-screw extruder start-up on a PE100 grade, the torque-limit speed permissive run by hand at the SOP's 2-min checks against the automatic sequence every minute; multi-step and branching covers (budget 2), four pruned edges into the live steps N1 and N4, the recipe range of the data sheet in the guards (M B P I); took the slot of `rover_terrain_6to12` (to the reserve) |
| `furnace_program_timebase` | 2 / 2 | 3 / 3 | controller-change | new 2026-10-27 (batch I5): stretch 4/5 (`lambda_min = 0.8`), widened cuts, load-bearing mode facts |
| `gantry_speed_zones` | 2 / 2 | 3 / 1 | controller-refinement | new 2026-10-27 (replaces `match_multi_rate`): a time stretch per speed zone (3, 2, 1), multi-step covers |
| `lit_girard08_robot` | 6 / 2 | 6 / 6 | abstraction | literature (Girard, Julius, Pappas, DEDS 2008), mode choice; new 2026-10-27 (batch I8); location changes sampled on both sides (the bridge's one evolve domain per side) |
| `h2_refuel_ambientbias` | 1 / 1 | 5 / 5 | sensor-fault | new 2026-10-28 (batch I11, from the reserve): a 70 MPa hydrogen fill whose dispenser's ambient sensor reads 10 K high, so the SAE J2601 end-pressure table returns 72.4 MPa; mode-keyed (exact stage rows, the top rows at the derived 2.9 MPa allowance), right-only repositioning out of a TOPOFF window, load-bearing checked cuts (R D I); fix round 4 (2026-10-29): start-only ABORT removed; widened cuts |
| `hydro_rejection_gatecal` | 3 / 3 | 2 / 2 | degraded-sensor | new 2026-10-27 (batch I5): mode-keyed (shared-grid equality before the breaker opens, a speed band after) |
| `rampmeter_poll_2to1` | 3 / 3 | 6 / 6 | degraded-network | new 2026-10-27 (batch I6), in the reserve from batch I7 to 2026-10-29, back in place of `insulin_basal_cgmloss` with the HCM requirement 8 veh/mi/ln: multi-step and branching covers |
| `lit_lz21_vehicle_position` | 2 / 2 | 3 / 3 | opacity | literature (Liu, Zamani, L-CSS 2021), mode choice; new 2026-10-27 (batch I8) |
| `molding_pack_checkring` | 3 / 3 | 2 / 2 | degraded-actuator | back from the reserve 2026-10-30 (review round 6, in place of `charger_fast_tapers`; in the reserve since batch I11): an injection-molding pack and hold phase with a worn check ring against a new one; mode-keyed (the hold row bounds the nozzle and the cavity pressure, the cooling row only the cavity pressure), physical domain (the 2000 bar pressure rating); letters D |
| `platoon_latency` | 3 / 3 | 2 / 1 | degraded-network | back from the reserve 2026-10-28 (batch I11; in the reserve from batch I9): the V2V feed-forward two control periods late (its Pade lag's error `e` bounded by the ISO 15622 jerk limit), against the design follower with an ideal link; mode-keyed (AEB row), right model shared with `platoon_linkloss` (D); fix round 4 (2026-10-29): start-only AEB removed on both sides, D gone |
| `platoon_linkloss` | 2 / 2 | 2 / 1 | dos-attack | redesigned 2026-10-27 (was `platoon_delay_linkloss`): mode-keyed (AEB row), CACC -> ACC fallback; batch I9: the deployed link-loss decision every 0.2 s (two-message timeout), multi-step covers; fix round 4 (2026-10-29): start-only AEB removed, D gone |
| `platoon_profiles` | 2 / 2 | 1 / 1 | controller-refinement | back from the reserve 2026-10-27 (batch I9) as the time-scaled design: SPORT = the CACC at 1.2 x bandwidth, exact re-timed SPORT rows at 6/5, the AEB at 1 (`lambda in [1, 1.2]`); mode-keyed (AEB row), right model shared with `platoon_linkloss`; fix round 4 (2026-10-29): AEB removed, SPORT kd 0.85 (critical damping), tolerance rows, D gone |
| `quad_light_lag` | 3 / 3 | 1 / 1 | model-refinement | redesigned 2026-10-27: altitude coordinate, rows from the 0.8 m altitude acceptance radius; the time scaling fixed to 6/5 (`lambda_min = lambda_max = 1.2`, batch I6) |
| `quad_light_profiles` | 2 / 2 | 3 / 3 | model-refinement | redesigned 2026-10-27: altitude coordinate; batch I9: conformance to the reference's NORMAL profile at the stated scaling 6/5 (the rows of `quad_light_airframe_20`), multi-step and branching covers, mode choice; review round 6 (2026-10-30): the three profiles on both sides (pilot switching), SPORT set point 2.5, per-profile stretch |
| `reactor_feed_wireless` | 2 / 2 | 4 / 4 | degraded-sensor | new 2026-10-28 (batch I11, from the reserve): an exothermic CSTR's feed interlock read through a WirelessHART transmitter every 2 min against the validated 1 min wired reading; multi-step and branching covers (budget 2, the design's deterministic level partition), four pruned edges into the live levels F1 and F4 (M B P) |
| `rover_ladder_2to3` | 3 / 3 | 3 / 3 | model-refinement | reinstalled 2026-10-27 on the canonical rover hierarchy (L3 / L2): clearance and heading rows, lambda 1 |
| `rover_ladder_3to6` | 6 / 6 | 3 / 3 | model-refinement | reinstalled 2026-10-27 (L6 / L3): clearance, heading and pitch rows, lambda 1 |
| `rover_ladder_6to8` | 8 / 8 | 3 / 3 | model-refinement | reinstalled 2026-10-27 (L8 / L6): + roll and rollover (LTR) rows; lambda [1, 1.25] from the timetable tolerance (S M I from the re-timed claim form, header) |
| `rover_ladder_8to12` | 12 / 12 | 3 / 3 | model-refinement | reinstalled 2026-10-27 (L12 / L8): heading, roll, rollover (LTR) and lane rows; lambda [1, 1.25] (S M I from the re-timed claim form, header) |
| `rover_patrol_lag` | 3 / 2 | 4 / 4 | model-refinement | reinstalled 2026-10-27: the rover with its motor lag against the first-order planning model; lead bound as an order property up to a 3/2 re-timing (S M R B from the claim form, header) |
| `rover_terrain_2to4` | 4 / 4 | 3 / 3 | model-refinement | redesigned 2026-10-26 (was `rover_terrain_3to6`): terrain chain, wheel slip and sinkage; zone-only right plan; batch I9: the plan's speed loop at the wheel loop's 3 /s again, progress against the plan re-timed within `lambda in [1, 3]` (S M I) |
| `rover_terrain_4to6` | 6 / 6 | 3 / 3 | model-refinement | redesigned 2026-10-26 (was `rover_terrain_6to8`): terrain chain, drive lag and roughness heave; right cap `w <= c_T`; lambda pinned to 1 (batch I6) |
| `lit_nahs25_engine_cooling` | 1 / 1 | 2 / 2 | sensor-attack | literature (NAHS 2025, Secs. 3-5, Examples 3/5), the source's forward distance 0.3, tight; new 2026-10-30 (batch 11, from the pre-landing demo): the opt-in `prelanding = true` (right-only certificate only before the landing, `docs/PRELANDING.md`), letter R; the genuine Cool guard closed to `temp >= 100` (disclosed); took the slot of `fuelcell_chp_dos` (to `skipped/`) |
| `lit_nahs25_salt_tank` | 1 / 1 | 2 / 2 | sensor-attack | literature (NAHS 2025), the source's Def. 8 distance 0 by stutter (S at stretch 0, `stutter = true`, 2026-10-29; the lock-step distance 3 before); new 2026-10-27 (batch I8); a related published scenario of the running example, not its source |
| `sat3w_detumble_phases` | 6 / 6 | 2 / 3 | model-refinement | nonblocking region, mode choice; 2026-10-27: the design model with both phases (FINE added), exact energy rows in both phases (no longer mode-keyed); batch I9: the flight mode manager's 2 s period against the design model's 1 s (M I X) |
| `sat_detumble_phases` | 4 / 4 | 2 / 3 | model-refinement | nonblocking region, mode choice; 2026-10-27: the design model with both phases (FINE added), exact energy rows in both phases (no longer mode-keyed); batch I9: the flight mode manager's 2 s period against the design model's 1 s (M I X) |
| `sat_detumble_weak` | 4 / 4 | 1 / 4 | degraded-actuator | nonblocking region, mode choice; 2026-10-27: both sides at the design-model level (one cause: the weakened gain); batch I9: the exact re-timed claim at the derating ratio 4/5 and the power-saving 2 s period (S M B X) |
| `syringe_relay_prearm` | 4 / 4 | 6 / 4 | controller-change | new 2026-10-27 (batch I5): mode-keyed, right-only repositioning (the validated relay's take-up) |
| `tank_dos_3to1` | 2 / 2 | 4 / 4 | dos-attack | redesigned 2026-10-27: a demand-paced four-pump station, the same staging law on both sides, the DoS holds the staging decision for up to three polls |
| `train_ato_odometry` | 1 / 1 | 3 / 3 | degraded-sensor | new 2026-10-27: stretches per pairing from 31/40 to 6/5 (`lambda_min = 0.75`) |
| `tunnel_jetfan_pairout` | 3 / 3 | 2 / 2 | degraded-actuator | new 2026-10-27 (batch I6): mode-keyed (the CO row dropped in fire mode), load-bearing mode fact |
| `turbine_startup_gearratio` | 1 / 1 | 4 / 4 | degraded-controller | new 2026-10-27: widened cuts; right-only repositioning, pruned parking edges (the letters R P I come from the one-sided claim form, header); lambda pinned to 1 (batch I6); review round 6 (2026-10-30): uniform rows (window form) |
| `ventilator_vc_cuffleak` | 2 / 2 | 2 / 2 | degraded-actuator | new 2026-10-27 (batch I5): mode-keyed (a relative volume row in inspiration, an absolute band in expiration); review round 6 (2026-10-30): inspiratory countdown timer `s`, physical domain (`s >= 0`, `V >= -0.4`); widened cuts |
| `watertank` | 1 / 1 | 3 / 5 | sensor-attack | the paper's running example (the NAHS 2025 salt-tank case, `lit_nahs25_salt_tank`, is a related published scenario with the same attack magnitude and band of 3, not its source) |
| `watertank_twospeed` | 1 / 1 | 3 / 6 | sensor-attack | redesigned 2026-10-27: six right modes (two-speed low fill, eco/boost mid fill, high, pump off), one uniform claim; per-pairing stretch; the `Fast -> PumpOff` edge removed in review round 6 (2026-10-30; pruned before) |
| `lit_csf25_salt_tank_hold` | 2 / 2 | 2 / 2 | dos-attack | literature (CSF 2025, timed attacks), stretch 1/3, mode-keyed, load-bearing mode facts; new 2026-10-29 (literature migration), in place of `zone_lightmass_schedule`; widened cuts |

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
they enter no declared count. `lit_freedm_meter_leaky`: the deterministic controller `batI` of the
FREEDM case study on both sides of `lit_freedm_meter` (the battery whenever it can still charge or
discharge, the grid otherwise); a surplus at a full battery, or a demand at an empty one, goes to
the grid while a run from another level keeps it on the battery, so no matching run keeps the
meters equal. A DECLINE is
not a proof of insecurity (the certifier is sound, not complete); the source proves the leak by
exhibiting the two runs. `lit_csf21_vehicle_thermo_leaky` (batch I8): `lit_csf21_vehicle_thermo` with an
air-conditioning load on the drive on both sides (accelerating while cooling gives 0.8 m/s^2
instead of 1); the thermostat command now changes the velocity, so the attacker who sets the
temperature reading sets the acceleration profile. Its header exhibits the leak by hand (five
windows of AccHeat then three of AccCool need a genuine start temperature that does not exist),
which the source's lock-step equivalence also rules out. `lit_csf21_vehicle_bus_thermoprio`
(2026-10-29): `lit_csf21_vehicle_bus` with the bus arbitration reversed on both sides (a cycle whose
thermostat reading asks for the other setting sends the thermostat message, and the drive holds its
action for that cycle; the source gives acceleration messages priority); the temperature reading
now reaches the velocity through the bus. Its header exhibits the leak by hand (an attacked run that
no genuine message/setting sequence matches, checked exhaustively over four cycles). The check
`RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt` must print
`DECLINED` for all three files.

## Assumption 1 negative exhibit (`benchmarks/negative_wellformed/`)

`lit_hypercert_vehicle_s8`: `lit_hypercert_vehicle` (in `benchmarks/skipped/` since 2026-10-28; the
exhibit is self-contained) with the position bound `s ≤ 8` in every evolve
domain (a round-2 design variant). The certifier CERTIFIES it (the relational invariant does
not see the bound), but its right model can block: every right guard admits `s = 8` with
`v > 0`, where the flow leaves the domain at once, so no evolution spans the control interval
and Assumption 1's nonblocking clause is false. The check of the successor clause alone
reports all five right modes `ok`; the two-clause check (since 2026-10-26) reports all five
`BLOCKING (leaves s <= 8.0)`, and `RELCERT_WELLFORMED_STRICT=1` DECLINES the file. It enters no
declared count (`docs/WELLFORMED.md` §4).
