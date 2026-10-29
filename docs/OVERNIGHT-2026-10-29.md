# Overnight benchmark improvement, 2026-10-29 (branch `benchmark-fixes`)

Three rounds of review, verification, fix, regeneration, build, checks, commit and push, per the
overnight brief. Each round: five fresh reviewer agents (10 benchmarks each, rubric
`docs/review-rubric.md` only, no earlier scores or fix lists), every claim acted on verified by
tool runs on scratch variants (bisection, ablations, simulation) before any edit, fixes confirmed
CERTIFIED with the five ablation verdicts before and after, the full regeneration chain
(`gen_v2_data.py`, the pack rows of `VerdictsV2/RunV2.lean` derived from the emitted covers,
`gen_bridge.py`, `refute_finder.py` + `gen_refute.py`), one serial `lake build`, every check of
`docs/CERTIFICATION-CHECK.md` with the declared counts, `scripts/paper_numbers.sh`, one commit per
round, push.

Starting state: tip 544177e, suite 49 (`lit_hypercert_vehicle` skipped), letters S 20 M 25 R 7
B 12 P 6 D 12 I 18 X 14, bridge 4800, modal 1007, handoff 503, reposition 73, strict gate 179,
refutations 67.

## Round 1

Review (`docs/BENCHMARK-REVIEW-2026-10-29-r1.md`, 49 files): overall histogram 1: 0, 2: 5, 3: 25,
4: 19, 5: 0; verdicts KEEP 32, POLISH 12, RETHINK 5, DROP 0; 19/49 (39 %) at 4 or better.

Verification (four read-only agents, `tmp/verify-v1..v4/`): every RETHINK and POLISH claim
tested. Refuted reviewer fixes (not applied): charger `c = 0` / real-time claim (RELCERT_SYNC=1
declines at every c up to 90 on both CC laws), fuelcell thresholds 56/74 (declines at every
c <= 7), turbine two-sided claim at stretch 1.05 (declines), tunnel floor 2.5 with FIRE 0.9
(declines), rover_terrain_2to4 w-row (certifies but loses S and M: kept as a header sentence),
engine ABORT removal (loses D). Confirmed and applied: everything listed below.

Edits (letters before -> after, every one measured by the paper-numbers run):

| benchmark | action | letters before | letters after | tight numbers in the header |
|---|---|---|---|---|
| `insulin_basal_cgmloss` | refill from the reserve (reserve scoring 4/5, two independent scorers over 27 candidates); Assumption 1 proof of 8c92730 builds unchanged | (reserve) | M B | tolerance 25 mg/dL from the 70-180 target range, tightest 20 (reserve header) |
| `zone_lightmass_schedule` | MODEL: evolve domain 5..30 on both sides (the instrumented range; the comfort band was the set-point span), rows 0.5 K (EN 15500 control-accuracy class) | S M B X | S M B X | 0.49 certifies, 0.48 declines (inductive 0.4848); 0.152 derivation kept as the cause paragraph |
| `sat_detumble_weak` | MODEL: left DETUMBLE = gyrostat couplings at k 0.4 with h' = 2 w3; right unchanged | S M B X | S M B X | E_L(t) = E_R(0.8 t) exact; states differ (RK4); lambda 0.79 and 0.81 decline |
| `rover_terrain_2to4` | CONSTANT: lambda_max 3.0 -> 2.7 (derived ratio 2.68 rounded to the grid) | S M I | S M I | 2.64 certifies, 2.63 declines; GRAVEL cover 67/50, PAVED 27/10 |
| `h2_refuel_ambientbias` | CONSTANT: lambda_max 6.0 -> 1.0 (every cover at 1); header | R D I | R D I | 2.90 certifies, 2.899 declines, 2.4 declines |
| `charger_fast_tapers` | HEADER | S M R B P D I | S M R B P D I | 2.00 / 1.997; window [2.00, 5.00]; re-timed lead 0.00 simulated |
| `fuelcell_chp_dos` | HEADER | M B P X | M B P X | 5.00 / 4.996 (segment-end successor obligation); drifts +4.30 / -5.83 K |
| `engine_start_highidle` | HEADER (clock model deferred) | R D I | R D I | ABORT a start only; low rows exact by that start |
| `turbine_startup_gearratio` | HEADER (scaled-gain model deferred to round 2) | R P I | R P I | one-sided; two-sided fails at the SPINUP -> RAMP handoff |
| `tunnel_jetfan_pairout` | HEADER (floor-2.6 model deferred) | D I | D I | floor load-bearing at 2.54 via c <= 100; FIRE envelope 1.35 |
| `acc_spoof_lag` | HEADER | S M | S M | -3.33 / -3.34 re-timed; real-time form -3.95 / -3.96 with w = v + a/2 |
| `acc_spoof_limp` | HEADER | M B I | M B I | -0.20 / -0.21 with choice; 1.90 / 1.89 without |
| `platoon_linkloss` | HEADER | M D | M D | timing 0.6 s; AEB trigger period not load-bearing |
| `platoon_profiles` | HEADER | S M D | S M D | SPORT rows exact; real-time tolerance 4.00 / 3.99 |
| `quad_light_lag` | HEADER | S M | S M | K = 4.905 /s a loop gain; K = 4.0 at lambda 1.24525 |
| `quad_light_profiles` | HEADER | S M B X | S M B X | same; ECO/SPORT starts the cover leaves |
| `rover_terrain_6to12` | HEADER | I | I | 0.028 / 0.029 edge, sigma 0.25 binding |
| `sat_detumble_phases` | HEADER | M I X | M I X | isotropic damping required; gains / 1000 still certify |

Dropped: none. Suite 50.

Checks (all green): `lake build` exit 0; `--check-quick-v2` 50 certified, modal 1241/1241,
handoff 542/542, non-connection 64/64, pruned 32/32, reposition 73/73, strict gate 188/188 (87
invariant, 101 exit); bridge 5245/5245 (4800 + 445 for the insulin instance); progress 199/199;
refute 215/215 (71 instances: four new witnesses on the new sat_detumble_weak left); refute
instances build; WellFormedBattery 66 standard axiom lines; AxiomCheck 9; relcert-test ALL PASS
(50 literals); negatives DECLINED; s8 exhibit BLOCKING / DECLINED. Letters S 20 M 26 R 7 B 13
P 6 D 12 I 18 X 14 (only the insulin row changed). Commit 8bdd98e, pushed.

## Round 2

Review (`docs/BENCHMARK-REVIEW-2026-10-29-r2.md`, 50 files, new reviewer-to-benchmark pairing):
overall histogram 1: 0, 2: 4, 3: 29, 4: 17, 5: 0; verdicts KEEP 30, POLISH 13, RETHINK 7, DROP 0;
17/50 (34 %) at 4 or better. The round-2 reviewers were stricter than round 1's on files whose
text did not change (`acc_tune_lag` 4 -> 3, `acc_tune_limp` 4 -> 2, `rover_patrol_lag` 3 with
RETHINK, `lit_lz21_vehicle_position` 3 -> 2, `watertank` 3 with the running example's copy
witness named); the RETHINKs of round 1 that received verified fixes moved up
(`sat_detumble_weak` 2 -> 4, `rover_terrain_2to4` 2 -> 3, `turbine_startup_gearratio` 2 -> 3
on the header alone), and the two header-only RETHINKs stayed at 2 (`charger_fast_tapers`,
whose constant is the tool's and whose letters R P B D the suite cannot spare; `sat_detumble_phases`,
whose honest header names the stylized actuators).

Verification (three read-only agents, `tmp/verify-v5..v7/`) plus two Lean agents for the model
changes the round-1 headers had announced. Refuted reviewer claims (not acted on): the
`acc_tune_limp` LIMP ceiling "tuned to the claim" (certifies up to 37.50 by the SPORT -> NORMAL
hop); the `acc_spoof_limp` ceiling "load-bearing" (certifies up to 40); the `lit_lz21`
non-copy partner (the three-level input cannot stop a generic velocity, the right blocks at 10
under any policy); the `h2` "stage boundary forces exact rows" (exactness rests on the ABORT
start); a two-sided `rover_patrol_lag` band (declines in every form); the `zone` far-bound
sentence replaced by the measured formula. Charger and `sat_detumble_phases` (RETHINK at 2 in
both rounds) were left as documented: the charger's constant is the tool's and its letters
R P B D cannot be replaced from the reserve; the satellite's actuators are stylized and the
header says so.

Edits (letters before -> after measured by the paper-numbers run; none changed):

| benchmark | action | letters | tight numbers in the header |
|---|---|---|---|
| `turbine_startup_gearratio` | MODEL: gains / 1.05 (0.0380952, 0.047619), domains = reachable start-up speeds (12.705 / 12.1); proof: domain constant | R P I | factor 1.05 certifies, 1.047 / 1.049 decline; two-sided slack 6.85 |
| `tunnel_jetfan_pairout` | MODEL: floor 2.6, cap 900, FIRE rows u_L <= u_R <= u_L + 1.42, u_L >= 3, NORMAL 0.41; proof: domain pins | D I | 0.41 / 0.40, 1.42 / 1.41; floor load-bearing at 2.54 |
| `engine_start_highidle` | MODEL: time-out clock, reachable ABORT (nothing pruned); proof rewritten at Var 3 | R D I | +4.00 / 3.996; low rows exact 0.00 |
| `acc_tune_limp` | MODEL: LIMP guard 20..36, DISENGAGE -0.1 v; proof: gain 1/10 | S M B D I X | ceiling 37.50 / 37.51; LIMP lead 7.00 / 6.99 |
| `acc_spoof_limp` | MODEL: DISENGAGE -0.1 v; header; proof: per-mode gain | M B I | -0.20 / -0.21 with choice; 1.90 / 1.89 without; 34.50 no-choice ceiling |
| `acc_tune_lag` | MODEL: speed row 3.34 at pinned stretch 2; header on tau | S M | 3.34 / 3.33 |
| 12 header-only files | `h2_refuel_ambientbias`, `platoon_profiles`, `platoon_latency`, `fuelcell_chp_dos`, `quad_light_lag`, `quad_light_profiles`, `insulin_basal_cgmloss`, `rover_terrain_2to4`, `lit_lz21_vehicle_position`, `rover_patrol_lag`, `zone_lightmass_schedule` (scenario plant-change), `rover_terrain_4to6` | unchanged | see `benchmarks/README.md`, "Review round 2" |

Dropped: none. Suite 50.

Checks (all green): `lake build` exit 0; `--check-quick-v2` 50 certified, modal 1250/1250,
handoff 541/541, non-connection 60/60, pruned 30/30, reposition 73/73, strict gate 188/188 (87
invariant, 101 exit); bridge 5246/5246; progress 197/197; refute 219/219 (73 instances);
WellFormedBattery 66 lines; AxiomCheck 9; relcert-test ALL PASS; negatives DECLINED; s8 exhibit
BLOCKING / DECLINED. Letters S 20 M 26 R 7 B 13 P 6 D 12 I 18 X 14, per-benchmark identical to
round 1. Commit 4b5d052, pushed.

## Round 3

Review (`docs/BENCHMARK-REVIEW-2026-10-29-r3.md`, 50 files, hash-based reviewer pairing): overall
histogram 1: 0, 2: 4, 3: 29, 4: 17, 5: 0; verdicts KEEP 32, POLISH 12, RETHINK 6, DROP 0; 17/50
(34 %) at 4 or better. The round-2 model changes were received as intended where the reviewer
saw them (`engine_start_highidle` 3 -> 4 with ABORT reachable; `acc_spoof_limp` 3 -> 4;
`tunnel_jetfan_pairout` RETHINK -> POLISH), while the four files at 2 are the structural
objections this suite keeps on purpose and documents in the headers: `charger_fast_tapers` (the
constant is the tool's; letters R P B D), `lit_lz21_vehicle_position` (a literature row whose
source bound blocks the right model), `rover_terrain_2to4` (the stretched form is the chain's
exhibit; the real-time form is stated), `turbine_startup_gearratio` (one-sided against an
existential reference; the domain restriction is disclosed as load-bearing).

Verification and fixes (one agent, measure-then-edit, `tmp/fix-r3/`): `acc_spoof_limp` LIMP guard
20..36 (the sibling's ceiling; certifies up to 40, without the choice up to 34.50, so the file now
carries X by the ECO -> NORMAL hop; letters M B I -> M B I X; row 1 tight -2.40 / -2.41 at the new
ceiling, row 2 -0.20 / -0.21 unchanged); `acc_tune_limp` lambda_max 6.0 -> 1.5 (identical battery
and covers; letters S M B D I X); headers of `gantry_speed_zones` (verdict block re-measured),
`tunnel_jetfan_pairout` (floor 2.6 = normal-ventilation minimum duty), `sat3w_detumble_phases`
(stylized wheel gain, gains / 1000 variant certifies), `fuelcell_chp_dos` (one garbled sentence).
Not acted on (structural, documented in the headers): the four files at 2 listed above;
`acc_spoof_lag` (the real-time form loses S and M, stated in the header); `quad_light_profiles`
row 4 and `watertank_twospeed` lambda_max (exhibit files of `docs/SUITE-REDESIGN.md`).

Dropped: none. Suite 50.

Checks (all green): `lake build` exit 0; `--check-quick-v2` 50 certified, modal 1248/1248,
handoff 541/541, non-connection 60/60, pruned 30/30, reposition 73/73, strict gate 188/188 (87
invariant, 101 exit); bridge 5246/5246; progress 197/197; refute 219/219 (73 instances);
WellFormedBattery 66 lines; AxiomCheck 9; relcert-test ALL PASS; negatives DECLINED; s8 exhibit
BLOCKING / DECLINED. Letters S 20 M 26 R 7 B 13 P 6 D 12 I 18 X 15.

## Final suite (50), overall scores per round and letters

| benchmark | r1 | r2 | r3 overall | r3 verdict | letters |
|---|---|---|---|---|---|
| `acc_spoof_lag` | 3 | 3 | 3 | POLISH | S M |
| `acc_spoof_limp` | 3 | 3 | 4 | POLISH | M B I X |
| `acc_tune_lag` | 4 | 3 | 3 | KEEP | S M |
| `acc_tune_limp` | 4 | 2 | 3 | POLISH | S M B D I X |
| `bottling_fill_strainer` | 4 | 4 | 4 | KEEP | S I |
| `charger_fast_tapers` | 2 | 2 | 2 | RETHINK | S M R B P D I |
| `elevator_start_discbrake` | 3 | 3 | 3 | POLISH | R D |
| `engine_start_highidle` | 3 | 3 | 4 | KEEP | R D I |
| `flaps_slow_approach` | 4 | 4 | 4 | KEEP | S |
| `fuelcell_chp_dos` | 2 | 3 | 3 | POLISH | M B P X |
| `furnace_program_timebase` | 4 | 4 | 4 | KEEP | S I |
| `gantry_speed_zones` | 3 | 3 | 3 | POLISH | S M |
| `grid_ffr_dos` | 4 | 4 | 3 | KEEP | M P |
| `h2_refuel_ambientbias` | 3 | 3 | 3 | RETHINK | R D I |
| `hydro_rejection_gatecal` | 4 | 4 | 4 | KEEP | D |
| `insulin_basal_cgmloss` | - | 4 | 4 | KEEP | M B |
| `lit_csf21_vehicle_bus` | 3 | 3 | 3 | KEEP | X |
| `lit_csf21_vehicle_thermo` | 3 | 3 | 3 | KEEP | X |
| `lit_drl_car_stop` | 3 | 3 | 3 | KEEP | X |
| `lit_drl_lane_control` | 3 | 3 | 3 | KEEP | X |
| `lit_freedm_meter` | 3 | 3 | 3 | KEEP | X |
| `lit_girard08_robot` | 4 | 4 | 3 | KEEP | X |
| `lit_lz21_vehicle_position` | 3 | 2 | 2 | RETHINK | X |
| `lit_nahs25_salt_tank` | 4 | 4 | 4 | KEEP | I |
| `platoon_latency` | 4 | 4 | 4 | KEEP | D |
| `platoon_linkloss` | 3 | 4 | 4 | KEEP | M D |
| `platoon_profiles` | 3 | 3 | 3 | POLISH | S M D |
| `quad_light_lag` | 3 | 3 | 3 | RETHINK | S M |
| `quad_light_profiles` | 3 | 3 | 3 | POLISH | S M B X |
| `reactor_feed_wireless` | 4 | 4 | 3 | POLISH | M B P |
| `rover_ladder_2to3` | 4 | 3 | 3 | KEEP |  |
| `rover_ladder_3to6` | 3 | 3 | 4 | KEEP |  |
| `rover_ladder_6to8` | 4 | 3 | 4 | KEEP | S M I |
| `rover_ladder_8to12` | 4 | 4 | 4 | KEEP | S M I |
| `rover_patrol_lag` | 3 | 3 | 3 | KEEP | S M R B |
| `rover_terrain_2to4` | 2 | 3 | 2 | RETHINK | S M I |
| `rover_terrain_4to6` | 4 | 3 | 3 | KEEP | I |
| `rover_terrain_6to12` | 3 | 3 | 4 | KEEP | I |
| `sat3w_detumble_phases` | 3 | 4 | 4 | POLISH | M I X |
| `sat_detumble_phases` | 3 | 2 | 3 | KEEP | M I X |
| `sat_detumble_weak` | 2 | 4 | 3 | KEEP | S M B X |
| `syringe_relay_prearm` | 4 | 4 | 3 | KEEP | R D |
| `tank_dos_3to1` | 4 | 3 | 4 | KEEP | M I |
| `train_ato_odometry` | 4 | 4 | 3 | KEEP | S M B |
| `tunnel_jetfan_pairout` | 3 | 3 | 3 | POLISH | D I |
| `turbine_startup_gearratio` | 2 | 3 | 2 | RETHINK | R P I |
| `ventilator_vc_cuffleak` | 4 | 4 | 4 | KEEP | D |
| `watertank` | 3 | 3 | 3 | KEEP | S M B |
| `watertank_twospeed` | 3 | 3 | 3 | KEEP | S M B P |
| `zone_lightmass_schedule` | 3 | 3 | 3 | POLISH | S M B X |

Score histograms (overall): round 1 (49 files) 2: 5, 3: 25, 4: 19; round 2 (50) 2: 4, 3: 29,
4: 17; round 3 (50) 2: 4, 3: 29, 4: 17. The brief's targets (no overall below 3, 60 % at 4 or
better) were not reached: the independent reviewers' scores vary by one point between rounds on
unchanged files (nine files moved down a point from round 1 to round 2 with no edit), and the
four files held at 2 are objections to the form of their claims that the suite keeps on purpose
(documented in `benchmarks/README.md`, "Review round 3").

## Letter distribution, start vs end

Start (544177e): S 20, M 25, R 7, B 12, P 6, D 12, I 18, X 14 (49 files). End (2a3c506): S 20,
M 26, R 7, B 13, P 6, D 12, I 18, X 15 (50 files): M and B from `insulin_basal_cgmloss`, X from
`acc_spoof_limp`; no letter lost on any benchmark (per-benchmark letters identical to the start
run for every other file, checked against `docs/paper-numbers/letters.md` after each round).

## Checks that failed, and how they were resolved

* Bridge declared count: `relcert-bridge-verdicts` reported `discharged 5245 but owes 4800`
  (round 1, the insulin instance) and `5246 but owes 5245` (round 2, the model changes); each
  time the measured total was set in `VerdictsV2/RunBridge.lean` and the executable rebuilt, as
  the brief prescribes (every group `unsat`, no FAIL line).
* `gen_refute.py` reported one stale instance after the engine model change
  (`engine_start_highidle_m003`, a mutant of the previous model); removed with `git rm` as the
  script asked, replaced by `_m008` on the new model.
* No check was red at any commit; nothing was reverted. The pack rows of `VerdictsV2/RunV2.lean`
  were re-derived from the emitted covers by a script validated against the committed table
  (32 of 36 benchmarks reproduced exactly; the differences are extra replay nodes the hand-written
  table listed), and every re-derived row discharged `unsat`.

## Commits (branch `benchmark-fixes`, all pushed)

* 8bdd98e round 1: insulin refilled, four model changes, thirteen header fixes.
* 4b5d052 round 2: six model changes (three Assumption 1 proofs rewritten, two adapted), twelve
  header fixes.
* 2a3c506 round 3: two constant changes, four header fixes.
* this document.

## Domain audit 2026-10-29

Rule (owner): an evolve domain states a physical constraint of the plant (a hardware limit, a
sensor range, a saturation, a trip); it must not be a closed-loop target, set point, asymptote or
reachable-set cap chosen so that the claim certifies. Scan (tip b1827f4, `relcert` with
`RELCERT_IMPLIED_CUT=1`; every two-sided evolve bound widened by 20 % of its range (W20), by 10x
(NODOM), by 5 % on the W20 decliners (W5), then one bound at a time on the W20 decliners): base
50/50 CERTIFIED; W20 41 C / 9 D; NODOM 36 C / 14 D (the five NODOM-only decliners stand on creep
floors widened below 0 or on boxes widened 10x; not acted on). The nine W20 decliners: class (a),
a physical limit load-bearing (`acc_tune_lag`, `rover_ladder_3to6`, `rover_ladder_6to8`,
`rover_ladder_8to12`); class (b), a closed-loop band (`flaps_slow_approach`, `platoon_latency`,
`quad_light_profiles`, `tunnel_jetfan_pairout`, `turbine_startup_gearratio`). Besides these,
`engine_start_highidle`'s round-2 domain (`5 <= N2`, `t <= 40`) was reverted to the physical one
(it was not load-bearing).

| benchmark | old bound | new bound | verdict at the new bound | action | letters before / after | tight numbers |
|---|---|---|---|---|---|---|
| `flaps_slow_approach` | `V` in [150, 185] kt (autothrust target F, selection speed S) | `V` in [130, 200] kt (VLS CONF 2 = 1.23 VS1G; flap placard VFE CONF 2) | DECLINED with the old rows (every EXT segment fails: above 190 kt the gap grows past 20, below F the slow aircraft is the faster one) | rows `V_R <= V_L + 25`, `V_L <= V_R + 10` installed, CERTIFIED; W20 now CERTIFIES; Assumption 1 proof adapted | S / S | 25.00 (24.99 declines) = (VFE - F)/2; 10.00 (9.99 declines) = (F - VLS)/2; with the placard at 190: 20.00 (19.99 declines); cause dependence 0.75 deg/s 12.50, 0.6 deg/s 20.00, 1 deg/s exact |
| `platoon_latency` | `e` in [-0.5, 0.5] m/s^2 (J tau, the jerk-reachable band) | `e` in [-20, 20] m/s^2 (two accelerations within the 1 g tyre-road limit) | DECLINED with the old rows (`abs(Delta g) <= 4` needs `abs(e) <= 0.5`) | row `abs(e_L) <= 0.5` added to the CACC rows, CERTIFIED; W20 CERTIFIES | D / D | e row 0.50 (0.49 declines); `abs(Delta g)` 4.00 (3.99 declines), unchanged |
| `quad_light_profiles` | `w <= 2.4` m/s (SPORT set point, both sides) | `w <= 3` m/s (PX4 MPC_Z_VEL_MAX_UP climb-rate limiter) | DECLINED with the old rows (row 4 `1.2 w_R <= w_L` is not inductive above `w_R = 2`) | row `w_L <= 2.4` added, CERTIFIED (SYNC, NO_CHOICE decline as before); W20 CERTIFIES; Assumption 1 proof adapted | S M B X / S M B X | 2.40 (2.39 declines); rows 1 to 4 unchanged |
| `turbine_startup_gearratio` | `w <= 12.705` (left) / `12.1` (right) rpm (rated targets) | `w <= 13.9755` / `13.31` rpm (overspeed trips, 110 % of rated; the deployed's read 5 % low) | DECLINED with the exact row (GEN x GEN from above rated: the deployed regulates more slowly); unary rows `w_R <= 12.1`, `w_L <= 12.705` DECLINED too (they block the right-only reposition) | GEN row `w_L <= 1.05 w_R + 0.061`, exact elsewhere, CERTIFIED; uniform rows decline (D); W20 DECLINES (the trip is physical and load-bearing, stated); Assumption 1 proof adapted | R P I / R P I D | 0.061 (0.060 declines) = the overspeed-recovery lag at the trip; factor 1.05 exact as before |
| `tunnel_jetfan_pairout` | `u >= 2.6` m/s (controller's minimum duty) | `u >= 0` | DECLINED (NORMAL_L: both segments fail; the reference's NORMAL mode is not well formed at low airflow, the CO mode fact is lost) | no claim-side fix (`benchmarks/skipped/tunnel_jetfan_pairout/SKIPPED.md`); SKIPPED, refilled by `antenna_track_kvretune` | D I / (out) | - |
| `antenna_track_kvretune` | (reserve) | `t >= 0`; `c`, `x` in [-2, 92] deg (limit switches) | CERTIFIED; W20 CERTIFIES; every counter-run CERTIFIES | refilled (best-scored reserve candidate with physical domains: round-1 reserve score P 4 R 4 C 5), Assumption 1 proof of fb55b6e restored unchanged | (in) / D | 0.0125 (TRACK), 0.085 (STOW), as its header |
| `engine_start_highidle` | `5 <= N2 <= 110`, `0 <= t <= 40` | `0 <= N2 <= 110`, `t >= 0` | CERTIFIED (same counter-run pattern) | domain reverted, header fixed, Assumption 1 proof adapted | R D I / R D I | 4.00 unchanged |
| `acc_tune_lag` | `a` in [-10, 10] (1 g), `v` in [0, 40] | unchanged | W5 DECLINES; `a.hi`, `a.lo` alone at 20 % DECLINE | header: physical and load-bearing (was "not load-bearing") | S M / S M | unchanged |
| `rover_ladder_3to6` | `z <= 0.15` m (suspension travel) | unchanged | W5 CERTIFIES; `z.hi` alone at 20 % DECLINES | header: physical and load-bearing | - / - | unchanged |
| `rover_ladder_6to8` | `z <= 0.15` m | unchanged | W5 CERTIFIES; `z.hi` alone at 20 % DECLINES | header: physical and load-bearing | S M I / S M I | unchanged |
| `rover_ladder_8to12` | `z <= 0.15` m, `v <= 8` m/s (governor) | unchanged | W5 CERTIFIES; `z.hi`, `v.hi` alone at 20 % DECLINE | header: physical and load-bearing | S M I / S M I | unchanged |

Reserve widening test (the same W20 on the 26 reserve files): every file CERTIFIES except
`lng_cooldown_overspray` and `quad_light_airframe_20` (noted in `benchmarks/reserve/README.md`).
Ablations re-measured for every edited benchmark (SYNC, NO_CHOICE, SYNC+NO_CHOICE, NO_PRUNE,
NO_PRUNE+NO_CHOICE, NO_REPO, NO_CUT, NO_IMPLIED_CUT, NO_LINEAR_CUT, without IMPLIED_CUT, OPREGION,
NO_PAIR_STRETCH, STRICT) and written into the headers: flaps SYNC and SYNC+NO_CHOICE decline (S);
platoon every run certifies (D from the uniform-row runs); quad SYNC, NO_CHOICE, NO_PRUNE+NO_CHOICE,
SYNC+NO_CHOICE decline (S, X); turbine SYNC, NO_PRUNE, NO_PRUNE+NO_CHOICE, SYNC+NO_CHOICE, NO_REPO,
NO_CUT, NO_IMPLIED_CUT and without IMPLIED_CUT decline (R P I; D from the uniform rows); engine SYNC,
NO_REPO, NO_CUT, NO_IMPLIED_CUT and without IMPLIED_CUT decline (R I; D from the uniform rows);
antenna every run certifies (D from the uniform rows).

Checks (all green; `lake build` exit 0, 9293 jobs, the five executables 18172): `--check-quick-v2` 50 certified, modal 1264/1264, handoff 544/544, non-connection 60/60, pruned 30/30, reposition 74/74, strict gate 189/189 (87 invariant, 102 exit), 0 UNKNOWN, 0 BLOCKING; `relcert-test` ALL PASS (50 literals); bridge 5283/5283 (declared count set after measuring, was 5246: the tunnel's 38 groups out, the antenna's in, the five re-emitted instances); progress 197/197; refute 260/260 (87 instances, was 73: two tunnel out, 13 antenna and three platoon in) and every refutation instance builds; WellFormedBattery 66 standard axiom lines (plus the 11 `CutLiftX` replay lines); AxiomCheck 9; both negatives DECLINED; `lit_hypercert_vehicle_s8` BLOCKING / DECLINED; `scripts/paper_numbers.sh` re-run (covers identical, letters S 20 M 26 R 7 B 13 P 6 D 13 I 17 X 15; per-benchmark letters identical to the previous run for every file but the three listed).

Letters: start (b1827f4) S 20 M 26 R 7 B 13 P 6 D 12 I 18 X 15; end S 20 M 26 R 7 B 13 P 6 D 13 I 17 X 15 (`tunnel_jetfan_pairout` D I out; `antenna_track_kvretune` D and the turbine's new D in; no other benchmark's letters changed).

Failed checks and how they were resolved: (1) the first `lake build` failed in `Bridge/TurbineStartupGearratio.lean` (`rowsSame IR = true` decided false: the turbine now has a per-mode row), fixed by adding it to `KEYED` in `scripts/gen_bridge.py` and re-emitting; (2) the second build failed in the same file (`3 ≠ 0`: the mode-keyed form needs four auxiliary coordinates, so the Assumption 1 lemma must be at dimension 3), fixed by lifting `WellFormed/TurbineStartupGearratio.lean` from `Var 2` to `Var 3` (two padding coordinates, their fields lower to 0) and re-emitting its pack rows and bridge at dimension 3 / 4 (the finder re-run on it, still no witness); (3) `relcert-bridge-verdicts` reported `discharged 5283 but owes 5246`, the measured total set in `VerdictsV2/RunBridge.lean` and the runner rebuilt; (4) `paper_numbers.sh` run once under `bash` instead of `zsh` wrote no run tables and its letters step failed on the stale table (`KeyError: tunnel_jetfan_pairout`); re-run under `zsh`, green. Nothing reverted.

Commits (branch `benchmark-fixes`, pushed): 6e1819f the audit (benchmarks, proofs, generated layers, counts, paper numbers); this section in the commit after it.

## One domain per benchmark 2026-10-29

Rule (owner): each benchmark has ONE physical evolve domain, the same text on every mode and on
both sides (left and right). A domain states physical constraints only (hardware limits, sensor
range, saturation, trips), never set points, asymptotes or reachable-set bands. Exception, kind
(iii): the two sides state the same physical limit in different coordinates; then the header
states the conversion in a `# Domain conversion (kind iii):` line and `scripts/check_one_domain.py`
admits the file. At tip e3d4e1e thirteen files had more than one distinct `evolve` line. Every
change was made on a scratch copy and run with `RELCERT_IMPLIED_CUT=1`; every edited file
CERTIFIED with its rows unchanged, so no claim-side fix was needed and nothing was dropped (suite 50).

| benchmark | old domains | new domain (both sides, every mode) | kind | verdict | claim change | letters before / after | tight numbers |
|---|---|---|---|---|---|---|---|
| `platoon_latency` | L `0 <= g <= 60`, `\|r\| <= 10`, `\|e\| <= 20`; R `g`, `r` only (no `e`) | the same box; the right declares `e`, frozen (`e' = 0`, inert) | (i) | CERTIFIED | none | D / D | unchanged: `\|Delta g\|` 4.00 (3.99 D), `e` row 0.50 (0.49 D), Q rows (0.99, 1.99 D), `g_L >= 5` 5.00, TTC 16 |
| `quad_light_lag` | L `0 <= w <= 2.4`, `0 <= a <= 14.715`; R `0 <= w <= 2.0`, `0 <= a <= 9.81` (terminal climb rates and thrust commands: set points) | `h >= 0` (ground), `0 <= w <= 3` (PX4 climb-rate limiter), `0 <= a <= 14.715` (1.5 g; `= 3 K`, which keeps the reference's `w <= 3`); guard = evolve | (iii) rejected: set points, one limit | CERTIFIED | none | S M / S M | row 1 0.38 (=); row 2 0.40 -> 0.51 (0.50 D); Psi upper 0.56 -> 0.45 (0.46 D); Psi lower 0.58 (=); rows 1, 2 from hover 0.25 -> 0.36 (0.35 D) |
| `rover_ladder_2to3` | R `psi` in [0, 0] | validity box (`psi` in [-0.6, 0.6], `v` in [0, 8], `s >= 0`); right `psi` frozen | (i) | CERTIFIED | none | - / - | unchanged |
| `rover_ladder_3to6` | R `theta_p`, `z`, `phi_r` in [0, 0] | validity box (`z` in [-0.15, 0.15] suspension travel, ...) | (i) | CERTIFIED | none | - / - | pitch 0.23 (0.22 D), unchanged |
| `rover_ladder_6to8` | R `omega_psi`, `omega_theta` in [0, 0] | validity box | (i) | CERTIFIED | none | S M I / S M I | pitch 0.23, roll 0.14, LTR 0.22, unchanged |
| `rover_ladder_8to12` | R `omega_z`, `omega_phi`, `y`, `omega_y` in [0, 0] | validity box | (i) | CERTIFIED | none | S M I / S M I | roll 0.15, LTR 0.35, lane 0.20, unchanged |
| `rover_patrol_lag` | L `v` in [0, 1.6], `s >= 0`, `\|a\| <= 2`, `0 <= a + 4 v <= 6.4` (lag envelope: reachable set); R `v`, `s` | `v` in [0, 1.6] (top speed), `s >= 0`, `\|a\| <= 2` (0.2 g traction); the right declares `a`, frozen | (i) + (ii) | CERTIFIED (the band is not needed) | none | S M R B / S M R B | lead row 0.59 -> 0.75 (0.74 D; the box admits braking at every speed); row (2) offset up to 0.79 -> 0.62 |
| `rover_terrain_2to4` | L `w >= 0.15` (the wheel controller's creep floor: policy); R `w >= 0` | `v`, `w` in [0, 0.8], `s >= 0`, `zs` in [0, 0.12] | (ii) | CERTIFIED | none | S M I / S M I | sigma 0.21 (0.20 D), lambda_max 2.64, unchanged |
| `sat_detumble_phases` | L `\|w_i\| <= 1`, `\|h\| <= 2`; R the same plus `\|h + 5 w3\| <= 2` | `\|w_i\| <= 1` (gyro range) | (ii), not a first integral | CERTIFIED | none | M I X / M I X | exact claim (no tolerance) |
| `sat_detumble_weak` | as above | `\|w_i\| <= 1` | (ii), not a first integral | CERTIFIED | none | S M B X / S M B X | lambda 0.8 pinned (0.79, 0.81 D), unchanged |
| `sat3w_detumble_phases` | L `\|w_i\|`, `\|h_i\|` box; R plus `\|h1 + 2 w1\|`, `\|h2 + 4 w2\|`, `\|h3 + 5 w3\| <= 2` | `\|w_i\| <= 1` | (ii), not a first integral | CERTIFIED (22 s, was 3 s) | none | M I X / M I X | exact claim |
| `train_ato_odometry` | L `v <= 28.21`, R `v <= 27.08` (true speed) | unchanged: one ATP intervention setting, 27.08 m/s on the speed reading; 28.21 = 27.08 / 0.96 | (iii), conversion stated | CERTIFIED | none | S M B / S M B | 1.07 (1.06 D), unchanged |
| `turbine_startup_gearratio` | L `w <= 13.9755`, R `w <= 13.31` (true speed) | unchanged: one overspeed trip, 13.31 rpm on the reading; 13.9755 = 1.05 x 13.31 | (iii), conversion stated | CERTIFIED | none | R P D I / R P D I | 0.061 (0.060 D), unchanged |

The satellites' bands, first-integral test (both phases; the gain `k` cancels): on the right
(design model, `w' = -k w`, `h' = J k w`) `h_i + J_i w_i` is constant in every mode, so the band is
a first integral there. On the left (the gyrostat) it is not: `sat_detumble_phases` and
`sat_detumble_weak` have `d/dt (h + 5 w3) = -2 w1 w2`; `sat3w_detumble_phases` has
`d/dt (h1 + 2 w1) = -w2 w3 + w3 h2 - w2 h3`, `d/dt (h2 + 4 w2) = 3 w1 w3 + w1 h3 - w3 h1`,
`d/dt (h3 + 5 w3) = -2 w1 w2 + w2 h1 - w1 h2`. So all three bands left the domain. The wheel box
`|h| <= 2` had to go with them: kept alone, the design model's own flow (`h' = 5 k w3`) crosses it,
and `relcert --wellformed` reports DETUMBLE and FINE (resp. NOMINAL, ECONOMY, SURVIVAL) BLOCKING
(leaves `h >= -2.0`), i.e. Assumption 1 fails (the refutation `docs/WELLFORMED.md` records for
before 2026-10-15). The claim (energy equality; `E' = -2 k E` on both sides whatever `h` is) needs
neither, so no row or cut was added. The wheel capacity and the momentum dump are now stated as
coverage gaps of the models. The kind (iii) files: either single true-speed box (27.08 or 28.21;
13.31 or 13.9755 on both sides) also CERTIFIES; the stated per-reading form keeps each model up to
its own trip.

Ablations (SYNC, NO_CHOICE, SYNC+NO_CHOICE, NO_PRUNE, NO_PRUNE+NO_CHOICE, NO_REPO, NO_CUT,
NO_IMPLIED_CUT, NO_LINEAR_CUT, without IMPLIED_CUT, OPREGION, NO_PAIR_STRETCH, STRICT) re-measured
on the eleven changed files: identical to the originals in every switch. W20 widening scan on the
thirteen final files: 9 CERTIFY; 4 DECLINE, as before, each on a physical, load-bearing bound
(`rover_ladder_{3to6,6to8,8to12}`: `z <= 0.15` suspension travel, 8to12 also `v <= 8`;
`turbine_startup_gearratio`: the trip). Headers: Domains paragraph rewritten (one domain, each
bound's physical source), a `One domain (2026-10-29)` line, verdict paragraphs re-dated. Assumption 1
(`RelCertifier/InstancesV2/WellFormed/*.lean`): ten proofs adapted (the domain lemmas; the
satellites' explicit runs now stay in the gyro box because each rate decays, `h` free; the
`_band_invariant` theorems kept as model facts of the design model; platoon's runs transported from
the `(g, r)` box, `sol_domR`); `RoverTerrain2to4` needed no change (its right domain was already
`w >= 0`). Docs: `docs/WELLFORMED.md`, `README.md`, `benchmarks/README.md`,
`docs/REFUTATION-RESULTS.md`, `docs/CERTIFICATION-CHECK.md`, the battery's docstrings.

Regeneration: `gen_v2_data.py` on the eleven (covers, progress and choice leaves unchanged; IR
leaves and `Cuts/quad_light_lag` changed), declared counts recomputed (unchanged), `gen_bridge.py`
(instances unchanged), `refute_finder.py --only` the eleven (fresh) + `gen_refute.py`.

Checks (all green; one serial `lake build`, exit 0): `--check-quick-v2` 50 certified, modal
1264/1264, handoff 544/544, non-connection 60/60, pruned 30/30, reposition 74/74, strict gate
189/189 (87 invariant, 102 exit), 0 UNKNOWN, 0 BLOCKING; `check_one_domain.py` `ONE DOMAIN: PASS
(50 benchmarks: 48 with one evolve domain, 2 kind (iii) with a stated conversion)`; `relcert-test`
ALL PASS (50 literals); bridge 5284/5284 (declared count set after measuring, was 5283);
progress 197/197; refute 261/261 (87 instances) and every refutation instance builds;
WellFormedBattery 66 standard axiom lines (plus the 11 `CutLiftX` replay lines); AxiomCheck 9; both
negatives DECLINED; `lit_hypercert_vehicle_s8` BLOCKING / DECLINED; `scripts/paper_numbers.sh`
under `zsh` (covers identical; total time 109 -> 126 s, the sat3w file).

Letters: start S 20 M 26 R 7 B 13 P 6 D 13 I 17 X 15; end the same, and identical per benchmark
(`docs/paper-numbers/letters.md` compared with the previous commit's).

Failed checks and how they were resolved: (1) after the domain change ten Assumption 1 proofs
failed to build (the domain characterization lemmas), adapted as above before the full build;
(2) `relcert-bridge-verdicts` reported `discharged 5284 but owes 5283` (no FAIL line: the left of
`quad_light_lag` gains the checked cut `w <= 3`, one more DI group), the measured total set in
`VerdictsV2/RunBridge.lean` and the runner rebuilt; (3) `gen_refute.py` reported the stale
`quad_light_lag_m023` (no witness on the new box), removed with `git rm`. Nothing reverted, nothing
left unchanged except the two kind (iii) models (headers only).

Commits (branch `benchmark-fixes`, pushed): 50ab23f the batch (benchmarks, proofs, generated layers,
counts, check script, paper numbers); this section in the commit after it.

## Fix round 4 (2026-10-29)

The verified items of review round 4 (`docs/BENCHMARK-REVIEW-2026-10-29-r4.md`, "Verified actionable
items"), acted on at tip 46c3fb3. Every change was made on a scratch copy and run with
`RELCERT_IMPLIED_CUT=1` before installation; letters were measured on the scratch copies with the
paper's own pipeline (the five counter-run configurations, `suite_v2_matrix.py`,
`suite_v2_letters.py`) before and after, every edited file re-run under the thirteen ablation
switches and the 20 % widening (W20), and every stated tight value bisected (0.01 tighter
declines). Owner's rules kept: one physical evolve domain per benchmark (`check_one_domain.py`
PASS), start-only modes carry no letter, a weaker claim certifying is not a finding.

| benchmark | finding (r4, verified) | action | letters before / after | tight numbers |
|---|---|---|---|---|
| `engine_start_highidle` | ABORT reached only from starts with the timer near 30 s; D and the exact start rows rested on it | physical trigger: start-air supply pressure `p` (frozen, the same bleed source on both sides, transducer range 0..60 psig); on low supply (`p < 35`) the starter's torque limit is reached at 25.5 % (`STARTER_LOW`), so a start from rest (N2 = 5 %, t = 0) is at 24.48 % at the 30 s time-out and aborts (a hung start); ABORT row tightened to exact; right model changed (new coordinate and mode), Assumption 1 proof adapted | R D I / R D I | start rows lead 0 (0.01 declines), timer slack 0 (0.01 declines), ABORT 0.00 (-0.01 declines), SELF/IDLE 4.00 (3.99 declines); uniform +4 declines (D genuine) |
| `platoon_latency` | AEB reachable only as a start; D only from AEB pairs; header time 2.0 s | no physical trigger keeps an AEB pairing sound under deployed-keyed rows (a lead-braking mode on both sides DECLINES: the design's braking mode shares the CACC guard; the two AEBs fire at different instants); AEB removed on both sides, the design floor row and the AEB row dropped; header time re-measured | D / none | `abs(Delta g)` 4.00, Q rows 1 / 2, `g_L >= 5` 5.00, TTC 16.00, `abs(e_L)` 0.50 (each 0.01 tighter declines); 0.5 s (was stated 2.0 s; the pre-fix file ran 1.16 s) |
| `platoon_linkloss` | same start-only AEB pattern (checked: the operating range is forward invariant under CACC and ACC) | AEB removed on both sides | M D / M | `Delta g` in [0, 15], Q forms [0, 3.75], [0, 7.5], `g_L >= 5`, TTC 20.00 |
| `platoon_profiles` | same start-only AEB; SPORT rows an exact gain-scaling identity (any slack certifies) | AEB removed; SPORT kd 0.9 -> 0.85 (critical damping; lambda 6/5 is now the natural-frequency ratio), so the exact rows DECLINE and a tolerance is bisected | S M D / S M | `abs(Delta g)` 3.34 = W / kp (W = 0.06 x the rated 10 m/s closing rate), modal forms 1.50 and 1.14, TTC 19.44 (19.45 declines); W20 now DECLINES (the tolerance scales with the rated closing rate, stated) |
| `h2_refuel_ambientbias` | start-only ABORT; header "letters R I" contradicted the D rule | no trigger reachable in the one-state model (all stage flows raise p; a time-out aborts every fill or none; temperature or ramp aborts need a second state); ABORT removed, STAGE1 guard from p = 0; header letter statements fixed | R D I / R D I | top rows 2.90 (2.89 declines); uniform `p_L <= p_R` declines (D) |
| `charger_fast_tapers` | P rested on FAULT edges no run takes | no trip reachable with SoC as the only state; FAULT removed on both sides, PRECHARGE from x = 0; c tightened; header P attribution removed | S M R B P D I / S M R B D I | c 1.00 (0.99 declines; the physical lead is 0, c = 1 is the FULL-pairing over-approximation, stated) |
| `grid_ffr_dos` | band certifies with an FFR that never fires | no attack-dependent claim under a sampled hold (segment certificates are time-free, so the hold segment is the dead-FFR flow); a rate-limited-fallback variant depends on the attack but has no letter; SKIPPED (`benchmarks/skipped/grid_ffr_dos/SKIPPED.md`) | M P / (out) | - |
| `canal_gate_notches` | refill | from the reserve (round-1 reserve score 4, letter X, bank-crest domain, W20 CERTIFIES); Assumption 1 proof restored from history. `molding_pack_checkring` (score 4, D) rejected: its 500 bar domain is the hold set point (DECLINES at the 2000 bar machine limit) | (in) / X | 0.10 (0.09 declines) against the stated 0.15 m operator tolerance |
| `rover_ladder_2to3` | heading row not load-bearing (certifies at 100) | heading row removed; a relational lag row (`s_R <= s_L + c`, `v_R <= v_L + d`) DECLINES for every c, d tried | none / none | clearance offset 0 (unchanged) |
| `bottling_fill_strainer` | row 5 implied by rows 1-3 | row removed; the shortfall bound 1.2 mL derived in the header from rows (1)-(3) | S I / S I | offset 1.20 exact (1.19 and 1.21 decline) |
| `rover_terrain_6to12` | three output-only rows; header `abs(v') <= 5.6` | body-pitch row and its ax, omega_phs auxiliaries removed (the squat chain is output-only); wheel floor 0.15 -> 0.13 (soil-and-slope validity, `mu_MUD w >= Z_max + g gamma`); header 6.4 | I / I | sigma 0.24 (0.23 declines), H 0.13 (0.12 declines) |
| `reactor_feed_wireless` | 9 K band justified only by limits the left meets alone | band 9 -> 8 K (tight), requirement restated relationally (reaction rate within a factor 2^(8/10) of the validated run's, van 't Hoff) | M B P / M B P | 8.00 (7.99 declines) |
| `quad_light_lag` | Psi constant 0.16 from removed envelopes; tight 0.45 | Psi band set to 0.45, the widest start relation for which the 0.8 m requirement holds | S M / S M | Psi 0.45 (0.46 declines); row 2 0.80 (0.79 declines); row 1 0.67 (0.66 declines) |
| `hydro_rejection_gatecal` | speed band 0.09 not tight; margin from a full-gate start is 0.073 | speed row 0.07 (the overspeed margin from the worst on-grid start, simulated peak 1.227 pu) | D / D | speed 0.027 with gate 0.027 (0.026 declines); gate window [0.02, 0.07] at speed 0.07; cause sweep re-measured (0.03, 0.05) |
| `watertank` | lambda_max 6 unjustified | lambda range [1, 2] | S M B / S M B | lambda_max 2 (1.95, 1.9 decline) |
| `watertank_twospeed` | lower row 2 vacuous | lower row 1.5 (the deployed's largest lag, 17 - 15.5) | S M B P / S M B P | 1.50 (1.49 declines) |
| `rover_terrain_2to4` | real-time form certifies at lambda 1 | kept the re-timed form (it alone gives S M); header states why: the plan re-initialized from the rover's ground speed while the wheels slip ahead; wheel floor 0 -> 0.05 (soil validity, shared with 4to6) | S M I / S M I | sigma 0.21 (0.20 declines), lambda_max 2.64 (2.63 declines) |
| `rover_terrain_4to6` | creep floor 0.15 (policy); composition with 2to4 broken | floor -> 0.05, the soil model's validity bound (`mu_MUD w >= Z_max`); floor 0 makes the right fail Assumption 1 (relcert --wellformed: MUD, GRAVEL, PAVED BLOCKING, the stalled rover leaves v >= 0); composition with 2to4 restored | I / I | sigma 0.21 (0.20 declines), H 0.13 (0.12 declines) |
| `acc_tune_lag` | l.72 "well inside" false | header: the guard's corners reach abs(a) = 28.75, the box clips it, load-bearing | S M / S M | - |
| `syringe_relay_prearm` | 100 min | 90 min | R D / R D | - |
| `sat_detumble_weak` | RK4 example started outside the guard (E = 1.06) | example from w = (0.4, 0.3, 0.2) (E = 0.88), numbers recomputed | S M B X / S M B X | - |
| `ventilator_vc_cuffleak` | 0.105 at 500 | 0.104 (0.103 declines) | D / D | - |
| `lit_lz21_vehicle_position` | (rejected item, checked) | none: smaller offsets (0, 0.5) certify, but delta = 1 is the source's secret / non-secret separation, already disclosed | X / X | - |

Drops and refills: `grid_ffr_dos` skipped, `canal_gate_notches` promoted (suite 50). Letters: start
(46c3fb3) S 20 M 26 R 7 B 13 P 6 D 13 I 17 X 15; end S 20 M 25 R 7 B 13 P 4 D 10 I 17 X 16 (charger
P, grid M P, the three platoon D out; canal X in; every other benchmark's letters identical,
`docs/paper-numbers/letters.md` compared with the previous commit's).

Paper numbers (`scripts/paper_numbers.sh` under zsh; covers identical): `numletterM` 26 -> 25,
`numletterP` 6 -> 4, `numletterD` 13 -> 10, `numletterX` 15 -> 16, `nummechM` 26 -> 25, `nummechP` 6 -> 4,
`nummechD` 13 -> 10, `numnochoice` 35 -> 34, `numnoprunedecl` 6 -> 4, `numnoprunenochoicedecl` 23 -> 20,
`numsyncnochoice` 14 -> 13, `numnoprune` 44 -> 46, `numnoprunenochoice` 27 -> 30, `numopregionout`
9 -> 11, total time 126 -> 123 s.

Assumption 1 (`RelCertifier/InstancesV2/WellFormed/`): ten proofs adapted (`EngineStartHighidle`: the
supply coordinate and `STARTER_LOW`; `H2RefuelAmbientbias`, `ChargerFastTapers`: the removed mode and
the widened first guard; `PlatoonLatency`, `PlatoonLinkloss`, `PlatoonProfiles`: the one-mode CACC
right model; `RoverTerrain2to4`, `4to6`, `6to12`: the wheel floors), `CanalGateNotches` restored
unchanged from history, `GridFfrDos` removed; all Z3-free, axioms propext, Classical.choice,
Quot.sound.

Regeneration: `gen_v2_data.py` on the seventeen changed files and the refill; pack rows of
`VerdictsV2/RunV2.lean` re-derived from the emitted covers (grid's removed); `gen_bridge.py`;
`refute_finder.py --only` the eighteen + `gen_refute.py` (70 stale instance and data files removed as
listed; grid's 21 no-witness records dropped with the benchmark).

Checks (all green; one serial `lake build`, exit 0): `--check-quick-v2` 50 certified, modal
1218/1218, handoff 537/537, non-connection 42/42, pruned 21/21, reposition 74/74, strict gate
186/186 (82 invariant, 104 exit), 0 UNKNOWN, 0 BLOCKING; `check_one_domain.py` PASS (48 + 2 kind
(iii)); `relcert-test` ALL PASS (50 literals); bridge 5180/5180 (declared count set after measuring,
was 5284); progress 194/194; refute 204/204 (74 instances, was 87) and every refutation instance
builds; WellFormedBattery 66 standard axiom lines (plus the 11 `CutLiftX` replay lines); AxiomCheck 9;
both negatives DECLINED; `lit_hypercert_vehicle_s8` BLOCKING / DECLINED.

Failed checks and how they were resolved: (1) the first `refute_finder.py` run crashed
(`JSONDecodeError` in its `lake env lean` dump) while the Lean proofs were being rebuilt in
parallel; re-run after the proofs built, green; (2) `relcert-bridge-verdicts` reported `discharged
5180 but owes 5284` (no FAIL line), the measured total set in `VerdictsV2/RunBridge.lean` and the
runner rebuilt; (3) the operating-region run listed admitted starts outside every right guard for the
three platoon files (their design floor rows were dropped) and for `engine_start_highidle` ABORT_L;
those headers claimed none, now corrected (such pairs have no right run and are not cases of the
claim). Nothing reverted. Deviation from the fix list: `rover_terrain_4to6`'s creep floor could not go
to 0 (the right model then fails Assumption 1, the stalled rover leaving v >= 0); it went to the soil
model's validity bound 0.05, which also restores the composition with `rover_terrain_2to4`.

Commits (branch `benchmark-fixes`, pushed): see the git log after 46c3fb3 (the fix commit, then this
section).

## Literature fidelity round (2026-10-29)

Goal (owner): the eight literature benchmarks must be faithful migrations of their sources. Standard
per file: (a) model as printed, departures only where the framework forces them, each with its
reason; (b) the claim carries the source's content (its theorem/property, its quantitative bound if
any, with the tight value); (c) non-trivial: the witness is not a plain copy unless the source's claim
is a copy-refinement, and removing the source's cause changes the verdict or the tight value (run);
(d) letters reported, never added for their own sake. Framework constraints kept as decided:
Assumption 1, sampled switching on both sides, one physical evolve domain. One research agent per
benchmark (or pair), read-only on scratch copies (`tmp/lit-r6/`), each reading the source PDF
section, then installed serially. No benchmark dropped.

| benchmark | source | fidelity (a/b/c) before -> after | changes | departures (forced) | letters before / after | tight numbers | cause test |
|---|---|---|---|---|---|---|---|
| `lit_lz21_vehicle_position` | Liu, Zamani, L-CSS 2021 (arXiv 2109.10993), Def. 2, assumption (2), Sec. V-A Eq. (17) | OK/FAIL/WEAK -> OK/OK/OK | rows: the exact offset `x_R = x_L + 1` replaced by Definition 2 at delta = 1: `x_R >= 1` (closure of the non-secret start `x_R > 1`; strictness follows since x is nondecreasing on `v >= 0`), `|x_L - x_R| <= 1`, `v_L = v_R`; header rewritten (source policy measured, coverage, boundary) | (1) no upper position bound (with `x <= 10` all three right modes BLOCKING); (2) input-copying partner: the source's printed policy is never in U on R0 and no admissible input makes its B non-increasing on about 29 % of X x X x U (published certificate invalid under its own input bound), the feedback cannot be stated (velocity-gap rows DECLINE); (3) three input levels (11 levels on the 0.01 grid also CERTIFY, strict, 5.7 s; not adopted); (4) secret start x_L = 0 uncovered at delta = 1 (the source's own boundary) | X / X | tool verdict independent of delta (0, 0.99, 1 all CERTIFY); coverage (z3): uncovered secret starts exactly [0, 1 - delta]; tight delta = 1 on (0, 1], the source's value | non-secret row removed: delta = 0 certifies and covers, tight delta 1 -> 0; velocity matching removed: DECLINED; NO_CHOICE: DECLINED |
| `lit_drl_car_stop` | Loos, Platzer, LICS 2016, Sec. 6 (Goals 1-3, time* <= event*) | WEAK/FAIL/FAIL -> unchanged, now disclosed | header only: Goals 1-3 mapped; why Goal 3 (Safe_eps keeps E for eps time, a bounded-time fact) is not expressible (joint-segment certificates are clock-free differential invariants, no resets); measured unsafety of the sampled Coast stand-in and of the permissive right | Coast stand-in (Assumption 1); sampled event side | X / X | 0 (guard inclusion); the source's Goal 3 margin 2v + 1 is invisible to the tool | Safe_eps margin removed: still CERTIFIED; Rsys = Lsys: CERTIFIED; only a negative margin (-0.01) DECLINES. Finer right period (eps/2, eps/4): DECLINED; event domain E as a claim conjunct: DECLINED (CERTIFIED with a Brake-only left = Goal 2 alone) |
| `lit_drl_lane_control` | Loos, Platzer, LICS 2016, Sec. 6 (lane control, after FM 2011) | WEAK/FAIL/FAIL -> unchanged, now disclosed | header only, as car_stop; the r5 collision claim confirmed (Coast stand-in: gap -0.5 after 8 cycles from (3.5, 1, 0)); the audit's 9-mode leader decline traced to a broken variant (incomplete `next` lists): with complete lists it CERTIFIES (6.7 s, wellformed 9/9) | as car_stop | X / X | 0 (guard inclusion) | as car_stop (margin removed: CERTIFIED; E conjunct: DECLINED; eps/2: DECLINED) |
| `lit_csf21_vehicle_thermo` | Xiang, Fulton, Chong, CSF 2021, Sec. VI-C, Def. 5 | OK/OK/WEAK -> OK/OK/OK | header only: measured cause test, why the d, v copy is the source's Def. 5 content (the thermostat setting is not copied), tightness | Coast at v <= 1, Brk from v >= 1 (Assumption 1); top speed; closed guards at temp = 20 | X / X | equality (tolerance 0) | the drive reads the thermostat (AC load on AccCool, `negative/lit_csf21_vehicle_thermo_leaky`): DECLINED; its hand run fails the source's H-equivalence for every genuine start |
| `lit_csf21_vehicle_bus` | same, Sec. VI-C(a)-(b), Figs. 11-12 | OK/OK/FAIL -> OK/OK/WEAK | header rewritten: quotes the source's arbitration (acceleration messages have priority: `ctrlbus = (?busV = a; ctrlt; busH := 1) U busH := 0`), so the bus is harmless by design and the genuine car never needs a thermostat message; the certificate is thermo's (disclosed); new negative exhibit `benchmarks/negative/lit_csf21_vehicle_bus_thermoprio` (arbitration reversed, DECLINED) | as thermo | X / X | equality | xtT right modes removed / one-message rule removed / genuine thermostat guard removed: all CERTIFIED (bus not load-bearing, as in the source); arbitration reversed with override modes: DECLINED, wellformed 16/16, leak confirmed by an exhaustive hand check (0 of 3^4 x 2^4 genuine sequences match) |
| `lit_freedm_meter` | Bohrer, Platzer, LICS 2018, Sec. 3 Fig. 2, Def. 5, Prop. 11 | WEAK/OK/OK -> OK/OK/OK | model: the zero-net battery modes BatD0R0, BatD1R1 no longer enabled at B = Bmax (`B < 10`, the source's batS test `B < Bmax or (n > 0 and B > 0)`; the old `B <= 10` was a convenience); header: departures (1)-(6) each with its reason, L = {gr, t}, Prop. 11's argument | meter E for gr (no assignments); one transformer; finite inputs; period-1 sampling (the source is not time-triggered); charge/discharge guards B <= 9, B >= n (Assumption 1); domain B <= 10 (the source's range) | X / X | equality (the source states no bound) | one grid mode gated on the secret like batI (GridD2R0 only at B < 2) on both sides: DECLINED; right only: DECLINED; full batI (`negative/lit_freedm_meter_leaky`): DECLINED |
| `lit_girard08_robot` | Girard, Julius, Pappas, DEDS 18 (2008), Sec. 5, Eqs. (6)-(8), Figs. 2-3, Theorem 2, Sec. 4.2.3 | OK/OK/WEAK -> OK/OK/OK | header only: Theorem 2 and beta = 0.4 cited, the Fig. 2 5 -> 6 guard reading, Fig. 3's 0.8-wide strips, unverifiable thesis pointer dropped, TIGHTNESS and CAUSE TEST | error coordinates (exact change of variables); planner more permissive than Fig. 3 (rows keyed by the left mode; the Fig. 3 edges DECLINE); sampled location changes (one evolve domain per side) | X / X | level 0.16 = precision 0.4 exactly (0.159999 declines) | gain 0 or damping removed: DECLINED at 0.16, 1, 100; gain 0.26 with the source V: DECLINED; gain 0.26 with V re-weighted 25: CERTIFIED at 0.16 (precision 2 v comes from the controller structure) |
| `lit_nahs25_salt_tank` | Xiang, Lanotte, Tini, Chong, Merro, NAHS 56 (2025), Sec. 7, Fig. 7, Def. 8 | OK/OK/WEAK -> OK/OK/OK | header only: Def. 8 direction (attacked forall, genuine exists), lock step disclosed, non-strict closure, TIGHTNESS and CAUSE TEST | attack projected exactly (On at xp >= 22, Off at xp < 28); closure of 25 < xp; lock step (stronger than Def. 8's reachable sets, the source's own proof) | I / I | upper row exactly 3.00 (2.99 declines) = the source's d = 3 | attack bound b = 4, 2, 1, 0.01: tight value = b each time; threshold 25 -> 26: tight 4.00 |

Fidelity scale per axis: OK / WEAK / FAIL. Six of eight files reach OK on (a), (b) and (c);
`lit_csf21_vehicle_bus` stays WEAK on (c) (the source's bus is harmless by design, see below); the two
dRL files stay WEAK/FAIL/FAIL, now disclosed. Letters unchanged for all eight (`docs/paper-numbers/letters.md`
compared with the previous commit's: only run times moved; `\totaltimes` 123 -> 124, `\numunderonesec`
28 -> 29). Mechanism letters were not a goal: no structure was added.

Assumption 1 (`RelCertifier/InstancesV2/WellFormed/`): no proof changed. `LitFreedmMeter.lean` builds
unchanged against the new guards (its `sat_guardR_bounds` closes `B < 10 -> B + 0 <= 10` by `linarith`);
`LitLz21VehiclePosition.lean` is untouched (right model unchanged); the six other right models are
byte-identical.

Not adopted (measured, recorded in the headers): the strict row `x_R > 1` in `lit_lz21_vehicle_position`
(CERTIFIED as stated, 0.4 s, but the suite's bridge generator states closed rows; the closure loses
nothing since x is nondecreasing); 11 input levels for lz21 (CERTIFIED, strict, 5.7 s; it narrows
departure (3) at the cost of an 11-mode Assumption 1 proof); the 9-mode three-valued leader for
`lit_drl_lane_control` (CERTIFIED 6.7 s once the variant's `next` lists are complete; it changes the
right model, so its Assumption 1 proof would be redone); a Safe_eps guard on the left Coast of the dRL
files (CERTIFIED, but the left then sticks at low speed).

### Recommendations for the files not made faithful

* `lit_drl_car_stop`, `lit_drl_lane_control`: KEEP WITH DISCLOSURE for now, as "dRL Goal 1 (Safe_eps
  implies Safe) between sampled controllers", not "time-triggered refines event-triggered". The source's
  theorem rests on Goal 3 (Safe_eps keeps the event domain for eps time), a bounded-time fact; the tool's
  joint-segment certificates are clock-free differential invariants and the format has no resets, so no
  faithful reading certifies (finer right period, E as a claim conjunct, nondeterministic envelope: all
  DECLINED or reduce to the same guard inclusion). Every published dRL-line refinement example (LICS 2016
  Sec. 6, Prebet-Platzer 2024 Example 1, Prebet-Platzer 2026 Sec. 4.3, Mitsch-Quesel-Platzer FM 2014
  Sec. 6) uses the same car-stop template with a copy witness, so a replacement must come from another
  line. If one row has to go, replace `lit_drl_car_stop` (it repeats the lane file's structure with a less
  specified source) with candidate 1 or 2 below.
* `lit_csf21_vehicle_bus`: KEEP WITH DISCLOSURE (the header now says its certificate is the thermo
  file's and why: the source's acceleration-message priority makes the bus harmless; the reversed
  arbitration is the new negative exhibit). Do not count it as an independent mechanism exhibit. If every
  literature row must carry distinct load-bearing content, replace it with: (i) NAHS 2025 (arXiv
  2403.05829) Secs. 3-5, the engine cooling system of Figs. 3-5, Examples 3 and 5 (bounded sensor attack,
  forward simulation distance 0.3 on the temperature: a tight value to test); (ii) CSF 2021 Sec. VI-A, the
  ABS of Fig. 9 with three wheel-speed sensors and majority voting (cause test: remove the voting;
  nonlinear slip, harder); (iii) CSF 2021 Sec. III-C(a), Fig. 5, the car with three voting velocity
  sensors (simple, same family as thermo).

### Candidate new literature benchmarks (to replace weak designed ones later)

1. Boost DC-DC converter: Girard, Pola, Tabuada, "Approximately bisimilar symbolic models for
   incrementally stable switched systems", IEEE TAC 55(1) 2010 (arXiv 0807.5022), Sec. 5.1, Fig. 2. Two
   affine modes (xc = 70, xl = 3, rc = 0.005, rl = 0.05, r0 = 1, vs = 1), switching at sample instants
   tau_s = 0.5 (the framework's own semantics). Claim: incremental stability under the printed common
   Lyapunov function (x - y)^T M (x - y), M = [[1.0224, 0.0084], [0.0084, 1.0031]] in [il, 5 vc],
   kappa = 0.014 (reproduced numerically, tight on mode 2): two copies from different states contract,
   witness not a copy. Departures: the symbolic (grid-snapped) model cannot be the right side (a discrete
   reset); the certified relation is the incremental-stability relation under the paper's bisimulation.
   Cause test: Euclidean distance in physical coordinates is not a Lyapunov function. Feasibility HIGH.
2. n-room building: Girard, Goessler, Mouelhi, "Safety controller synthesis for incrementally stable
   switched systems using multiscale symbolic models", IEEE TAC 61(6) 2016, Sec. V-B, Table II. Linear,
   n + 1 heater modes (alpha = 1/20, beta = 1/200, gamma = 1/100, te = 10, th = 50), precision 0.4,
   period 5; box rows |T_L,i - T_R,i| <= c invariant under a shared mode, domain [10, 50]^n (physical);
   scales n = 3..5. Same departures as 1. Feasibility HIGH.
3. Engine cooling under a bounded sensor attack: Xiang, Lanotte, Tini, Chong, Merro, NAHS 2025 (arXiv
   2403.05829), Secs. 3-5, Figs. 3-5, Examples 3 and 5: forward simulation distance 0.3 on temperature
   between attacked and genuine system (the same robustness content as the salt tank, a different plant
   and a stated bound). Departures as `lit_nahs25_salt_tank` (lock step, closure). Feasibility HIGH (not
   yet scoped by a tool run).
4. Approximate bisimulation of a 3-D polynomial system by a 2-D linear one: Girard, Pappas, "Approximate bisimulations for nonlinear dynamical systems",
   CDC-ECC 2005, Sec. V, precision 0.590. Strongly non-trivial witness (lower-dimensional linear model). Warning:
   random sampling finds a positive Lie derivative of the printed V inside V <= 0.348 (e.g. 0.56); confirm
   with Z3 first: if the certificate is wrong, the example is a known-false exhibit, not a benchmark.
   Feasibility MEDIUM-LOW.
5. CSF 2021 Sec. VI-A ABS with three wheel-speed sensors and majority voting (Xiang, Fulton, Chong):
   non-interference of a single compromised sensor with braking; cause test: remove the voting.
   Nonlinear slip dynamics. Feasibility MEDIUM-LOW.

Rejected (reason): Anand et al. 2105.05493 room temperature (a discrete-time map; one mode; the
right side is the same deterministic system); dwell-time switched systems (GPT10 Sec. 5.2, GGM16 Sec. V-C:
a minimum dwell time cannot be stated with windows of at most eps); Lanotte et al. CSF 2017 engine
(discrete time, counters, resets); Kalat ECC 2022 (the lz21 vehicle, already noted in its header);
Skorokhod and conformance work (distances measured by testing, no proved bound); ACAS X refactoring
(relates formulas, not systems).

### Regeneration, checks, commits

Regeneration: `gen_v2_data.py` on the eight (leaves changed only for `lit_freedm_meter`: IR, cuts;
`lit_lz21_vehicle_position`: IR, cover); the pack rows of `VerdictsV2/RunV2.lean` unchanged (the literature
files close by choice and have no packs; declared counts recomputed, unchanged); `gen_bridge.py` (instances
unchanged); `refute_finder.py --only` the eight (929 records, was 926: lz21 19 mutants, was 16; witnesses
74, unchanged; the one literature witness, `lit_girard08_robot` m016, re-found) + `gen_refute.py` (its
mutant file re-written with the new header).

Checks (all green; one serial `lake build`, exit 0): `--check-quick-v2` 50 certified, modal 1218/1218,
handoff 537/537, non-connection 42/42, pruned 21/21, reposition 74/74, strict gate 186/186 (82 invariant,
104 exit), 0 UNKNOWN, 0 BLOCKING; `check_one_domain.py` PASS (48 + 2 kind (iii)); `relcert --wellformed`
186 modes ok; `relcert-test` ALL PASS (50 literals); bridge 5183/5183 (declared count set after measuring,
was 5180: lz21 35 -> 38); progress 194/194; refute 204/204 (74 instances) and every refutation instance
builds; WellFormedBattery 66 standard axiom lines (plus the 11 `CutLiftX` replay lines); AxiomCheck 9;
the three negatives DECLINED (`lit_csf21_vehicle_bus_thermoprio` new); `lit_hypercert_vehicle_s8`
BLOCKING / DECLINED; `scripts/paper_numbers.sh` under zsh (covers identical; letters identical per
benchmark).

Failed checks and how they were resolved: (1) `relcert-bridge-verdicts` reported `discharged 5183 but
owes 5180` (no FAIL line; the three extra groups are lz21's longer row), the measured total set in
`VerdictsV2/RunBridge.lean`, the runner rebuilt and re-run: 5183/5183. Nothing reverted.

Commits (branch `benchmark-fixes`, pushed): the literature fidelity commit, then this section.

## Literature migration + audit (2026-10-29)

Goal (owner): replace weak designed and literature rows with faithful migrations of published examples, under
the fidelity standard of the previous section ((a) model as printed, departures only where forced and listed;
(b) the source's claim and bound, tight value measured; (c) non-trivial: no copy witness unless the source's
claim is a copy, removing the source's cause changes the verdict or the tight value; (d) letters reported).
Framework rules kept: Assumption 1 as is, sampled switching, one physical evolve domain, suite exactly 50.

### Phase A: candidates, installs, swap, removals

| benchmark | source | status | fidelity a/b/c (after audit) | tight vs source | cause test | letters |
|---|---|---|---|---|---|---|
| `lit_gpt10_boost_converter` | Girard, Pola, Tabuada, IEEE TAC 55(1) 2010, Sec. 5.1, Sec. 4.1, Thm. 4.1, Def. 3.2 | INSTALLED (replaces `lit_drl_car_stop`) | OK / OK / OK (first draft WEAK/WEAK/OK, fixed in Phase A: see audit) | eps 2.58 certifies, 2.57 declines (computed 2.5783) vs the source's eps = 2.6 at eta = 1/(40 sqrt 2) (its sufficient bound 145 eta = 2.563) | eta halved: 1.29 / 1.28 (linear in eta); no drift: exact rows; Euclidean norm in the source's physical coordinates: DECLINED; M = I: DECLINED at 2.6; NO_CHOICE: DECLINED | X |
| `lit_csf25_salt_tank_hold` | Xiang et al., IEEE CSF 2025, Sec. VII, Fig. 8, Figs. 9-12, Props. 4, 6, 7, Def. 8 (owner-approved addition, design V2) | INSTALLED (replaces `zone_lightmass_schedule`) | WEAK / WEAK / OK (audit: the held decision is keyed on the fresh level, not the source's stale reading; disclosed) | Inc slope 1.31 (1.30 declines), the mechanism of the paper's 1.3 at another start; Dec 0.25 (0.24 declines) | hold 1 / 2 / 3 / 4 min: Inc slope 0 / 0.99 / 1.31 / 1.48 (= 0.03 x 65.5 x (1 - 1/H)) | S D I |
| `rampmeter_poll_2to1` | reserve (RESERVE-R6 reframe): HCM 6th ed. Exhibit 12-15 level-of-service bands | SWAPPED IN (replaces `insulin_basal_cgmloss`) | designed file | requirement 8 veh/mi/ln, tightest 7.00 (6.99 declines) | poll 20 s: exact; 40 s: 7; 50-60 s: 9; 80 s: 11 (8 holds up to 40 s) | M B (unchanged from the reserve) |
| n-room building | Girard, Goessler, Mouelhi, IEEE TAC 61(6) 2016, Sec. V-B, Table II | NOT INSTALLED | - | - | - | - |
| engine cooling | Xiang et al., NAHS 56 (2025), Secs. 3-5, Examples 3, 5 | NOT INSTALLED | - | - | - | - |
| 3-D polynomial vs 2-D linear | Girard, Pappas, CDC-ECC 2005, Sec. V | NOT INSTALLED (fallback tried) | - | - | - | - |
| three voting velocity sensors | Xiang, Fulton, Chong, CSF 2021, Sec. III-C(a), Fig. 5 | NOT INSTALLED (fallback considered) | - | - | - | - |

Why the three requested files that are not installed could not be made faithful and certifying:

* **n-room building (GGM16 Sec. V-B).** The source's precision is the approximate bisimulation of Theorem 4 between
  the building and its multiscale quantized model at eta = 0.28, tau = 80, N = 4, eps = 0.4, with a common
  delta-GUAS Lyapunov function that is not printed. Encoded like the boost file (left = the building pushed by the
  quantizer's error, per room +-eta/(sqrt n tau) per window, the 2^n corners times n + 1 heater modes; right = the
  building copying the heater by choice; rows: one Euclidean quadratic row on the room differences): n = 3 has 32
  left modes and exceeds the tool's 300 s budget (ERROR at 305 s; an 8-mode subset alone takes 168 s); box rows
  (|T_L,i - T_R,i| <= c, linear) DECLINE even for the copy without perturbation (the coupled rooms make each row
  depend on the others, which the linear-row route does not combine); a constant-disturbance variant (disturbance
  as left state) did not finish in 600 s. The copy form (incremental stability of two runs, 0.3 s) certifies for
  every c, so it fails (c). Measured on the way: with the Euclidean V the stand-in's tight precision is 0.70 for every
  n, and the source's pair (eta = 0.28, eps = 0.4) does not satisfy its own condition (14) for that V (kappa = beta =
  1/200 is the best rate any common Lyapunov function can have, the all-off mode's uniform direction decays at beta;
  (14) at s = 0 then needs eta <= 0.132).
* **Engine cooling (NAHS 2025, Examples 3 and 5).** The source's forward distance 0.3 (Def. 8) compares reachable
  SETS (attacked (99.2, 101.3] against genuine (99.5, 101], Example 7); a run-wise forall-exists relation is false:
  in lock step, from the source's pre temp = 100 the attacked controller may cool (a reading 100.3 > 100) while the
  genuine one must heat, a gap of 1.5 after one period, and any band <= 0.3 would need temp_L <= 99.7 whenever
  temp_R <= 100 and temp_L > 100.3 whenever temp_R > 100, impossible as temp_R crosses 100. With a stretch range
  ([0.5, 2], [0.1, 10], [0, 1], [1, 10]) every pairing of the two-sided band fails (DECLINED); right-only
  repositioning, which a set distance would allow, is not admitted for two-sided rows (SUITE-REDESIGN finding 5).
* **Fallbacks.** Girard-Pappas 2005 (OVERNIGHT candidate 4): the printed bisimulation function is not one: its Lie
  derivative is positive inside its own sublevel set V <= 0.348 (0.589 at (x1, x2, x3, e2, e3) = (0.846, -7.64, -3.80,
  -0.088, -0.480), random search), and relcert returns ERROR (Z3 inconclusive) on the faithful file; a known-false
  certificate, not a benchmark. CSF 2021 three-sensor voting car (OVERNIGHT candidate 5's neighbour): after
  projecting the attack through the vote the attacked model is byte-identical to the genuine one (a copy, the
  source's claim), the third CSF 2021 file and a near-duplicate of `lit_csf21_vehicle_thermo`; not installed. The
  owner then approved `lit_csf25_salt_tank_hold` as the second new literature file.

Removals (to `benchmarks/skipped/<b>/` with SKIPPED.md): `lit_drl_car_stop` (X; the dRL Goal-1-only copy, kept
`lit_drl_lane_control`); `insulin_basal_cgmloss` (M B; the reserve swap); `zone_lightmass_schedule` (S M B X; r5
overall 2, structural objection: the 0.5 K row certifies only by the 5..30 degC domain). Selection of the designed
file: no P, D or R carrier removed; of the two r5-scored-2 candidates without P/D/R and with a structural objection
(`acc_spoof_limp` M B I X, `zone_lightmass_schedule` S M B X), zone loses the most plentiful S instead of I. Only one
designed file was removed: two of the three requested literature files could not be installed, and the owner-approved
CSF 2025 file took the third slot.

Letter arithmetic: out `lit_drl_car_stop` (X), `insulin_basal_cgmloss` (M B), `zone_lightmass_schedule` (S M B X); in `lit_gpt10_boost_converter` (X), `rampmeter_poll_2to1` (M B), `lit_csf25_salt_tank_hold` (S D I): net M -1, B -1, X -1, D +1, I +1. Totals (`docs/paper-numbers/letters.md`) S 20 M 25 R 7 B 13 P 4 D 10 I 17 X 16 -> S 20 M 24 R 7 B 12 P 4 D 11 I 18 X 15 (strict D 6 -> 7). No P or R carrier removed; the scarce D gains one. Literature count 8 -> 9 (41 designed + 9).

Lean: Assumption 1 proofs `InstancesV2/WellFormed/LitGpt10BoostConverter.lean` and `LitCsf25SaltTankHold.lean`
(direct over the bridge's automaton, the three standard axioms, no sorry), both on a new generic lemma
`Proofs/Flow/LipschitzRun.lean` (`exists_odeSol_of_lipschitz`: a globally Lipschitz field has runs of every length,
one uniform Picard step of length 1/(K + 1) chained by `chainN`; `lipschitz_rightBlock` for the right block);
`RampmeterPoll2to1.lean` restored from 95033f6^ (builds unchanged). Generated: leaves (`gen_v2_data.py`), bridge
instances (`gen_bridge.py`, `lit_csf25_salt_tank_hold` keyed), pack rows for the two non-choice files (29 + 2, derived
from the emitted covers), refutation records (`refute_finder.py --only` the three: 53 mutants, no witness; the 48
records of the removed files dropped; `gen_refute.py`: 74 instances unchanged).

Checks (all green; library and the five executables built serially, no sorry): `--check-quick-v2` 50 certified,
modal 1160/1160, handoff 2827/2827 (537 before: the boost's 48 all-to-all abstraction modes add 2256 vacuous
transitions), non-connection 44/44, pruned 22/22, reposition 74/74, strict gate 181/181 (80 invariant, 101 exit);
`relcert-test` ALL PASS; bridge 7433/7433 (5183 before; the boost alone 2450); progress 194/194; refute 204/204
(74 instances); WellFormedBattery 66 lines at the three standard axioms (plus the 11 `CutLiftX` replay lines),
AxiomCheck 9; negatives DECLINED (3); `lit_hypercert_vehicle_s8` BLOCKING / DECLINED under strict; one domain PASS
(48 + 2 kind (iii)). Failed checks and their resolution: the first `--check-quick-v2` and bridge runs reported the
declared counts (modal 1218, handoff 537, non-connection 42, pruned 21, wellformed 186, bridge 5183) against the
measured ones; the declared counts in `VerdictsV2/RunV2.lean` and `RunBridge.lean` were set after measuring and the
runners rebuilt; every query had come back unsat. Nothing reverted.

Paper numbers (`scripts/paper_numbers.sh docs/paper-numbers` under zsh): covers identical across the two emissions; `numbers.tex` changes: `\numlit` 8 -> 9; letters M 25 -> 24, B 13 -> 12, D 10 -> 11, I 17 -> 18, X 16 -> 15 (`\nummechM/B/D/c/cplus` likewise: 25/13/10/17/6 -> 24/12/11/18/7); `\numnochoice` (certified without choice) 34 -> 35; `\numnoprunenochoice` 30 -> 31, `\numnoprunenochoicedecl` 20 -> 19; `\numnocut` 33 -> 32; `\numguardonly` 44 -> 43; `\totaltimes` 124 -> 181 s, `\numunderonesec` 29 -> 26, `\slowesttime` 31 -> 50 s (the slowest benchmark is now `lit_gpt10_boost_converter`, 50 s, the 48-mode abstraction; was `rover_ladder_8to12`). Run time on this machine (Apple, Z3 4.15.x): 45 min 46 s for the whole script.

### Phase B: independent audit of the nine literature files

Four fresh auditors (no migration notes; the sources, the files and the standard only), scratch copies under
`tmp/lit-audit-r7/slice{A,B,C,D}/`, a frozen relcert binary. Every header measurement they re-ran reproduced,
except the girard08 departure (1) claim (below).

| file | a | b | c | discrepancies (source location) | fixed / open |
|---|---|---|---|---|---|
| `lit_gpt10_boost_converter` | WEAK -> OK | WEAK -> OK | OK | B1 (SUBSTANTIVE, Sec. 4.1): the four-corner drift of the first draft, integrated through e^(A s), misses up to 2 % of the lattice cell, so the left did not contain the abstraction; B2: departure (1) not forced, a polygon covering the source's eta-ball certifies; B3 (header): "the same label p" is the choice witness, not certified | fixed in Phase A (new install): 24-gon covering the eta-ball, re-measured (2.58 / 2.57, eta halved 1.29 / 1.28, cause tests); B3 disclosed |
| `lit_girard08_robot` | WEAK | OK | OK (the copy of w is forced by beta = 0.4) | R1: departure (1)'s "physical coordinates: ERROR at 40 s" not reproduced, the physical-coordinate file CERTIFIES in 53 s (level 0.1599 and NO_CHOICE DECLINE), so the error coordinates are not forced; R2: the physical reading (planner, obstacle) is ours, labelled | header corrected; switching the model to physical coordinates OPEN (substantive) |
| `lit_nahs25_salt_tank` | OK | OK | OK | 3 is the lock-step supremum; Def. 8's reachable-set value from xp = 50 is 0 (both reach (25, 50]); Fig. 7 omits the reset t := 0; lambda pinned is not forced (tight 3 also for lambda ranges) | header fixed (wording, reset disclosed) |
| `lit_csf21_vehicle_thermo` | OK | OK | OK | the negative exhibit `lit_csf21_vehicle_thermo_leaky` still had the pre-2026-10-28 Coast guards (v >= 0); Def. 5 is lock-step in iterations, not durations; leaky time 0.9 s -> 0.4 s | fixed (exhibit guards v <= 1, still DECLINED; header wording) |
| `lit_csf21_vehicle_bus` | OK | OK | OK (caveat: the positive certificate is the thermo file's; the bus content is in the negative exhibit, disclosed) | thermoprio time 1.5 s -> 0.9 s; the left cannot change its thermostat on a Brk -> Coast cycle (weakens the claim, not load-bearing) | time fixed; the minor point OPEN |
| `lit_drl_lane_control` | WEAK | WEAK | WEAK | A = B = eps = 1 is our instantiation (the source is symbolic); the "two UNKNOWN, none blocking" note should say neither is shown nonblocking; the two-level leader, the closed strict guards and the top speed are conveniences, not forced; the source's 2 v_f + 1 margin is not load-bearing (tight margin 0, -0.001 DECLINES) | header fixed; the WEAK axes OPEN (disclosed: Goal 3 not expressible) |
| `lit_freedm_meter` | OK | OK | OK | l. 46-47 misstated the source's batS test; the claim (E equal at every instant) is a trace statement, stronger than Def. 5's final states; the battery guards are forced on the right only (the literal source tests on the left CERTIFY); domain B <= 10 not forced (disclosed) | header fixed; literal left guards OPEN (option) |
| `lit_lz21_vehicle_position` | WEAK | OK | WEAK | l. 63: the printed policy ranges exactly over [1.45, 3.85] on R0 (header [1.47, 3.82]); the left can be confined to the source's x <= 10 by guards (CERTIFIED); 11 input levels certify; the tool verdict is independent of delta (delta acts through coverage, outside the tool) | constant fixed; the two closer models OPEN (options) |
| `lit_csf25_salt_tank_hold` | WEAK | WEAK | OK | SUBSTANTIVE (paper.tex ~4060-4075, Fig. 10 mid_a): the held decision is keyed on the fresh level at S, while the source's DoS keeps the stale pre-attack reading, whose worst case the paper proves; a stale/free-decision variant CERTIFIES with Inc slope about 2.06 (6.2 lb at the end of the hold, the paper's 6) only without the psi_b envelope rows; "rounded down" gloss wrong (the paper's 1.295 <= 1.3 is sound at xp_L >= 35; 1.31 is at 34.5); Cors. 1-2 are in Sec. V-B; 3.93 vs 6 not comparable | header fixed (departure (3) now a disclosure); the stale-reading model OPEN (substantive) |
