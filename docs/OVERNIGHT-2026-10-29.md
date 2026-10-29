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
