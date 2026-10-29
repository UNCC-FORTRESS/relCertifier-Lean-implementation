# Benchmark review, round 3 (2026-10-29; suite_v2 at 4b5d052, 50 benchmarks)

Five fresh reviewer agents, 10 benchmarks each, rubric `docs/review-rubric.md` only; the reviewers did not see earlier reviews, scores or fix lists. Findings are reviewer claims; every claim acted on was verified by a tool run first (the round's fix log is in `docs/OVERNIGHT-2026-10-29.md`).

## Ranked table (worst first)

| benchmark | P | R | C | overall | verdict | one-line reason | prev overall |
|---|---|---|---|---|---|---|---|
| `charger_fast_tapers` | 3 | 2 | 4 | 2 | RETHINK | the 2 % bound is the tool's artifact over a physical lead of 0 (lines 52-57, 70-81); the claim one cares about (real-time lead of the raised limit, 7 %) is the declined one (lines 58-61) | 2 |
| `lit_lz21_vehicle_position` | 3 | 2 | 5 | 2 | RETHINK | witness copies the left at a constant offset, rows hold for every offset (l.31-34); the source's x <= 10 bound is dropped for the witness (l.38-41); header itself says "not a mechanism exhibit" (l.51) | 2 |
| `rover_terrain_2to4` | 3 | 2 | 4 | 2 | RETHINK | file deliberately keeps a claim against a plan sped up 2.7x although the stronger real-time form certifies at lambda 1 (lines 90-95); the slip rows are a one-sided (left-only) invariant, not relational (lines 162-164) | 3 |
| `turbine_startup_gearratio` | 3 | 2 | 4 | 2 | RETHINK | left evolve w <= 12.705 (l.135) already yields the requirement's 12.71 rpm bound (l.46-47); the domain restriction is admittedly load-bearing (l.94-101); letters witness the one-sided existential form, not the cause (l.67-71) | 3 |
| `h2_refuel_ambientbias` | 3 | 3 | 4 | 3 | RETHINK | ABORT is a start-only mode no fill reaches (lines 15-17); it alone forces the exact stage rows and the D letter (lines 33-38, 49-52); without it the file is R I with one uniform row | 3 |
| `quad_light_lag` | 3 | 3 | 4 | 3 | RETHINK | set-point command through the motor lag but feedback K w lag-free (lines 16-19) is unphysical for one P loop; K = g/2 picked for a round 6/5 ratio (lines 24-25); claim holds only at the exact pinned stretch (lines 38-40) | 3 |
| `acc_spoof_lag` | 3 | 3 | 4 | 3 | POLISH | tau = 0.375 s chosen for rational roots (l.19-22), guards are modal-coordinate hulls (l.65-75); rows are re-timed signatures, the real-time overspeed requirement is left out of the file (l.33-37) | 3 |
| `acc_tune_limp` | 4 | 4 | 3 | 3 | POLISH | lambda_max = 6.0 (l.85) unpinned while the cover is stated at 3/2 and 1 (l.73-74) and sibling files pin; letter-accounting prose (l.44-49) | 2 |
| `elevator_start_discbrake` | 4 | 3 | 4 | 3 | POLISH | brake state b never enters the z, v dynamics (lines 97, 103, 109), so the exact-conformance rows are structural; the only relational content is the LIFT/UP entry timing | 3 |
| `fuelcell_chp_dos` | 3 | 3 | 3 | 3 | POLISH | 7 K is a requirement margin (tightest 5); header concedes the physical claim is 0 and both prunings need the Tin range; garbled sentence at lines 30-31 | 3 |
| `gantry_speed_zones` | 4 | 3 | 4 | 3 | POLISH | the claim is an exact time reparametrization (0.00 certifies at lambda_max 3, line 42) so the 10 mm band is slack; verdict block (line 68) still dated to the round-A binary | 3 |
| `platoon_profiles` | 4 | 3 | 3 | 3 | POLISH | letter D rests on AEB_L, entered only as a start (lines 9-11, 95-98); batch history clutters the header | 3 |
| `quad_light_profiles` | 3 | 3 | 4 | 3 | POLISH | K = g/2 picked for the round 6/5 (l.31); row 4 (l.143) restricts admitted starts without a stated requirement; ECO/SPORT are never run and only supply B and X (l.75-79) | 3 |
| `reactor_feed_wireless` | 3 | 3 | 4 | 3 | POLISH | interlock direction (feed rises with T, no high-T stop) and the symmetric 9/9 limits read as design values tuned to 9; certificate is 10x the simulated effect | 4 |
| `tunnel_jetfan_pairout` | 3 | 4 | 4 | 3 | POLISH | domain floor u >= 2.6 is admitted "not a physical limit" (line 54) and load-bearing at 2.54 for the NORMAL CO row via the c <= 100 fact (lines 52-53); physics otherwise checks to the digit | 3 |
| `zone_lightmass_schedule` | 4 | 3 | 4 | 3 | POLISH | the 0.5 K row sits 0.015 above a tight value set by the domain's far bound (lines 59-66; 33 degC would decline), reachable gap 0.057 K (line 68); witness copies the left's level (X, lines 88-94) | 3 |
| `acc_tune_lag` | 3 | 3 | 5 | 3 | KEEP | exact modal identity holds only at the one lag tau = 0.32 s chosen to make the slow-root ratio exactly 2 (lines 14-24); honest and tight, but the claim is fragile in a physical constant | 3 |
| `grid_ffr_dos` | 4 | 3 | 4 | 3 | KEEP | correct swing/droop arithmetic; 0.24 a_R is the FFR-loss margin, so the claim cannot distinguish the 0.3 s DoS from a dead FFR (lines 44-46); instantaneous droop not flagged | 4 |
| `lit_csf21_vehicle_bus` | 4 | 3 | 4 | 3 | KEEP | faithful non-interference instance of CSF'21 Fig. 11/12; departures (1)-(3) only by reference to the sibling file | 3 |
| `lit_csf21_vehicle_thermo` | 4 | 3 | 5 | 3 | KEEP | faithful instantiation with every deviation listed (lines 42-58); the witness copies the left by construction (thermostat decoupled from d, v), which is the source's property | 3 |
| `lit_drl_car_stop` | 4 | 3 | 5 | 3 | KEEP | sampled right disclosed as the deviation (lines 31-41); content reduces to guard inclusion Safe_eps implies Safe (lines 54-55), thin but it is dRL Goal 1 | 3 |
| `lit_drl_lane_control` | 3 | 3 | 5 | 3 | KEEP | faithful, fully disclosed dRL Goal 1, but the relation is the identity with the right copying the left's action pair; the whole content is Safe_eps => Safe; three-valued leader DECLINES for an unidentified cause | 3 |
| `lit_freedm_meter` | 3 | 3 | 5 | 3 | KEEP | honest rendering of Prop. 11, but the witness never uses its battery (grid-only right also certifies), so the nondeducibility claim is thin; discretized unit demands | 3 |
| `lit_girard08_robot` | 3 | 3 | 4 | 3 | KEEP | certified planner is a superset of Fig. 3 (departure 2) and the 0.16 row is left-only; both disclosed | 4 |
| `rover_ladder_2to3` | 4 | 3 | 5 | 3 | KEEP | clearance rows are real and tight at offset 0 (lines 48-50); the heading row is an unforced contracting start condition (any value in [0, 0.6] certifies, line 52) | 3 |
| `rover_patrol_lag` | 4 | 3 | 4 | 3 | KEEP | one-sided lead against a plan that may run 3/2 faster and advance alone; letters come from the 1 m slack, not the lag (lines 7-10, 73-78), candidly stated; tight 0.59 of 1 m | 3 |
| `rover_terrain_4to6` | 4 | 3 | 4 | 3 | KEEP | sound refinement chain step; half the rows are unary left-only safety rows (l.119), relational rows are structural constant-0 | 3 |
| `sat_detumble_phases` | 3 | 4 | 5 | 3 | KEEP | same claim as sat3w, but the x, y actuators are unnamed isotropic rate dampers of wheel authority chosen because the claim is false at magnetorquer gains (disclosed); the 3-wheel sibling is the physically consistent form | 2 |
| `sat_detumble_weak` | 3 | 4 | 4 | 3 | KEEP | exact energy equality with a non-copy witness is strong; the 2 s duty cycle (lines 33-36) is an invented period that alone yields M and B | 4 |
| `syringe_relay_prearm` | 4 | 3 | 4 | 3 | KEEP | careful physics; "up to re-timing" dominance of C is weaker than the real-time hazard claim, disclosed | 4 |
| `train_ato_odometry` | 4 | 3 | 4 | 3 | KEEP | 1.11 m/s sits in the 0.06 m/s window [1.07, 1.13) where only the stretch rescues it; M and B not load-bearing (lines 88-89) | 4 |
| `watertank` | 3 | 3 | 4 | 3 | KEEP | the paper's running example; the 3 dm band is around a nominal run sped up 2x, so the reference is not a nominal history | 3 |
| `watertank_twospeed` | 3 | 4 | 4 | 3 | KEEP | both constants are exact tank margins (upper pinned from both sides, lower tightest 1.50); lambda_max = 6 unexplained | 3 |
| `acc_spoof_limp` | 4 | 4 | 4 | 4 | POLISH | AASHTO-justified closing-speed row with tight evidence; LIMP guard ceiling 30 (l.113) contradicts the sibling's "fault not conditioned on speed" and leaves CRUISE->LIMP above 30 m/s uncovered although the header says it certifies (l.35-36) | 3 |
| `sat3w_detumble_phases` | 4 | 4 | 4 | 4 | POLISH | correct gyrostat with three wheels, exact energy equality through phase handovers via cubic cancellation; the header omits the stylized gain scale (k = 0.5 /s is ~100x a microsat wheel) that the 4-D sibling discloses | 4 |
| `bottling_fill_strainer` | 4 | 4 | 5 | 4 | KEEP | clean physics (integrator fill, 40 ms valve lag), requirement tied to the 2 mL giveaway margin, tight 1.2 derived from (1-0.85) x 8 mL | 4 |
| `engine_start_highidle` | 4 | 4 | 5 | 4 | KEEP | +4 % is the physical idle increment (tight at 4.00); low phases are identical on both sides, so their rows are identity rows; the "light-off timer" is really a motoring time-out and ABORT is reachable only from elevated timer starts | 3 |
| `flaps_slow_approach` | 4 | 4 | 5 | 4 | KEEP | hardware ratio 1/2, requirement-backed 20 kt, analytic tight value 17.5 with evidence (lines 39-41); grid fragility disclosed (lines 72-79) | 4 |
| `furnace_program_timebase` | 4 | 4 | 5 | 4 | KEEP | 8 degC is a stated AMS 2750 Class 3 requirement with the tight 6.40 measured; the SOAK generator rate 0.1 /min (10x the ramp rate) is an unexplained constant | 4 |
| `hydro_rejection_gatecal` | 4 | 4 | 4 | 4 | KEEP | real test procedure, requirement-derived tolerances with tight values, mode-dependent rows forced by the droop coupling | 4 |
| `insulin_basal_cgmloss` | 4 | 4 | 4 | 4 | KEEP | cited physiology constants, lossy-link cause, requirement-derived 25 mg/dL with tight 20/0.4 and cause-dependence table | 4 |
| `lit_nahs25_salt_tank` | 4 | 4 | 5 | 4 | KEEP | source model and source distance 3, tight (2.99 declines); the xp >= 25 strengthening rows restrict the claim to the region reachable from the source's pre, stated | 4 |
| `platoon_latency` | 4 | 4 | 5 | 4 | KEEP | |Delta g| <= 4 m = J tau / kp, tight and derived; the D letter is carried by an AEB no run enters (lines 5-8), disclosed | 4 |
| `platoon_linkloss` | 4 | 4 | 4 | 4 | KEEP | 0 <= Delta g <= 15 m tight at both ends, fallback modes genuinely exercised; AEB again start-only (lines 43-46), kd_a chosen to keep the CACC poles (line 22) | 4 |
| `rover_ladder_3to6` | 4 | 4 | 5 | 4 | KEEP | pitch row reads the model (tight 0.23 = grade + heave kick, line 52-55; tripled coupling declines); clearance rows chain | 3 |
| `rover_ladder_6to8` | 4 | 4 | 5 | 4 | KEEP | SI model with justified requirement constants and a timetable-derived stretch; the LTR row is implied by the heading and roll rows as stated (header admits it); the deployed-only guard v <= c is a load-bearing reachability fact, not a physical limit | 3 |
| `rover_ladder_8to12` | 4 | 4 | 4 | 4 | KEEP | S comes from the claim form (plan-tolerance rows, lines 86-92) more than from the added dynamics (+0.052 m); left guard v <= c is a load-bearing start condition (lines 110-116), both disclosed | 4 |
| `rover_terrain_6to12` | 4 | 4 | 5 | 4 | KEEP | slope/pitch/squat refinement with derived aux constants and a sensitivity window on the grade; the domain gamma, theta_p <= 0.02 pins the ramp and the MUD guard freezes the pitch, so the pitch lag only acts after the ramp | 3 |
| `tank_dos_3to1` | 4 | 4 | 4 | 4 | KEEP | physical tank and staging law, DoS hold is the single cause, 0.8 m from a submergence requirement, tight 0.72 and hold-length table | 3 |
| `ventilator_vc_cuffleak` | 4 | 4 | 5 | 4 | KEEP | constants derived from a resistor network and ISO 80601-2-12 tolerances, phase-keyed rows forced by flow vs pressure control; the relative INSP row 0.004 + 0.15 V_R goes negative for V_R < -0.027 L (admissible starts), a wart | 4 |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 4 | 29 | 17 | 0 |

Verdicts: KEEP 32, POLISH 12, RETHINK 6, DROP 0. Overall >= 4: 17/50 (34 %). Overall < 3: 4.

## Delta vs previous round

Previous histogram (1..5): 0, 4, 29, 17, 0 over 50; this round: 0, 4, 29, 17, 0 over 50.

Up: `acc_spoof_limp` 3->4, `acc_tune_limp` 2->3, `engine_start_highidle` 3->4, `rover_ladder_3to6` 3->4, `rover_ladder_6to8` 3->4, `rover_terrain_6to12` 3->4, `sat_detumble_phases` 2->3, `tank_dos_3to1` 3->4.

Down: `grid_ffr_dos` 4->3, `lit_girard08_robot` 4->3, `reactor_feed_wireless` 4->3, `rover_terrain_2to4` 3->2, `sat_detumble_weak` 4->3, `syringe_relay_prearm` 4->3, `train_ato_odometry` 4->3, `turbine_startup_gearratio` 3->2.

## Reviewer notes by group

### G1

# Review G1 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

Line numbers refer to benchmarks/suite_v2/<name>/input.txt. Matrix/letters cells checked against docs/paper-numbers/matrix.md and letters.md.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_spoof_lag | 3 | 3 | 4 | 3 | POLISH | tau = 0.375 s chosen for rational roots (l.19-22), guards are modal-coordinate hulls (l.65-75); rows are re-timed signatures, the real-time overspeed requirement is left out of the file (l.33-37) |
| acc_spoof_limp | 4 | 4 | 4 | 4 | POLISH | AASHTO-justified closing-speed row with tight evidence; LIMP guard ceiling 30 (l.113) contradicts the sibling's "fault not conditioned on speed" and leaves CRUISE->LIMP above 30 m/s uncovered although the header says it certifies (l.35-36) |
| acc_tune_limp | 4 | 4 | 3 | 3 | POLISH | lambda_max = 6.0 (l.85) unpinned while the cover is stated at 3/2 and 1 (l.73-74) and sibling files pin; letter-accounting prose (l.44-49) |
| hydro_rejection_gatecal | 4 | 4 | 4 | 4 | KEEP | real test procedure, requirement-derived tolerances with tight values, mode-dependent rows forced by the droop coupling |
| insulin_basal_cgmloss | 4 | 4 | 4 | 4 | KEEP | cited physiology constants, lossy-link cause, requirement-derived 25 mg/dL with tight 20/0.4 and cause-dependence table |
| lit_lz21_vehicle_position | 3 | 2 | 5 | 2 | RETHINK | witness copies the left at a constant offset, rows hold for every offset (l.31-34); the source's x <= 10 bound is dropped for the witness (l.38-41); header itself says "not a mechanism exhibit" (l.51) |
| quad_light_profiles | 3 | 3 | 4 | 3 | POLISH | K = g/2 picked for the round 6/5 (l.31); row 4 (l.143) restricts admitted starts without a stated requirement; ECO/SPORT are never run and only supply B and X (l.75-79) |
| rover_terrain_4to6 | 4 | 3 | 4 | 3 | KEEP | sound refinement chain step; half the rows are unary left-only safety rows (l.119), relational rows are structural constant-0 |
| tank_dos_3to1 | 4 | 4 | 4 | 4 | KEEP | physical tank and staging law, DoS hold is the single cause, 0.8 m from a submergence requirement, tight 0.72 and hold-length table |
| turbine_startup_gearratio | 3 | 2 | 4 | 2 | RETHINK | left evolve w <= 12.705 (l.135) already yields the requirement's 12.71 rpm bound (l.46-47); the domain restriction is admittedly load-bearing (l.94-101); letters witness the one-sided existential form, not the cause (l.67-71) |

## acc_spoof_lag

Model: car speed v and realised acceleration a under a cruise loop a_cmd = 0.5 (30 - v_meas) through a first-order powertrain lag tau = 0.375 s; left reads the speed 25 % high (settles at 24 m/s), right is unspoofed.
Property: at stretch 3/2, v_L(t) <= v_R(1.5 t) and the dominant-mode speed u_L <= u_R - 6 exactly (the spoofed car is the reference sped up 3/2 and lowered by 6 m/s).
Concern (P): tau = 0.375 s is chosen because both closed loops then have rational real roots (l.19-22), not from a powertrain datum; both guards (l.103, l.111) are forward-invariant hulls in modal coordinates, with the left hull widened after a run from the engagement box "dipped to 22.6 m/s and ended" (l.69-70). Concern (R): both rows are re-timed statements; the header concedes the real-time overspeed bound is "not a row of this file" and certifies separately at lambda 1 (l.33-37), and row 1 certifies down to -3.33 (l.32-33), so its constant 0 is 3.3 m/s loose along the cover.
Mechanism cells: S M in header (l.5), letters.md S M, matrix M1 yes (lambda 3/2) M2 yes: agree.
Fix: justify tau from a powertrain source (a 0.3-0.5 s range) and say the rational roots are a convenience; cut the batch-I4 "Consequence" paragraph (l.55-63), which quotes rows the file does not contain; state in one sentence that the real-time overspeed claim lives in acc_spoof_lag's lambda-1 sibling if one is kept.

## acc_spoof_limp

Model: one speed loop; left is spoofed 25 % high in CRUISE (settles 24 m/s) and may latch LIMP (0.3 (22 - v)) at any 2 s debounce; right is the unspoofed loop with driver-selectable ECO/NORMAL/SPORT set speeds and a DISENGAGE coast below 20 m/s, 1 s period.
Property: v_L <= v_R (never faster than the reference) and 0.7 v_R <= v_L + 4 (closing speed absorbable by a 2 s-gap follower under AASHTO stopping values), both modes.
Concern (P): LIMP guard 20 <= v <= 30 (l.113) while CRUISE runs to 40 (l.108): a CRUISE run latching LIMP above 30 m/s ends, so part of the deployed behaviour is uncovered; the header says LIMP on the whole domain still certifies (l.35-36) and the sibling acc_tune_limp states that a fault latch "is not conditioned on speed" (its l.28-29). The 30 m/s ceiling is kept only so that RELCERT_NO_CHOICE=1 still certifies (l.36-39), which is a tool-side reason.
Mechanism cells: M B I in header (l.5), letters.md M B I, matrix M2 yes M3 yes M6 yes: agree. The header is candid that no letter comes from the spoof (l.25-30).
Fix: set the LIMP guard to v >= 20 and v < 40 (certifies per l.35-36) and re-measure the NO_CHOICE line (expect certify up to 34.50 only, or a hop ECO -> NORMAL and letter X); keep the AASHTO row as is.

## acc_tune_limp

Model: left is an aftermarket tune, CRUISE 0.75 (30 - v), latching LIMP 0.3 (25 - v); right is the stock controller with NORMAL 0.5, COMFORT 0.4, SPORT 0.6 toward 30 m/s and DISENGAGE below 20 m/s; 0.1 s periods both sides.
Property: in CRUISE v_L = v_R exactly at stretch 3/2 (the tune is NORMAL 1.5 times faster); in LIMP v_L <= v_R at stretch 1.
Concern (C): lambda_min = 1.0, lambda_max = 6.0 (l.84-85) is a searched range although the header states the cover at 3/2 and 1 (l.73-74) and the sibling files were "pinned, unused range gone"; the file carries a stretch range it does not use. Lines 44-49 argue the D letter under "the rule of 2026-10-27", which is methodology rather than scenario. Minor (R): the LIMP hop SPORT -> NORMAL is needed only in the 1 m/s sliver 35-36 m/s (l.58-62); disclosed.
Mechanism cells: S M B D I X in header (l.4), letters.md S M B D I X, matrix M1 M2 M3 M5 M6 yes: agree.
Fix: set lambda_max = 1.5 and state that CRUISE pairs at 3/2 and LIMP at 1 (per-pairing stretch); condense l.44-49 to one sentence ("rows differ because the exact row is false in LIMP; the uniform exact row DECLINES").

## hydro_rejection_gatecal

Model: hydro unit with gate servomotor (4 s), droop 5 %, mechanical starting time 8 s, in a load-rejection test: ONGRID (t < 20 s, speed = grid frequency, gate holds 0.85 load) then REJECT (breaker open, gate to no-load 0.1, rotor accelerates on the excess gate); left's gate transducer reads 0.02 of stroke low.
Property: on the grid t, w equal and |g gap| <= 0.027 (3 % dispatch tolerance); after rejection t equal, |w gap| <= 0.09 (overspeed protection 1.30 pu against the commissioned peak 1.2055), |g gap| <= 0.027.
Concern: none of substance. Tight values given (0.02/0.02, l.40-43), cause table (l.61-64), uniform rows shown to need 0.18 (l.47-55). The speed band 0.09 is 4.5x the tight 0.02 but is the stated protection margin. Domains are stroke and runaway limits (l.68-71).
Mechanism cells: D in header (l.5), letters.md D, matrix M5 yes (3/3 handoffs unsat): agree.

## insulin_basal_cgmloss

Model: insulin action X (55 min absorption, Hovorka), glucose G relaxing in 60 min toward 120 + 50 (b - X), patient need b constant in [0.5, 1.3] U/h; a 9-level basal table (suspend below 70, 0.2 U/h steps per 30 mg/dL band) read every 5 min on the right and every 10 min on the left (every other Bluetooth reading lost).
Property: |G_L - G_R| <= 25 mg/dL, |X_L - X_R| <= 0.5 U/h, b equal, in every level; 25 keeps the deployed inside the 70-180 consensus range at the validated loop's settling points.
Concern: minor. The requirement argument holds only at settling (l.37-38, "transiently the validated run can be anywhere in [40, 400]"), disclosed. The simulated worst gap is 1.4 mg/dL against a certified 20 (l.61-63), disclosed as an inductive envelope. Some declared left successors are unreachable upward (SUSP -> L2, l.101: from 69.9 the rise in 10 min is at most 19.2 mg/dL), harmless over-approximation.
Mechanism cells: M B in header (l.5), letters.md M B, matrix M2 yes M3 yes: agree.

## lit_lz21_vehicle_position

Model: Liu-Zamani 2021 single-lane vehicle, double integrator x' = v, v' = u with u in {-0.05, 0, 0.05} held 1 s, v kept in [0, 0.1] by the guards; left is the secret run (x in [0, 1] at start), right the non-secret partner 1 m ahead.
Property: v_L = v_R and x_R = x_L + 1 forever (delta-approximate initial-state opacity with delta = 1).
Concern (R): the witness copies the left's input and keeps a constant offset; the header states the rows certify for every offset 0, 0.5, 2, 5, 9, 50, -1 (l.31-34), so delta = 1 is not loaded and the content is translation invariance; the rubric deducts for witnesses that copy the left. Concern (P): the source's state bound x <= 10 is removed "for the WITNESS, not because the source's claim fails" (l.38-41); with it restored --wellformed reports BLOCKING (l.44-46). The input set is three levels instead of U = [-0.05, 0.05] (l.56-63). The header is exemplary in disclosure, including "a literature row, not a mechanism exhibit" (l.51).
Mechanism cells: X in header (l.5), letters.md X, matrix: no M1-M6 letters: agree.
Fix: either (a) switch to the ECC 2022 infinite-step variant the header already measured (l.67-72: Xs = [5.5, 6], offset 0.75), where the offset is pinned from both sides by the secret set (an offset at or below 0.5 puts the partner inside Xs, above 1 breaks delta) and record the declining offsets, or (b) drop the file and keep lit_lz21 as a citation only; in either case restore x <= 10 at least as the admitted start range and say that the unbounded evolve is the one departure.

## quad_light_profiles

Model: quadrotor climb h' = w, w' = T/m - g - K w with a P velocity loop commanding thrust for the reference mass; the deployed airframe is 20 % lighter (terminal climb 2.4 against 2.0 m/s); the reference may select NORMAL/ECO/SPORT profiles at any 1 s interval.
Property: at stretch 6/5 the deployed's altitude is within 0.8 m (PX4 acceptance radius) of the NORMAL reference's altitude at time 1.2 t, strengthened by a conserved steady-climb gap Psi <= 0.8 and 1.2 w_R <= w_L.
Concern (P): K = 4.905 = g/2 is chosen so the ratio is "the round 6/5" (l.31-32); the header shows PX4's default K = 4 certifies pinned at 1.24525, so the claim survives, but the constant is tuned. ECO and SPORT (l.132-141) are admissible starts the cover leaves at its first decision and never runs; the header admits "with them removed the file certifies with S M alone" (l.75-79), so B and X are supplied by decoration. Concern (R): row 4, 1.2 w_R <= w_L (l.143), is not a requirement but a start-set restriction (two airframes starting at the same non-zero climb rate are excluded); l.64-70 state rows 1-3 "are not loaded by the dynamics" and that 0.8 m is the admitted start radius, so the certificate's content is the conservation of Psi plus the stretch.
Mechanism cells: S M B X in header (l.5), letters.md S M B X, matrix M1 yes (6/5) M2 yes M3 yes: agree.
Fix: state row 4 as the admitted-start condition it is (or replace it by hover-start evidence) and either remove ECO/SPORT (letters become S M, honest) or keep them with the mechanisms line saying B and X come from the profile graph only and are not load-bearing for the claim.

## rover_terrain_4to6

Model: terrain rover over MUD/GRAVEL/PAVED zones with traction stiffness, drag and sinkage per zone; right is the 4-DOF ideal wheel-speed loop (u, zh pinned), left adds a lagged speed command u' = 4 (c_T - u) and a heave amplitude zh' = rho_T v - zh.
Property: v_L <= v_R, s_L <= s_R (the lagged rover never faster than or ahead of the ideal-drive model), slip window w_L <= v_L + 0.25, heave zh_L <= 0.15 (bump stop), plus three auxiliary rows (w_L <= w_R, zs_R <= zs_L, w_L <= u_L).
Concern (R): of the eight conjuncts (l.119), zh_L <= 0.15, v_L <= w_L, w_L <= u_L and w_L <= v_L + 0.25 are unary left-only facts; the relational rows are structural constant-0 orderings, tight by construction. The tolerances 0.25 and 0.15 are stated requirements with tight values 0.21 and 0.13 (l.36-38). The entry guards u <= c_T / w <= c_T (l.80, l.102) are reachability facts rather than physical limits, justified at l.44-47.
Mechanism cells: I in header (l.6), letters.md I, matrix M6 yes: agree.
Verdict KEEP as a chain step; its value is the transitivity 12-DOF <= 6-DOF <= 4-DOF (l.51-53).

## tank_dos_3to1

Model: tank level h' = 0.005 n - 0.001 w h fed by n staged pumps, demand conductance rising w' = 0.02 (22 - w) (morning surge), staging n = round(w / 4) decided every 10 s on the right and held up to 30 s on the left (DoS drops two of three polls).
Property: h_L <= h_R (a stale decision is always a lower stage, so the attacked tank cannot overflow when the nominal does not) and h_R <= h_L + 0.8 m (outlet submergence 0.15 m against the nominal floor 0.95 m), w equal.
Concern: minor. The claim is scoped to a monotone surge (l.13-14, l.31); a falling demand would invert h_L <= h_R, which the header does not say explicitly. Left next(P2) lists P5 (l.88) though 30 s crosses at most two band edges (l.25-26); harmless over-declaration. Tight 0.72 and the hold-length table (l.40-47) make 0.8 a real margin.
Mechanism cells: M I in header (l.5), letters.md M I, matrix M2 yes M6 yes, M3 no (chain): agree.

## turbine_startup_gearratio

Model: NREL 5-MW rotor speed in start-up phases SPINUP (free-spin toward 9 rpm), RAMP (pitch loop toward 7.5 rpm), GEN (toward rated 12.1 rpm), STOP (brake); the deployed controller divides generator speed by the stale ratio 97 instead of 92.4, so thresholds and targets are 1.05 times higher and the loop gains 1.05 times lower.
Property: w_L <= 1.05 w_R in every mode against an existential reference that may be in a later phase.
Concern (R): the header derives the requirement (deployed below 12.71 < 13.31 rpm, l.45-47) from the claim, but the left evolve domain w <= 12.705 (l.135) already states it; with the physical range (16 rpm, above the 13.31 rpm limit) the file DECLINES under every switch (l.96-98), so the domain, not the relation, carries the requirement. The factor 1.05 is "tight" only because 1.049 and 1.051 change the admitted start set at the 2.0/2.1 rpm thresholds (l.48-50), not through the dynamics. The header itself shows R, P, I appear at g = 1.00 with w_L <= w_R (l.67-71) and that every two-sided form is near-vacuous (l.72-89). Concern (P): "the domain restriction is load-bearing" (l.14-15, l.94-101) is exactly a domain tuned to the claim, candidly disclosed.
Mechanism cells: R P I in header (l.4), letters.md R P I, matrix M4 yes M6 yes M6+ yes: agree.
Fix: make the domain physical (0 to 16 rpm, or to the 13.31 rpm trip, both sides) and move the start-up scope into stated rows w_L <= 12.705 and w_R <= 12.1 (inductive on each side since every target is at most its row's constant), so that the claim is visibly "about start-ups" and the overspeed consequence is not a modeling assumption; if the one-sided relation still certifies only with the reference allowed to run ahead alone, state a timing claim instead (the deployed reaches cut-in no later than 1.05 times the reference's time) or drop the file.

### G2

# Review G2 (independent, rubric RUBRIC.md): 10 benchmarks of benchmarks/suite_v2

Sources read: each input.txt in full; docs/paper-numbers/matrix.md rows 10, 11, 13, 17, 18, 22, 23, 32, 39, 40; docs/paper-numbers/letters.md rows 8, 9, 11, 15, 16, 20, 21, 30, 37, 38. Line numbers below are input.txt lines.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| charger_fast_tapers | 3 | 2 | 4 | 2 | RETHINK | the 2 % bound is the tool's artifact over a physical lead of 0 (lines 52-57, 70-81); the claim one cares about (real-time lead of the raised limit, 7 %) is the declined one (lines 58-61) |
| elevator_start_discbrake | 4 | 3 | 4 | 3 | POLISH | brake state b never enters the z, v dynamics (lines 97, 103, 109), so the exact-conformance rows are structural; the only relational content is the LIFT/UP entry timing |
| flaps_slow_approach | 4 | 4 | 5 | 4 | KEEP | hardware ratio 1/2, requirement-backed 20 kt, analytic tight value 17.5 with evidence (lines 39-41); grid fragility disclosed (lines 72-79) |
| grid_ffr_dos | 4 | 3 | 4 | 3 | KEEP | correct swing/droop arithmetic; 0.24 a_R is the FFR-loss margin, so the claim cannot distinguish the 0.3 s DoS from a dead FFR (lines 44-46); instantaneous droop not flagged |
| h2_refuel_ambientbias | 3 | 3 | 4 | 3 | RETHINK | ABORT is a start-only mode no fill reaches (lines 15-17); it alone forces the exact stage rows and the D letter (lines 33-38, 49-52); without it the file is R I with one uniform row |
| lit_csf21_vehicle_thermo | 4 | 3 | 5 | 3 | KEEP | faithful instantiation with every deviation listed (lines 42-58); the witness copies the left by construction (thermostat decoupled from d, v), which is the source's property |
| lit_drl_car_stop | 4 | 3 | 5 | 3 | KEEP | sampled right disclosed as the deviation (lines 31-41); content reduces to guard inclusion Safe_eps implies Safe (lines 54-55), thin but it is dRL Goal 1 |
| quad_light_lag | 3 | 3 | 4 | 3 | RETHINK | set-point command through the motor lag but feedback K w lag-free (lines 16-19) is unphysical for one P loop; K = g/2 picked for a round 6/5 ratio (lines 24-25); claim holds only at the exact pinned stretch (lines 38-40) |
| rover_patrol_lag | 4 | 3 | 4 | 3 | KEEP | one-sided lead against a plan that may run 3/2 faster and advance alone; letters come from the 1 m slack, not the lag (lines 7-10, 73-78), candidly stated; tight 0.59 of 1 m |
| rover_terrain_2to4 | 3 | 2 | 4 | 2 | RETHINK | file deliberately keeps a claim against a plan sped up 2.7x although the stronger real-time form certifies at lambda 1 (lines 90-95); the slip rows are a one-sided (left-only) invariant, not relational (lines 162-164) |

## charger_fast_tapers

Model: one-state SoC x with PRECHARGE/BULK/ABSORB/FULL/FAULT; the deployed charger raises only the CC constant (0.125 vs 0.1, line 140 vs 168) and decides every 0.012 min against 0.006 min (lines 133, 161); the reference carries two taper options.
Property: against the profile replayed at 5/4 speed, the deployed SoC never leads by more than 2 % (PRECHARGE: never leads).
Concern (R): lines 52-57 state the physical lead is 0.00 from every start and the 2 is the tool's value; lines 70-81 trace both units to the FAULT x FAULT re-timed pairing and the FULL floor gap. The replayed profile is at least as fast in every phase (lines 64-65), so "never leads the sped-up profile" carries little content, and the ∃ over the two tapers never binds for a one-sided bound (the faster taper always serves), making B cosmetic. The claim one would care about, the real-time lead the raised limit buys (up to 7 %, lines 59-61), declines.
Concern (P): FAULT self-discharge x' = -0.01 x (line 24, 155) is 1 %/min, orders of magnitude above real self-discharge; the "constant-current" phase is an exponential (lines 18, 32-35, admitted); the 2:1 decision period is a design value (line 41).
Fix: remove FAULT on both sides (lines 74-75 report c = 1.00 then, the FULL-floor unit only) and test the other direction at lambda 1, x_R <= x_L with the ∃ taking the slow taper ("the raised limit never slows the fill"), which is the physical content of the cause; if it declines, say so in the header and keep the re-timed form with c = 1 as an upper bound only.

## elevator_start_discbrake

Model: car z, v and brake lift b through LIFT/UP/APP/STOP; the retrofit changes only the lift constant k (50 vs 5, lines 91 vs 119).
Property: z and v equal in every mode (exact conformance) and, while the deployed car still lifts, the reference brake is no further lifted; the reference may finish its slower lift alone.
Concern: b does not appear in z' or v' in any mode (lines 97, 103, 109, 125, 131, 137), so once UP is entered the motion rows hold by identical ODEs; the relational content is only that the reference can wait in LIFT (right-only step). The STOP guard conjunct z + v/4 <= 20.5 (line 110) was added for the well-formedness gate (lines 60-62) but has a physical reading. P and C are fine.
Fix (header): state in one line that b is decoupled from the motion ODE, so the claim's content is the entry timing of UP and the LIFT conjunct; otherwise KEEP.

## flaps_slow_approach

Model: flap angle f and airspeed V through EXT/CONF2; one hydraulic system lost halves the flap rate (0.5 vs 1 deg/s, lines 109 vs 123); first-order deceleration whose rate grows with flap drag.
Property: at equal flap positions (reference re-timed by 1/2 while the flaps move, 1 once set) the FLAPS SLOW aircraft is never faster and at most 20 kt slower.
Concern: none of substance. The domain V in [150, 185] (line 68) is the manoeuvre's window, forward invariant, not a bound on the claim; the exact flap rows hinge on 1/2 being a grid point (lines 72-79, disclosed as a tool limitation). Flap rate 1 deg/s is assumed (line 20-21), stated.

## grid_ffr_dos

Model: swing equation x' = 6.25(0.1 a - d) - 2.625 x (line 10, checked: H = 4 s, 1/R + D = 21) with NORMAL/FFR/TRIP; the DoS holds the supervisor decision 0.3 s against 0.1 s (lines 88, 104); the left omits TRIP as unreachable (lines 28-31, verified: flow at -1.5 Hz is >= 2.06 Hz/s up).
Property: the attacked island is never above the nominal one and at most 0.24 a_R Hz below it; FFR never activates earlier.
Concern (R): 0.24 = 0.1/0.42 is the support of the whole FFR; lines 44-46 report that a deployed FFR that never activates also certifies at 0.24, so the claim bounds total FFR loss, not the 0.2 s delay. Justified by the protection-plan margin (lines 36-41) and tight (0.23 declines), so acceptable but weak as a DoS statement.
Concern (P, minor): the primary droop is instantaneous (line 9), which is the usual swing-equation shortcut but not flagged as a deviation; a governor lag would make the FFR's role larger.
Fix (header): one line that the droop is instantaneous and that the bound is the FFR-loss margin, not the delay's effect; otherwise KEEP.

## h2_refuel_ambientbias

Model: tank pressure p through three ramp stages, TOPOFF, COMPLETE and a start-only ABORT (p < 0.5); the 10 K sensor bias shifts the end pressure 70.0 to 72.4 (lines 129-130, 169-170).
Property: in the ramp stages the deployed never leads; from TOPOFF on it leads by at most 2.9 MPa (2.4 shift plus 0.5 the certificate needs).
Concern (P/R): ABORT (lines 15-17, 140-144, 180-184) is declared as a successor of STAGE1/STAGE2 (lines 114, 120) yet both edges are pruned and no fill enters it; lines 33-38 and 49-52 state that the exact stage rows and the D letter exist only because of the (STAGE1_L, ABORT_R) start pairing, and that with ABORT removed the uniform row p_L <= p_R + 2.9 certifies with letters R I. A letter and a row's exactness resting on an unreachable mode is a tuned structure. The staged ramp is a design value, not J2601's (lines 23-24, disclosed).
Fix: remove ABORT on both sides, state the uniform row p_L <= p_R + 2.9 (lines 50-52 report CERTIFIED), accept letters R I; keep the 0.5 caveat (lines 55-59). If ABORT is kept, make it reachable (e.g. a leak-check abort on a pressure-drop condition) so that D reflects a real fallback.

## lit_csf21_vehicle_thermo

Model: CSF 2021 car (d, v, temp) with six modes action x thermostat; the attacked car picks any thermostat setting, the genuine one reads temp (guards lines 129-160); A = B = eps = 1 from the journal follow-up (lines 20-22).
Property: d and v equal at every instant (the source's H-equivalence formula).
Concern: the thermostat is decoupled from d, v on both sides (temp' only), so the genuine car matches by hopping into the attacked action (X) and the witness copies the left; this is the source's property, so acceptable. Deviations (Coast stand-in at v <= 1, top speed 40, thermo in {-1, 1}) are all listed (lines 42-58). None otherwise.

## lit_drl_car_stop

Model: x, v with Accel/Coast/Brake; left Accel guarded by Safe_eps (line 86), right by Safe (line 104); A = B = eps = 1, m = 50 (line 43).
Property: identity refinement x_L = x_R, v_L = v_R, the time-triggered controller refining the permissive one.
Concern: the right is sampled, not event-triggered (lines 31-41, disclosed as the deviation), so what is certified is Goal 1, the arithmetic implication Safe_eps implies Safe; the relational certificate is a guard inclusion with the witness copying the left. Thin, but faithful to what the suite can express and honestly stated. The v <= 10 top speed is a convenience (lines 44-47), stated. None otherwise.

## quad_light_lag

Model: climb h, w with a first-order thrust lag a' = 10 (a_cmd - a); the lighter airframe scales a_cmd and the climb-rate feedback by 1.25 (lines 88, 96).
Property: altitudes within 0.8 m at times t and 1.2 t (PX4 acceptance radius), with a conserved steady-climb gap Psi bounded by 0.16 m as strengthening.
Concern (P): lines 16-19 admit that the set-point part of the thrust command passes through the motor lag while the feedback K w acts without lag; a single P velocity loop commands one thrust and all of it passes the motors, so the model is a simplification chosen so that Psi is conserved (a fully lagged loop with tau = 0.1 s has complex roots at K = 4.905, s^2 + 10 s + 49 = 0). K = 4.905 = g/2 is chosen for the round 6/5 (lines 24-25; other K certify at their own pinned ratio, lines 25-30, which mitigates the tuning concern). The claim holds only at the exact pinned stretch (lines 38-40), stated.
Fix: route the whole command through the lag, a' = (1/tau)((m_R/m)(g + K (w_sp - w)) - g - a), with tau = 0.05 s (real roots at K = 4.905: s^2 + 20 s + 98) and rederive Psi; if no conserved form exists, keep the file but move the lag-split sentence to the top of the header as the model's stated simplification and say the loop is not PX4's.

## rover_patrol_lag

Model: zone planner SLOW/MEDIUM_ECO/MEDIUM_BRISK/FAST on both sides; the left adds a motor current lag tau = 3/16 s (lines 106-121), the right is the first-order plan.
Property: the lagged rover is never more than 1 m ahead of the plan re-timed by at most 3/2 and advanced alone into the rover's zone, with a look-ahead odometer row P_L <= P_R + 0.375 as strengthening.
Concern (R): the plan may run faster and jump ahead, so "never ahead by more than 1 m" is an order property with the lead bound shrinking as more re-timing is allowed (0.59 at 3/2, 0.38 at 6, lines 43-45); lines 7-10 and 73-78 state that all four letters come from the 1 m slack and not from the lag. The two-sided real-time claim declines (lines 52-61). The domain cut 0 <= a + 4 v <= 6.4 (line 108) is a derived invariant rather than a physical limit, declared not load-bearing (lines 29-34).
None blocking: the requirement (waypoint radius) and the tight value are given and the cause dependence is measured; KEEP.

## rover_terrain_2to4

Model: 4-DOF rover (ground speed v, odometer s, wheel speed w, sinkage zs) over MUD/GRAVEL/PAVED against the 2-DOF no-slip plan with w, zs pinned (lines 122-158).
Property: the rover is never faster than or ahead of the plan re-timed by up to 2.7, and the slip velocity w - v stays in [0, 0.25].
Concern (R): lines 90-95 report that adding w_L <= v_R certifies the real-time claim at lambda 1 (SYNC certifies, letters I), and that this file keeps the stretched form "deliberately, as the chain's exhibit"; lines 68-69 and 81-82 say 2.7 is not a mission requirement. A claim against a plan allowed to run 2.7x faster is weaker than the one the tool already certifies, chosen for its letters. The slip rows (lines 162-164, v[l] <= w[l], w[l] <= v[l] + 0.25) mention only left variables, so they are a single-system invariant carried as a row, and the only relational rows are the two one-sided ones.
Concern (P): left guards carry the invariant w <= c_T (lines 123, 129, 135), a controller fact not a controller guard, placed there so the cut mechanism can use it (lines 9-10, 105-106); the creep floor w >= 0.15 (line 124) excludes rest and is what makes v = 0 forward invariant (lines 54-56).
Fix: adopt the real-time form (add w[l] <= v[r], lambda_min = lambda_max = 1) as the suite file, which the header says certifies with SYNC; if the chain wants a stretched exhibit, state a mission allowance for the plan's re-timing or keep the stretched form in benchmarks/reserve.

### G3

# Review G3 (independent, rubric RUBRIC.md): 10 benchmarks of suite_v2

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| engine_start_highidle | 4 | 4 | 5 | 4 | KEEP | +4 % is the physical idle increment (tight at 4.00); low phases are identical on both sides, so their rows are identity rows; the "light-off timer" is really a motoring time-out and ABORT is reachable only from elevated timer starts |
| furnace_program_timebase | 4 | 4 | 5 | 4 | KEEP | 8 degC is a stated AMS 2750 Class 3 requirement with the tight 6.40 measured; the SOAK generator rate 0.1 /min (10x the ramp rate) is an unexplained constant |
| lit_drl_lane_control | 3 | 3 | 5 | 3 | KEEP | faithful, fully disclosed dRL Goal 1, but the relation is the identity with the right copying the left's action pair; the whole content is Safe_eps => Safe; three-valued leader DECLINES for an unidentified cause |
| lit_freedm_meter | 3 | 3 | 5 | 3 | KEEP | honest rendering of Prop. 11, but the witness never uses its battery (grid-only right also certifies), so the nondeducibility claim is thin; discretized unit demands |
| lit_nahs25_salt_tank | 4 | 4 | 5 | 4 | KEEP | source model and source distance 3, tight (2.99 declines); the xp >= 25 strengthening rows restrict the claim to the region reachable from the source's pre, stated |
| rover_ladder_6to8 | 4 | 4 | 5 | 4 | KEEP | SI model with justified requirement constants and a timetable-derived stretch; the LTR row is implied by the heading and roll rows as stated (header admits it); the deployed-only guard v <= c is a load-bearing reachability fact, not a physical limit |
| rover_terrain_6to12 | 4 | 4 | 5 | 4 | KEEP | slope/pitch/squat refinement with derived aux constants and a sensitivity window on the grade; the domain gamma, theta_p <= 0.02 pins the ramp and the MUD guard freezes the pitch, so the pitch lag only acts after the ramp |
| sat3w_detumble_phases | 4 | 4 | 4 | 4 | POLISH | correct gyrostat with three wheels, exact energy equality through phase handovers via cubic cancellation; the header omits the stylized gain scale (k = 0.5 /s is ~100x a microsat wheel) that the 4-D sibling discloses |
| sat_detumble_phases | 3 | 4 | 5 | 3 | KEEP | same claim as sat3w, but the x, y actuators are unnamed isotropic rate dampers of wheel authority chosen because the claim is false at magnetorquer gains (disclosed); the 3-wheel sibling is the physically consistent form |
| ventilator_vc_cuffleak | 4 | 4 | 5 | 4 | KEEP | constants derived from a resistor network and ISO 80601-2-12 tolerances, phase-keyed rows forced by flow vs pressure control; the relative INSP row 0.004 + 0.15 V_R goes negative for V_R < -0.027 L (admissible starts), a wart |

## engine_start_highidle

Model: a 2-state (N2 %, timer s) five-phase turbofan ground start, first-order spool per phase, deployed idle 66 % vs reference 62 %.
Property: below starter cut-out the deployed is never ahead of the reference in N2 and the reference timer never ahead of the deployed's; above cut-out N2_L <= N2_R + 4 (the idle increment).
Concerns: (a) lines 10-11 and 16: the "light-off timer" runs only in STARTER (motoring below 25 %), so it is a starter/hung-start time-out, not a light-off timer (which runs from fuel-on, i.e. in LIGHTOFF); naming only. (b) line 17-20: with the installed dynamics N2 reaches 25 % from 5 % in 16 s, so ABORT is reached only from starts with t already near 30 (an initial-state artifact, no degraded spool). (c) lines 145-146: STARTER and LIGHTOFF dynamics are identical on both sides (lines 81/115, 87/121), so the 0-tolerance rows there are identity rows; the only non-identity content is +4 in SELF/IDLE/ABORT, which is tight (line 35) and physical (equilibria 66 vs 62).
Mechanisms R D I agree with letters.md and matrix (M5 yes, M6 yes, M6+ yes).
No fix required; if polishing, rename t "starter time-out timer" at line 10.

## furnace_program_timebase

Model: setpoint generator s (first-order to each segment target) and load T (5 min lag), deployed program at 80 % rate (kap 0.008 vs 0.01), re-timed by lambda = 4/5.
Property: up to the recipe's permitted re-timing the deployed setpoint equals the validated one and the load is within 8 degC of the validated load; two envelope rows on the reference load.
Concerns: (a) line 15 / lines 90, 112: the SOAK generator rate 0.1 /min (left 0.08) is 10x the PREHEAT/HEAT rate 0.01 with no physical reason given (a real programmer ramps linearly then holds); the segment thresholds 640/860 are 10 degC below the targets so the first-order generator actually crosses them, which is a model convenience. (b) lines 29-32: AMS 2750 Class 3 is a spatial uniformity class; using it as the load-deviation tolerance for a rate change is a reinterpretation (stated as "the tolerance the validated profile was qualified with"), acceptable but a stretch. (c) the stretch window [0.8, 1.0] is exactly the deployed rate, so the s rows are exact by construction (line 48, admitted); the T residual 6.40 (line 41) is the real content and the 8 degC claim is loose by 1.6 degC with a stated requirement.
Mechanisms S I agree (M1 yes 4/5, M6 yes, M6+ yes).

## lit_drl_lane_control

Model: follower/leader gap d and two speeds, A = B = eps = 1, six (follower, leader) bang-bang action pairs per side; left Accel guarded by Safe_eps, right Accel by Safe.
Property: identity relation (d, v_f, v_l equal) in every left mode, stretch 1: every run of the conservative sampled follower is a run of the permissive sampled follower.
Concerns: (a) lines 51-54, 144-149: the relation is the identity and the witness copies the left's action pair at each window (line 56-57); the certified content reduces to Safe_eps => Safe (which holds trivially since 2 v_f + 1 >= 0) plus equal guards elsewhere. A literature refinement benchmark legitimately has this shape, but it is the thinnest relational content in the group. (b) line 37-38, 92/97: Coast only at v_f <= 1 and Brake only from v_f >= 1 (lines 102, 107) mean the follower cannot brake below 1 m/s, a stand-in disclosed as such. (c) lines 31-34: a three-valued leader DECLINES for an unidentified cause, left open since 2026-10-28; the file should say whether this is a tool limitation or a modeling error before the paper cites "dRL case study". (d) line 53: the event guard Safe is "ours"; cite the thesis formula so a reader can check the instantiation.
Mechanism X agrees (matrix M6 vacuous, M2/M3 no).

## lit_freedm_meter

Model: battery level B in [0, 10] and cumulative grid meter E; 12 modes per side = {battery, grid} x demand {0,1,2} x renewable {0,1}, battery modes enabled when one period keeps B in range.
Property: equal meters at all times from any pair of battery levels (nondeducibility of B through E).
Concerns: (a) lines 42-47: the witness never uses its battery and "a right model with the six grid modes only ... also CERTIFIES"; the certified fact is that the grid branch is always available, which is one line of the source's proof. The claim is faithful but thin: no constraint ever forces the right to touch B. (b) lines 24, 70-129: BatD0R0 and BatD1R1 are flow-identical to GridD0R0 and GridD1R1 (B' = E' = 0), redundant modes; demands are unitless integers per period (line 24, reals in the source). (c) line 31: E has no domain, correct physically (net export) and stated.
Mechanism X agrees.
No fix required for KEEP; a stronger variant would add a grid import cap (e.g. E' <= 1 on the right) so that the battery is sometimes the only witness, but that departs from the source and should be a separate file.

## lit_nahs25_salt_tank

Model: 1-D salt mass xp in a 100 gal tank, On xp' = 0.1 (25 - xp), Off frozen; attacked guards On xp >= 22 / Off xp < 28 (bounded reading error 3 projected onto xp) vs genuine 25.
Property: |xp_L - xp_R| <= 3 and both >= 25 in both left modes.
Concerns: (a) lines 26-28 and 104-105: the rows xp_L, xp_R >= 25 make the genuine Off (line 99, xp < 25) never admissible and restrict the attacked On start to xp >= 25; this is justified from the source's pre xp = 50 (line 27) but means the certified claim is the source's forward distance only on the region above the On equilibrium, not from every related pair in the attacked guard set. Stated in deviation (2), line 39-41. (b) line 31: the symmetric row xp_R <= xp_L + 3 is slack (certifies at 0); kept at 3 as the source's distance, fine. (c) line 36-38: no evolve domain, matching the source; salt nonnegativity is implied by xp >= 25 anyway.
Mechanism I agrees (M6 yes, M6+ vacuous widened atom xp <= 28 frozen).

## rover_ladder_6to8

Model: 8-state UGV (speed, odometer, heading and pitch with second-order cascades, heave, roll) in three speed zones, against the 6-state level with yaw/pitch rates pinned at 0; reference re-timed by lambda in [1, 1.25].
Property: the rover is never faster or farther than the re-timed reference; heading, pitch, roll and LTR requirement bands on the left; plan tolerance bands on the right.
Concerns: (a) lines 60-63 and the LTR conjunct at lines 186-188: the rollover row as stated follows from the heading and roll rows (0.771 < 0.8); it is a consequence, not an independent claim; the header admits it and reports the dynamic tightest 0.22, but the file's row is the implied one. (b) lines 108-114 and guards at 148/154/160: the deployed-only guard v <= c is a reachability fact used as a start condition and is load-bearing ("from a start above it the clearance rows fail at every lambda > 1"); it is not a physical limit, and the right guards lack it, so the claim is "from governed entries only". Disclosed. (c) line 54: the heading row certifies at any value (0.05 tested); 0.35 is a requirement, fine, but the row carries no information about the step. (d) lines 25-26: the along-track loss coefficients 0.3 theta_p^2 and 0.2 phi_r^2 are unsourced constants.
Mechanisms S M I agree (M1 11/10, M2 B=2, M6 yes).

## rover_terrain_6to12

Model: 12-state terrain rover (ground speed, wheel speed, drive command, terrain term, two-stage heave, grade, chassis pitch, filtered longitudinal acceleration, squat pitch cascade) on a 0.02 rad ramp then level, against the 6-state flat-ground model, lambda 1.
Property: the sloped compliant rover is never faster or ahead of the flat-ground model; slip window 0.25 m/s, heave <= 0.15, chassis pitch + squat <= 0.15; derived aux rows.
Concerns: (a) lines 63 and 103/104: the domain gamma, theta_p in [0, 0.02] together with the MUD guard gamma >= 0.02 and theta_p >= 0.02 pins both to exactly 0.02 on the ramp, so theta_p' = 2 v (gamma - theta_p) = 0 there: the advertised one-wheelbase pitch lag (line 29-30) never acts on the ramp, only on the easing after its top. Route geometry as a domain is acceptable, but the Theta tightness (0.13, analytic 0.12 = 0.02 + 0.1, line 55-56) is set by that pinned grade. (b) line 45: "H = 0.15 wheel radii" while zh's domain is [0, 0.5] and zh' = rho v - zh carries units of m/s x s; state zh's unit once. (c) lines 48-49 and 142: the aux ordering rows u_L <= u_R, w_L <= w_R, zs_R <= zs_L are preserved by identical dynamics on both sides (lines 102/124), so they are free; stated as auxiliary.
Mechanism I agrees (M6 yes).

## sat3w_detumble_phases

Model: 6-state gyrostat (three body rates, three wheel momenta, J = diag(2,4,5)) with DETUMBLE k = 0.5 and FINE k = 0.3, flight manager at 2 s, against the decoupled design model at 1 s with a SAFE sink. The gyrostat equations (lines 17-20) check against Euler's equations with wheel momenta.
Property: the full body's energy w.Jw equals the design model's at every instant through phase handovers (tolerance 0 both ways).
Concerns: (a) lines 40-42: k = 0.5 /s gives wheel torques near 1 N m at the DETUMBLE envelope, two orders above a microsat wheel; sat_detumble_phases discloses this as a stylized time unit (its lines 28-34) and reports the gain/1000 measurement; this header does not. (b) lines 96-101 and 127/132/137: the momentum band |h_i + J_i w_i| <= 2 is a right-only evolve domain, a constraint on the reference's initial state; the left has no band, asymmetric but explained. (c) the two sat files make the same claim with the same letters; this one is the physically consistent form (three wheels absorb three rates).
Mechanisms M I X agree (M2 B=2 with hop, M6 yes, M4 vacuous).
Fix (POLISH): add the stylized-gain paragraph and the gain/1000 result of sat_detumble_phases (lines 28-34) to this header, or point to it.

## sat_detumble_phases

Model: 4-state gyrostat (three body rates, one z-wheel momentum) with isotropic rate damping on all axes, otherwise as sat3w.
Property: energy equality as in sat3w.
Concerns: (a) lines 17-27: the x, y actuators are unnamed "rate dampers of the same authority as the wheel"; the header shows the claim is false at magnetorquer gains (E_L - E_R = +0.067 at 2 s), so the isotropic gain is chosen so that the claim holds ("a requirement of the claim"). Disclosed candidly, but it is a plant tuned to the property; the 3-wheel sibling needs no such assumption. (b) line 28-31: time unit stylized, disclosed. (c) same momentum-band asymmetry as sat3w (lines 114-119).
Mechanisms M I X agree.
No fix if the suite wants a 4-D scaling point beside the 6-D one; otherwise fold into sat3w.

## ventilator_vc_cuffleak

Model: breath clock and lung volume, INSP constant flow 0.4 L/s for 1 s then EXP passive emptying; left has a cuff leak of conductance 0.002 L/s/cmH2O through a resistor network (constants at lines 20-25 reproduce from R_aw, R_tube, C, PEEP, g).
Property: equal breath clocks; in INSP |V_L - V_R| <= 4 mL + 15 % of V_R (ISO delivered-volume accuracy), in EXP |V_L - V_R| <= 0.08 L (ISO PEEP accuracy x C).
Concerns: (a) line 30 / line 113: the relative tolerance 0.004 + 0.15 V_R is negative for V_R < -0.0267 L, and V_R in [-0.4, 0] is admissible at t = 0 (line 59-61, guard lines 86/102), so such pairs are excluded by the row rather than by physics; ISO's 15 % refers to the set tidal volume, not the delivered-so-far volume. Harmless for the breath that matters (V_R >= 0 at the start) but a cleaner row is 0.004 + 0.15 x 0.4 at the end of inspiration or a start condition V >= 0. (b) line 61-63: V - 0.4 t <= 0 is a reachability fact used as a domain (forward invariant, stated); not a physical limit. (c) lines 32-35: applying a ventilator accuracy spec to a leak-induced lung-volume deficit is a reinterpretation, stated.
Mechanism D agrees (M5 3/3 handoffs unsat).

### G4

# Benchmark review G4 (independent, rubric RUBRIC.md)

Scored from benchmarks/suite_v2/<name>/input.txt, docs/paper-numbers/matrix.md and docs/paper-numbers/letters.md only. Line numbers refer to input.txt.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| fuelcell_chp_dos | 3 | 3 | 3 | 3 | POLISH | 7 K is a requirement margin (tightest 5); header concedes the physical claim is 0 and both prunings need the Tin range; garbled sentence at lines 30-31 |
| lit_csf21_vehicle_bus | 4 | 3 | 4 | 3 | KEEP | faithful non-interference instance of CSF'21 Fig. 11/12; departures (1)-(3) only by reference to the sibling file |
| lit_girard08_robot | 3 | 3 | 4 | 3 | KEEP | certified planner is a superset of Fig. 3 (departure 2) and the 0.16 row is left-only; both disclosed |
| platoon_profiles | 4 | 3 | 3 | 3 | POLISH | letter D rests on AEB_L, entered only as a start (lines 9-11, 95-98); batch history clutters the header |
| reactor_feed_wireless | 3 | 3 | 4 | 3 | POLISH | interlock direction (feed rises with T, no high-T stop) and the symmetric 9/9 limits read as design values tuned to 9; certificate is 10x the simulated effect |
| sat_detumble_weak | 3 | 4 | 4 | 3 | KEEP | exact energy equality with a non-copy witness is strong; the 2 s duty cycle (lines 33-36) is an invented period that alone yields M and B |
| syringe_relay_prearm | 4 | 3 | 4 | 3 | KEEP | careful physics; "up to re-timing" dominance of C is weaker than the real-time hazard claim, disclosed |
| train_ato_odometry | 4 | 3 | 4 | 3 | KEEP | 1.11 m/s sits in the 0.06 m/s window [1.07, 1.13) where only the stretch rescues it; M and B not load-bearing (lines 88-89) |
| watertank | 3 | 3 | 4 | 3 | KEEP | the paper's running example; the 3 dm band is around a nominal run sped up 2x, so the reference is not a nominal history |
| watertank_twospeed | 3 | 4 | 4 | 3 | KEEP | both constants are exact tank margins (upper pinned from both sides, lower tightest 1.50); lambda_max = 6 unexplained |

## fuelcell_chp_dos
Model: PEM fuel-cell CHP stack temperature T' = (Tin + rise - T)/120 at three current levels; right = nondeterministic protocol with overlapping bands deciding every 10 s; left = deterministic selection held 20 s by a DoS on the Modbus link (lines 9-22).
Property: the attacked stack stays within 7 K of some protocol-permitted temperature history, Tin equal (lines 24-28, rows 164-166).
Concern: (a) lines 30-37 state the physically true claim is exact (tolerance 0) and that the 5 K floor is "the tool's segment-end obligation, not the attack's effect"; the file's 7 is a requirement margin that only transfers the window [45, 85] when the reference starts inside the steady band [52, 78], which the header half-says (lines 27-30). (b) Lines 69-76: both prunings hold only for Tin ranges inside (38, 58), and [36, 56] / [40, 60] decline at 7, so the domain Tin in [40, 56] (line 13, "a design range of this file") is also the certificate's window. (c) Line 30-31 "The physical content of the smaller than the certificate" is garbled; line 19 "8 K inside its band edges" is true for LOW/HIGH only (MED's thresholds 52/78 are 2 K inside (50, 80)). (d) The certified tolerance set is non-monotone ([5, 8], then 10; lines 53-57), which a reader will find fragile.
Fix: repair lines 30-31 and 19; state the window-transfer reading conditionally (reference starting in [52, 78]); move the Tin-window dependence from "limitation" prose to the Domains paragraph.

## lit_csf21_vehicle_bus
Model: CSF'21 internal-bus car (d, v, temp): left = attacked car, six action x thermostat modes with free thermostat changes; right = genuine car, twelve modes keyed by the message type that delivered the setting (lines 20-30).
Property: distance and velocity equal in every left mode, i.e. the cabin-temperature attacker cannot influence the drive (lines 32-36).
Concern: the witness copies the left's action every cycle (line 47-50); that is the source's non-interference content, so acceptable, but the relational work is the bus constraint only. Deviations (1)-(3) are given only by pointer to lit_csf21_vehicle_thermo (line 38); the v <= 39 Acc cap (line 40) is a tool convenience. Letters X agree with letters.md and matrix (no M1-M5).
Fix: none required (KEEP); optionally inline deviations (1)-(3).

## lit_girard08_robot
Model: Girard-Julius-Pappas planar robot (6-D, written in tracking-error coordinates e, z, w) against the 2-D kinematic planner over six headings (lines 8-37).
Property: planner position equals the robot's controller reference w and the robot's error energy e^2 + 100 z^2 <= 0.16, giving the source's 0.4 precision; 0.1599 declines (lines 39-44; Lie derivative check at line 42 verified).
Concern: departure (2), lines 53-64: the planner gets edges between every pair of overlapping enlarged invariants and guards equal to the enlarged invariants instead of the 0.8 m strips, so what is certified is a 0.4-simulation by a strictly more permissive abstraction than Fig. 3. Departure (6), lines 73-79: the robot's location invariants become entry guards with the whole plane as evolve domain (no physical domain at all, lines 109 etc.), a sampled-switching robot the source does not have. The quadratic row is a unary invariant of the left; the relational row w_L = y2_R is matched by a heading hop plus identical w dynamics.
Fix: none required (KEEP); the header already flags both departures.

## platoon_profiles
Model: one CACC link (g, r), SPORT profile kp 0.18 / kd 0.9 against NORMAL 0.125 / 0.75, same AEB r' = -0.5 r, period 0.1 s (lines 18-57). The re-timing g_S(t) = g_N(1.2 t), r_S(t) = 1.2 r_N(1.2 t) is exact (checked).
Property: SPORT rows = exact re-timing in the two modal coordinates plus left-only floors g_L >= 5 and g_L + 2 r_L >= 5; AEB rows exact at lambda 1 (lines 59-79, rows 151-152).
Concern: D is counted in the headline letters (line 6, letters.md S M D, matrix M5 yes) although lines 9-11 and 95-98 concede that AEB_L is entered only as a start (the handoff SPORT -> AEB is unsat, line 89-91) and that with AEB_L removed the file certifies with S M. The AEB rows compare two identical latched systems (trivial equality). Lines 12-16 are batch history, not benchmark content. Lines 69-70 admit the SPORT rows "carry no tolerance content"; the property's value is the refinement reading only.
Fix: either present D as "mode-dependent rows on a start-only fallback" in the mechanisms line, or drop AEB_L and claim S M; delete lines 12-16.

## reactor_feed_wireless
Model: reactor temperature T' = 0.1 (p + 4k - T) at four feed levels selected by temperature thresholds; right reads every 1 min, left every 2 min (WirelessHART) (lines 11-29).
Property: |T_L - T_R| <= 9 and equal cooling water; 9 = distance from the validated envelope [19, 51] to the limits 10 and 60 (lines 31-39); tightest 8.00, window [8, 10].
Concern: (a) lines 16-19: a feed interlock that admits more feed the hotter the reactor, with no high-temperature feed stop (line 70 "not modeled"), is the opposite of a runaway interlock; the accumulation rationale needs a feed-inventory state the model lacks, and the "exothermic" reactor has no temperature-dependent heat release (linear per level). (b) Lines 31-36: the two limits sit exactly 9 K from both ends of the validated envelope; the boiling point 60 and the stop at 10 are not listed among the "design values of this file" (lines 73-75) though they are. (c) Line 64-65: simulated worst gap 0.87 K against a 9 K certificate.
Fix: mark 60 / 10 degC as design values and say the envelope-plus-9 margin is their origin; either add the high-T feed stop as a declared sink or re-describe the interlock as a semi-batch feed-rate schedule and drop "runaway".

## sat_detumble_weak
Model: left = gyrostat (Euler equations for J = diag(2, 4, 5) with a z-wheel; coefficients verified) at derated gain 0.4; right = decoupled design model at profiles 0.5 / 0.45 / 0.42 plus SAFE sink (lines 17-50).
Property: body energy E_L(t) = E_R(0.8 t) exactly; E' = -0.8 E on the left verified (couplings and wheel terms cancel). States differ, so the witness is not a copy (lines 56-66).
Concern: lines 33-36: the 2 s deployed period is "a design value of this file" invented for the power-saving duty cycle, and it is the sole source of M and B (line 11); line 46-48: one uniform 80 % derating on torquers and wheel is what makes the ratio exact. The right-only momentum band (lines 107-113, evolve 134) is disclosed.
Fix: none required (KEEP); consider citing a duty-cycled ADCS mode to ground the 2 s.

## syringe_relay_prearm
Model: two-channel syringe pump relay (v1, v2, plasma fraction C, driver slack b); left pre-arms channel 2 at 5 mL left, right takes up slack at the switchover (lines 11-39). Rates, driver speed (0.09 mm/min from a 26.6 mm bore) and k = 0.29 /min from a 2.4 min half-life check out.
Property: delivered volumes equal up to re-timing; C equal and b_R <= b_L before syringe 2 delivers; C_R <= C_L from RUN2 on (lines 41-55).
Concern: the "matched instant" after the right's lone 11 min take-up makes C_R <= C_L hold because C_R fell alone (lines 61-63); the real-time hazard claim (the pre-armed relay never leaves less drug in plasma) is the one a clinician would state and it fails only in END, which the header explains indirectly (lines 78-80). The b_R <= b_L row is a certificate artifact (lines 67-72, disclosed). Letters R D agree with letters.md / matrix M5.
Fix: none required (KEEP); one sentence saying why the real-time one-sided claim fails (END_L while the validated relay still delivers) would make the re-timing choice obvious.

## train_ato_odometry
Model: first-order ATO speed loop v' = k (25 - v_meas) at three performance levels; left reads 0.96 v after a wheelset exchange (lines 10-23). ETCS margins and the domain tops 27.08 / 28.21 are sourced (lines 65-69).
Property: 0 <= v_L - v_R <= 1.11 m/s against a design run re-timed per pairing in [0.75, 1.25] (lines 25-37).
Concern: lines 49-54: at real time the claim certifies only from 1.13, so the ETCS requirement 1.11 holds only through the stretch, in a window of width 0.06 m/s; the requirement sentence (lines 28-29) reads as a real-time statement. Lines 88-89: NO_PAIR_STRETCH also certifies with budget 1, so M and B (matrix M2 M3 yes) are exhibited, not load-bearing.
Fix: none required (KEEP); say in the Property paragraph that the real-time bound is 1.13 and the 1.11 is a speed-history claim.

## watertank
Model: the paper's running example: tank x' = k (c - x), right Low / MidEco / MidBoost / High / PumpOff, left with a 3 dm sensor offset, doubled low gain and locked boost (lines 8-35).
Property: |x_L - x_R| <= 3 in every mode; first row tight at 3.00 (Lie-neutral boundary, lines 41-46), second row slack to 1.50.
Concern: the matched nominal run is sped up by lambda = 2 in Low and Mid (line 53-54), so the band is around a nominal trajectory run twice as fast, not a nominal history; the two-channel attack (line 23-31) is constructed so that the gain ratio is exactly 2. Domain not load-bearing (lines 49-51) is good.
Fix: none required (KEEP, running example).

## watertank_twospeed
Model: same attacked tank against a nominal controller whose low fill is staged Fast (gain 2 below 7) / Slow (gain 1 on [7, 10)) (lines 13-39).
Property: x_L <= x_R + 3 (sensor offset = interlock margin) and x_R <= x_L + 2 (underflow margin); upper pinned from both sides (2.99 and 3.01 decline, a PumpOff start becomes admissible above 3), lower tightest 1.50 (lines 41-54).
Concern: minor: lambda_max = 6.0 (line 91) is never explained in either watertank file (needed 2); the P letter comes from a declared edge Fast -> PumpOff that is dead by Fast's own flow (lines 69-73), acceptable as an interlock declaration. Letters S M B P agree with letters.md and matrix M1-M4.
Fix: none required (KEEP).

### G5

# Review G5 (independent, rubric RUBRIC.md; repo read-only)

Files read in full: benchmarks/suite_v2/<name>/input.txt for the ten names below; their rows and `###` sections in docs/paper-numbers/matrix.md; their rows in docs/paper-numbers/letters.md. Line numbers below refer to the benchmark's input.txt. `bound_T` is on the tool's IGNORED list (RelCertifier/Trusted/KeyAudit.lean:17), so its value is never a concern.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_tune_lag | 3 | 3 | 5 | 3 | KEEP | exact modal identity holds only at the one lag tau = 0.32 s chosen to make the slow-root ratio exactly 2 (lines 14-24); honest and tight, but the claim is fragile in a physical constant |
| bottling_fill_strainer | 4 | 4 | 5 | 4 | KEEP | clean physics (integrator fill, 40 ms valve lag), requirement tied to the 2 mL giveaway margin, tight 1.2 derived from (1-0.85) x 8 mL |
| gantry_speed_zones | 4 | 3 | 4 | 3 | POLISH | the claim is an exact time reparametrization (0.00 certifies at lambda_max 3, line 42) so the 10 mm band is slack; verdict block (line 68) still dated to the round-A binary |
| platoon_latency | 4 | 4 | 5 | 4 | KEEP | |Delta g| <= 4 m = J tau / kp, tight and derived; the D letter is carried by an AEB no run enters (lines 5-8), disclosed |
| platoon_linkloss | 4 | 4 | 4 | 4 | KEEP | 0 <= Delta g <= 15 m tight at both ends, fallback modes genuinely exercised; AEB again start-only (lines 43-46), kd_a chosen to keep the CACC poles (line 22) |
| rover_ladder_2to3 | 4 | 3 | 5 | 3 | KEEP | clearance rows are real and tight at offset 0 (lines 48-50); the heading row is an unforced contracting start condition (any value in [0, 0.6] certifies, line 52) |
| rover_ladder_3to6 | 4 | 4 | 5 | 4 | KEEP | pitch row reads the model (tight 0.23 = grade + heave kick, line 52-55; tripled coupling declines); clearance rows chain |
| rover_ladder_8to12 | 4 | 4 | 4 | 4 | KEEP | S comes from the claim form (plan-tolerance rows, lines 86-92) more than from the added dynamics (+0.052 m); left guard v <= c is a load-bearing start condition (lines 110-116), both disclosed |
| tunnel_jetfan_pairout | 3 | 4 | 4 | 3 | POLISH | domain floor u >= 2.6 is admitted "not a physical limit" (line 54) and load-bearing at 2.54 for the NORMAL CO row via the c <= 100 fact (lines 52-53); physics otherwise checks to the digit |
| zone_lightmass_schedule | 4 | 3 | 4 | 3 | POLISH | the 0.5 K row sits 0.015 above a tight value set by the domain's far bound (lines 59-66; 33 degC would decline), reachable gap 0.057 K (line 68); witness copies the left's level (X, lines 88-94) |

## acc_tune_lag
Model: one car's cruise loop a_cmd = k (30 - v) through a first-order powertrain lag tau = 0.32 s; left gain 0.75 /s (aftermarket retune), right 0.5 /s (stock); single CRUISE mode on each side with the engaged envelope as guard (lines 48-62).
Property: the retune's dominant-mode speed u = v + a / r_fast equals the stock car's at twice the elapsed time (exact rows 1-2 at pinned lambda = 2), plus |v_L - v_R| <= 3.34 m/s (tight: 3.33 declines, line 43-44).
Concern: tau = 0.32 s is "the unique powertrain lag at which the retune's dominant time constant is exactly half the stock one" (lines 14-17); at tau = 0.30 s the exact rows DECLINE (line 22). The exact claim therefore holds on a measure-zero set of a plant constant, i.e. a constant tuned to the claim, although the header says so and gives the robust alternative (|u_L - u_R| <= 0.35 at lambda = 7/4, line 23). Mechanism cells agree (S M; M1 M2; letters S M). Units and roots check (lines 20-21).
If changed: state the modal tolerance row at a stock-like tau (0.30 s) instead of the exact identity; otherwise keep, the fragility is disclosed.

## bottling_fill_strainer
Model: rotary filler, metered volume V and valve opening u; FILL (u = 1, V' = Q) then CLOSE at the pre-close volume 994 mL with a 40 ms pneumatic valve lag (u' = -25 u); right Q = 200 mL/s, left Q = 170 mL/s (clogged strainer, 85 %).
Property: the predicted final volume Psi = V + (Q/25) u of the deployed equals the commissioned one minus 1.2 mL (exact), u_L <= u_R, V_L <= V_R, and the deployed fill is at most 2 mL short (the giveaway margin, Directive 76/211/EEC cited, lines 30-33); FILL re-timed at lambda = 17/20 within the carousel's 1.25x sector allowance (line 33-35).
Concern: none of substance. Row (5) at 2 mL is a stated requirement while the tight value 1.20 is also given (line 36); the CLOSE guard conjunct Psi <= 1060 was added for the well-formedness gate but is justified as unreachable-state exclusion (lines 64-71). "degraded-actuator" is really a degraded supply, cosmetic. Cells agree (S I; M1 M6; NO_CUT declines in matrix).

## gantry_speed_zones
Model: two decoupled first-order axis servos x' = 2 (0.5 - x), y' = (0.3 - y) at commissioning; the production program scales both gains by a zone override (3 / 2 / 1 along x), right is one MOVE mode (lines 15-31).
Property: |x_L - x_R| <= 0.01 and |y_L - y_R| <= 0.01 m per left mode up to a per-mode stretch in [1, 3]; the 10 mm is the commissioning clearance margin (lines 35-38).
Concern: a uniform override is an exact time reparametrization of the same vector field, so the relational content is mathematically trivial: tolerance 0.00 certifies with lambda_max = 3 (line 42) and even an arbitrary zone schedule certifies (lines 54-57); the 10 mm band exists only to make the verdict grid-independent (lines 10-13, 44-49). R is carried by the matching mechanism, not by the claim. Clarity: the verdict block (line 68) is "measured 2026-10-26 with the round-A binary" while the claim was changed after round A (lines 10-13); it is ambiguous whether the listed counter-run verdicts were taken on the band form. Cells agree (S M; M1 M2; M6+ vacuous).
Fix: re-measure the verdict block on the current file and binary and date it; optionally add a physical reason the axes are not scaled alike in practice (the non-uniform override variant that DECLINES, line 53) to give the band real content.

## platoon_latency
Model: one CACC link (gap g, range rate r) with kp = 0.125, kd = 0.75; the deployed follower's predecessor-acceleration feed-forward is a 0.2 s first-order lag of the true value, its error e bounded by J tau = 0.5 m/s^2 under the ISO 15622 jerk limit (lines 32-41); modes CACC_UP / CACC_DN (jerk sign) and a latched AEB; right has an ideal link (no e).
Property: |Delta g| <= 4 m (= J tau / kp, the static allowance; 3.99 declines, lines 56-61), two derived modal bands, collision freedom and TTC floor of the deployed, design engaged; AEB rows exact.
Concern: the AEB is reachable only as a start on both sides (lines 5-8, 89-94), so the mode-dependent-rows letter D is produced by a mode no run enters; with AEB removed the file certifies with no letter (line 7-8). The physics behind this (design follower autonomous under ideal feed-forward, lead cruising) is sound and the header says it plainly, but a reader of the D count should know it. Two overlapping verdict blocks (lines 100-111 and 112-119) could be merged. Cells agree (D; M5 yes; M4 vacuous).

## platoon_linkloss
Model: same link; the deployed falls back to radar-only ACC (set point 35 m, kd_a = 0.6 chosen so the poles equal the CACC's, lines 22-23) whenever the link drops, re-engages when it returns, with a two-message timeout (left period 0.2 s vs 0.1 s, lines 39-47); right CACC always up.
Property: 0 <= Delta g <= 15 m (never closer than the design, never more than (h_a - h_c) v_ref farther; both ends tight, lines 68-72), derived modal bands, deployed collision freedom and TTC floor, design engaged; AEB exact.
Concern: as in platoon_latency the AEB is start-only (lines 43-46) and carries D. Secondary: kd_a is picked to make ACC and CACC differ only in set point (line 22-23), which is what makes the stratified bands exact; a plausible design choice but convenient. The SPORT paragraph (lines 24-25) belongs to platoon_profiles and is dead text here. Cells agree (M D; M2 M5).
Fix (cosmetic): drop lines 24-25.

## rover_ladder_2to3
Model: 3-DOF rover (v, s, psi) with zone set points 3 / 5 / 6.5 m/s on the odometer, heading loop psi' = -psi and along-track loss s' = v (1 - psi^2/2), against the 2-DOF point model; synchronous, no mechanism.
Property: v_L <= v_R and s_L <= s_R (clearance transfers; offset 0 is tight in the direction that matters, s_L <= s_R + 1 declines, lines 48-50) and |psi_L| <= 0.35 rad (camera half field of view).
Concern: the heading channel is never excited anywhere on the ladder (psi' = -psi, no disturbance), so the heading row is a start condition kept by contraction: every value in [0, 0.6] certifies (line 52). The rung's real content is the pair of clearance rows, which is modest but genuine (a rover 1 m ahead can be in the faster zone). Cells agree (no letter; all matrix cells no).

## rover_ladder_3to6
Model: L6 (adds pitch, heave, roll with a 1 s suspension and slip/crab losses in s') against L3 (rover_ladder_2to3's left), synchronous.
Property: clearance rows, psi_L = psi_R (identical heading loops), |theta_p_L| <= 0.25 rad (mast tilt-stabilizer range); tight 0.23 = grade 0.15 + heave kick 0.5 x 0.15 (lines 51-55), and tripling the coupling declines.
Concern: none of substance; the roll channel moves on the left but carries no row here (deferred to 6to8 by the ladder plan, line 36-39), fine. Cells agree (no letter).

## rover_ladder_8to12
Model: L12 (second-order heave and roll, tire slip y with compliance 0.03 m per m/s^2 feeding the body lateral acceleration) against L8; stretch range [1, 1.25] from the dispatcher's 80 % crossing-slot rule (lines 74-84); cover at 11/10, budget 2.
Property: clearance rows against the re-timed reference; heading, roll (tight 0.15 vs 0.2), LTR <= 0.8 (tight 0.35), lane |y| <= 0.25 (tight 0.20; 5x compliance declines); plan-tolerance rows on the reference equal to 6to8's left rows so the ladder composes (lines 68-72).
Concern: (a) the stretch is needed mostly by the claim form: the plan-tolerance rows admit a reference at its worst attitude beside a level rover with the same v, s, forcing lambda >= 1.0965 "whatever the step's dynamics" (lines 86-92), while the added dynamics alone gain only 0.052 m in 8 s; S and I persist with the left ODEs replaced by the right's (lines 7-9, 100-101). The header owns this. (b) The left guards carry v <= c, a start condition that is load-bearing (without it DECLINES, lines 110-116); justified as reachable-state closure since set points rise along the route, but it is a guard the proof needs rather than a controller condition. (c) Heading rows are unforced (any value down to 0.05 certifies, line 55). Cells agree (S M I; M1 M2 M6; NO_CUT declines).

## tunnel_jetfan_pairout
Model: 1.6 km tunnel air column u' = a n - k u^2 with ten (right) or eight (left) two-speed jet fans, well-mixed CO c' = e - (u/L) c, procedure clock t with the alarm at 600 s; NORMAL (fans low, c <= 100) then FIRE (fans full, 100 MW fire adds 1.1 ppm/s). Every constant (a = 0.009, k = 0.00171875, steady 3.236 / 3.618 / 6.472 / 7.236 m/s, 70 / 78.3 / 278 / 311 ppm) recomputes exactly from lines 16-26.
Property: NORMAL: clocks equal, u_L <= u_R <= u_L + 0.41, c_R <= c_L <= c_R + 30 ppm (PIARC 70 design + 30 stays under the 100 normal-operation limit), u_L >= 3; FIRE: velocity band 1.42 and u_L >= 3 m/s (critical velocity, NFPA 502). Tight values 0.41 / 1.42 / CO 12.1 given with roots (lines 59-63).
Concern: the domain floor u >= 2.6 m/s is admitted to be "not a physical limit (a tunnel with its fans off has u = 0)" (line 54, lines 98-102) and is load-bearing: the reference's NORMAL guard c <= 100 is kept by the flow only for u >= 2.533, floor 2.54 certifies and 2.53 declines (lines 52-53). The fire requirement was moved into a row (u_L >= 3) precisely to stop the domain carrying it, but the normal-operation row still rests on a floor the header disowns. Everything else (fixed alarm time, no spin-up, no buoyancy) is listed under "not modeled" (lines 27-28). Cells agree (D I; M5 M6; NO_CUT declines).
Fix: give the floor a physical reading and state it as such, e.g. the normal-ventilation minimum duty (the controller never stops all fans while the tunnel is open to traffic; eight fans at low speed hold 3.236 m/s steady, so 2.6 is below every admitted steady state), or make the reference's NORMAL guard well formed without it (a stated row u_R >= 2.6 is already implied by u_R >= u_L >= 3). Then delete "not a physical limit" from line 54.

## zone_lightmass_schedule
Model: lumped zone T' = ((Kp + U)/C) (T_set - T) under a load-compensated proportional reheat law; right closed-loop rate 0.02 /min (medium-mass zone, three EN 15232 levels chosen nondeterministically), left 0.04125 /min (light zone, 165/80 of the rate) with a two-level day/night schedule; stretch pinned at the design ratio 2.
Property: |T_L - T_R| <= 0.5 K against the reference trace replayed at twice the speed; 0.5 K is the EN 15500 control-accuracy class (lines 50-52).
Concern: the row's tight value is 0.0303 x (largest distance from a set point to a domain bound) (lines 59-63): 0.4848 on 5..30 degC, so the 0.5 requirement certifies with 0.015 to spare and would decline with an upper bound of 33 degC or a lower bound of 4 degC (lines 63-66). The header argues 5..30 is the room-sensor span and explicitly rejects the earlier comfort-band domain as "tuned to the claim" (lines 104-106), but the requirement-domain coincidence remains the thing the verdict hinges on; the reachable separation is 0.057 K (lines 66-70). Also the witness copies the left's level at every hop and re-selects it at the extra right decision (X, lines 88-94); the header argues this is what refinement against a permissive strategy means, which is fair, and the dynamics check is not vacuous (0.48 declines). Cells agree (S M B X; M1 M2 M3; B reported as degenerate, line 95-97).
Fix: cite the source of the 5..30 degC instrumented range (a sensor data sheet or the standard's measuring range) in line 64 so the domain is anchored outside the file; otherwise keep.
