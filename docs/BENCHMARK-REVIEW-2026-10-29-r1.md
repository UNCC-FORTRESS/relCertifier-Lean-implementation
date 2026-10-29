# Benchmark review, round 1 (2026-10-29; suite_v2 at 544177e, 49 benchmarks)

Five fresh reviewer agents, 10 benchmarks each, rubric `docs/review-rubric.md` only; the reviewers did not see earlier reviews, scores or fix lists. Findings are reviewer claims; every claim acted on was verified by a tool run first (the round's fix log is in `docs/OVERNIGHT-2026-10-29.md`).

## Ranked table (worst first)

| benchmark | P | R | C | overall | verdict | one-line reason | prev overall |
|---|---|---|---|---|---|---|---|
| `charger_fast_tapers` | 3 | 2 | 3 | 2 | RETHINK | the 2 % constant is tool slack (l.60-67 admits it); physically the deployed never leads the replayed profile, and the CC phase is exponential, not constant current (l.32-34) | 1 |
| `fuelcell_chp_dos` | 3 | 2 | 3 | 2 | RETHINK | with a 20 s hold the deployed trajectory is itself protocol-permitted (bands 8 K / 2 K inside, max drift 4.7 K LOW, 6.3 K HIGH), so the physical tolerance is 0; the "tightest 5.00 = one level step" (l.37-38) is tool slack, and the Tin range is tuned to the pruning (l.53-56) | 3 |
| `rover_terrain_2to4` | 4 | 2 | 4 | 2 | RETHINK | lambda_max 3 is the certificate's need, not a requirement (line 71-75); the omitted row w_L <= v_R makes the claim real-time | 3 |
| `sat_detumble_weak` | 3 | 2 | 5 | 2 | RETHINK | left vector field is the right's scaled by 0.8, so the witness is the left's own trajectory re-timed; profiles 0.45/0.42 exist to force the choice | 3 |
| `turbine_startup_gearratio` | 3 | 2 | 4 | 2 | RETHINK | one-sided claim against an existential reference that may run ahead is near-unary (header admits letters hold at g = 1); loop gains not scaled by the cause | 3 |
| `acc_spoof_lag` | 4 | 3 | 4 | 3 | POLISH | row 1 is sold as the real-time overspeed requirement (l.31-33) but is only certified re-timed at lambda 3/2; the real-time form is not certified | 4 |
| `acc_spoof_limp` | 4 | 4 | 3 | 3 | POLISH | "tightest -0.20" (l.51-54) is only reachable with committed choice; against every driver selection the LIMP x SPORT equilibria force intercept >= 1.1 (l.58 says so itself) | 3 |
| `engine_start_highidle` | 3 | 3 | 4 | 3 | POLISH | ABORT edges from STARTER/LIGHTOFF can never fire (flows rise at 5 %, l.40-43) and the abort rule (l.15) is not how a hung start is aborted; the exact low rows are forced by that artifact (l.24-25) | 3 |
| `h2_refuel_ambientbias` | 4 | 3 | 4 | 3 | POLISH | One-sided top rows at 2.9 where the physical gap is 2.4 (line 41-45, certificate artifact relabelled as a requirement at line 34-36); lambda_max = 6.0 (line 92) unused; duplicate verdict block (lines 67-86) | 3 |
| `platoon_linkloss` | 3 | 4 | 4 | 3 | POLISH | 0.2 s period imposed on every deployed decision incl. the radar AEB trigger to earn M (line 9, 42-43); stale 1.5 s timing (line 101) | 4 |
| `platoon_profiles` | 4 | 3 | 4 | 3 | POLISH | SPORT rows are an exact re-timing true by gain construction (line 25-28), no tolerance; line 13 says it replaced platoon_latency, which is still in the suite | 3 |
| `quad_light_lag` | 3 | 4 | 5 | 3 | POLISH | linear drag k/m = 4.905 /s giving 2 m/s terminal climb under 1 g net thrust is a proxy constant, not a plant parameter (line 12-15) | 4 |
| `quad_light_profiles` | 3 | 4 | 4 | 3 | POLISH | same drag proxy (line 15-21); ECO/SPORT exist on the right only as starts the witness immediately leaves (line 53-57), supplying B and X | 3 |
| `rover_terrain_6to12` | 3 | 4 | 5 | 3 | POLISH | the 0.02 rad "bank" is sized to the creep-floor invariance (line 55-56); squat driven by the accelerometer's lagged report (line 31-35) | 3 |
| `sat_detumble_phases` | 3 | 3 | 5 | 3 | POLISH | gyrostat exact, but k = 0.5 /s on magnetorquers is 2-3 orders off and FINE has no attitude state; witness mirrors the left's phase | 4 |
| `tunnel_jetfan_pairout` | 3 | 3 | 5 | 3 | POLISH | FIRE requirement is met by the domain floor u >= 3.2 (a forward-invariant set, not a physical limit), so the FIRE row carries no smoke-control content | 3 |
| `zone_lightmass_schedule` | 3 | 3 | 5 | 3 | POLISH | domain = comfort band [16, 21] (line 84) is tuned, not physical; 0.152 is tight but tied to no requirement; claim is close to a scaling identity | 2 |
| `elevator_start_discbrake` | 4 | 3 | 4 | 3 | KEEP | exact motion conformance is thin (z, v dynamics identical outside LIFT; R needed even at k_L = k_R, l.51-53) but honest and physical | 3 |
| `gantry_speed_zones` | 4 | 3 | 4 | 3 | KEEP | Sound plant and matching exhibit, but the path equality is exact by construction (line 42: tightest 0.00) and the 10 mm band is grid-independence slack dressed as a clearance requirement (line 36-37) | 3 |
| `lit_csf21_vehicle_bus` | 3 | 4 | 5 | 3 | KEEP | Faithful bus encoding with every deviation stated; source model is a toy car (d' = -v, v' = a) so P is capped | 3 |
| `lit_csf21_vehicle_thermo` | 3 | 4 | 5 | 3 | KEEP | Faithful to Fig. 6 and Def. 5 with deviations (1)-(3) stated; toy plant caps P | 3 |
| `lit_drl_car_stop` | 3 | 3 | 5 | 3 | KEEP | Refinement reduces to guard inclusion (line 54-55) so the witness copies the left; honestly scoped to Open Goal 1 (line 37-38) | 3 |
| `lit_drl_lane_control` | 3 | 3 | 4 | 3 | KEEP | Same guard-inclusion refinement; header carries an unexplained DECLINE for the three-valued leader (line 31-34) that should be resolved or moved out of the header | 3 |
| `lit_freedm_meter` | 3 | 3 | 5 | 3 | KEEP | Nondeducibility holds because a grid-only right certifies (line 46-47): the secret never enters the witness, which is the source's own argument but makes the certified claim weak | 2 |
| `lit_lz21_vehicle_position` | 3 | 3 | 5 | 3 | KEEP | translation-invariant copy witness on an unbounded road (source bound x <= 10 dropped); disclosed, but the certified content is the start pairing only | 3 |
| `rover_ladder_3to6` | 4 | 3 | 5 | 3 | KEEP | honest lambda-1 rung; relational content is thin (losses only slow the rover, psi rows are an identity) but the pitch row is tight and model-reading | 4 |
| `rover_patrol_lag` | 4 | 3 | 5 | 3 | KEEP | 1 m acceptance radius is a requirement with tight evidence (0.59), but the re-timed plus right-only-repositioned "order" claim buys little; tau = 3/16 chosen for rational roots | 3 |
| `sat3w_detumble_phases` | 4 | 3 | 5 | 3 | KEEP | as sat_detumble_phases with wheels on all axes (gain 10x high rather than 1000x); claim content is the no-work cancellation plus phase mirroring | 3 |
| `watertank` | 3 | 4 | 5 | 3 | KEEP | running example; toy plant (a pump that also drains, latched PumpOff never entered) but tight first row and domain-independent certificate | 3 |
| `watertank_twospeed` | 3 | 4 | 5 | 3 | KEEP | same toy plant; both constants tied to stated tank margins with a cause table (s, 4.5 - s) | 3 |
| `acc_tune_lag` | 4 | 4 | 4 | 4 | KEEP | exact dominant-mode identity at stretch 2 is the retune's spec, cause-dependent (0.8 declines), guards are justified hulls | 4 |
| `acc_tune_limp` | 4 | 4 | 4 | 4 | KEEP | exact CRUISE row vs NORMAL plus forced-zero LIMP row; D is rule-counted (l.41-45, disclosed) and the 36 m/s ceiling (l.26) is a bare constant | 3 |
| `bottling_fill_strainer` | 4 | 4 | 4 | 4 | KEEP | 2 mL giveaway requirement with physical tightest 1.2 = (1-0.85)x8 mL; strainer, valve and sector constraints all physical | 4 |
| `flaps_slow_approach` | 4 | 4 | 5 | 4 | KEEP | hardware ratio 1/2, exact flap rows plus a placard-relevant speed row with physical tightest 17.5 = (1-1/2)(S-F); grid dependence disclosed | 4 |
| `furnace_program_timebase` | 4 | 4 | 5 | 4 | KEEP | Physical furnace lag, exact program rows plus a measured-tight load band under a stated uniformity class; only the ten-fold SOAK gain (line 15) is ad hoc | 4 |
| `grid_ffr_dos` | 4 | 4 | 5 | 4 | KEEP | Correct swing-equation constants, tight 0.24 Hz band with an engineering reading; the FFR latch written as a guard x - 2a <= -0.4 (line 16, 98) and the TRIP-less left (line 28) are stated conveniences | 3 |
| `hydro_rejection_gatecal` | 4 | 4 | 5 | 4 | KEEP | Clean droop/swing model, both tolerances traced to dispatch and overspeed requirements with tight bounds measured; REJECT governor is open-loop to no-load gate (line 18-22), stated | 3 |
| `lit_girard08_robot` | 4 | 4 | 5 | 4 | KEEP | source-faithful 0.4-precision simulation, tight (0.1599 declines); only the unary quadratic row is load-bearing, the w = y2 rows are the copying witness | 3 |
| `lit_nahs25_salt_tank` | 4 | 4 | 5 | 4 | KEEP | source's forward distance 3 reproduced, tight (2.99 declines), mode fact I genuinely load-bearing | 4 |
| `platoon_latency` | 4 | 4 | 4 | 4 | KEEP | derived and tight latency allowance J tau / kp = 4 m; AEB rows reachable as starts only, so D is physically inert | 3 |
| `reactor_feed_wireless` | 4 | 4 | 5 | 4 | KEEP | requirement-justified 9 K band with tightness window [8, 10]; P and B genuinely load-bearing; thermal constants are stated design values | 4 |
| `rover_ladder_2to3` | 4 | 4 | 5 | 4 | KEEP | clean clearance refinement (offset 0 tight: +1 declines); heading channel unforced so the 0.35 row is a start condition | 3 |
| `rover_ladder_6to8` | 4 | 4 | 5 | 4 | KEEP | stretch 1.25 tied to a stated timetable with analytic need 1.0965; LTR row is implied by the heading and roll rows (line 61-62) | 3 |
| `rover_ladder_8to12` | 4 | 4 | 5 | 4 | KEEP | same design as 6to8 with a non-redundant LTR row; 31 s of the 40 s default budget (line 126-128) is a flakiness risk, pitch rows not carried to the 12-DOF left | 4 |
| `rover_terrain_4to6` | 4 | 4 | 5 | 4 | KEEP | real-time refinement with every auxiliary row justified; "torque state" u is a speed (m/s) | 3 |
| `syringe_relay_prearm` | 4 | 4 | 5 | 4 | KEEP | real relay scenario, checked units; volume rows are near-tautological by construction, the content is the one-sided C row | 4 |
| `tank_dos_3to1` | 4 | 5 | 5 | 4 | KEEP | requirement-justified 0.8 with bisection evidence that discriminates 30 s from 40 s holds; surge-only demand is the one simplification | 4 |
| `train_ato_odometry` | 4 | 4 | 5 | 4 | KEEP | correct odometry scaling and ETCS margins; the witness may pair the deployed against a design run in another performance level | 4 |
| `ventilator_vc_cuffleak` | 4 | 4 | 5 | 4 | KEEP | clean resistor-network derivation, ISO 80601 bounds; EXP band reads a PEEP accuracy as a mid-expiration volume band | 4 |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 5 | 25 | 19 | 0 |

Verdicts: KEEP 32, POLISH 12, RETHINK 5, DROP 0. Overall >= 4: 19/49 (38 %). Overall < 3: 5.

## Delta vs previous round

Previous histogram (1..5): 1, 3, 30, 16, 0 over 50; this round: 0, 5, 25, 19, 0 over 49.

Up: `acc_tune_limp` 3->4, `charger_fast_tapers` 1->2, `grid_ffr_dos` 3->4, `hydro_rejection_gatecal` 3->4, `lit_freedm_meter` 2->3, `lit_girard08_robot` 3->4, `platoon_latency` 3->4, `rover_ladder_2to3` 3->4, `rover_ladder_6to8` 3->4, `rover_terrain_4to6` 3->4, `zone_lightmass_schedule` 2->3.

Down: `acc_spoof_lag` 4->3, `fuelcell_chp_dos` 3->2, `platoon_linkloss` 4->3, `quad_light_lag` 4->3, `rover_ladder_3to6` 4->3, `rover_terrain_2to4` 3->2, `sat_detumble_phases` 4->3, `sat_detumble_weak` 3->2, `turbine_startup_gearratio` 3->2.

Not in this round: `lit_hypercert_vehicle`.

## Reviewer notes by group

### G1

# Review G1 (independent, rubric RUBRIC.md): acc_spoof_lag, acc_spoof_limp, acc_tune_lag, acc_tune_limp, bottling_fill_strainer, charger_fast_tapers, elevator_start_discbrake, engine_start_highidle, flaps_slow_approach, fuelcell_chp_dos

Sources read: benchmarks/suite_v2/<name>/input.txt (full), docs/paper-numbers/matrix.md and letters.md rows. Mechanism letters in all ten headers agree with letters.md and the matrix cells (checked per file; no disagreement found). Line numbers below refer to input.txt.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_spoof_lag | 4 | 3 | 4 | 3 | POLISH | row 1 is sold as the real-time overspeed requirement (l.31-33) but is only certified re-timed at lambda 3/2; the real-time form is not certified |
| acc_spoof_limp | 4 | 4 | 3 | 3 | POLISH | "tightest -0.20" (l.51-54) is only reachable with committed choice; against every driver selection the LIMP x SPORT equilibria force intercept >= 1.1 (l.58 says so itself) |
| acc_tune_lag | 4 | 4 | 4 | 4 | KEEP | exact dominant-mode identity at stretch 2 is the retune's spec, cause-dependent (0.8 declines), guards are justified hulls |
| acc_tune_limp | 4 | 4 | 4 | 4 | KEEP | exact CRUISE row vs NORMAL plus forced-zero LIMP row; D is rule-counted (l.41-45, disclosed) and the 36 m/s ceiling (l.26) is a bare constant |
| bottling_fill_strainer | 4 | 4 | 4 | 4 | KEEP | 2 mL giveaway requirement with physical tightest 1.2 = (1-0.85)x8 mL; strainer, valve and sector constraints all physical |
| charger_fast_tapers | 3 | 2 | 3 | 2 | RETHINK | the 2 % constant is tool slack (l.60-67 admits it); physically the deployed never leads the replayed profile, and the CC phase is exponential, not constant current (l.32-34) |
| elevator_start_discbrake | 4 | 3 | 4 | 3 | KEEP | exact motion conformance is thin (z, v dynamics identical outside LIFT; R needed even at k_L = k_R, l.51-53) but honest and physical |
| engine_start_highidle | 3 | 3 | 4 | 3 | POLISH | ABORT edges from STARTER/LIGHTOFF can never fire (flows rise at 5 %, l.40-43) and the abort rule (l.15) is not how a hung start is aborted; the exact low rows are forced by that artifact (l.24-25) |
| flaps_slow_approach | 4 | 4 | 5 | 4 | KEEP | hardware ratio 1/2, exact flap rows plus a placard-relevant speed row with physical tightest 17.5 = (1-1/2)(S-F); grid dependence disclosed |
| fuelcell_chp_dos | 3 | 2 | 3 | 2 | RETHINK | with a 20 s hold the deployed trajectory is itself protocol-permitted (bands 8 K / 2 K inside, max drift 4.7 K LOW, 6.3 K HIGH), so the physical tolerance is 0; the "tightest 5.00 = one level step" (l.37-38) is tool slack, and the Tin range is tuned to the pruning (l.53-56) |

## acc_spoof_lag
Model: one car, cruise loop a_cmd = 0.5(30 - v) through a 0.375 s powertrain lag (v' = a, a' = (8/3)(a_cmd - a)); left reads v 25 % high so it aims at 24 m/s; one mode each side, guards are the forward-invariant hulls of the engagement box (l.57-67), 0.1 s period.
Property: v_L <= v_R and u_L <= u_R - 6 with u the dominant-mode speed, at stretch 3/2 (left time t against right time 1.5 t): the spoofed car is the stock car run 3/2 faster aiming 6 m/s lower.
Concern: l.31-33 present row 1 as the overspeed requirement ("must never make the car faster than the unspoofed reference"), which is a real-time statement; the file certifies it only re-timed, and l.49-55 show that the real-time rows which certify at lambda 1 are lower bounds on v_L (shortfall), not the overspeed bound. Row 2 is an equality physically (both dominant modes decay at 1/s after re-timing), so stating it one-sided (l.36 "tight at -6") hides nothing but should say so. tau = 0.375 s chosen for rational roots (l.19-22) is a modeling convenience, disclosed.
Fix: reword l.31-33 to "re-timed overspeed bound" and state that the real-time v_L <= v_R is not certified (or add it at lambda 1 as a separate file); optionally note row 2 holds with equality.

## acc_spoof_limp
Model: 1-D speed loops; left CRUISE v' = 0.625(24 - v) (25 % spoof) with a latched LIMP v' = 0.3(22 - v) at any 2 s decision; right NORMAL/ECO/SPORT 0.5 /s toward 30/27/33 with DISENGAGE below 20 m/s, 1 s period.
Property (both left modes): v_L <= v_R and 0.7 v_R <= v_L + 4 (AASHTO closing-speed bound, chord of the concave stopping-distance bound, l.42-49).
Concern: l.51-54 claim the intercept certifies down to -0.20 and l.54 derives "a margin of 4.2 m/s on the requirement". That needs the cover to commit the reference away from SPORT: at the LIMP x SPORT equilibria (22, 33) the row needs 0.7 x 33 - 22 = 1.1, and l.58 states exactly this closing speed. So the no-choice margin is at most 2.9 m/s, and the stated tightness is in a weaker semantics than the headline "against every driver selection" (l.56-57). Also l.23-28 concede that no letter comes from the spoof (M, B from the 2 s debounce; I from the latch).
Fix: re-measure the intercept bisection under RELCERT_NO_CHOICE=1 and report both numbers at l.51-54; keep the requirement value 4.

## acc_tune_lag
Model: the same lagged cruise loop (tau = 0.32 s, chosen for rational roots, l.14-17) with gain 0.75 (retune) against 0.5 (stock); one mode each side, engagement-box hulls as guards.
Property: u_L = u_R (two rows) at stretch 2: the retuned dominant mode is the stock dominant mode with its time constant halved, exact.
Concern: none substantive. The right guard is a modal hull rather than a speed band because "with a free the reference blocks or leaves the band" (l.50-52): a certificate-driven choice, but it is the reachable hull of a stated engagement box, so acceptable. lambda is searched on [1, 6] (l.72-73) while the sibling acc_spoof_lag pins it; harmless.

## acc_tune_limp
Model: 1-D; left CRUISE v' = 0.75(30 - v) on [20, 36] with latched LIMP v' = 0.3(25 - v); right NORMAL/COMFORT/SPORT (0.5/0.4/0.6 toward 30) plus DISENGAGE; 0.1 s both sides.
Property: CRUISE v_L = v_R at stretch 3/2 (tune = NORMAL 1.5x faster, choice commits the driver to NORMAL); LIMP v_L <= v_R at lambda 1, constant forced by the handoff.
Concern: minor. The 36 m/s "resume ceiling" (l.26, guard l.80) is a bare constant with no source. D is counted only under the 2026-10-27 rule since uniform v_L <= v_R certifies (l.41-45); disclosed, but the letter is thin. The per-mode stretch (3/2 in CRUISE, 1 in LIMP) means the LIMP row compares states at different elapsed times after a re-timed prefix; the header should say that in one sentence.
Fix (optional): source or drop the 36 m/s constant (l.26); one sentence on what v_L <= v_R means after the re-timed CRUISE prefix.

## bottling_fill_strainer
Model: flowmeter-controlled filler, FILL V' = Q (valve confirmed open) until the 994 mL pre-close volume, CLOSE with a 40 ms pneumatic valve (u' = -25 u, in-flight Q/25); left Q = 170 (clogged strainer, 85 %), right Q = 200; 5 ms period; domain V in [0, 1060] brimful.
Property: predicted final volume Psi_L = Psi_R - 1.2 (exact, strengthening), u_L <= u_R, V_L <= V_R, and the requirement V_R - V_L <= 2 mL (giveaway margin, Directive 76/211/EEC), with FILL re-timed at 17/20 within the carousel sector [0.8, 1].
Concern: none substantive. Tightest 1.20 = (1 - 0.85) x 8 mL is physical and the cause dependence is tabulated (l.47-50). The sector bound 1.25x (l.33-35) and the Psi <= 1060 guard conjunct (l.64-71) are stated design values; the latter is physically forced. The exact-ratio grid dependence (l.44-46) is a tool limitation, disclosed.

## charger_fast_tapers
Model: SoC x only; PRECHARGE 0.2(20 - x) on [10, 15), BULK x' = k(100 - x) (k = 0.125 left, 0.1 right), ABSORB slow/fast tapers, FULL, latched FAULT below 10 %; right 0.006 min period, left 0.012 min (decides every other request cycle, l.37-40, "a design value of this file").
Property: against the profile replayed 1.25x faster, x_L <= x_R + 2 (PRECHARGE: x_L <= x_R): the deployed never leads the replay by more than 2 % SoC.
Concern: (1) R: l.60-67 state that c = 2 is set by two tool artifacts (the FAULT x FAULT re-timed pairing and the FULL floor) and that "the charging pairings themselves hold at any positive c"; physically the deployed BULK equals the replayed BULK and its PRECHARGE/ABSORB are slower than the replay, so the deployed never leads at all. The constant is not a requirement and not tight physics; l.46-50 nevertheless call it a "Requirement". (2) P: a constant-current phase is linear in SoC, not x' = k(100 - x) (l.32-34, "a constant-rate BULK was not tested"); the FAULT edges from PRECHARGE and BULK (l.123, l.128, l.151, l.156) can never fire (flows rise at 10 %, l.72-75), so P is produced by unreachable edges. (3) The left period halving exists to produce M (l.37-40).
Fix: either (a) state the claim as the exact re-timed identity in BULK (c = 0) with FAULT removed and the FULL/ABSORB floor handled by the guard x < 99, and present the tool slack as such, or (b) move to a real-time claim with a physical constant (l.52 says the equal-time lead is up to 7 %), which needs a constant-rate BULK and a clocked certificate; otherwise drop. Reword l.46-50 to stop calling 2 % a requirement.

## elevator_start_discbrake
Model: 20 m up-trip with z, v, brake lift b; LIFT holds the car until b >= 0.95, UP speed loop toward 1.6 m/s, APP toward 0.25 m/s from 18 m, STOP v' = -4 v with rest position z + v/4 <= 20.5; drum brake k = 5 (right) vs disc brake k = 50 (left); 0.1 s period.
Property: z_L = z_R and v_L = v_R in every mode, plus b_R <= b_L in LIFT: the retrofit does not change the validated motion profile, up to the reference finishing its slower lift alone (right-only step).
Concern: the motion rows are preserved because the z, v dynamics are identical and independent of b outside LIFT; the only content is that both cars stay held until their own brake confirms. l.51-53 disclose that R is needed by the claim form even at k_L = k_R, so R is not caused by the retrofit. Domains and the STOP conjunct (l.57-64) are physical. l.17 "rest at about 19.96 m" assumes arrival at 0.25 m/s while l.68 says about 0.5 m/s; cosmetic.
Fix (optional): align l.17 with l.68.

## engine_start_highidle
Model: core speed N2 through STARTER (toward 30), LIGHTOFF (toward 55), SELF and IDLE (toward idle), latched ABORT below 5 %; left idle 66 % (high idle), right 62 %; 1 s sequencer.
Property: N2_L <= N2_R in STARTER/LIGHTOFF (start phases unchanged), N2_L <= N2_R + 4 in SELF/IDLE/ABORT (the idle increment), with the reference allowed to run ahead alone.
Concern: ABORT is entered only below 5 % N2 (l.15, guards l.102, l.136) while STARTER drives N2 toward 30 % from >= 5 %, so STARTER -> ABORT and LIGHTOFF -> ABORT (l.80, l.86, l.114, l.120) never fire (l.40-43 confirm); a hung start is aborted on stagnation or EGT, not on N2 falling below 5 %. The forcing of the exact low rows (l.24-25) is by an ABORT start paired against a motoring deployed, an artifact of this unreachable mode, not physics; the low phases have identical dynamics, so N2_L = N2_R there. The +4 bound is physical (equilibria 66 vs 62) and tight.
Fix: drop the never-firing ABORT edges and the ABORT row, or give ABORT a reachable entry (a sequencer time-out needs a clock variable); reword l.15 and l.24-25 accordingly. Letters would lose nothing (P is not counted).

## flaps_slow_approach
Model: flap angle f (10 -> 15 deg at 1 deg/s normal, 0.5 deg/s with one hydraulic system, FCOM half speed) and airspeed V decelerating toward F = 150 kt with flap-drag-dependent rate; S = 185 kt start; 0.1 s period.
Property: f_L = f_R (re-timed at 1/2 while moving, 1 once set), V_L <= V_R (placard side, exact) and V_R <= V_L + 20 kt (operator speed window), tightest 17.5 = (1 - 1/2)(S - F).
Concern: none substantive. The V domain [F, S] is the manoeuvre envelope and its top is load-bearing for the 20 kt window (l.41-42: S = 195 declines), disclosed. The 20 kt source (AFS window around the managed target, l.33-36) is a speed-vs-target window, borrowed for a slow-vs-normal comparison; acceptable as a stated requirement. The exact-grid dependence (l.72-79) is a tool limitation, disclosed.

## fuelcell_chp_dos
Model: stack temperature T' = (Tin + rise - T)/120 with rise 12/17/22 K at LOW/MED/HIGH, Tin constant in [40, 56]; right = protocol with overlapping bands (LOW < 60, MED (50, 80), HIGH > 70), 10 s decisions; left = deterministic bands (< 52, [52, 78], > 78) held 20 s by the DoS.
Property: |T_L - T_R| <= 7 and Tin equal: the attacked stack stays within 7 K of some protocol-permitted trajectory.
Concern: (1) R: the deployed's own trajectory is protocol-permitted under the hold: MED_L is forward invariant inside the MED band (l.73-75); from LOW (T < 52) T rises at most (68 - 40)/120 x 20 = 4.7 K, staying below 60; from HIGH (T > 78) it falls at most (100 - 62)/120 x 20 = 6.3 K, staying above 70. So the protocol can copy the deployed at every 10 s mark and the physical tolerance is 0; the "tightest 5.00 = one level's rise step" and the non-monotone window (l.37-41) are tool slack from the segment-end successor obligation (l.47-52), not physics. The 7 K requirement (l.25-33) is justified, but the benchmark then certifies slack, not the attack's effect. (2) P: the Tin range [40, 56] is tuned so that both prunings exist and both targets are live (l.53-56: [36, 56] and [40, 60] decline); the EN 442 justification is plausible but the dependence is on the certificate, not on physics.
Fix: make the hold physically consequential, e.g. move the deployed's HIGH threshold to 74 and LOW to 56 (l.18-19, l.99, l.111) so that a 20 s hold can carry T out of the held level's protocol band; then the one-level 5 K step is the physical excursion and 7 K is a real margin. Reword l.37-38 to attribute the measured 5.00 correctly. Alternatively use a 30 s hold with the 10 K tolerance (l.65-66), where the deployed genuinely leaves the HIGH band.

### G2

# Review G2 (benchmarks/suite_v2, branch benchmark-fixes), independent reviewer

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| furnace_program_timebase | 4 | 4 | 5 | 4 | KEEP | Physical furnace lag, exact program rows plus a measured-tight load band under a stated uniformity class; only the ten-fold SOAK gain (line 15) is ad hoc |
| gantry_speed_zones | 4 | 3 | 4 | 3 | KEEP | Sound plant and matching exhibit, but the path equality is exact by construction (line 42: tightest 0.00) and the 10 mm band is grid-independence slack dressed as a clearance requirement (line 36-37) |
| grid_ffr_dos | 4 | 4 | 5 | 4 | KEEP | Correct swing-equation constants, tight 0.24 Hz band with an engineering reading; the FFR latch written as a guard x - 2a <= -0.4 (line 16, 98) and the TRIP-less left (line 28) are stated conveniences |
| h2_refuel_ambientbias | 4 | 3 | 4 | 3 | POLISH | One-sided top rows at 2.9 where the physical gap is 2.4 (line 41-45, certificate artifact relabelled as a requirement at line 34-36); lambda_max = 6.0 (line 92) unused; duplicate verdict block (lines 67-86) |
| hydro_rejection_gatecal | 4 | 4 | 5 | 4 | KEEP | Clean droop/swing model, both tolerances traced to dispatch and overspeed requirements with tight bounds measured; REJECT governor is open-loop to no-load gate (line 18-22), stated |
| lit_csf21_vehicle_bus | 3 | 4 | 5 | 3 | KEEP | Faithful bus encoding with every deviation stated; source model is a toy car (d' = -v, v' = a) so P is capped |
| lit_csf21_vehicle_thermo | 3 | 4 | 5 | 3 | KEEP | Faithful to Fig. 6 and Def. 5 with deviations (1)-(3) stated; toy plant caps P |
| lit_drl_car_stop | 3 | 3 | 5 | 3 | KEEP | Refinement reduces to guard inclusion (line 54-55) so the witness copies the left; honestly scoped to Open Goal 1 (line 37-38) |
| lit_drl_lane_control | 3 | 3 | 4 | 3 | KEEP | Same guard-inclusion refinement; header carries an unexplained DECLINE for the three-valued leader (line 31-34) that should be resolved or moved out of the header |
| lit_freedm_meter | 3 | 3 | 5 | 3 | KEEP | Nondeducibility holds because a grid-only right certifies (line 46-47): the secret never enters the witness, which is the source's own argument but makes the certified claim weak |

## furnace_program_timebase

Model: three-segment heat-treatment program (PREHEAT/HEAT/SOAK first-order setpoint generator) driving a load with a 5 min lag, left at 80 % program rate (kap 0.008 vs 0.01, SOAK 0.08 vs 0.1), right as validated.
Property: up to a time stretch in [0.8, 1], the deployed setpoint equals the validated one and the deployed load is within 8 degC of the validated load, with the validated load's tracking envelope (s_R - T_R <= 32, T_R <= s_R) as strengthening rows.
Checks: 32 envelope is sound (d(s-T)/dt <= 6.3 - 0.2 (s-T) < 0 at 32; T never overshoots since every target is approached from below); 6.4 residual = (1 - 0.8) x 32 matches the measured tightest 6.40 (line 41); r-sweep (line 45-47) shows the bound moves with the cause.
Concerns: (a) line 15, SOAK gain 0.1 is ten times the HEAT gain with no stated reason (a real program ramps at a rate then holds; a tenfold filter change at 860 degC is a modelling choice, not a program feature); (b) line 29-30, AMS 2750 Class 3 +-8 degC is a spatial temperature-uniformity class, used here as a tracking tolerance against the validated profile; acceptable as the qualified tolerance but the header should say it is being reused in that role.
Mechanism cells agree: header S I / M1 M6 M6+ = letters.md "S I", matrix.md M1 λ=4/5, M6 and M6+ with load-bearing implied-contraction cuts, NO_CUT and NO_IMPLIED_CUT DECLINED, SYNC DECLINED.

## gantry_speed_zones

Model: two-axis gantry with independent first-order position loops toward (0.5, 0.3); left applies a zone-scheduled uniform speed override (x3, x2, x1 by x-band), right runs at the commissioning gains in one mode.
Property: on each axis the production path stays within 10 mm of the commissioned path, up to a per-left-mode stretch in [1, 3].
Concern (R): since both loops scale by the same factor, the production path is exactly a time reparametrization of the commissioned one (line 32-33), and the header measures the tightest tolerance as 0.00 (line 42). The 0.01 band exists so the verdict does not hinge on the stretch grid (line 10-13); the "10 mm clearance margin" of line 36-37 is asserted to match it, not derived from a stated fixture layout. The claim is therefore a matching exhibit (M1 M2) with a nominally physical tolerance, not a tolerance someone measured. Also, line 68: verdicts were measured with the round-A binary on 2026-10-26, not the branch binary; matrix.md (CERTIFIED 1269 ms, FREE λ=3 B=3, APPROACH λ=2 B=2) does confirm the cover, so the mechanism cells agree (S M / M1 M2 / letters.md "S M").
Minor: APPROACH guard x < 0.45 (line 95) with reach 0.466 (line 29) is consistent; PLACE guard upper bound 0.8 is the travel limit, fine.
If polishing: state the 10 mm margin as a design value of this file, and re-date the verdict block on the branch binary.

## grid_ffr_dos

Model: aggregated swing equation of an island grid (H = 4 s, 5 % droop, damping 1 pu: x' = 6.25 (0.1 a - d) - 2.625 x, constants verified), battery FFR latched at 49.6 Hz with a 0.2 s ramp, generator trip at 48.5 Hz on the right; left supervisor holds each decision 0.3 s (DoS drops two of three commands).
Property: in both left modes x_L <= x_R, x_R <= x_L + 0.24 a_R, a_L <= a_R, d_L = d_R: the attacked island is never above the nominal one and at most the FFR's own support (0.1 / 0.42 = 0.238 Hz) below it once the nominal FFR ramps.
Checks: tightest 0.24 (0.23 declines, line 42); exact claim certifies without the attack and declines with it (line 46-48); P window in d_max (0.168, 0.63) measured (line 54-57); flow at -1.5 Hz with d = 0.3, a = 0 is +2.06 Hz/s as stated (line 29).
Concerns: (a) line 16 and 98, the FFR latch is encoded as the guard x - 2a <= -0.4, a release line that climbs out of the domain once a > 0.7; the factor 2 is an encoding constant with no physical meaning (a real FFR latches on a timer or a reset threshold), and it is what makes the right guards leave a coverage gap (line 63-66). (b) line 28-30, the left has no TRIP mode while the right does; the argument that the deployed trip can never fire is sound but the asymmetry is a modelling convenience that also removes a vacuous row. Neither changes the verdict.
Mechanism cells agree: header M P / M2 M4 = letters.md "M P", matrix.md B=3 covers, pruned NORMAL->TRIP and FFR->TRIP, NO_PRUNE DECLINED, SYNC CERTIFIED.

## h2_refuel_ambientbias

Model: one-variable staged pressure-ramp fill (p' = 0.05 (set - p), stages 20/40/60 MPa, top-off toward end + 0.5, COMPLETE at end, ABORT below 0.5 MPa); right ends at 70.0 MPa, left at 72.4 MPa because the ambient sensor reads 10 K high (70 x (1 + 10/288), verified).
Property: in STAGE1-3 the deployed pressure never leads the reference (p_L <= p_R); in TOPOFF/COMPLETE/ABORT p_L <= p_R + 2.9.
Concerns: (a) R, line 34-36 vs 41-45: the physical overfill is 2.4 MPa (deployed completes at 72.4, reference holds 70.0); the extra 0.5 is admitted at line 41-45 to be a certificate artifact (the top-off's exit at the end pressure cannot be used, so even the unbiased s = 0 case needs 0.50). Line 34-36 nevertheless presents 2.9 as the requirement ("plus the 0.5 MPa top-off margin"), which is the artifact restated as a design number. (b) The top rows are one-sided and the safety reading "ends below 73.4 MPa" (line 36) is implied by the left model alone (every left set point <= 72.9, domain forward invariant, line 63), so the relational content is only "the deployed never exceeds the reference by more than 2.9", with the reference free to complete first. (c) Line 92: lambda_max = 6.0 although every cover is at lambda 1 (line 56, 72) and letters.md records no S; a leftover that widens the stretch search for nothing. (d) Lines 67-86 contain two verdict blocks (2026-10-26 and 2026-10-28) saying the same thing; line 51 refers to engine_start_highidle for no reason a reader of this file can use.
Mechanism cells agree: header R D I / M5 M6 M6+ = letters.md "R D I" with uniform rows DECLINED and handoff 12/12; matrix.md M5 yes, M6 and M6+ yes with NO_CUT and NO_IMPLIED_CUT DECLINED, NO_REPO DECLINED.
Fix (POLISH): set lambda_max = 1.0; reword line 34-36 to "2.4 MPa end-pressure shift plus the 0.5 MPa the certificate needs even at zero bias (see below)" so the number is not sold as a requirement; delete one of the two verdict blocks and the engine_start_highidle aside.

## hydro_rejection_gatecal

Model: hydro unit with gate servo (time constant 4 s), T_m = 8 s, unit self-regulation 1, 5 % droop, on a sequencer clock: ONGRID (speed is the grid's, |w| <= 0.004, gate holds 0.85 load with droop) until t = 20 s, then REJECT (gate to speed-no-load 0.1, unit accelerates on the excess gate); left gate transducer reads 0.02 low, so its loop sits 0.02 more open.
Property: mode-dependent; on the grid the speeds are equal and the gates within 0.027 (+-3 % of rated power via P = (g - 0.1)/0.9); after the rejection the speeds are within 0.09 (overspeed trip 1.30 minus the commissioned peak 1.2055) and the gates within 0.027.
Checks: left ONGRID target 0.87 - 20 w and REJECT target 0.12 are the right ones for g_meas = g - 0.02 (lines 95, 101); tight gate 0.02 = the offset, tight speed 0.02 (line 40-43), uniform rows need 0.18 (line 53-55), offset sweep (line 61-64) crosses the requirement between 0.02 and 0.03.
Concerns: (a) line 18-22, after the breaker opens the governor only drives the gate open-loop to the no-load position and speed is unregulated, so the deployed unit settles 2 % fast forever; a real governor switches to speed control after rejection. The header states that re-synchronization and speed-no-load regulation are not modelled, so this is a stated truncation of the scenario, not an error. (b) The 0.09 speed band is 4.5x the measured tightest; justified by the stated protection margin, acceptable under the rubric.
Mechanism cells agree: header D / M5 = letters.md "D" with ONGRID/REJECT uniform rows DECLINED, "D_rows D_strict"; matrix.md M5 yes 3/3 handoffs, nothing pruned, SYNC CERTIFIED.

## lit_csf21_vehicle_bus

Model: CSF 2021 Sec. VI-C car (d' = -v, v' = a) with thermostat sharing one bus message per cycle; left is the attacked car (thermostat reading arbitrary, six modes with the one-message successor rule), right is the genuine car (twelve modes split by message type so the temperature test gates only thermostat messages).
Property: d and v equal in every left mode: the attacker owning the cabin-temperature reading cannot change the car's motion through the shared bus.
Concern: none on faithfulness; deviations (1)-(4) are stated (lines 38-45), including the source's quirk at temps = T (line 42-45). P is capped at 3 because the source plant is a toy (unit accelerations, no vehicle dynamics), as for all three CSF/dRL files; the bus mechanism is a control-structure exhibit rather than a plant. The A/T mode split (line 28-30) doubles the right state space for a format reason, which the header explains.
Mechanism cells agree: X only; matrix.md λ=1, single segment, nothing pruned, NO_CHOICE DECLINED; letters.md "X".

## lit_csf21_vehicle_thermo

Model: CSF 2021 Fig. 4 car with the Fig. 6 interior thermostat; left attacked (thermostat free), right genuine (Cool at temp >= 20, Heat at temp <= 20); A = B = 1, eps = 1 from the NAHS 2025 follow-up; Coast at v <= 1 and Brk from v >= 1 added on both sides for Assumption 1.
Property: d and v equal in every left mode (the source's Def. 5 equivalence formula, per state).
Concern: none beyond the toy plant (P 3). The direction argument (line 36-40: the converse is immediate because the attacked program contains the genuine one) is correct, and the Coast restriction to v <= 1 (line 48-50) brings the attacked car closer to the source. Line 57 "temperature has no domain" is the source's, fine.
Mechanism cells agree: X only; matrix.md λ=1, single segment, nothing pruned; letters.md "X".

## lit_drl_car_stop

Model: sampled form of the dRL stop-sign refinement: left Accel guarded by Safe_eps (x + v^2/2 + 2v + 1 <= 50), right Accel by Safe (x + v^2/2 <= 50), Coast at v <= 1 and Brake from v >= 1 on both sides, A = B = 1, eps = 1, m = 50.
Property: x and v equal in every left mode: the time-triggered controller refines the permissive one.
Concern (R): the left's mode set is a syntactic subset of the right's (Safe_eps implies Safe, lines 54-55; Coast and Brake identical), so the witness is the left's own action and the certificate exercises only the hop (X). The header says exactly this (line 35-38: Goal 1 only, Goals 2 and 3 not represented) and shows the Prebet-literal file declines for a real reason (line 39-41), so C is exemplary; the benchmark is honest but thin. P 3 for the toy plant with ours-chosen top speed 10 (line 44-47, stated as a well-formedness convenience).
Mechanism cells agree: X only; matrix.md λ=1, single segment, nothing pruned, NO_CHOICE DECLINED; letters.md "X".

## lit_drl_lane_control

Model: sampled dRL local lane control, follower and leader each choosing {A, -B} per cycle (follower also Coast at v_f <= 1), left follower Accel guarded by FM 2011 eq. (7) Safe_eps, right by our Safe (d >= v_f^2/2 - v_l^2/2); state (d, v_f, v_l).
Property: gap and both speeds equal in every left mode (refinement at the identity relation).
Concerns: (a) R, as for car_stop: guard inclusion, witness copies the left's action pair (line 55-59). (b) C, line 31-34: a three-valued leader {A, 0, -B} on both sides DECLINES "at the left mode AccelLCoast after AccelLAccel and AccelLBrake close by choice; the cause is not identified (open)". Identical mode sets on both sides with the same guard inclusion should certify by the same hop; an unexplained decline on a near-identical variant is either a tool incompleteness worth documenting elsewhere or a modelling slip in that variant, and leaving it open in a suite header invites the question. (c) Line 16-17 and 53: Safe is "ours" because LICS 2016 does not print it; stated once, fine.
Fix (if touched): either resolve the three-valued leader decline and state the cause, or move the note to a diagnostics file; the benchmark itself needs no change.
Mechanism cells agree: X only; matrix.md λ=1, nothing pruned, NO_CHOICE DECLINED; letters.md "X".

## lit_freedm_meter

Model: single-transformer FREEDM microgrid (LICS 2018 Fig. 2) with the batS controller, demand d in {0, 1, 2} and renewable r in {0, 1} as per-cycle mode choices, battery B in [0, 10] private, cumulative meter E public; twelve modes per side (battery or grid serves the demand).
Property: initial-state nondeducibility of B: E_L = E_R in every left mode from every pair of battery levels.
Concern (R): the witness never uses the battery; a grid-only right certifies (line 46-47) because for each left net draw in {-1, 0, 1, 2} a grid mode with that draw exists (line 43-44). This is the source's own argument for Prop. 11, but it means the certified claim is "the right can reproduce any draw by choosing its own demand and renewable", with the secret playing no role; the left's battery modes all have E' = 0 and are matched by GridD0R0 or GridD1R1 regardless of B. Modes BatD0R0 and BatD1R1 (lines 70-74, 85-89) are dynamically identical to GridD0R0 and GridD1R1 and could be dropped without loss. Deviations (1)-(4) are stated carefully (lines 18-39), including that the capacity test admits a zero-net cycle at a full battery that the source's does not (line 28-30); the leaky batI counterpart exists as a negative benchmark (line 53).
Mechanism cells agree: X only; matrix.md λ=1, single segment, nothing pruned, NO_CHOICE DECLINED; letters.md "X".

### G3

# Review G3 (independent, rubric RUBRIC.md)

Benchmarks: lit_girard08_robot, lit_lz21_vehicle_position, lit_nahs25_salt_tank, platoon_latency, platoon_linkloss, platoon_profiles, quad_light_lag, quad_light_profiles, reactor_feed_wireless, rover_ladder_2to3. Line numbers refer to `benchmarks/suite_v2/<name>/input.txt`. Mechanism letters in every header agree with `docs/paper-numbers/letters.md` (X; X; I; D; M D; S M D; S M; S M B X; M B P; --) and with the matrix cells M1-M5 of `docs/paper-numbers/matrix.md`.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| lit_girard08_robot | 4 | 4 | 5 | 4 | KEEP | source-faithful 0.4-precision simulation, tight (0.1599 declines); only the unary quadratic row is load-bearing, the w = y2 rows are the copying witness |
| lit_lz21_vehicle_position | 3 | 3 | 5 | 3 | KEEP | translation-invariant copy witness on an unbounded road (source bound x <= 10 dropped); disclosed, but the certified content is the start pairing only |
| lit_nahs25_salt_tank | 4 | 4 | 5 | 4 | KEEP | source's forward distance 3 reproduced, tight (2.99 declines), mode fact I genuinely load-bearing |
| platoon_latency | 4 | 4 | 4 | 4 | KEEP | derived and tight latency allowance J tau / kp = 4 m; AEB rows reachable as starts only, so D is physically inert |
| platoon_linkloss | 3 | 4 | 4 | 3 | POLISH | 0.2 s period imposed on every deployed decision incl. the radar AEB trigger to earn M (line 9, 42-43); stale 1.5 s timing (line 101) |
| platoon_profiles | 4 | 3 | 4 | 3 | POLISH | SPORT rows are an exact re-timing true by gain construction (line 25-28), no tolerance; line 13 says it replaced platoon_latency, which is still in the suite |
| quad_light_lag | 3 | 4 | 5 | 3 | POLISH | linear drag k/m = 4.905 /s giving 2 m/s terminal climb under 1 g net thrust is a proxy constant, not a plant parameter (line 12-15) |
| quad_light_profiles | 3 | 4 | 4 | 3 | POLISH | same drag proxy (line 15-21); ECO/SPORT exist on the right only as starts the witness immediately leaves (line 53-57), supplying B and X |
| reactor_feed_wireless | 4 | 4 | 5 | 4 | KEEP | requirement-justified 9 K band with tightness window [8, 10]; P and B genuinely load-bearing; thermal constants are stated design values |
| rover_ladder_2to3 | 4 | 4 | 5 | 4 | KEEP | clean clearance refinement (offset 0 tight: +1 declines); heading channel unforced so the 0.35 row is a start condition |

## lit_girard08_robot
Model: Girard-Julius-Pappas planar robot (double integrator + dynamic tracking controller, written in error coordinates e, z, w; lines 107-140, derivation checked: z' = -z/2 - e/200 is correct) against the 2-D kinematic planner (lines 146-180), six headings, planner guards enlarged by 0.4.
Property: the planner's point equals the controller reference (w_L = y2_R) and the robot's tracking energy e^2 + 100 z^2 <= 0.16, i.e. |y1 - y2| <= 0.4 (lines 183-188); tight, 0.1599 declines (line 42, Lie derivative -0.16 - 2 e.v checked).
Strongest concern: the only relational rows are the equalities the witness satisfies by copying w (committed hop into the robot's heading, line 81-83); the load-bearing row is unary on the left. This is the source's relation, so acceptable. Departures (2), (3), (6) (extra planner edges, whole-plane evolve on both sides, lines 109, 149) make the certified abstraction weaker than Fig. 3 and are disclosed (lines 53-79).
Fix: none required.

## lit_lz21_vehicle_position
Model: the Liu-Zamani single-lane vehicle, x' = v, v' = u in {-0.05, 0, 0.05} held 1 s, both sides (lines 90-128); left = secret run, right = non-secret partner.
Property: v_R = v_L and x_R = x_L + 1 (lines 131-133): a partner 1 m ahead (delta = 1, the source's intruder precision) exists for every secret run.
Strongest concern: the relation is preserved by any identical input because the dynamics are translation-invariant in x (header admits it, line 33), and the partner is the exact copy (line 46); the source's bound x <= 10, which is what makes the source's claim need a non-copying partner, is dropped (line 38-43, evolve line 93). The certified claim is the unbounded-road variant with three input levels (line 48-55), weaker than the source's. All of this is candidly stated, so C is exemplary; R stays at 3 because the witness trivially copies the left.
Fix: none required for KEEP; if a stronger literature claim is wanted, restore x <= 10 on both evolve domains and give the right a stop/hold mode so the partner may lag inside [0, 1] of the secret run (a model change, RETHINK scope).

## lit_nahs25_salt_tank
Model: the NAHS'25 brine tank, xp' = 0.1 (25 - xp) in On, 0 in Off; left = controller on an attacked reading (On if xp >= 22, Off if xp < 28, lines 75-85), right = genuine (threshold 25, lines 91-101); no evolve domain, as the source.
Property: |xp_L - xp_R| <= 3 with both tanks above the On equilibrium 25 (lines 104-105): a 3 lb reading error moves the salt by at most 3 lb.
Strongest concern: the lower bounds xp >= 25 restrict the claim to the post-settling region (they exclude the genuine Off entirely, line 60); justified by the source's pre xp = 50 and invariant (line 27-28), and the other band side is slack (c' = 0 certifies, line 31) and disclosed. The I letter is real: NO_CUT and NO_IMPLIED_CUT decline (line 58-59, matrix M6/M6+ agree).
Fix: none.

## platoon_latency
Model: CACC follower with the predecessor-acceleration feed-forward delayed 0.2 s, modeled by a first-order lag whose error e obeys e' = +-2.5 - 5 e (lines 127, 132; W = J tau = 0.5 m/s^2 domain, line 129, forward invariant), against the ideal-link follower (lines 144-153); shared radar AEB on 0 <= g + 2 r < 5.
Property: |g_L - g_R| <= 4 m (the static allowance J tau / kp, tight: 3.99 declines, line 57), modal forms at 2 W and 4 W, deployed gap floor 5 m and TTC floor, design engaged; AEB exact (lines 155-157).
Strongest concern: the AEB mode is unreachable from the related pairs by construction (rows keep g_L + 2 r_L >= 5, line 155; design CACC -> AEB pruned, line 90-91; no actuator saturation, so the ideal CACC cancels any predecessor manoeuvre), so the AEB rows (line 157) are exercised by identical starts only and the D letter rests on a physically inert mode. Header states the facts (lines 89-91, 105) but sells D (line 4-5) without saying the differing row is start-only. Minor: jerk strictly between +-J (a cruising predecessor) is not a run of the model (line 130); covered by convexity, stated at line 42-43.
Fix (optional, within KEEP): one sentence at line 4-5 saying the AEB rows are reachable only as starts.

## platoon_linkloss
Model: the same follower with a radar-only ACC fallback (set point 35 m, line 128) entered on V2V loss, deployed decision period 0.2 s (line 121) against the design's 0.1 s (line 139); AEB as above.
Property: 0 <= g_L - g_R <= 15 m = (h_a - h_c) v_ref, tight on both ends (line 68-69), modal forms in [0, 15 rho] (verified: Q_0.25' = -0.5 Q + 1.875), floors; AEB exact (lines 151-153).
Strongest concern: the 0.2 s period is applied to the whole deployed decision loop, including the radar AEB trigger (line 42-43), although the two-message timeout justifies only the CACC/ACC switch; line 9 states that the period was changed in batch I9 to produce the letter M (the equal-period file had D only). Harmless in effect because the AEB is never entered from the rows (line 87-93), but it is a constant chosen for the letter. Line 101-102 reports 1.5 s where letters.md measures 0.6 s.
Fix: justify the 0.2 s period as the deployed supervisor's rate for every decision (or state that the AEB-trigger delay is moot since the rows keep the TTC floor), and refresh the timing at line 101.

## platoon_profiles
Model: the follower in SPORT (kp 0.18, kd 0.9, line 111) against NORMAL (kp 0.125, kd 0.75, line 124); lambda = 6/5 for the SPORT pairing, 1 for the AEB pairing (lines 104-105).
Property: g_L(t) = g_R(1.2 t), r_L = 1.2 r_R exactly (four equalities, line 134) plus the deployed's gap and TTC floors; AEB exact (line 135).
Strongest concern: the SPORT gains are defined as the exact bandwidth scaling of NORMAL (line 25-28; checked: 1.44 kp, 1.2 kd), so the exact re-timing rows are true by construction and the property carries no tolerance; the relational content is the identification of lambda and the modal coordinates. The D letter again rests on the start-only AEB (line 78-79 says so). Line 13 states the file "takes the place of platoon_latency", but platoon_latency is in the suite (matrix row 28, letters row 26).
Fix: correct line 13; state at line 6-9 that the AEB rows are start-only. If a tolerance is wanted, a SPORT profile with the same kd and 1.44 kp (same bandwidth, lower damping) would give a non-exact claim.

## quad_light_lag
Model: climb with motor thrust lag, a' = 10 (a_cmd - a), w' = a - (k/m) w, h' = w; left is the 20 %-lighter airframe (a_cmd 14.715, k/m 6.13125; line 72), right the reference (9.81, 4.905; line 80); lambda pinned 6/5 (lines 65-66, justified lines 20-24).
Property: |h_L(t) - h_R(1.2 t)| <= 0.8 m (PX4 NAV_MC_ALT_RAD) with the conserved steady-climb gap Psi in [-0.16, 0.16] (line 85; conservation d/dt [h + ((w - w_t) + tau (a - a_cmd))/(k/m)] = w_t checked); tightness by bisection (lines 42-46).
Strongest concern: a linear drag k/m = 4.905 /s that caps the climb at 2 m/s under a net 1 g of thrust (line 13) is not a quadrotor's aerodynamics (a 2 m g thrust climbs far faster); k is a proxy for the climb-rate loop, and the 1.25 scaling of k/m with mass (line 15) is only right under a loop-gain reading (K/m). Domains are the terminal rates themselves (line 73-74, 81-82), which the proxy fixes. Everything else (lambda pinning, row derivation, Psi sign flip) is clearly stated.
Fix: header lines 12-15: say that k w models the closed-loop climb-rate response (a P velocity loop designed for m_R), not aerodynamic drag, and why both T/m and k/m scale by 1.25 under that reading.

## quad_light_profiles
Model: the lag-free lighter airframe (w' = 14.715 - 6.13125 w, line 96) against a reference with pilot-selectable climb profiles NORMAL/ECO/SPORT (lines 104-117, complete graph); lambda pinned 6/5.
Property: |h_L(t) - h_R(1.2 t)| <= 0.8 m against the NORMAL profile, with Psi <= 0.8 and 1.2 w_R <= w_L (line 119; the climb-rate row checked to hold for w_R <= 2).
Strongest concern: same drag proxy as quad_light_lag (line 15-21). Also, the ECO and SPORT reference modes are admissible starts from which the witness immediately hops to NORMAL (line 53-57); they are never used by the witness and exist on the right to produce B and X (line 5-9 says so). The scenario (deployed must be matched by some pilot selection) is legitimate, but the branching is decorative. Timing 0.5 s at line 76 vs 0.2 s measured, fine.
Fix: same header fix as quad_light_lag; under the loop-gain reading ECO/NORMAL/SPORT become climb-rate set points 1.6/2.0/2.4 m/s (7.848 = 4.905 x 1.6 etc.), which is a cleaner statement than "90 %/110 % thrust" (line 20-21).

## reactor_feed_wireless
Model: CSTR temperature T' = 0.1 (p + 4 k - T) at four feed levels keyed on T thresholds 25/35/45 (lines 119-141), coolant p in [15, 35] constant, T in [15, 60] (boiling), deployed sampled every 2 min (line 117) vs validated every 1 min (line 145).
Property: |T_L - T_R| <= 9 K and p_L = p_R (lines 172-175): the deployed stays within the margin that separates the validated envelope [19, 51] from the boil (60) and the reaction-stop (10) limits; tightest 8.00, window [8, 10] (lines 36-39).
Strongest concern: the inductive 9 K envelope is far above the simulated worst gap 0.87 K (line 64-65); the header discloses it and ties 9 to the requirement, so acceptable. Thermal constants and thresholds are design values of the file (line 73-74), not a cited reactor; the feed-up-with-temperature interlock is plausible for accumulation prevention but a real plant would add the high-T trip (stated not modeled, line 70-72). P and B are genuinely load-bearing (NO_PRUNE declines, line 94; letter windows line 76-79).
Fix: none.

## rover_ladder_2to3
Model: rover L3 (v, s, psi; s' = v (1 - psi^2/2), psi' = -psi, lines 96-108) against the point model L2 (psi pinned at 0 by evolve, lines 118-132); three speed zones on the odometer s.
Property: v_L <= v_R and s_L <= s_R (the rover never faster or ahead of the reference, so reference clearances transfer) and |psi_L| <= 0.35 (lines 136-138); offset 0 tight in the only non-trivial direction (s_L <= s_R + 1 declines, line 48-50).
Strongest concern: the heading channel is unforced (psi' = -psi, no disturbance or curvature), so the rung's new row is a start condition that any bound in [0, 0.6] satisfies (line 51-52, admitted); the clearance rows carry the content (v_L <= v_R needs the zone argument s_L <= s_R => c_L <= c_R, which holds since the set points increase along the route, line 11-12). Header "mechanisms: none" matches letters "--".
Fix: none (a bounded heading disturbance would make the 0.35 row load-bearing, but the rung is honest as is).

### G4

# Review G4: rover ladder, rover patrol, terrain chain, satellite detumbling

Rubric: scratchpad/review-r1/RUBRIC.md. Repo read-only. Sources read: benchmarks/suite_v2/<name>/input.txt (full), docs/paper-numbers/matrix.md rows 34-44, docs/paper-numbers/letters.md rows 32-42. Line numbers below are input.txt header lines.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| rover_ladder_3to6 | 4 | 3 | 5 | 3 | KEEP | honest lambda-1 rung; relational content is thin (losses only slow the rover, psi rows are an identity) but the pitch row is tight and model-reading |
| rover_ladder_6to8 | 4 | 4 | 5 | 4 | KEEP | stretch 1.25 tied to a stated timetable with analytic need 1.0965; LTR row is implied by the heading and roll rows (line 61-62) |
| rover_ladder_8to12 | 4 | 4 | 5 | 4 | KEEP | same design as 6to8 with a non-redundant LTR row; 31 s of the 40 s default budget (line 126-128) is a flakiness risk, pitch rows not carried to the 12-DOF left |
| rover_patrol_lag | 4 | 3 | 5 | 3 | KEEP | 1 m acceptance radius is a requirement with tight evidence (0.59), but the re-timed plus right-only-repositioned "order" claim buys little; tau = 3/16 chosen for rational roots |
| rover_terrain_2to4 | 4 | 2 | 4 | 2 | RETHINK | lambda_max 3 is the certificate's need, not a requirement (line 71-75); the omitted row w_L <= v_R makes the claim real-time |
| rover_terrain_4to6 | 4 | 4 | 5 | 4 | KEEP | real-time refinement with every auxiliary row justified; "torque state" u is a speed (m/s) |
| rover_terrain_6to12 | 3 | 4 | 5 | 3 | POLISH | the 0.02 rad "bank" is sized to the creep-floor invariance (line 55-56); squat driven by the accelerometer's lagged report (line 31-35) |
| sat_detumble_phases | 3 | 3 | 5 | 3 | POLISH | gyrostat exact, but k = 0.5 /s on magnetorquers is 2-3 orders off and FINE has no attitude state; witness mirrors the left's phase |
| sat_detumble_weak | 3 | 2 | 5 | 2 | RETHINK | left vector field is the right's scaled by 0.8, so the witness is the left's own trajectory re-timed; profiles 0.45/0.42 exist to force the choice |
| sat3w_detumble_phases | 4 | 3 | 5 | 3 | KEEP | as sat_detumble_phases with wheels on all axes (gain 10x high rather than 1000x); claim content is the no-work cancellation plus phase mirroring |

## rover_ladder_3to6

Model: 6-DOF rover (speed loop, heading loop, first-order pitch/heave/roll settling to grade and cross-slope, quadratic progress losses) against the 3-DOF reference (attitude pinned at 0), three odometer zones, lambda = 1.
Property: the rover is never faster or farther than the reference, headings coincide, and pitch stays within the 0.25 rad stabilizer range (tightest 0.23, analytic 0.225, heave-3x variant declines).
Concern: the relational rows are near-identities: v_L <= v_R holds with identical loops, psi_L = psi_R is literally the same ODE, and s_L <= s_R follows from non-negative losses. The pitch row is a unary left invariant (theta_p' = -theta_p + 0.15 + 0.5 z with |z| <= 0.15). Line 46-47 cites "s_L <= s_R + 1 DECLINES" as if it were evidence; a weaker claim declining says only that it is not inductive (the rover 1 m ahead can be in a faster zone), not that the row is tight. Loss coefficients 0.3, 0.2 in s' (line 20-21) are stylized, stated as such.
Fix (optional): drop the s_L <= s_R + 1 remark or label it as a non-inductive weaker claim.

## rover_ladder_6to8

Model: 8-DOF rover (yaw and pitch inertia in the cascade chart) against the 6-DOF reference; stretch range [1, 1.25] from a dispatch timetable (slot opens at 80 % of plan time, line 71-82).
Property: rover never faster or farther than the re-timed reference; heading, pitch (tight 0.23), roll (tight 0.14 vs 0.2 requirement), LTR <= 0.8 (tight 0.22); plan tolerances on the reference's attitude.
Concern: the LTR row is implied by the heading and roll rows already in the invariant (8 x 0.7 / 9.81 + 0.2 = 0.771, line 60-63), so it is carried for the requirement list rather than certified by the dynamics; the heading rows certify at any value (line 53-54), so they are inductive-trivial boxes with no disturbance input. The left guard conjunct v <= c (lines 147, 153, 159) is a reachability invariant used as a start restriction; the header admits it is load-bearing (line 110-114). All three are disclosed; the stretch is the strong part: a requirement-backed bound, an analytic need (1.0965), and a cause test (the added inertia gains +0.147 m in 6 s, line 90-92).
Fix: none required; the LTR row could be marked "consequence" in the header line 60 to avoid counting it as a certified requirement.

## rover_ladder_8to12

Model: 12-DOF rover (heave and roll inertia, tire-slip offset y driven by centripetal plus gravity load) against the 8-DOF reference; same timetable stretch.
Property: clearance against the re-timed reference; heading, roll (tight 0.15), LTR including the slip acceleration (tight 0.35, not implied by the other rows), lane 0.25 m (tight 0.20, compliance-5x variant declines); plan tolerances equal to 6to8's left rows, so the chain composes.
Concern: (a) line 126-128: 31 s of the 40 s default budget, CPU-bound on the stretch grid; a loaded machine turns this CERTIFIED into a timeout, so the headline suite number is fragile. (b) the 12-DOF left carries no pitch rows (theta_p, omega_theta are in the model but not in the invariant, line 191), so the composed chain never certifies the pitch requirement on the deployed 12-DOF model; 6to8 certifies it only on the 8-DOF left. (c) The ODE for omega_phi (line 151) matches the header's a_b = a + y'' derivation; checked.
Fix: run this file with RELCERT_TIME_BUDGET_MS above the default in the suite script; optionally add the two pitch rows to the left (cascade contraction, cheap) so the chain top carries every requirement.

## rover_patrol_lag

Model: patrol rover with first-order motor lag (tau = 3/16 s) against the lag-free planning model, four odometer zones with a switchable MEDIUM profile, stretch [1, 3/2] plus right-only repositioning.
Property: the lagged rover is never more than 1 m (waypoint acceptance radius) ahead of the matched plan run, with a look-ahead-odometer strengthening P_L <= P_R + 0.375 derived from tau x a_max.
Concern: the claim is stated against a plan that may be re-timed by up to 3/2 and advanced alone (line 39-45, 57-64); with repositioning, "every waypoint the rover reaches has already been registered in the matched plan run" holds against a plan that was moved ahead to make it hold, so the order statement has little operational content. The header itself shows the letters come from the 1 m slack and not from the lag (line 7-10, 66-71), and that the two-sided version a dispatcher would want DECLINES (line 52-54). tau = 3/16 is picked for rational roots (line 22-23), not from a motor. The 1 m requirement, its tightness (0.59, line 44) and the 0.375 derivation are good.
Fix: none required for KEEP; a header sentence saying what the re-timed and repositioned order claim guarantees to the dispatcher (a lower bound on the rover's arrival time at each waypoint) would make the R case.

## rover_terrain_2to4

Model: 4-DOF terrain rover (wheel-speed loop at 3 /s, ground speed through traction stiffness, drag and sinkage) against the 2-DOF no-slip plan (v' = 3 (c_T - v)), three terrain zones; lambda in [1, 3].
Property: rover never faster or farther than the plan re-timed by up to 3; slip window 0 <= w - v <= 0.25 (tight 0.21, analytic 0.21).
Concern: lambda_max = 3 has no requirement behind it; line 67-75 derive it from the largest ratio "the chain can need" ((mu + r)/3 = 2.68) plus margin, i.e. from the certificate. A plan clock allowed to run 3x faster makes the clearance claim nearly content-free (the plan on PAVED passes every stop line eventually; the bound only says the rover's arrival time is at least a third of the plan's). The stretch is needed only because the natural auxiliary row is missing: the plan's v_R obeys the same loop as the rover's w_L (w' = 3 (c_T - w), line 28 vs line 24), so w_L <= v_R is inductive given s_L <= s_R (c_L <= c_R along the route) and the left cut w <= c_T, and with it v_L <= w_L <= v_R and s_L <= s_R hold in real time; the synchronous failures come from starts with w_L > v_R, which the row excludes. rover_terrain_4to6 already uses exactly this kind of row (w_L <= w_R). Line 12-14 shows the batch chose the 3x re-timing over a real-time form to keep letters S M.
Fix: add w[l] <= v[r] to the three rows (lines 146-148), set lambda_max = 1, re-measure; expect CERTIFIED under SYNC with letters I, and the chain statement (line 63) becomes real-time end to end. If an S exhibit is wanted it should not come from omitting a row.

## rover_terrain_4to6

Model: adds a lagged drive state u (u' = 4 (c_T - u)), wheel w' = 3 (u - w), and a first-order heave envelope zh' = rho_T v - zh to rover_terrain_2to4's left; right is exactly that left; lambda = 1.
Property: lagged rover never faster or farther than the ideal-drive model; slip window (tight 0.21); heave below the 0.15 bump stop (tight 0.13, analytic 0.125); auxiliary orderings w_L <= w_R, zs_R <= zs_L, w_L <= u_L, each shown necessary.
Concern: line 2 and 17-18 call u the "motor torque state" but it is a speed reference in m/s compared with w and c_T (guards u <= c_T, line 78); the heave "amplitude" zh' = rho v - zh is an envelope abstraction, not a suspension model (line 19-20). Neither changes the certificate. The zs_R <= zs_L ordering across zones is sound (Z_T decreases along the route).
Fix: rename u to "drive speed reference (motor lag)" in lines 2, 17; no constant change.

## rover_terrain_6to12

Model: adds the bank grade gamma (0.02 rad on MUD, easing at 0.5 /m after), chassis pitch lagging by one wheelbase, slope load -9.81 theta_p on v', second-order heave, a 0.2 s lagged acceleration ax, and a squat pitch cascade driven by ax; right is rover_terrain_4to6's left; lambda = 1.
Property: sloped compliant rover never faster or farther than the flat 6-DOF model; slip window (tight 0.24), heave 0.15 (tight 0.13), body pitch theta_p + phs <= 0.15 (tight 0.13, analytic 0.12); auxiliary rows with derived constants ax <= 2.0 = mu_PAVED sigma, omega_phs <= 0.1.
Concern: (a) line 15 calls a 0.02 rad (1.1 degree) slope a "bank" the rover "climbs out of"; line 55-56 shows the number is what keeps v' > 0 at the creep floor (0.375 - 0.12 - 0.196 > 0), i.e. a model constant sized to the domain's forward invariance, and it also sets the Theta tightness (0.02 + 0.1). (b) line 31-35: ax is "the acceleration as the accelerometer reports it (0.2 s lag)" yet the suspension squat is driven by that sensor signal; squat follows the drive force, not a report. (c) In MUD the guard gamma >= 0.02 with the domain gamma <= 0.02 pins the grade (line 95-96), fine but worth saying.
Fix: header only: call the stretch a gentle ramp and state the grade is the steepest the creep floor climbs; describe ax as the filtered body acceleration (drivetrain build-up) rather than the accelerometer's report, or drive phs by the v' expression directly if the file is re-run.

## sat_detumble_phases

Model: gyrostat (J = diag(2,4,5), z-wheel) with magnetorquer rate damping k = 0.5 /s (DETUMBLE) and k = 0.3 /s (FINE, E <= 0.125 entry), 2 s flight decisions, against the decoupled design model at 1 s with an added SAFE sink; lambda = 1.
Property: body energy E = w.Jw of the full body equals the design model's at every instant through phase handovers (exact; declines with one coupling term removed, line 64-66).
Concern: (a) line 17, 39: tau_i = -k J_i w_i with k = 0.5 /s is up to 0.7 N m from magnetorquers on a 60 kg satellite, 2-3 orders above real dipole torques; the detumble time constant of 2 s is a stylized time unit, not stated as such. (b) line 41-45: "fine pointing" has no attitude state; FINE is a weaker rate damper with a rate envelope as capture criterion. (c) R: both sides satisfy E' = -2kE in matching phases, so the relational content is the no-work cancellation plus the witness committing to the deployed's phase (line 68-76); the design model never decides anything the flight did not. Honest and exact, but thin. Equations checked against Euler's equations with a z-wheel: correct.
Fix: header: either declare the time unit scaled (or make the x, y actuators wheels/thrusters) and call FINE a "fine rate-damping phase"; no constant change needed for the certificate.

## sat_detumble_weak

Model: both sides the decoupled design model; left derated k = 0.4 /s at 2 s decisions, right three power profiles (0.5, 0.45, 0.42) plus SAFE at 1 s; lambda pinned at 4/5.
Property: E_L(t) = E_R(0.8 t) exactly (declines at 0.79, 0.81 and at lambda 1).
Concern: line 49-51 states it: the left field is the NOMINAL right field scaled by 0.8 in every coordinate, so the witness is the left's own trajectory re-timed; the energy rows are a projection of that identity, and the detumble-budget requirement (1.25 T) is read off the scaling by inspection. The ECONOMY and SURVIVAL profiles (line 43, constants 0.45/0.42 "battery states") have no role in the claim except to make the choice letter X non-vacuous. P: the left is the design model, not the plant (line 18-19), so the "degraded actuator" is a gain scaling of an abstraction; an 80 % torque limit (line 41-42) is a saturation, not a gain.
Fix: make the left the gyrostat of sat_detumble_phases at k_L = 0.4 (keep the right as is; the design model's momentum band stays conserved on the right). Then E_L(t) = E(0) e^{-0.8 t} = E_R(0.8 t) still holds exactly at lambda 4/5 only, but w_L is not w_R re-timed (the couplings do not scale with k), so the witness is not a copy; the header's one-cause sentence (line 45-46) becomes "derating on the real body against the design model's profiles". If the file must stay at the design-model level, at least say in the header that the claim is a re-timed state identity projected to energy (POLISH).

## sat3w_detumble_phases

Model: three-wheel gyrostat (each wheel absorbs its axis rate, h_i' = k J_i w_i), same phase logic and periods as sat_detumble_phases, 6 states per side; lambda = 1.
Property: energy equality through phase handovers (exact; declines with the +0.5 w3 h2 term removed, line 65-66).
Concern: as sat_detumble_phases (c): witness mirrors the left's phase, content is the cancellation w.(w x H) = 0 (12-variable NRA queries, a real scaling point). Gains 0.5 /s on wheels give torques near 1 N m (line 16-20), roughly 10x a microsat wheel but not absurd; FINE still has no attitude state (line 42-46). Equations checked against Euler's equations with three wheels: correct. Per-axis momentum band only on the right (line 127), correct since it is conserved only without the couplings.
Fix: none required; share the FINE-phase wording fix with sat_detumble_phases.

### G5

# G5 review: syringe_relay_prearm .. zone_lightmass_schedule

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| syringe_relay_prearm | 4 | 4 | 5 | 4 | KEEP | real relay scenario, checked units; volume rows are near-tautological by construction, the content is the one-sided C row |
| tank_dos_3to1 | 4 | 5 | 5 | 4 | KEEP | requirement-justified 0.8 with bisection evidence that discriminates 30 s from 40 s holds; surge-only demand is the one simplification |
| train_ato_odometry | 4 | 4 | 5 | 4 | KEEP | correct odometry scaling and ETCS margins; the witness may pair the deployed against a design run in another performance level |
| tunnel_jetfan_pairout | 3 | 3 | 5 | 3 | POLISH | FIRE requirement is met by the domain floor u >= 3.2 (a forward-invariant set, not a physical limit), so the FIRE row carries no smoke-control content |
| turbine_startup_gearratio | 3 | 2 | 4 | 2 | RETHINK | one-sided claim against an existential reference that may run ahead is near-unary (header admits letters hold at g = 1); loop gains not scaled by the cause |
| ventilator_vc_cuffleak | 4 | 4 | 5 | 4 | KEEP | clean resistor-network derivation, ISO 80601 bounds; EXP band reads a PEEP accuracy as a mid-expiration volume band |
| watertank | 3 | 4 | 5 | 3 | KEEP | running example; toy plant (a pump that also drains, latched PumpOff never entered) but tight first row and domain-independent certificate |
| watertank_twospeed | 3 | 4 | 5 | 3 | KEEP | same toy plant; both constants tied to stated tank margins with a cause table (s, 4.5 - s) |
| zone_lightmass_schedule | 3 | 3 | 5 | 3 | POLISH | domain = comfort band [16, 21] (line 84) is tuned, not physical; 0.152 is tight but tied to no requirement; claim is close to a scaling identity |

## syringe_relay_prearm
Model: two-channel syringe pump in relay mode (v1, v2, plasma fraction C with k = 0.29/min, driver slack b at 0.09 mm/min); the deployed relay pre-arms channel 2 at v1 >= 45 mL, the validated relay takes up slack only at the switchover. Units check (26.6 mm ID gives 0.09 mm/min at 0.05 mL/min; ln2/2.4 = 0.289).
Property: per mode, delivered volumes equal exactly; before syringe 2 delivers C equal and b_R <= b_L (a stated helper row); from RUN2 on C_R <= C_L, i.e. the pre-armed relay never leaves less drug in plasma than the validated relay at the matched instant.
Concern: the volume rows (line 42-47) hold by construction (same Q, same end points) once the right may run its take-up alone with the left frozen; the whole content is the one-sided C row plus the b ordering, which the header discloses (line 72-76). Minor: left RUN1 -> READY (line 37, 125) needs b >= 1 before any pre-arm, only an admitted-start artifact. Mechanism cells (R D, M5 13/13, no λ) agree with matrix and letters.

## tank_dos_3to1
Model: tank level h' = 0.005 n - 0.001 w h with a demand surge w' = 0.02 (22 - w); the demand-paced station stages P2..P5 by w-band every 10 s (right) or every 30 s under a poll-dropping DoS (left). Equilibria 5 n / w and band arithmetic check.
Property: attacked level never above the nominal (exact) and never more than 0.8 m below it, w equal. 0.8 = nominal floor 0.95 minus the 0.15 m submergence minimum; tightest 0.72 at 30 s, 0.84 at 40 s, so the requirement separates a 3:1 from a 4:1 hold (line 40-43).
Concern: the demand is surge-only (line 13), so "stale decision is always a lower stage" is a property of the input class, not of the controller; a falling demand would flip h_L <= h_R. Stated clearly, scenario still real. Cells M2/M6 agree with letters M I.

## train_ato_odometry
Model: first-order ATO speed loop v' = k (25 - v_meas) in three performance levels (k = 0.05/0.045/0.04), the deployed reading 806/840 = 0.96 of true speed after a wheelset exchange; domains 5..27.08 (ETCS dV_ebi) and 5..28.21 (seen through the under-read).
Property: 0 <= v_L - v_R <= 1.11 m/s (ETCS dV_warning 4 km/h) against a design run re-timed per pairing in [0.75, 1.25]; tightest 1.07, model bound 1.042, the 0.03 gap is the stretch grid (line 30-33).
Concern: every left level admits every right level (line 85-86), so the witness may match PL1_L against a PL3 design run at 6/5; the physical scenario is one traffic management commanding the same level to one train, which would be same-level pairing. The bound is dominated by the level-independent 1.042 offset, so the claim's content survives; add one header sentence that the design run's level is the witness's choice. S window [1.07, 1.13) around the 1.11 requirement is disclosed (line 53-54). Cells M1 M2 M3 agree with letters S M B.

## tunnel_jetfan_pairout
Model: 1.6 km tunnel air column u' = a n - 0.00171875 u^2 (friction and portal losses check, a = 0.009 per fan), well-mixed CO c' = e - (u/L) c, fire alarm at t = 600 s adding 1.1 ppm/s; eight fans against ten. Steady states 3.236/3.618 and 78.3/70.0 ppm recomputed and correct.
Property: in NORMAL, c_L <= c_R + 30 (PIARC 70 -> 100 ppm) with a velocity strengthening 0.5 and exact one-sided rows; in FIRE only u_L <= u_R.
Concern: the domain floor u >= 3.2 (line 81-83, 108) is the invariant set of a tunnel whose fans are already running, not a physical limit, and it is what makes the fire requirement (critical velocity 3 m/s) hold "by the domain alone" (line 39-42); so the FIRE row certifies nothing about smoke control and the mode-dependence D reduces to dropping a row that became false. Also the normal controller runs all fans at low speed regardless of CO (line 21), no staging.
Fix: lower the velocity floor below the critical velocity (u >= 2.5; both FIRE and NORMAL flows point inward there) with c capped at 900 ppm (forward invariant for u >= 2.5), and give FIRE the row u_R <= u_L + 0.9 (steady gap 0.76) so the smoke-control requirement is a certified relational claim; if that declines, rewrite lines 3-4 so the header does not announce a velocity requirement that the claim does not state.

## turbine_startup_gearratio
Model: NREL 5-MW start-up as four first-order phases (SPINUP to 9 rpm, RAMP to 7.5, GEN to 12.1, STOP brake), the deployed controller reading speed 5 % low after a 92.4:1 gearbox replaced the 97:1.
Property: w_L <= 1.05 w_R in every mode, the deployed never faster than 1.05 times an existentially chosen, re-timed reference run.
Concerns: (1) R: the header itself shows (line 43-56) that R, P, I and the one-sided form all hold at g = 1.00 for w_L <= w_R between identical systems, i.e. the claim is satisfied by letting the reference run ahead; the content reduces to the unary bound w_L <= 12.705 (the GEN target) against the reference's 12.1, and every two-sided form declined (line 57-65). (2) P: the cause is applied to thresholds and targets only (line 28-30); with v_meas = w / 1.05 the pitch and generator loops in true-speed coordinates have gains 0.04/1.05 = 0.0381 and 0.05/1.05 = 0.0476, not the 0.04 and 0.05 of lines 107 and 113 (train_ato_odometry scales its gain correctly, line 21 there). This is load-bearing: with the scaled GEN gain, a start in GEN above rated (domain allows w <= 16, line 70) with w_L = 1.05 w_R decays more slowly on the left, so w_L > 1.05 w_R after the first step and the claim should decline. (3) STOP is never entered (both parking edges pruned, line 47-50); it exists only as a start.
Fix: scale the left loop gains by 1/1.05 and restrict GEN starts to w <= 12.705 (the only physically reachable GEN states of a start-up), then look for a claim that pins the cause from both sides, e.g. same-phase admissible starts with w_R <= w_L <= 1.05 w_R in RAMP and GEN at a stretch 1.05 (the deployed loop is the reference's with its coordinates scaled); if no two-sided claim certifies, drop the benchmark: the one-sided form adds no information beyond the unary GEN bound.

## ventilator_vc_cuffleak
Model: one volume-controlled breath (0.4 L/s for 1 s, PEEP 10, C = 0.04, R_aw 5, R_tube 8); the deployed has a cuff leak of conductance 0.002 L/s/cmH2O at the trachea node. The resistor-network ODEs (0.376 - 0.0495 V; -1.942 V - 0.0122; -1.923 V) recompute exactly.
Property: in INSP |V_L - V_R| <= 4 mL + 15 % V_R (ISO 80601-2-12 volume accuracy applied to the volume delivered so far), in EXP |V_L - V_R| <= 0.08 L (PEEP accuracy 2 cmH2O times C); tightest 0.104 and 0.0647.
Concern: the EXP band reinterprets an end-expiratory PEEP accuracy as a volume band throughout expiration (line 36), and its tightest value 0.0647 is simply the INSP row's end value carried across the handoff (line 38-39), so the 0.08 is a requirement in name but a handoff residue in fact. The INSP relative row with V_R < 0 (domain -0.4, line 59) forces V_R >= -0.027 at starts; harmless. Cells (M5 3/3, no λ) agree with letters D.

## watertank
Model: the paper's running example: x' = k (c - x) set-point "pump" controller with Low/MidEco/MidBoost/High and a latched PumpOff interlock; the deployed has a 3 dm sensor offset, a doubled Low gain and a locked boost profile.
Property: |x_L - x_R| <= 3 in every mode against a re-timed nominal (λ = 2 in Low and Mid); first row tight at 3.00 (neutral boundary derived in line 42-46), second row slack to 1.50 but kept as the symmetric offset band.
Concern: toy plant: the High mode "pump" drains, levels in dm; PumpOff is never entered (Low rises from 2) and the deployed has no interlock although it runs the same software behind the offset (line 32-34). Acceptable for the running example; the domain-independence claim (line 49-51) is a real strength. Cells M1 M2 M3 agree with letters S M B.

## watertank_twospeed
Model: the same attacked tank against a nominal low fill staged Fast (gain 2, x < 7) and Slow (gain 1, 7 <= x < 10).
Property: x_L <= x_R + 3 (sensor offset = interlock margin, exactly tight from both sides) and x_R <= x_L + 2 (underflow margin, tightest 1.50) in every mode, with a cause table (s, 4.5 - s) over the offset (line 55-59).
Concern: same toy-plant limits as watertank; the upper bound's tightness from above (3.01 declines, line 52) comes from PumpOff becoming an admissible start, i.e. from the admitted-start set, not from the dynamics; disclosed. Round-A note (line 8-11) explains the dropped D and I honestly. Cells M1-M4 agree with letters S M B P.

## zone_lightmass_schedule
Model: lumped zone with a load-compensated proportional reheat law, T' = a (T_set - T), a = 0.02 in the medium-weight commissioned zone and 0.04125 in a lightweight zone (EN ISO 13790 classes 165 and 80 kJ/m^2K); levels COMFORT/STANDBY/ECONOMY (EN 15232), the deployed schedule using two of them.
Property: |T_L - T_R| <= 0.152 K against the reference trace replayed at λ = 2, the design heat-capacity ratio; the tolerance measures the 2.0625 vs 2 mismatch (line 50-54, derivation checks: 0.00125 x 5 / 0.04125).
Concern: the domain [16, 21] (line 84-85, 112) is the comfort band, not a physical range of zone air temperature, and the header shows the tolerance triples (0.485) on the instrumented range 5..30 (line 61-63): the domain is tuned to the 0.152 claim. The 0.152 is tied to no requirement; the "inherited comfort band" (line 48) is the domain itself; B is degenerate and X comes from the claim form (line 79-81, disclosed). With a first-order law the claim is a time-scaling identity up to the class rounding, so its engineering content is thin.
Fix: use the instrumented range 5 <= T <= 30 as the domain and state the tolerance as a requirement: 0.5 K, the control-accuracy class of EN 15500 / ISO 7730 room controllers (the header's own 0.485 certifies, 0.48 declines, so the evidence is already measured); keep the 0.152 derivation as the cause-dependence paragraph.
