# Benchmark review, 2026-10-28 (suite_v2 at 4c47fd4, 50 benchmarks)

Five independent reviewers, ten benchmarks each, one rubric (docs/review-rubric: P physical model, R relational property, C clarity/faithfulness, each 1-5; overall = weakest axis dominates; verdict KEEP / POLISH / RETHINK / DROP). Read-only review of `benchmarks/suite_v2/<b>/input.txt` and `docs/paper-numbers/matrix.md`; nothing was changed. Reviewer findings are claims to be verified before acting, not measurements.

Verdicts: KEEP 26, POLISH 21, RETHINK 3.  Overall scores: 1: 1, 2: 3, 3: 30, 4: 16.

## Ranked table (worst first)

| # | benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|---|
| 1 | `charger_fast_tapers` | 2 | 1 | 2 | 1 | RETHINK | at lambda 1 the row x_L <= x_R + 2 is false at equal times (deployed leads by about 7 % SoC at t = 9 min); it certifies only because the reference runs ahead alone to FULL, where x_L <= 100 <= x_R + 1 is the domain; CC phase modelled as exponential |
| 2 | `lit_hypercert_vehicle` | 3 | 2 | 5 | 2 | RETHINK | witness is a translated copy of the secret run; the source's formal claim is false (header (1)) and the file certifies a changed reading; near-duplicate of lit_lz21 |
| 3 | `lit_freedm_meter` | 4 | 2 | 4 | 2 | POLISH | a battery-independent witness (grid modes only) realizes every left draw, so the secret never matters; header's X justification is wrong |
| 4 | `zone_lightmass_schedule` | 4 | 2 | 5 | 2 | RETHINK | exact re-timing identity against a reference strategy that may select any level, so the witness copies the left's schedule; certifies only at the rounded ratio 2 (real 2.06) |
| 5 | `acc_tune_limp` | 3 | 3 | 4 | 3 | POLISH | LIMP row v_L <= v_R holds pointwise against every reference mode (no relational content); same unphysical DISENGAGE; "limp map the tune adds" is a second cause |
| 6 | `gantry_speed_zones` | 3 | 3 | 5 | 3 | POLISH | tightest tolerance is 0.00 (uniform gain scaling is a time reparametrization by construction); no servo saturation at 3x override |
| 7 | `grid_ffr_dos` | 3 | 3 | 5 | 3 | POLISH | 0.24 a_R band is the no-FFR margin, certifies for any delay and persists after both FFRs are at full power; latch encoded by ad hoc guard x - 2a <= -0.4 |
| 8 | `h2_refuel_ambientbias` | 3 | 3 | 5 | 3 | POLISH | ABORT is unreachable by any flow (start-only) and exists to force the stage rows; lambda_max = 6 unexplained |
| 9 | `lit_lz21_vehicle_position` | 3 | 3 | 5 | 3 | POLISH | same copy witness but the source's claim survives and the offset is the source's delta; the three-level input (header (3)) narrows the universally quantified secret run and is not flagged as a weakening |
| 10 | `quad_light_profiles` | 3 | 3 | 5 | 3 | POLISH | the reference's ECO/SPORT modes exist only to be hopped out of at every window start; B and X are earned by modes the witness never runs |
| 11 | `sat_detumble_weak` | 3 | 3 | 5 | 3 | POLISH | E_L = E_R at lambda = 0.8 is the linear-scaling identity k_L = 0.8 k_NOM; ECONOMY/SURVIVAL gains 0.45/0.42 exist only to be hopped out of |
| 12 | `elevator_start_discbrake` | 4 | 3 | 5 | 3 | KEEP | right-only lift is a genuine 0.5 s re-timing; but outside LIFT the witness is the identical drive copying the left, so the content is the LIFT ordering row only |
| 13 | `engine_start_highidle` | 4 | 3 | 5 | 3 | KEEP | realistic CFM56-class numbers; rows below cut-out are identical dynamics, above cut-out the +4 bound is the idle increment itself; ABORT (N2 < 5) can never be entered |
| 14 | `lit_csf21_vehicle_bus` | 4 | 3 | 4 | 3 | KEEP | faithful to CSF'21 VI-C with disclosed deviations; witness copies the action (acceleration message always available) |
| 15 | `lit_csf21_vehicle_thermo` | 4 | 3 | 5 | 3 | KEEP | faithful to CSF'21 Fig. 6 with disclosed deviations; non-interference witness is the source's |
| 16 | `lit_drl_car_stop` | 4 | 3 | 5 | 3 | KEEP | honest sampled form of dRL Sec. 6; certifies Open Goal 1 only (Safe_eps implies Safe), stated |
| 17 | `lit_drl_lane_control` | 4 | 3 | 5 | 3 | KEEP | same pattern as car_stop, Safe is the file's own instantiation; open three-valued-leader decline disclosed |
| 18 | `lit_girard08_robot` | 4 | 3 | 5 | 3 | KEEP | faithful Girard'08 reproduction, tight 0.16; relational content is the planner copying w (choice hop), and the certified planner automaton is more permissive than Fig. 3 (disclosed) |
| 19 | `platoon_profiles` | 4 | 3 | 4 | 3 | POLISH | exact re-timing is true by construction of the SPORT gains; header line 38 states a wrong Lie derivative for g + 2 r under SPORT |
| 20 | `rover_ladder_2to3` | 4 | 3 | 5 | 3 | KEEP | base rung; its only new row (heading 0.35) is an unforced start condition, certifies at any value |
| 21 | `rover_ladder_6to8` | 4 | 3 | 4 | 3 | POLISH | LTR row at 0.8 is implied by the heading and roll rows (header admits 0.771 < 0.8); heading rows hold for any value |
| 22 | `rover_patrol_lag` | 4 | 3 | 5 | 3 | KEEP | claim is sound but its letters come from the 1 m slack, not the lag (header says so); domain carries a derived cut, not a physical limit |
| 23 | `rover_terrain_2to4` | 4 | 3 | 4 | 3 | POLISH | lambda_max = 3 is set by what the cover needs (2.7 + margin), not by any requirement |
| 24 | `rover_terrain_4to6` | 4 | 3 | 4 | 3 | POLISH | u is called a torque state but has speed units; the rung's one new bound H = rho_MUD c_MUD is a one-line consequence of v <= c_T |
| 25 | `tunnel_jetfan_pairout` | 4 | 3 | 5 | 3 | POLISH | NORMAL rows are good, but the FIRE row (u_L <= u_R) states no requirement: the smoke-control velocity is carried by the domain floor 3.2 alone |
| 26 | `turbine_startup_gearratio` | 4 | 3 | 5 | 3 | POLISH | the one-sided claim's practical content (w_L <= 12.71 rpm) is a unary consequence of the left's own targets; header already discloses that R, P, I come from the claim form |
| 27 | `acc_spoof_limp` | 3 | 4 | 5 | 3 | POLISH | AASHTO-derived row 2 is good; DISENGAGE v' = -0.5 v is a 1 g brake and is unreachable by construction; 2 s vs 1 s period asymmetry exists only to earn M B |
| 28 | `fuelcell_chp_dos` | 3 | 4 | 5 | 3 | POLISH | good DoS story and tight 5 K; Tin range [40, 56] sits 2 K inside the pruning window (38, 58) on both ends and "56" is not a heating-design return value |
| 29 | `hydro_rejection_gatecal` | 3 | 4 | 5 | 3 | POLISH | mode-keyed power/speed requirements are real and tight, but water inertia and speed feedback in REJECT are omitted without disclosure |
| 30 | `platoon_latency` | 3 | 4 | 5 | 3 | POLISH | |Delta g| <= J tau / kp = 4 tight and derived, scaling with tau measured; AEB is reachable only as a start because follower acceleration is unsaturated (not stated) |
| 31 | `rover_terrain_6to12` | 3 | 4 | 4 | 3 | POLISH | the 0.02 rad "bank" is the largest grade the creep floor can climb (v' = 0.059 at v = 0): tuned, and pinned exactly in MUD by guard + domain |
| 32 | `sat3w_detumble_phases` | 3 | 4 | 5 | 3 | POLISH | gyrostat physics and energy identity are correct, but the wheel gain k = 0.5 /s (1 N m wheel torque at 1 rad/s, 2 s detumble time constant) is unjustified for a 60 kg microsatellite |
| 33 | `watertank` | 3 | 4 | 5 | 3 | KEEP | the running example: toy proportional pump with a two-channel adversary; first row tight at the offset, second row slack (1.50) |
| 34 | `watertank_twospeed` | 3 | 4 | 5 | 3 | KEEP | same toy plant, both constants now justified as tank margins (3 offset/interlock, 2 underflow); adds P and per-pairing stretch |
| 35 | `acc_spoof_lag` | 4 | 4 | 5 | 4 | KEEP | clean dominant-mode claim with tight evidence; tau = 0.375 s picked for rational roots (disclosed), row 1 is a re-timed not real-time comparison |
| 36 | `acc_tune_lag` | 4 | 4 | 4 | 4 | KEEP | exact "stock loop twice as fast" claim at lambda 2; labelled degraded-controller though it is a faster retune; stretch searched in [1, 6] while header says stated |
| 37 | `furnace_program_timebase` | 4 | 4 | 5 | 4 | KEEP | AMS 2750 Class 3 tolerance, tight 6.40 measured, residual derived; generator is a first-order filter, not a linear ramp |
| 38 | `lit_nahs25_salt_tank` | 4 | 4 | 5 | 4 | KEEP | faithful NAHS'25 tank, attack projected exactly onto xp, distance 3 tight (2.99 declines), I load-bearing and matrix agrees |
| 39 | `platoon_linkloss` | 4 | 4 | 5 | 4 | KEEP | real fallback (ACC, two-message timeout), 0 <= Delta g <= 15 tight at both ends; leftover SPORT text in a file without SPORT |
| 40 | `quad_light_lag` | 4 | 4 | 5 | 4 | KEEP | lag on both sides, stretch pinned to the terminal-rate ratio with the grid artefact disclosed, Psi strengthening derived, tightness bisected |
| 41 | `reactor_feed_wireless` | 4 | 4 | 5 | 4 | KEEP | invented but disclosed thermal constants, physical domains, 9 K justified by two process limits, tight 8.00, letter windows measured |
| 42 | `rover_ladder_3to6` | 4 | 4 | 5 | 4 | KEEP | pitch row tight (0.23 vs analytic 0.225, 3x coupling declines); chain composes exactly |
| 43 | `rover_ladder_8to12` | 4 | 4 | 4 | 4 | KEEP | LTR (0.35 tight, not implied) and lane (0.20 tight, 5x compliance declines) are real; 31 s of a 40 s budget and a loose composition phrase |
| 44 | `sat_detumble_phases` | 4 | 4 | 5 | 4 | KEEP | correct gyrostat, energy equality is a real detumble-budget claim, cause test given; ideal magnetorquer torque undisclosed |
| 45 | `tank_dos_3to1` | 4 | 4 | 4 | 4 | POLISH | header says the decision is held "up to 30 s" but the left holds every decision exactly 30 s; outflow linear in head is an undisclosed simplification |
| 46 | `bottling_fill_strainer` | 5 | 4 | 5 | 4 | KEEP | physically exact in-flight-volume story, 1.2 mL tight bound follows from the model, 2 mL from 76/211/EEC margin |
| 47 | `flaps_slow_approach` | 5 | 4 | 5 | 4 | KEEP | FCOM half-speed ratio as the stretch, placard-speed reading of V_L <= V_R, 17.5 = (1 - 1/2)(S - F) derived; 20 kt from AFS/FSF windows |
| 48 | `syringe_relay_prearm` | 5 | 4 | 5 | 4 | KEEP | pump geometry, drug kinetics and slack take-up all check out; keyed rows with tight evidence and a clinical requirement |
| 49 | `ventilator_vc_cuffleak` | 5 | 4 | 5 | 4 | KEEP | resistor-network ODEs verified to the digit; ISO 80601 rows per phase with tight evidence |
| 50 | `train_ato_odometry` | 4 | 5 | 5 | 4 | KEEP | odometry scale factor, ETCS margins and domains all sourced; tolerance tight (1.07 vs 1.11 requirement); performance levels as gain scaling is the only stretch |

## Reviewer notes by group

# G1 review: acc_spoof_lag .. fuelcell_chp_dos (suite_v2, tip 4c47fd4)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_spoof_lag | 4 | 4 | 5 | 4 | KEEP | clean dominant-mode claim with tight evidence; tau = 0.375 s picked for rational roots (disclosed), row 1 is a re-timed not real-time comparison |
| acc_spoof_limp | 3 | 4 | 5 | 3 | POLISH | AASHTO-derived row 2 is good; DISENGAGE v' = -0.5 v is a 1 g brake and is unreachable by construction; 2 s vs 1 s period asymmetry exists only to earn M B |
| acc_tune_lag | 4 | 4 | 4 | 4 | KEEP | exact "stock loop twice as fast" claim at lambda 2; labelled degraded-controller though it is a faster retune; stretch searched in [1, 6] while header says stated |
| acc_tune_limp | 3 | 3 | 4 | 3 | POLISH | LIMP row v_L <= v_R holds pointwise against every reference mode (no relational content); same unphysical DISENGAGE; "limp map the tune adds" is a second cause |
| bottling_fill_strainer | 5 | 4 | 5 | 4 | KEEP | physically exact in-flight-volume story, 1.2 mL tight bound follows from the model, 2 mL from 76/211/EEC margin |
| charger_fast_tapers | 2 | 1 | 2 | 1 | RETHINK | at lambda 1 the row x_L <= x_R + 2 is false at equal times (deployed leads by about 7 % SoC at t = 9 min); it certifies only because the reference runs ahead alone to FULL, where x_L <= 100 <= x_R + 1 is the domain; CC phase modelled as exponential |
| elevator_start_discbrake | 4 | 3 | 5 | 3 | KEEP | right-only lift is a genuine 0.5 s re-timing; but outside LIFT the witness is the identical drive copying the left, so the content is the LIFT ordering row only |
| engine_start_highidle | 4 | 3 | 5 | 3 | KEEP | realistic CFM56-class numbers; rows below cut-out are identical dynamics, above cut-out the +4 bound is the idle increment itself; ABORT (N2 < 5) can never be entered |
| flaps_slow_approach | 5 | 4 | 5 | 4 | KEEP | FCOM half-speed ratio as the stretch, placard-speed reading of V_L <= V_R, 17.5 = (1 - 1/2)(S - F) derived; 20 kt from AFS/FSF windows |
| fuelcell_chp_dos | 3 | 4 | 5 | 3 | POLISH | good DoS story and tight 5 K; Tin range [40, 56] sits 2 K inside the pruning window (38, 58) on both ends and "56" is not a heating-design return value |

## acc_spoof_lag

Model: one car, speed loop a_cmd = 0.5 (30 - v_meas) through a 0.375 s powertrain lag; left reads v_meas = 1.25 v (settles at 24 m/s), right unspoofed. Both periods 0.1 s.
Property: along the re-timed cover (lambda 3/2) the spoofed car is never faster (v_L <= v_R) and its dominant-mode speed u = v + a/r_f sits exactly 6 m/s below the reference's (u_L <= u_R - 6, tight at -6.01). I checked the roots ((s+1)(s+5/3), (s+2/3)(s+2)), the modal coordinates and both envelope corner sets; all agree with the header.
Concern: row 1 is the stated requirement ("never faster than the unspoofed reference") but it is checked at matched re-timed instants (v_L(t) vs v_R(3t/2)), not in real time; the header itself says the real-time rows certify only at lambda 1 and cannot be added. The requirement text should say "along the re-timed pairing". tau = 0.375 s is chosen for rational roots (disclosed; a plausible lag).
Fix (optional): none required; one clause in the Property paragraph stating that row 1 is a re-timed statement.

## acc_spoof_limp

Model: 1-D speed loop; left CRUISE v' = 0.625 (24 - v) with a latched LIMP v' = 0.3 (22 - v); right NORMAL/ECO/SPORT 0.5 (set - v) with DISENGAGE v' = -0.5 v below 20 m/s. Left period 2 s (debounce), right 1 s.
Property: v_L <= v_R (constant 0 forced by the 20 m/s floor) and 0.7 v_R <= v_L + 4, the chord of the AASHTO closing-speed bound (I re-derived -8.5 + sqrt(72.25 + 13.6 v_R); 10.05 at 20, 16.32 at 40; chord 4 + 0.3 v_R lies below). Tight evidence given (intercept -0.20).
Concern: DISENGAGE v' = -0.5 v is a 10 m/s^2 deceleration at 20 m/s, not a driver hand-back; and it can never be entered (pruned, excluded as a start), so it exists to be pruned. The header admits "no letter of this file comes from the spoof itself"; the 2 s/1 s period asymmetry is a design knob for M and B.
Fix: replace DISENGAGE dynamics by a coast (v' = -0.5 or -0.02 v); the pruning certificates use the engaged modes' floor accelerations, so verdicts should not move. Either justify the 2 s debounce from a plausibility-monitor spec or state it as a design value in one line (the header already does the latter, so this is minor).

## acc_tune_lag

Model: same car and 0.32 s lag; left gain 0.75 /s, right 0.5 /s; both periods 0.1 s. Roots and envelopes check out.
Property: exact equality of the dominant-mode speeds u_L = u_R at lambda 2 ("the stock response twice as fast"); not implied by the domains since it pins a_R.
Concern: scenario label "degraded-controller" (header line 3 and matrix M7) for an aftermarket retune that is faster, not degraded; "the factor 2 ... lies on the tool's stretch grid" while the file searches lambda in [1, 6] (acc_spoof_lag pins its ratio; be consistent). The exact claim is tight by construction, so the "0.8 /s declines" evidence is tautological.
Fix (optional): relabel as controller-change/retune; pin lambda_min = lambda_max = 2 as the sibling file does.

## acc_tune_limp

Model: 1-D; left CRUISE v' = 0.75 (30 - v) with latched LIMP v' = 0.3 (25 - v); right NORMAL/COMFORT/SPORT (0.5/0.4/0.6 toward 30) and DISENGAGE v' = -0.5 v. Periods 0.1 s both.
Property: CRUISE v_L = v_R at lambda 3/2 with the reference committed to NORMAL; LIMP v_L <= v_R at lambda 1.
Concern: the LIMP row carries no relational content: at v_L = v_R = v the slowest reference rate 0.4 (30 - v) exceeds 0.3 (25 - v) for all v <= 45, so v_L <= v_R holds against every reference mode without any choice or cut. The CRUISE row is refinement by construction (the reference run is the left run re-timed). "One cause" is really two: a gain change plus a limp mode the stock reference lacks. Same unphysical, never-entered DISENGAGE as acc_spoof_limp; the 36 m/s "resume ceiling" (left CRUISE guard) is an unexplained constant.
Fix: give LIMP a two-sided row using the measured lead (v_R <= v_L + 7, header says 7.00 is tight) so the limp map's slowdown is the stated requirement; fix DISENGAGE dynamics; either justify 36 or use 40.

## bottling_fill_strainer

Model: metered volume V and valve opening u; FILL V' = Q u with u = 1, CLOSE u' = -25 u (40 ms actuator) with product still flowing; right Q = 200 mL/s, left 170 mL/s (85 % strainer). 5 ms decisions.
Property: with Psi = V + (Q/25) u the predicted final volume, Psi_L = Psi_R - 1.2, u_L <= u_R, V_L <= V_R, V_R - V_L <= 2 (giveaway margin, 76/211/EEC). I verified Psi is constant in CLOSE and V_R - V_L = 1.2 (1 - u) in [0, 1.2], so the 1.20 tight value is the model's own.
Concern: none of substance. The CLOSE guard conjunct V + (Q/25) u <= 1060 is an installation patch for the well-formedness gate rather than physics (an overflowing bottle would be a mode, not a guard), but it is disclosed and unreachable.
Fix: none.

## charger_fast_tapers

Model: SoC x; right PRECHARGE 0.2 (20 - x), BULK 0.1 (100 - x), two tapers 0.05/0.07 (100 - x), FULL hold, FAULT below 10 %; left all rates x 1.25 with the slow taper; periods 0.012 vs 0.006 min.
Property: x_L <= x_R + 2 in every charging mode (x_L <= x_R in PRECHARGE), read as "deployed SoC never exceeds the certified profile's by more than the BMS accuracy, at equal times (lambda 1)" (header line "The claim compares the two at equal times").
Concern (strongest in this group): the real-time statement is false. From equal starts at 15 % the joint BULK run gives x_L - x_R = 85 (e^{-0.1 t} - e^{-0.125 t}), maximal at t = 8.9 min with a lead of 7.0 % SoC; on the boundary x_L = x_R + 2 the joint derivative is -2.25 + 0.025 x_R < 0 for x_R < 90, so no BULK/BULK pairing can keep the row. The file certifies through right-only repositioning ("BULK_L through the tapers to FULL"), i.e. the reference runs ahead alone to FULL and holds there while the deployed charges; the row then reads x_L <= 100 <= x_R + 1, which is the domain top against the FULL floor. That is exactly why the "tightest" value is 1.00 (0.99 declines): it is 100 - 99, not a property of the charger. The one-sided bound against an existential reference that may advance in time is vacuous here, and the BMS-accuracy motivation does not describe what is certified. Physical model also weak: the "constant-current" BULK phase is exponential (rate 8.5 %/min at 15 %, 2.1 %/min at 79 %); a 25 % current-limit raise would not scale the CV taper or the precharge current; FAULT is a latch on x < 10 that charging can never reach.
Fix: restate as the ACC-lag pattern: the deployed is the profile at 1.25x rate, so pair at the exact stretch lambda = 5/4 with x_L = x_R exact (branching from the taper choice survives, M and B from the period ratio survive), and drop RO; or keep lambda 1 but make the row two-sided (x_R <= x_L + e) so repositioning cannot park the reference at FULL, and model BULK as a true CC ramp (x' = c) with a FAULT trigger independent of SoC. Rewrite the Property paragraph after the change; the current "equal times" sentence is wrong as stated.

## elevator_start_discbrake

Model: car position z, speed v, brake lift b; LIFT (b' = k (1 - b), car held), UP (speed loop toward 1.6 m/s), APP (levelling 0.25 m/s), STOP (v' = -4 v, brake drops); right k = 5 /s (drum), left k = 50 /s (disc). 0.1 s periods.
Property: z and v equal in every mode (exact conformance, constant 0) and b_R <= b_L in LIFT; the reference completes its 0.5 s-longer brake lift alone (right-only step).
Concern: outside LIFT the two cars have identical dynamics from identical states, so the witness copies the left; the whole relational content is the LIFT ordering row plus the handoff that drops it. That is legitimate for an actuator-change conformance claim but thin. Minor physics: 1.28 m/s^2 initial acceleration is above passenger-elevator practice (about 1 m/s^2), and in STOP the brake drops (b' = -5 b) while the car still moves (v' = -4 v); real drives set the brake after electrical stop. The STOP rest-position conjunct is a gate patch, disclosed.
Fix: none required; if the suite wants more content here, let the deployed drive differ too (e.g. a retuned speed loop with a tolerance row) so the UP/APP rows are not copies.

## engine_start_highidle

Model: core speed N2; STARTER 0.1 (30 - n), LIGHTOFF 0.08 (55 - n), SELF 0.15 (idle - n), IDLE 0.5 (idle - n), ABORT below 5 %; right idle 62 %, left 66 % (high idle). 1 s sequencer. Phase times (16 + 22 + 12 s) are plausible for a CFM56-class ground start.
Property: N2_L <= N2_R below starter cut-out (forced 0), N2_L <= N2_R + 4 above (tight 4.00); the reference may run ahead alone across a phase boundary.
Concern: below cut-out the sides are identical, so the row is a copy; above cut-out the +4 bound is the idle increment itself (the difference obeys d' = 0.15 (4 - d) or 0.5 (4 - d), so 4 is the equilibrium offset, not a margin a designer would learn from the tool). ABORT is latched on N2 < 5, which no motoring phase can reach (a hung start aborts on EGT or time, not on N2 collapsing); it exists only as an edge to prune, and pruning is not load-bearing anyway.
Fix (optional): keep; if ABORT is retained, give it a reachable trigger or drop it and the pruning sentences.

## flaps_slow_approach

Model: flap angle f and CAS V; V' = -(0.02 + 0.001 f)(V - 150), flaps 1 deg/s (both hydraulics) vs 0.5 deg/s (FLAPS SLOW); EXT then CONF2 at 15 deg. 0.1 s periods. Speeds from Airbus Safety First #24, half speed from the FCOM.
Property: at equal flap angle (lambda 1/2 while moving, 1 once set) the slow aircraft is never faster (placard reading) and at most 20 kt slower (AFS/FSF 20 kt windows); tight 17.5 = (1 - 1/2)(S - F), which I re-derived from D' = -k D + k (V_R - F)/2.
Concern: none of substance. The inductive 17.5 kt is far above the simulated 4.5 kt gap because the certificate admits starts anywhere in [F, S] on both sides; the header says so. VLS floor not modelled (disclosed).
Fix: none.

## fuelcell_chp_dos

Model: stack temperature T with a constant return temperature Tin, T' = (Tin + rise - T)/120 at LOW/MED/HIGH current (rises 12/17/22 K); right protocol permits levels in overlapping bands and decides every 10 s; left deterministic bands with selections held 20 s by the DoS.
Property: |T_L - T_R| <= 7 K and equal Tin; 7 K derived from the window [45, 85] against steady [52, 78]; tight 5 K = one rise step; non-monotone certifiable window [5, 8] and 10 disclosed.
Concern: the Tin domain [40, 56] is load-bearing for pruning and the header shows [36, 56] and [40, 60] decline, so both ends sit about 2 K from failure; 56 degC is not a design return value (the cited pairs give 45 and 55) and reads as tuned to the window. The deployed selecting current by stack temperature (rather than heat or electrical demand) is a simplification of a CHP controller. The 7 K requirement derivation assumes the protocol's T_R stays in its steady band, which transients do not guarantee.
Fix: set Tin to [40, 55] (55/45 design return, 40 at part load) and re-measure; state in one line that the protocol's transient T_R may leave [52, 78], so the 7 K is a margin against the steady band only.


---

# G2 review: furnace_program_timebase .. lit_freedm_meter (suite_v2, benchmark-fixes 4c47fd4)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| furnace_program_timebase | 4 | 4 | 5 | 4 | KEEP | AMS 2750 Class 3 tolerance, tight 6.40 measured, residual derived; generator is a first-order filter, not a linear ramp |
| gantry_speed_zones | 3 | 3 | 5 | 3 | POLISH | tightest tolerance is 0.00 (uniform gain scaling is a time reparametrization by construction); no servo saturation at 3x override |
| grid_ffr_dos | 3 | 3 | 5 | 3 | POLISH | 0.24 a_R band is the no-FFR margin, certifies for any delay and persists after both FFRs are at full power; latch encoded by ad hoc guard x - 2a <= -0.4 |
| h2_refuel_ambientbias | 3 | 3 | 5 | 3 | POLISH | ABORT is unreachable by any flow (start-only) and exists to force the stage rows; lambda_max = 6 unexplained |
| hydro_rejection_gatecal | 3 | 4 | 5 | 3 | POLISH | mode-keyed power/speed requirements are real and tight, but water inertia and speed feedback in REJECT are omitted without disclosure |
| lit_csf21_vehicle_bus | 4 | 3 | 4 | 3 | KEEP | faithful to CSF'21 VI-C with disclosed deviations; witness copies the action (acceleration message always available) |
| lit_csf21_vehicle_thermo | 4 | 3 | 5 | 3 | KEEP | faithful to CSF'21 Fig. 6 with disclosed deviations; non-interference witness is the source's |
| lit_drl_car_stop | 4 | 3 | 5 | 3 | KEEP | honest sampled form of dRL Sec. 6; certifies Open Goal 1 only (Safe_eps implies Safe), stated |
| lit_drl_lane_control | 4 | 3 | 5 | 3 | KEEP | same pattern as car_stop, Safe is the file's own instantiation; open three-valued-leader decline disclosed |
| lit_freedm_meter | 4 | 2 | 4 | 2 | POLISH | a battery-independent witness (grid modes only) realizes every left draw, so the secret never matters; header's X justification is wrong |

## furnace_program_timebase
Model: a two-state (setpoint s, load T) heat-treatment furnace; the program generator is a first-order filter per segment (PREHEAT/HEAT/SOAK), the load follows with a 5 min lag; left runs the program at 80 % rate (kap 0.008, SOAK 0.08), right at the validated rate.
Property: up to a stretch in [0.8, 1] the deployed setpoint equals the validated one and the load is within 8 degC (AMS 2750 Class 3), with stated strengthening rows s_R - T_R <= 32 and T_R <= s_R.
Concern: minor. The generator is a first-order filter ("approaches each segment's target as a first-order filter"), whereas furnace programmers use linear ramps; the SOAK filter rate 0.1 /min is 10x the HEAT rate with no stated reason ("close on the soak setpoint"). Neither affects the claim's logic; the residual derivation (1 - lambda) x 32 = 6.4 and the measured window are convincing. Matrix M1/M6/M6+ agree with the header.
Fix: none required; optionally one line on why SOAK's filter is faster.

## gantry_speed_zones
Model: two independent first-order axis servos (x' = 2(0.5 - x), y' = 1(0.3 - y) at commissioning); left scales both gains by a zone override 3/2/1 along x, right is the commissioned run in one mode.
Property: production path within 10 mm of the commissioned path on each axis, up to a per-mode stretch in [1, 3].
Concern: the claim is an identity. The header reports "Tightest tolerance 0.00 with lambda_max = 3" and "an arbitrary zone schedule ... CERTIFIED": a uniform gain scaling of a first-order servo is exactly a time reparametrization, so the 10 mm requirement is slack that only serves grid independence, and the zones play no role. Physically, at override 3 the x axis commands 3 m/s from rest with no velocity or acceleration limit; servo saturation is the one thing that would break uniform scaling in a real gantry and the model excludes it silently.
Fix: add a header line stating the unsaturated-servo assumption as a deviation from the plant (the override is a time reparametrization only below the velocity/acceleration limits), and say explicitly that the 10 mm claim is a requirement-level slack over an exact identity. A rate-limited variant (velocity cap at the commissioning max) would make the tolerance load-bearing but is a model change.

## grid_ffr_dos
Model: aggregated swing equation x' = 6.25(0.1 a - d) - 2.625 x with instantaneous droop, battery FFR ramp a' = 5(1 - a) latched at 49.6 Hz, trip at 48.5 Hz; left holds each supervisor decision 0.3 s (DoS drops 2 of 3 commands), right decides every 0.1 s.
Property: x_L <= x_R, x_R <= x_L + 0.24 a_R, a_L <= a_R, same incident; the attacked island is never above the nominal one and at most the FFR's own support (0.1/0.42 Hz) below it.
Concern: (R) the certified band is the FFR-loss margin, and the header itself shows it certifies for a 1 s hold and for an FFR that never activates, so the certificate does not quantify the 0.3 s DoS at all; it also keeps a 0.24 Hz allowance after both FFRs are at full power, where both flows have the same equilibrium. (P) the FFR latch is written as the guard "x - 2a <= -0.4", with the coefficient 2 chosen so the flow keeps the guard ("the release line rises above the model's range once a > 0.7"); that is a modelling device, not a controller behaviour. The pruning window analysis (d_max in (0.168, 0.63)) is good evidence. Matrix M2/M4 agree with the header.
Fix: try the row x_R <= x_L + 0.24 (a_R - a_L), which vanishes once a_L = a_R and would separate the DoS from a lost FFR; if it declines, keep 0.24 a_R but say in the Property paragraph that the certified bound is the no-FFR envelope. Replace the latch guard by a stated latched flag, or add one header line saying the guard form is a latch encoding.

## h2_refuel_ambientbias
Model: one-state tank pressure p with a staged first-order ramp (set points 20/40/60, then end + 0.5), COMPLETE holds; left's ambient sensor reads 10 K high so the J2601 table returns 72.4 instead of 70.0 MPa.
Property: during the stages p_L <= p_R exactly; from TOPOFF on p_L <= p_R + 2.9 (end-pressure shift 2.4 plus the 0.5 top-off margin), i.e. the deployed tank ends below 73.4 MPa.
Concern: ABORT ("a fall below 0.5 MPa during the fill means a leak") can never be entered by any flow: every stage flow rises at 0.5 MPa, there is no leak dynamics, and the header admits STAGE1/2 -> ABORT is pruned. Its only effect is as a start state that forces the exact stage rows ("a lead of 0.01 MPa declines (a reference already aborted below 0.5 MPa becomes an admissible start ...)"), so the stage tightness evidence is an artifact of a dead mode, not of the physics. Also lambda_max = 6.0 in [problem] while the header says "every cover is at lambda 1, so no S". The 2.9 derivation and the s = 0 caveat (0.5 needed even without bias) are honest. Matrix M5/M6/M6+ agree.
Fix: either drop ABORT and restate the stage requirement on its own, or give it dynamics (a LEAK mode p' = -k p reachable from a guard) so the pruning is of a real fallback; set lambda_max = 1.0 or explain the 6.

## hydro_rejection_gatecal
Model: three states (test clock t, gate g, speed deviation w); on the grid the governor holds a 0.85 load reference with 5 % droop and w is the grid frequency; at t = 20 the breaker opens, the gate is driven to speed-no-load and the unit accelerates with T_m = 8 s; left's gate transducer reads 0.02 of stroke low.
Property: ONGRID speeds equal and gates within 0.027 (+-3 % of rated power); REJECT speeds within 0.09 (1.30 pu overspeed setting minus the commissioned 1.2055 peak) and gates within 0.027.
Concern: two undisclosed physical omissions. (i) No water inertia (T_w, the non-minimum-phase response that dominates a hydro load rejection). (ii) In REJECT the governor ignores speed: "g' = (0.1 - g_meas) / 4" has no droop term, whereas the same governor's droop (the ONGRID law) would close the gate on overspeed; the header only says "the later speed-no-load regulation [is] not modeled". Both make the rejection worse than the plant, so the claim is conservative, but a reviewer will ask. Requirements and tightness (gate 0.02 = the offset, 0.019 declines) are good; the uniform-row analysis (smallest uniform band 0.18) is a strong case for D. Matrix M5 agrees.
Fix: one header line disclosing the omitted water-time constant and the open-loop REJECT gate law; or add the droop term to REJECT (g' = (0.1 - g_meas - 20 w)/4 on both sides) and re-measure.

## lit_csf21_vehicle_bus
Model: CSF'21 Sec. VI-C car (d' = -v, v' = a in {1, 0, -1}, temp' = thermo in {-1, 1}) whose thermostat and drive share one bus message per cycle; left is the attacked car (thermostat free), right is the genuine car with twelve modes (action x thermostat x message type).
Property: d_L = d_R and v_L = v_R in every left mode: the cabin-temperature attacker cannot change how the car moves.
Concern: the witness copies the left's action every cycle via the acceleration message, which the header says is "always possible"; the thermostat never constrains d, v, so the claim is immediate once the bus constraint (one message per cycle) is encoded. That is the source's claim, so acceptable for a literature row. Header nits: a broken line in deviation (4) ("so the source then / writes"), and "batch I8" is internal jargon. Deviations (Coast at v <= 1, Brk from v >= 1, top speed 40, thermo in {-1, 1}, closed guards at temp = 20) are all stated.
Fix: none beyond the two header nits.

## lit_csf21_vehicle_thermo
Model: the same car with the Fig. 6 thermostat, no bus; six modes per side; the genuine thermostat reads the true temperature (Cool at temp >= 20, Heat at temp <= 20).
Property: d_L = d_R, v_L = v_R (the source's H-equivalence formula), from any pair of cabin temperatures.
Concern: as for the bus file, the witness is the action copy with the thermostat setting the true temperature allows; the content is that the hop is always legal (at temp = 20 both settings are enabled by closed guards). The deviations and the direction argument (converse immediate since temps := * contains temps := temp) are stated carefully. The leaky negative counterpart exists.
Fix: none.

## lit_drl_car_stop
Model: dRL Sec. 6 stop-sign car, A = B = 1, eps = 1, m = 50, three actions (Accel under a guard, Coast at v <= 1, Brake from v >= 1); left guards Accel by Safe_eps (FM 2011 eq. 7), right by Safe (x + v^2/2 <= 50).
Property: x_L = x_R, v_L = v_R: the conservative sampled controller refines the permissive sampled one.
Concern: the header says it plainly: the certified content is Open Goal 1 (Safe_eps implies Safe) over identical plants; Goals 2 and 3 (event domain kept for eps) are not representable in this suite. The witness copies the left's action. Acceptable as a literature row because every deviation (sampled right side, Coast stand-in, top speed 10, closed guards, v >= 0 load-bearing with the Prebet-literal file declining) is stated and measured.
Fix: none.

## lit_drl_lane_control
Model: dRL Sec. 6.4 local lane control reduced to gap d and two speeds; follower actions Accel (Safe_eps / Safe), Coast at v_f <= 1, Brake from v_f >= 1; leader action in {A, -B} as a mode choice on both sides.
Property: d, v_f, v_l equal on both sides in every left mode.
Concern: Safe on the right ("d >= v_f^2/2 - v_l^2/2") is the file's own instantiation (the source does not print it), and the leader is reduced from [-B, A] to two values; the header discloses an unresolved decline with a three-valued leader ("the cause is not identified ... open"). The witness copies the left's action pair. Otherwise the same honest pattern as car_stop.
Fix: none required; closing the three-valued-leader question would strengthen the row.

## lit_freedm_meter
Model: LICS'18 FREEDM transformer with one battery B in [0, 10] and a cumulative meter E; demand d in {0, 1, 2} and renewable r in {0, 1} are mode choices on both sides; battery modes (E' = 0) are enabled when one period keeps B in range, grid modes (E' = d - r) always.
Property: nondeducibility of B through the meter: E_L = E_R in every left mode from any pair of battery levels.
Concern: the secret never matters. Since d and r are free on the right, the grid modes alone realize every left meter rate (GridD0R0 or GridD1R1 for 0, GridD1R0 or GridD2R1 for 1, GridD2R0 for 2, GridD0R1 for -1), so a witness that never touches the battery exists from every B_R. The header's X justification ("the witness mode depends on the second run's own battery level, so the right must choose it") is therefore inaccurate: choice is needed only to track the left's draw per window. This triviality is inherited from the source (Prop. 11's proof is "the grid branch is always available"), but as a relational benchmark the claim is implied by the right's input freedom; sharing d, r between the runs (the physically meaningful version, same environment) would make it fail, which is the actual leak.
Fix (header): describe the grid-only witness and correct the X paragraph. Fix (optional, model): a variant with d, r shared between runs as a negative row, next to the batI leaky file, to show what nondeducibility with a shared environment would need.


---

# G3 review (suite_v2, branch benchmark-fixes, tip 4c47fd4)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| lit_girard08_robot | 4 | 3 | 5 | 3 | KEEP | faithful Girard'08 reproduction, tight 0.16; relational content is the planner copying w (choice hop), and the certified planner automaton is more permissive than Fig. 3 (disclosed) |
| lit_hypercert_vehicle | 3 | 2 | 5 | 2 | RETHINK | witness is a translated copy of the secret run; the source's formal claim is false (header (1)) and the file certifies a changed reading; near-duplicate of lit_lz21 |
| lit_lz21_vehicle_position | 3 | 3 | 5 | 3 | POLISH | same copy witness but the source's claim survives and the offset is the source's delta; the three-level input (header (3)) narrows the universally quantified secret run and is not flagged as a weakening |
| lit_nahs25_salt_tank | 4 | 4 | 5 | 4 | KEEP | faithful NAHS'25 tank, attack projected exactly onto xp, distance 3 tight (2.99 declines), I load-bearing and matrix agrees |
| platoon_latency | 3 | 4 | 5 | 3 | POLISH | |Delta g| <= J tau / kp = 4 tight and derived, scaling with tau measured; AEB is reachable only as a start because follower acceleration is unsaturated (not stated) |
| platoon_linkloss | 4 | 4 | 5 | 4 | KEEP | real fallback (ACC, two-message timeout), 0 <= Delta g <= 15 tight at both ends; leftover SPORT text in a file without SPORT |
| platoon_profiles | 4 | 3 | 4 | 3 | POLISH | exact re-timing is true by construction of the SPORT gains; header line 38 states a wrong Lie derivative for g + 2 r under SPORT |
| quad_light_lag | 4 | 4 | 5 | 4 | KEEP | lag on both sides, stretch pinned to the terminal-rate ratio with the grid artefact disclosed, Psi strengthening derived, tightness bisected |
| quad_light_profiles | 3 | 3 | 5 | 3 | POLISH | the reference's ECO/SPORT modes exist only to be hopped out of at every window start; B and X are earned by modes the witness never runs |
| reactor_feed_wireless | 4 | 4 | 5 | 4 | KEEP | invented but disclosed thermal constants, physical domains, 9 K justified by two process limits, tight 8.00, letter windows measured |

## lit_girard08_robot
Model: Girard-Julius-Pappas planar robot (double integrator + dynamic tracking controller, written in error coordinates e, z, w) against its 2-D kinematic planner model, six heading locations on both sides, lambda pinned to 1.
Property: the planner's point equals the robot's controller reference (w_L = y2_R) and the robot's tracking error satisfies e^2 + 100 z^2 <= 0.16, i.e. |y1 - y2| <= 0.4, the source's precision; tight (0.1599 declines, line 42).
Concern: the relational rows are an exact copy maintained by the planner hopping into the robot's heading at every window start (line 81); the quadratic is a unary invariant of the robot. Departure (2) (lines 53-64) makes the certified abstraction strictly more permissive than Fig. 3 (any overlapping location in both directions, guards = enlarged invariants), and (3)/(6) replace the source's location invariants by sampled guards with a whole-plane evolve domain on both sides. All disclosed, and a coarser abstraction is still a sound one, but what is certified is weaker than the source's theorem.
Matrix: X is not a matrix column; M1-M6 all no/vacuous, consistent with the header's counter-runs.

## lit_hypercert_vehicle
Model: the HyperCertificates Sec. 9.2 vehicle (s' = v, v' = w in {-0.04..0.04}, 1 s hold) on both sides; left = secret run, right = non-secret partner.
Property: v_L = v_R and s_R = s_L + 2 forever (initial-state opacity with the velocity observed).
Concern: the witness is the secret run translated by 2 m with the same acceleration; the dynamics never read s, so the claim is a translation symmetry (the header's own cause test, lines 32-35, confirms that any position dependence breaks it). Header (1) (lines 38-55) establishes that under the source's formal state set [0, 8] the property is FALSE, so the file certifies a different reading. lit_lz21_vehicle_position is the same vehicle, same witness, same offset trick, with a source claim that survives.
Fix: keep one opacity vehicle (lz21). If a HyperCertificates row is wanted, make the partner unable to copy: certify the source's delta-closeness |v_L - v_R| <= 0.01 with a partner that may differ in acceleration (the header says the naive row declines at the velocity limits, so the row needs a velocity-dependent partner rule), or move the speed-zone variant (a genuine leak) to the refutation set.

## lit_lz21_vehicle_position
Model: Liu-Zamani CSL'21 vehicle (x' = v, v' = u in {-0.05, 0, 0.05}), position observed with delta = 1; left secret, right partner.
Property: v_L = v_R and x_R = x_L + 1; the partner starts delta ahead in the source's R0 and stays exactly delta away.
Concern: copy witness again (not the source's feedback policy, header (2) notes that policy is not input-admissible). Header (3) replaces U = [-0.05, 0.05] by three levels: this restricts the universally quantified secret run, so the certified claim is weaker than the source's; the line reads as a neutral modeling choice. Header (4) admits that at x_L = 0 the partner x_R = 1 is in the closed Xs (a flaw of the source's R0 too).
Fix (POLISH): state in (3) that the three-level input narrows the secret run's behaviours (the copy witness would work for the whole interval, but only three levels are certified).

## lit_nahs25_salt_tank
Model: 100 gal brine tank, xp' = 0.1 (25 - xp) with the valve On, 0 Off, 1 min period; left = controller under a bounded (+-3 lb) sensor attack projected exactly onto xp (On iff xp >= 22, Off iff xp < 28), right = genuine (threshold 25).
Property: |xp_L - xp_R| <= 3 and both tanks above the On equilibrium 25; 3.00 tight (2.99 declines), the slack row xp_R <= xp_L tight at 0 (line 29-31).
Concern: none of substance. The claim rests on mode facts (Off holds below 28, genuine On keeps xp >= 25), which is exactly the source's disjunctive invariant collapsed to a band; header mechanism I, matrix M6/M6+ yes with NO_CUT and NO_IMPLIED_CUT DECLINED, agree. The admissible starts exclude the genuine Off (header says so), a direct consequence of the xp_R >= 25 row, which is the source's invariant.
Minor: header "about 0.15 s" vs matrix 207 ms.

## platoon_latency
Model: one CACC link (gap g, range rate r) with the predecessor-acceleration feed-forward arriving through a 0.2 s lag; the lag error e' = +-J - e/tau with J = 2.5 (ISO 15622), |e| <= J tau = 0.5; right = ideal link; shared AEB latched; 0.1 s period both sides.
Property: |Delta g| <= 4 = J tau / kp (tight: 3.99 declines), two derived modal rows (2 W, 4 W, tight), deployed gap >= 5 and TTC >= 2 s, design engaged.
Concern: the follower's acceleration is unsaturated, so the CACC operating range is forward invariant on both sides and the AEB is never entered from CACC (line 90-91: the CACC -> AEB handoffs are unsat); the mode-dependent rows (D) are therefore carried by a mode reachable only as a start. The lag is the Pade (0,1) stand-in for the delay (line 35, stated). Jerk switching is tied to the 0.1 s control instants (line 41); the convexity argument on line 42 covers intermediate jerks but not mid-window switches, unless the certificate is a differential-inclusion invariant.
Fix (POLISH): say that follower acceleration is not saturated and hence the AEB is reachable only as a start of the claim; one measurement block instead of two (lines 97-115).

## platoon_linkloss
Model: the same link; left degrades to radar-only ACC (time gap 1.2 s, set point 35 m, kd_a = 0.6 keeps the poles) under link loss, decides every 0.2 s (two-message timeout); right CACC always up, 0.1 s.
Property: 0 <= Delta g <= 15 = (h_a - h_c) v_ref, both ends tight, modal rows in [0, 15 rho], deployed gap and TTC floors, design engaged.
Concern: minor. With a lead that cruises (a_pred = 0, line 12) the CACC/ACC difference reduces to the set point, which is the honest content of the file. M is earned mechanically (two identical CACC design cycles per deployed window, since the only alternative edge is pruned). Same AEB-only-as-start observation as platoon_latency. Lines 24-25 and 35 define and invoke a SPORT profile that this file does not contain (shared-text leftover); header "about 1.5 s" vs matrix 604 ms.
Matrix M2/M5 yes, M4 vacuous: agrees with the header's M D.

## platoon_profiles
Model: the same link with the SPORT CACC (kp 0.18, kd 0.9: the NORMAL loop at 1.2x bandwidth) against the NORMAL design; lambda = 6/5 on the SPORT pairing, 1 on the AEB pairing.
Property: g_L(t) = g_R(1.2 t) and r_L = 1.2 r_R exactly (four inequalities in modal coordinates), plus the deployed's gap and TTC floors; AEB rows exact at lambda 1.
Concern: the exact re-timing holds by construction (kp x 1.44, kd x 1.2 is the definition of a 6/5 time scaling), so the certified content beyond the tautology is the compatibility of the operating range and AEB with the stretch, which is real but thin. Line 38 is wrong: under SPORT d/dt (g + 2 r) = -0.36 (g - 20) - 0.8 r, not -0.3 (g + 2 r - 20); g + 2 r is a modal coordinate of NORMAL (pole 0.25) but not of SPORT (poles 0.3, 0.6). The TTC floor is still forward invariant on |r| <= 10 (on g + 2 r = 5 the derivative is 5.4 - 0.08 r > 0), so the verdict is unaffected, but the stated reason ("a sublevel set of the slow mode") is false for SPORT.
Fix (POLISH): correct line 38 (and the "slow mode" sentence) to the direct boundary computation.

## quad_light_lag
Model: quadrotor climb with a 0.1 s thrust lag (h, w, a), linear drag; left airframe 20 % lighter (T/m and k/m x 1.25, terminal 2.4 m/s), right reference (terminal 2.0); lambda pinned to 6/5.
Property: |h_L(t) - h_R(1.2 t)| <= 0.8 (PX4 NAV_MC_ALT_RAD) with the conserved steady-climb gap Psi within +-0.16 (derived: 0.8 less the largest transient term).
Concern: none of substance. 0.8 is a stated requirement, not tight (0.40/0.38 bisected with Psi at 0.16); the stretch grid artefact of the earlier [1, 2] range is disclosed (lines 22-23). Domains are the climb-from-hover envelope (0 <= w <= terminal, 0 <= a <= a_cmd), forward invariant rather than tuned. Linear drag is a simplification not named as such.
Matrix M1 lambda = 6/5, M2 B = 2: agrees with S M.

## quad_light_profiles
Model: the same climb without the lag; left lighter airframe at NORMAL thrust; right reference whose pilot may select NORMAL/ECO/SPORT at every 1 s interval (complete graph).
Property: |h_L(t) - h_R(1.2 t)| <= 0.8 against the NORMAL reference, with Psi <= 0.8 and 1.2 w_R <= w_L (the airframe_20 rows).
Concern: the ECO and SPORT reference modes are never run in any joint segment; the cover hops out of them at every window start (lines 53-60, matrix cover: ECO:hop -> NORMAL, SPORT:hop -> NORMAL). They are admissible starts only, so B and X are earned by modes that contribute nothing to the certified relation; the deployed has no profile selection, which is the asymmetry that produces the letters. No tightness evidence for 0.8 or Psi <= 0.8 on this file (only the hover value 0.0163).
Fix (POLISH): state that the profile modes are left at every window start and that the claim is the NORMAL-only claim of quad_light_airframe_20 with a larger start set; a stronger version would give the deployed the same three profiles, so that the reference must follow the deployed's selection (choice with content, as in lit_girard08_robot).

## reactor_feed_wireless
Model: exothermic CSTR, T' = 0.1 (p + 4 k - T), four feed levels selected by temperature band (feed only as fast as the reaction consumes it), cooling water p in [15, 35] constant; left reads every 2 min (WirelessHART), right every minute.
Property: |T_L - T_R| <= 9 and p_L = p_R; 9 K justified by the boiling point (60 vs max 51) and the feed-accumulation floor (10 vs min 19); tightest 8.00 (two levels), certified window [8, 10], non-monotone above (disclosed, lines 36-39).
Concern: minor. The thermal constants and the staircase interlock are design values of this file (admitted, lines 73-75), without hysteresis (settling points can sit exactly on a threshold, e.g. F2 at p = 17). The certified envelope (8-9 K) is an order of magnitude above the simulated worst gap (0.87 K, line 65), an honest statement of what the inductive method sees. Two verdict blocks (lines 91-106) say the same thing.
Matrix M2/M3/M4 yes with NO_PRUNE DECLINED: agrees with M B P.


---

# G4 review: rover ladder, rover patrol/terrain, sat detumble (suite_v2, branch benchmark-fixes 4c47fd4)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| rover_ladder_2to3 | 4 | 3 | 5 | 3 | KEEP | base rung; its only new row (heading 0.35) is an unforced start condition, certifies at any value |
| rover_ladder_3to6 | 4 | 4 | 5 | 4 | KEEP | pitch row tight (0.23 vs analytic 0.225, 3x coupling declines); chain composes exactly |
| rover_ladder_6to8 | 4 | 3 | 4 | 3 | POLISH | LTR row at 0.8 is implied by the heading and roll rows (header admits 0.771 < 0.8); heading rows hold for any value |
| rover_ladder_8to12 | 4 | 4 | 4 | 4 | KEEP | LTR (0.35 tight, not implied) and lane (0.20 tight, 5x compliance declines) are real; 31 s of a 40 s budget and a loose composition phrase |
| rover_patrol_lag | 4 | 3 | 5 | 3 | KEEP | claim is sound but its letters come from the 1 m slack, not the lag (header says so); domain carries a derived cut, not a physical limit |
| rover_terrain_2to4 | 4 | 3 | 4 | 3 | POLISH | lambda_max = 3 is set by what the cover needs (2.7 + margin), not by any requirement |
| rover_terrain_4to6 | 4 | 3 | 4 | 3 | POLISH | u is called a torque state but has speed units; the rung's one new bound H = rho_MUD c_MUD is a one-line consequence of v <= c_T |
| rover_terrain_6to12 | 3 | 4 | 4 | 3 | POLISH | the 0.02 rad "bank" is the largest grade the creep floor can climb (v' = 0.059 at v = 0): tuned, and pinned exactly in MUD by guard + domain |
| sat_detumble_phases | 4 | 4 | 5 | 4 | KEEP | correct gyrostat, energy equality is a real detumble-budget claim, cause test given; ideal magnetorquer torque undisclosed |
| sat_detumble_weak | 3 | 3 | 5 | 3 | POLISH | E_L = E_R at lambda = 0.8 is the linear-scaling identity k_L = 0.8 k_NOM; ECONOMY/SURVIVAL gains 0.45/0.42 exist only to be hopped out of |

## rover_ladder_2to3
Model: 3-DOF rover (v, s, psi) with heading loop psi' = -psi and along-track loss s' = v(1 - psi^2/2) against the 2-DOF point plan, three odometer zones with rising speed set points, lambda = 1.
Property: the rover is never faster than and never ahead of the plan (offset 0; +1 m certifies, -1 m declines), and |psi| <= 0.35 rad (camera half field of view).
Concern: the heading channel has no excitation (no path curvature, no disturbance), so psi only decays from its start; the header concedes "every value in [0, 0.6] certifies" (line 52). The rung's own requirement row is therefore a start condition, and the clearance rows follow from identical speed loops plus a nonnegative loss. Physically clean (LTR = a/g checks against track/cog), units fine, matrix row agrees ("no code exercised").
Fix (optional): none needed as a chain base; if the heading row should carry content, add a per-zone path curvature kappa_T so psi' = -psi + kappa_T v and the 0.35 bound becomes tight.

## rover_ladder_3to6
Model: adds pitch, heave and roll (theta_p' = -theta_p + grade + 0.5 z, z' = -z, phi_r' = -phi_r + xslope + 0.015 v r) and their progress losses, against the 3-DOF left of 2to3 with those three pinned.
Property: clearance rows, psi_L = psi_R (true helper), |theta_p| <= 0.25 (tilt stabilizer range).
Concern: none of weight. Tight evidence is good (0.23 certifies, 0.22 declines, analytic 0.15 + 0.5 x 0.15 = 0.225; coupling x3 declines). The 0.3 and 0.2 loss coefficients in s' (line 20) are ad hoc but only slow the left. The right's guards match 2to3's left exactly, so the chain composes.

## rover_ladder_6to8
Model: yaw and pitch become second order (critically damped cascade, omega states), lateral acceleration a = v(omega_psi - psi) drives roll; against the 6-DOF model, plan re-timed by at most 1.25 (timetable slot at 80 % of plan arrival).
Property: clearance against the re-timed reference; heading, pitch, roll, LTR <= 0.8 on the left; plan-tolerance rows on the reference so the chain composes.
Concerns: (1) line 60-63: the LTR row as stated (0.8) "follows from the heading and roll rows" (8 x 0.7/9.81 + 0.2 = 0.771), so it is a redundant conjunct; the interesting number (tight 0.22) is not what is claimed. (2) The heading rows certify "any value (0.05 tested)" (line 53-54): a start condition carried for the roll row's sake. (3) The deployed guard v <= c (line 147) is a start restriction the right side does not carry; justified as reachable-invariant but it is what makes the re-timed reference dominate, i.e. load-bearing by the header's own account (line 110-114). (4) Line 119-120 says 8to12's right "is this file's left with ... pinned"; 8to12's right drops the v <= c guard, so it is a superset (see 8to12).
Fix: drop the LTR row here (8to12 carries it non-redundantly) or state it at the certified-tight value with the 0.8 requirement noted; say explicitly that the heading rows are start conditions.

## rover_ladder_8to12
Model: heave and roll become second order and tire slip y, omega_y moves (omega_y' = -omega_y + 0.03(a + g phi_r); y'' feeds the body lateral acceleration and roll); against the 8-DOF left of 6to8 with those four pinned; lambda <= 1.25.
Property: clearance; heading (any value), roll <= 0.2 (tight 0.15), LTR <= 0.8 with slip acceleration (tight 0.35; other rows only give 0.87), lane |y|, |omega_y| <= 0.25 (tight 0.20; 5x compliance declines); plan tolerances = 6to8's left rows.
Concerns: (1) 31 s of the 40 s default budget (line 126-128): a slower machine makes the headline row DECLINE for a timing reason; worth pinning RELCERT_TIME_BUDGET_MS in the recipe or recording the 1.5 run (20 s). (2) The right guards (lines 174, 180, 186) do not carry v <= c while 6to8's left guards do, so "Right (L8, rover_ladder_6to8's left ...)" (line 45) is loose; composition still works for right starts with v <= c (forward invariant along the route), which the header should say. (3) LTR 0.8 vs tight 0.35 is loose but requirement-justified (20 % margin to wheel lift).
Fix: none required; polish the two header points above.

## rover_patrol_lag
Model: patrol rover with a first-order motor current lag (tau = 3/16 s, a' = (16/3)(c - v - a)) against the lag-free planning model, same four-zone planner (SLOW/MEDIUM_ECO/MEDIUM_BRISK/FAST), plan re-timed in [1, 3/2] and advanced alone.
Property: s_L <= s_R + 1 (1 m waypoint acceptance radius) plus a derived look-ahead row P_L <= P_R + 0.375; an order property, not real time.
Concerns: (1) The header's own cause test (lines 66-71) shows the mechanisms S M R B come from the 1 m slack admitting a rover already in the next zone, with or without the lag; the lag only moves the tight lead from 0 to 0.59 m. The file is honest, but the mechanism story is about the claim form. (2) Line 29-30: the domain conjunct 0 <= a + 4v <= 6.4 is a closed-loop invariant used to make the box forward invariant, not a physical limit; the rubric asks for physical limits only (it is declared non-load-bearing, so acceptable). (3) lambda_max = 3/2 is "15/11 rounded up" (line 61), a tool bound, not a mission requirement, disclosed.
Fix: none required.

## rover_terrain_2to4
Model: wheel-speed loop w' = 3(c_T - w), ground speed through soil v' = mu_T(w - v) - r_T v - zs, sinkage relaxation, over MUD/GRAVEL/PAVED zones, against the no-slip plan v' = 3(c_T - v); lambda in [1, 3].
Property: never faster than and never ahead of the plan re-timed by at most 3; slip velocity w - v in [0, 0.25] (traction-controller threshold; tight 0.21 with an analytic derivation).
Concern: lines 67-79: the allowance 3 is chosen because 2.5 declines and 2.7 certifies ("3 keeps the stated value 0.3 above the needed point"). A claim "within its allowance" needs an allowance that comes from somewhere other than the cover; as it stands the stretch range is tuned to the claim the way the rubric forbids for domains. The slip row is the real content and is good. Minor: the left creep floor w >= 0.15 and zs <= 0.12 are set so that v' > 0 at v = 0 (line 51-52); plausible but convenient. Right w box [0, 0.8] differs from the left's [0.15, 0.8] (line 130 vs 108).
Fix: source lambda_max from a stated requirement (e.g. a route-time slot: the plan's schedule may be read up to 3x faster because the mission only uses the plan for stop-line positions), or state the claim as "re-timed by at most 2.7 (measured need)" and drop the margin language.

## rover_terrain_4to6
Model: adds a drive-command lag u' = 4(c_T - u), w' = 3(u - w), and a first-order heave envelope zh' = rho_T v - zh, against the 4-DOF left of 2to4 (exact, guards included); lambda = 1.
Property: clearance, slip window (0.25, tight 0.21 as in 2to4: the lag adds nothing), heave zh <= 0.15 (bump stop; tight 0.13), plus three ordering rows w_L <= w_R, zs_R <= zs_L, w_L <= u_L.
Concerns: (1) Line 2 and 17: u is "the motor torque state" but has units of m/s (w' = 3(u - w)); it is a lagged speed command. (2) The rung's only new requirement, H, is bounded by rho_MUD c_MUD = 0.125 through v <= w <= u <= c_T; true and tight but a one-line consequence of the set point, so the rung mostly shows the lag does not break the chain. (3) The zh domain [0, 0.5] is a validity box, fine.
Fix: rename u (lagged drive command, m/s) or give it torque units with a stated gain; keep otherwise.

## rover_terrain_6to12
Model: adds the bank grade gamma (0.02 rad on MUD, easing as gamma' = -0.5 v gamma after), chassis pitch lagging the grade by one wheelbase, slope load -9.81 theta_p on v', second-order heave, accelerometer lag ax, and squat pitch phs; against the 6-DOF left of 4to6.
Property: clearance, slip (tight 0.24 vs 0.21 on flat ground: the slope shows), heave, body pitch theta_p + phs <= 0.15 (camera nose-up limit; tight 0.13 vs analytic 0.12), and derived aux rows (ax <= 2.0 = mu_PAVED sigma, omega_phs <= 0.1).
Concerns: (1) Line 15: a "bank" of 0.02 rad (1.1 degrees). At v = 0 the creep floor gives v' = 2.5 x 0.15 - 0.12 - 9.81 x 0.02 = 0.059 (line 55-56): the grade is the largest value for which the domain stays forward invariant, i.e. tuned to the model's climbability rather than to a terrain. A real bank (0.1 rad) stalls this rover. (2) MUD guard gamma >= 0.02 and theta_p >= 0.02 with domain <= 0.02 (lines 95-96) pins both to exactly 0.02 in MUD, so the pitch channel is constant there and only acts on GRAVEL/PAVED; the header should say so. (3) One-sided rows (ax, phs upper only) are justified by the nose-up requirement but leave braking squat unbounded; fine.
Fix: either raise the traction (mu_MUD, creep floor) so a stated bank grade from a terrain source (e.g. 0.1 rad) is climbable and keep the forward-invariance argument, or justify 0.02 rad as a measured route grade; add the "pinned in MUD" sentence.

## sat_detumble_phases
Model: full gyrostat (J = diag(2, 4, 5), z-wheel momentum h, B-dot style rate damping k = 0.5 in DETUMBLE, 0.3 in FINE) against the design model that drops the gyroscopic and wheel couplings; same phase logic (E <= 1 / E <= 0.125), flight decides every 2 s, design every 1 s, lambda = 1. Euler equations and the energy identity E' = -2kE checked by hand: correct.
Property: body energy of the real spacecraft equals the design model's at every instant through phase handovers (tolerance 0), so detumble-time and capture-time budgets computed on the design model hold.
Concerns: (1) Magnetorquers are modeled as ideal three-axis rate dampers tau_i = -k J_i w_i; a magnetorquer cannot torque along the local field, so this is a physics deviation the header should name (line 17). (2) The 2 s flight period is "a design value of this file" (line 31-32), chosen to produce M; disclosed. (3) The momentum band |h + 5 w3| <= 2 is on the right only; correct, since it is not conserved on the left, and the header explains it.
Fix: none required; one sentence on the ideal-torque assumption.

## sat_detumble_weak
Model: both sides the linear design model w_i' = -k w_i, h' = 5 k w3; left derated to k = 0.4 with a 2 s duty cycle; right offers NOMINAL 0.5, ECONOMY 0.45, SURVIVAL 0.42 and SAFE; lambda pinned to 4/5.
Property: E_L = E_R exactly against the NOMINAL profile re-timed by 0.8: a detumble budget T on the design model is 1.25 T on the degraded spacecraft.
Concerns: (1) The claim is the identity w(t) = w^NOM(0.8 t) for a diagonal linear system, i.e. k_L = 0.8 k_NOM; it is exact and tight by construction, and a reader computes it in one line. The non-trivial content is only the profile choice and the 2:1 period. (2) ECONOMY and SURVIVAL (0.45, 0.42, line 43) are not sourced and can never match 0.4 at lambda 0.8; they exist to be hopped out of (X) and to be retained at a joint step (B). (3) The "degraded spacecraft" is the design model, not the plant; the header defers the couplings to sat_detumble_phases, so this file is a degraded design model. (4) Scores and letters are disclosed with care; matrix cells (M1 M2 M3, pruning and cut vacuous) agree with the header.
Fix: put the gyrostat on the left (the couplings do no work at any gain, as the header says, and phases shows Z3 handles the cancellation), so the weakened side is the physical plant and the file is no longer a pure linear rescaling; source the profile gains (battery states) and the 2 s duty cycle, or reduce the right to NOMINAL + SAFE and accept losing X and B.


---

# G5 review (suite_v2, branch benchmark-fixes, tip 4c47fd4)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| sat3w_detumble_phases | 3 | 4 | 5 | 3 | POLISH | gyrostat physics and energy identity are correct, but the wheel gain k = 0.5 /s (1 N m wheel torque at 1 rad/s, 2 s detumble time constant) is unjustified for a 60 kg microsatellite |
| syringe_relay_prearm | 5 | 4 | 5 | 4 | KEEP | pump geometry, drug kinetics and slack take-up all check out; keyed rows with tight evidence and a clinical requirement |
| tank_dos_3to1 | 4 | 4 | 4 | 4 | POLISH | header says the decision is held "up to 30 s" but the left holds every decision exactly 30 s; outflow linear in head is an undisclosed simplification |
| train_ato_odometry | 4 | 5 | 5 | 4 | KEEP | odometry scale factor, ETCS margins and domains all sourced; tolerance tight (1.07 vs 1.11 requirement); performance levels as gain scaling is the only stretch |
| tunnel_jetfan_pairout | 4 | 3 | 5 | 3 | POLISH | NORMAL rows are good, but the FIRE row (u_L <= u_R) states no requirement: the smoke-control velocity is carried by the domain floor 3.2 alone |
| turbine_startup_gearratio | 4 | 3 | 5 | 3 | POLISH | the one-sided claim's practical content (w_L <= 12.71 rpm) is a unary consequence of the left's own targets; header already discloses that R, P, I come from the claim form |
| ventilator_vc_cuffleak | 5 | 4 | 5 | 4 | KEEP | resistor-network ODEs verified to the digit; ISO 80601 rows per phase with tight evidence |
| watertank | 3 | 4 | 5 | 3 | KEEP | the running example: toy proportional pump with a two-channel adversary; first row tight at the offset, second row slack (1.50) |
| watertank_twospeed | 3 | 4 | 5 | 3 | KEEP | same toy plant, both constants now justified as tank margins (3 offset/interlock, 2 underflow); adds P and per-pairing stretch |
| zone_lightmass_schedule | 4 | 2 | 5 | 2 | RETHINK | exact re-timing identity against a reference strategy that may select any level, so the witness copies the left's schedule; certifies only at the rounded ratio 2 (real 2.06) |

## sat3w_detumble_phases
Model: 6-D gyrostat (body rates + three wheel momenta, J = diag(2,4,5)) with DETUMBLE/FINE rate-damping phases, against the design model that drops the gyroscopic and wheel-coupling terms; flight decides every 2 s, design every 1 s.
Property: the body energy E = w.Jw of the full model equals the design model's at every instant in both phases (tolerance 0 both ways), so detumble/capture budgets computed on the design model hold.
I re-derived the Euler equations from J w' = -w x (Jw + h) - h' and all six cubic coefficients match; E' = -2kE is exact on both sides, so the claim is a genuine identity, non-trivial in the solver (12-variable NRA) and not implied by the domains. X, M and I are honestly attributed (M from the period ratio, restored in batch I9 for mechanism coverage).
Concern: k = 0.5 /s (DETUMBLE) and 0.3 /s (FINE) are stated without a source; at |w| = 1 rad/s this is a 1 N m wheel torque and a 2 s detumble time constant, two orders above microsatellite wheels (0.01 to 0.1 N m), and the 1 s / 2 s decision periods are chosen against that time scale. The 2 N m s wheel capacity is also generous for a 60 kg bus.
Fix (POLISH): either cite a wheel/torque figure or state in the header that gains and periods are in accelerated time (the identity is scale-free; k and both periods scale together without changing any verdict), so that the gain is not read as a plant constant.

## syringe_relay_prearm
Model: two-channel syringe pump in relay at 3 mL/h (v1, v2 delivered volumes, plasma fraction C with a 2.4 min half-life, driver slack travel b); the deployed relay pre-arms channel 2 at 5 mL remaining, the validated relay takes up the 1 mm slack only at the switchover (11.1 min interruption).
Property: both syringes deliver exactly the validated volume history (up to the re-timing of the validated relay's interruption); C equal before the deployed switches to syringe 2, and C_R <= C_L from then on (no added hypotension risk); b_R <= b_L as a disclosed strengthening.
Checked: 0.05 mL/min over a 26.6 mm bore gives 0.09 mm/min, k = ln 2 / 2.4 = 0.29, 1 mm / 0.09 = 11.1 min; all correct. Tightness evidence (offsets of 0.01 decline on both C rows and on b), cause dependence, pre-arm point and driver-speed windows are all measured and reported.
Concern: none of substance. The volume rows are exact on both sides but say nothing about timing by construction (the right-only step absorbs the 11 min); the header says so plainly.

## tank_dos_3to1
Model: tank level h fed by a four-stage pump station (5 mm/s per pump) against a pressure-driven demand 0.001 w h, with an exogenous demand surge w' = 0.02(22 - w); the attacked station holds each staging decision 30 s instead of 10 s.
Property: during the surge the attacked tank is never above the nominal one (exact), and never more than 0.8 m below it (the 0.95 m nominal floor minus the 0.15 m submergence requirement); w equal on both sides.
Good: bound depends on the hold (0.50 / 0.72 / 0.84 for 20 / 30 / 40 s), the law-dependence and NO_CUT ablations are reported, and the derivation d' = 0.005 k - 0.001 w d is right.
Concerns: (1) the header ("held for up to three polls", "up to 30 s") describes a DoS that drops some polls, but Lsys has epsilon = 30.0, so every decision is held exactly 30 s; a hold of 10 or 20 s is not an instance of the certified model (the shorter-hold bounds are separate measurements, not corollaries). (2) The outflow is linear in h, not the sqrt(h) of an orifice; "pressure-driven demand" reads as physics but is a modeling choice and should be named as one. (3) The 0.95 m nominal floor that sets the 0.8 requirement rests on simulation, not on a certified unary invariant.
Fix (POLISH): header to say "every decision held 30 s (two of three polls dropped in lock-step)" and to list the linear outflow and the simulated 0.95 floor as modeling assumptions.

## train_ato_odometry
Model: first-order ATO speed loop v' = k(25 - v_meas) in three performance levels (k = 0.05 / 0.045 / 0.04 /s), traffic management switching level at any 0.5 s cycle; the deployed train reads 806/840 = 0.96 of the true speed after a wheelset exchange.
Property: 0 <= v_L - v_R <= 1.11 m/s against a design run re-timed by a per-pairing stretch in [0.75, 1.25]: the miscalibrated train never exceeds a calibrated run by more than the ETCS 4 km/h warning margin, and is never slower.
Good: requirement and both domain ends are sourced (ETCS dV_warning, dV_ebi, linear traction range), the model bound 1.042 and the stretch-grid slack to 1.07 are explained, the cause window (c = 0.95 declines) is measured, and Lean passes the sub-unit stretches unchanged.
Concern: performance levels that scale the loop gain while holding the same permitted speed are a stylized reading of CBTC performance levels (which usually derate acceleration or target speed); and the lower row 0 relies on the matched start v_L = v_R being admitted (stated). Neither affects the claim's value.

## tunnel_jetfan_pairout
Model: 1.6 km tunnel air column u' = a n - K u^2 with ten (right) or eight (left) jet fans, well-mixed CO c' = e - (u/L) c, a fire alarm at t = 600 s switching fans to full speed and adding 1.1 ppm/s of fire CO.
Property: in NORMAL, equal clocks, u_L <= u_R <= u_L + 0.5, c_R <= c_L <= c_R + 30 ppm (PIARC 70 ppm design, 100 ppm normal-operation limit); in FIRE only t equal and u_L <= u_R.
Checked: K = (0.02 x 200 + 1.5)/3200 = 0.00171875, a = 1037/(1.2 x 60 x 1600) = 0.009, steady 3.618 / 7.236 m/s, 70.0 ppm, 1.1 ppm/s from 0.12 kg/s CO; all correct. Tightness (13.52 ppm at strengthening 0.5; 0.39 window) and the D and I ablations are measured.
Concern: the header's own framing ("once the fire mode is engaged the requirement is on the longitudinal air velocity") is not in the claim. The FIRE row u_L <= u_R is derived and exact (eight fans are never faster than ten) and carries no tolerance; the 3 m/s critical-velocity requirement is met "by the domain alone" (u >= 3.2 forward invariant), i.e. it is a unary fact, and the 4.2 m/s gap was dropped as domain-implied. So the fire phase, the point of the benchmark, has no relational content.
Fix (POLISH): add a FIRE row u_R <= u_L + d with d just above the tightest certifying value (steady gap 0.76 m/s; try d = 1.0, well below the domain-implied 4.1) and state it as "one pair out costs at most d of fire-mode velocity"; record the bisection as for the NORMAL rows.

## turbine_startup_gearratio
Model: NREL 5 MW start-up as four first-order phases on rotor speed (SPINUP toward 9 rpm, RAMP toward 7.5, GEN toward 12.1, STOP braking), the deployed controller dividing generator speed by the old 97:1 ratio on a 92.4:1 gearbox, so every threshold and target it acts on is 1.05 times higher.
Property: w_L <= 1.05 w_R in every mode, against a re-timed reference that may run alone (R); 1.05 is exactly tight (1.049 declines, 1.06 declines for a disclosed spurious reason) and the g-window up to 1.1 is measured.
Concern: the header is admirably candid that R, P and I come from the one-sided claim form, not the cause, and that every two-sided variant declines or is near-vacuous. What remains is weak: the stated requirement ("bounded by 12.71 rpm < 13.31 rpm") follows from the left's own targets alone (all <= 12.705, forward invariant from below-rated starts); the relational form adds only that a reference ahead in phase bounds the deployed, and the existential reference is free to race ahead. Phase gains 0.03 / 0.04 / 0.05 /s and the proportional brake w' = -0.1 w are invented (plausible time scales, not sourced).
Fix (POLISH): state in the header what the relational claim certifies beyond the unary bound (phase-wise tracking at the 1.05 factor), or pin the reference to the deployed's phase at the window start (RELCERT_NO_REPO semantics) and report whether the claim survives; if the unary bound is all that is wanted, the file is a weak suite member.

## ventilator_vc_cuffleak
Model: one volume-controlled breath (0.40 L at 0.40 L/s for 1 s, PEEP 10, C = 0.04 L/cmH2O, R_aw 5, R_tube 8) with a 500 cmH2O.s/L cuff leak at the trachea against a sealed cuff; flow-controlled inspiration, pressure-controlled expiration.
Property: in INSP the deployed lung volume is within ISO 80601-2-12's +-(4 mL + 15 %) of the reference's delivered volume so far; in EXP within +-0.08 L (ISO PEEP accuracy +-2 cmH2O times C).
Checked: both leak ODEs re-derived from the resistor network (INSP 0.376 - 0.0495 V; EXP -1.942 V - 0.0122 via P_t = (0.2 PA + 1.25)/0.327); exact. Tightness (0.104 fraction, 0.0647 L band) and the leak-resistance window for D are measured; the mode dependence has a real cause (integrator vs relaxation).
Concern: the EXP band 0.08 is loose against the physics (6.3 mL settle) and is in fact set by the INSP row's end-of-breath value carried through the handoff; the header says so. The relative INSP row is only satisfiable for V_R >= -0.027 L, so INSP starts with a strongly negative lung volume are excluded by the claim rather than the guard; harmless (a breath starts at V = 0) but could be stated.

## watertank
Model: the paper's running example, a 25 dm tank with proportional pump modes (Low toward 12.5, two Mid profiles toward 17, High draining to 17, a latched PumpOff interlock), against a deployed controller whose sensor reads 3 dm low and whose pump is forced to double gain in Low and to the boost profile in Mid.
Property: |x_L - x_R| <= 3 in every mode, the tolerance being the sensor offset; the first row is exactly tight (neutral Lie derivative on the boundary, 2.99 declines), the second certifies down to 1.50 and is kept at 3 for symmetry.
Concern: a toy plant (a pump that also drains, k = 1 /min, an attacker who "doubles the gain") and a claim that holds only up to a stretch of 2, so the aggressive pump's faster fill is hidden by re-timing; both are disclosed and acceptable for the running example. The slack second row (3 where 1.50 is tight and watertank_twospeed justifies 2) is the only loose constant; the header should either justify 3 on the lower side (it does not) or align with twospeed's underflow-margin reading.

## watertank_twospeed
Model: the same attacked tank against a nominal controller whose low fill has two speeds (Fast 2 <= x < 7 at gain 2, Slow 7 <= x < 10 at gain 1), everything else as in watertank.
Property: x_L <= x_R + 3 and x_R <= x_L + 2 in every mode, each constant read as a tank margin (offset = interlock margin; 2 = the reference's interlock height, so the deployed is never empty while the reference pumps). Upper exactly tight (2.99 and 3.01 decline), lower tight at 1.50, requirement 2; the (s, 4.5 - s) cause table is a nice touch.
Concern: same toy plant as watertank; the file earns its slot by P (Fast -> PumpOff pruned, NO_PRUNE declines) and per-pairing stretches (Fast 1, Slow 2, MidEco 3/2) that no single stretch covers. Header and matrix agree (S M B P = M1 M2 M3 M4). None beyond the plant's simplicity.

## zone_lightmass_schedule
Model: lumped zone T' = ((Kp + U)/C)(T_set - T) under a three-level occupancy schedule (21 / 19 / 16 degC), the deployed zone having half the heat capacity (0.04 vs 0.02 /min) and a two-level schedule; the reference may select any level at any 5 min decision.
Property: T_L = T_R exactly at stretch lambda = 2: the light zone traces the reference zone's temperature at twice the speed.
Concern: the claim is a time-rescaling identity, and the reference is a fully permissive strategy, so the cover's witness is the left's own schedule replayed at half speed (the header says X is "an identity hop in the set point" and that the reference "must re-select the current level"): the right copies the left, which the rubric flags. The practical reading ("visits exactly the temperatures the reference permits") is weak because a strategy that may pick any level at any time permits everything in [16, 21] from any start. It is also brittle: the real ratio is 2.06, rounded to 2, and 1.9 / 2.1 decline, so the certificate does not cover the stated plant. The header also mislabels the choice mechanism as "M6" (M6 is the cut column; matrix shows M6 vacuous for this file).
Fix (RETHINK): make the reference the commissioned zone under the same two-level schedule (COMFORT/ECONOMY, with STANDBY dropped or reachable only from COMFORT) and claim a band |T_L - T_R| <= d at the true ratio with lambda searched on a grid around 2 (the drift after a set-point step at a 3 % rate mismatch decays, so a small d should certify), reporting the tightest d; or, if the exact identity is wanted as an S/M showcase, say so and state that the reference's permissiveness makes the claim a schedule-replay check. Either way fix the M6 label.
