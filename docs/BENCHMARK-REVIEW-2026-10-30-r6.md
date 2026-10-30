# Benchmark review, round 6 (2026-10-30; suite_v2 at 74ea076, 50 benchmarks)

Five fresh reviewer agents, 10 benchmarks each, rubric `docs/review-rubric.md` plus the accepted list of decided structural choices (below); the reviewers did not see earlier reviews, scores or fix lists. Every finding carries a severity (HIGH: claim false, letter from an artifact, domain doing the claim's work, stronger claim certifies, header number wrong; LOW otherwise). Findings are reviewer claims; every claim acted on was verified by a tool run first (the fix log is in `docs/OVERNIGHT2-2026-10-30.md`).

# Accepted list: decided structural choices (do NOT re-raise these as findings)

These are owner decisions or disclosed, measured departures. A finding that only restates one of
them is not a finding. You may still flag a header that states one of them WRONGLY (wrong number,
wrong reason), or a claim that is false, or a letter that comes from an artifact.

1. Assumption 1 (the right model is nonblocking and successor-complete) is kept as is; where a right
   model needs a stand-in mode to satisfy it (e.g. the Coast stand-in of `lit_drl_lane_control`), the
   stand-in is disclosed in the header and accepted.
2. Sampled switching on both sides (mode changes only at window boundaries of length at most
   epsilon), lock step unless the file states a stretch.
3. ONE physical evolve domain per benchmark: the same `evolve` text on every mode of both sides,
   physical limits only (hardware, sensor range, saturation, trips). Exception "kind (iii)": the two
   sides state the same physical trip in two reading scales, with a `# Domain conversion (kind iii):`
   header line (`train_ato_odometry`: 27.08 vs 28.21 = 27.08 / 0.96; `turbine_startup_gearratio`:
   13.31 vs 13.9755 = 1.05 x 13.31). A physical bound that is load-bearing and therefore sets a tight
   value (stated as such in the header, e.g. suspension travel, the overspeed trip, a 1 g limit) is
   accepted; flag it only if the bound is NOT physical (a set point, asymptote, reachable band).
4. Stretch 0 ("stutter", letter W: the witness waits) is opt-in per file (`[problem] stutter = true`)
   and used only where the claim is time-abstract (e.g. `lit_nahs25_salt_tank`: the source's Def. 8
   compares reachable sets, so distance 0); a stutter certificate does not promise that the reference
   keeps pace, and the header says so. Not a finding.
5. Literature files: the departures listed in a header as forced by the format are accepted; in
   particular `lit_lz21_vehicle_position` uses delta = 1 (the source's secret / non-secret separation,
   disclosed); the dRL file (`lit_drl_lane_control`) certifies dRL Goal 1 between sampled controllers
   and cannot state Goal 3 (a bounded-time fact; disclosed limitation); `lit_csf21_vehicle_bus` has the
   thermo file's certificate by the source's own design (acceleration-message priority makes the bus
   harmless; the content is in the negative exhibit, disclosed); `lit_gpt10_boost_converter` states
   only condition (3) of Definition 3.2 (the converse direction was measured and is not expressible
   in the format; disclosed).
6. Run time is not a concern (minutes are fine). Handoff counts are not a quality measure.
7. The suite has exactly 50 files; mechanism letters are measured by the paper's pipeline
   (`docs/paper-numbers/letters.md`), never read off a header.


## Ranked table (worst first)

| benchmark | P | R | C | overall | verdict | one-line reason | prev overall |
|---|---|---|---|---|---|---|---|
| `acc_spoof_limp` | 3 | 3 | 3 | 2 | RETHINK | No letter comes from the spoof (as the header admits); X comes only from LIMP starts above 34.5 m/s, which the header's own 2 s debounce makes unreachable | 2 |
| `charger_fast_tapers` | 3 | 2 | 2 | 2 | RETHINK | c = 1 is the tool's FULL over-approximation (physical lead 0); S not forced (λ=1 file CERTIFIED); D only from the FULL unit; wrong rate numbers | 2 |
| `fuelcell_chp_dos` | 3 | 2 | 4 | 2 | RETHINK | P and X come only from start-only LOW_L/HIGH_L windows; the Tin design range sets the verdict; the 7 K claim is weaker than the true 0 | 2 |
| `platoon_linkloss` | 4 | 4 | 3 | 2 | RETHINK | Rows are good and tight, but the only letter M comes from a single-mode right whose 0.1 s epsilon changes no run | 3 |
| `quad_light_lag` | 2 | 3 | 3 | 2 | RETHINK | The lag acts only on a constant feedforward, so it never interacts with the loop (built so Psi is conserved); the a bound equals the left's asymptote; the 0.8 tightness comes from the chosen Psi band | 3 |
| `quad_light_profiles` | 3 | 3 | 4 | 2 | RETHINK | B and X come from ECO/SPORT, which the witness never runs (removing them gives S M); the P-only loop ignores PX4's integral term | 3 |
| `rover_patrol_lag` | 4 | 2 | 4 | 2 | RETHINK | The requirement is real-time (1 m waypoint radius), but the certified claim is a re-timed one-sided order. The twin shows the letters come from the slack. | 2 |
| `hydro_rejection_gatecal` | 4 | 3 | 2 | 2 | POLISH | File's REJECT speed row is 0.07; the header states 0.09 (requirement) in four places | 2 |
| `h2_refuel_ambientbias` | 4 | 3 | 3 | 3 | RETHINK | D and I genuine; R is needed only for TOPOFF_L/STAGE3_R start pairs that no handoff produces; "real-time" wording false for those starts | 3 |
| `rover_terrain_2to4` | 3 | 3 | 3 | 3 | RETHINK | S M are needed only for wheel-ahead states that no run from a matched start reaches; the real-time form (+ row w_L <= v_R) certifies with I only | 3 |
| `turbine_startup_gearratio` | 4 | 3 | 3 | 3 | RETHINK | D comes only from overspeed starts above rated that no run reaches (start-only states). | 2 |
| `acc_tune_lag` | 3 | 3 | 4 | 3 | POLISH | tau = 0.32 is picked so the exact ratio-2 claim holds; the exact modal rows are correct; row 3's 3.34 is set by the guard/box geometry far outside any reachable state | 2 |
| `canal_gate_notches` | 3 | 4 | 4 | 3 | POLISH | X genuine, tolerance justified, law dependence measured; but RAISE/LOWER are start-only (HOLD band is forward invariant, no disturbance), so the "law dependence" rests on start-only modes | 3 |
| `elevator_start_discbrake` | 3 | 4 | 3 | 3 | POLISH | R and D are real (brake-lift re-timing); header's rest position (19.96 m) is wrong, the trip rests at 20.07 m, 7 cm past the 20 m landing | 2 |
| `engine_start_highidle` | 4 | 3 | 2 | 3 | POLISH | R D I genuine, but the header calls the 4 % bound "a real-time one": in lock step from a normal start the gap reaches 5.5 % | 2 |
| `flaps_slow_approach` | 4 | 4 | 3 | 3 | POLISH | Clean per-mode S; the 25/10 tight values come from VFE/VLS (accepted, physical), but the header also says the domain is "not load-bearing" (true only because the guards repeat [130, 200]) | 4 |
| `platoon_profiles` | 4 | 3 | 3 | 3 | POLISH | The P_0.45 row is implied by the other two rows. The "tight" 3.34 / 1.50 and their derivation from W/kp are not the dynamics' values. | 3 |
| `rampmeter_poll_2to1` | 3 | 3 | 2 | 3 | POLISH | M B genuine; "tightest 7.00" contradicts the header's own certifying 5.00 (a structural fixed point); k domain is the reachable band, not the 45 capacity limit | - |
| `reactor_feed_wireless` | 3 | 4 | 3 | 3 | POLISH | Tolerance tight at 8 (two feed levels); B and P are real, but both hold only in a +-2 K window of the coolant range; crude thermal model; two verdict blocks | 3 |
| `rover_terrain_6to12` | 3 | 3 | 4 | 3 | POLISH | the route-grade domain theta_p <= 0.02 sets the slip verdict; 3 of the 6 new coordinates are output-only (dim 12 inflated) | 3 |
| `sat_detumble_weak` | 4 | 3 | 3 | 3 | POLISH | The exact energy identity is correct (the couplings do no work); header says X comes from the derating but also says X persists at k_L = 0.5; history noise | 3 |
| `train_ato_odometry` | 4 | 3 | 3 | 3 | POLISH | Good cause/tolerance story; M and B come from cross-level pairings that "same commands" excludes and are not forced; verdict block predates the 10-29 domain change | 4 |
| `ventilator_vc_cuffleak` | 3 | 4 | 4 | 3 | POLISH | Good physics and ISO requirements, D is real; but the domain `V <= 0.404`, `V - 0.4 t <= 0` is a reachable band (one breath from PEEP) and it carries the INSP->EXP handoff | 4 |
| `watertank_twospeed` | 3 | 4 | 3 | 3 | POLISH | Tight rows with cause dependence; P comes from the Fast -> PumpOff edge into a sink that no flow ever enters (start-only); the verdict block predates the 1.5 row | 3 |
| `gantry_speed_zones` | 4 | 3 | 4 | 3 | KEEP | A uniform override is a time reparametrization, so S and M are honest; the claim is exact at the file's own range (0.00 certifies), and 0.01 is justified as the clearance requirement; the zone schedule is not load-bearing | 3 |
| `lit_csf21_vehicle_bus` | 3 | 3 | 5 | 3 | KEEP | Source's equality claim, trivial by the source's design (accepted #5); negative exhibit carries the content | 2 |
| `lit_drl_lane_control` | 3 | 3 | 4 | 3 | KEEP | Faithful, fully disclosed dRL Goal 1. Content is static guard inclusion (margin 0 and Rsys = Lsys both certify); Coast stand-in accepted | 2 |
| `lit_girard08_robot` | 4 | 3 | 4 | 3 | KEEP | The source's relation with tight 0.16. Its relational part is the identity w_L = y2_R. The abstraction is enlarged (disclosed). | 3 |
| `lit_lz21_vehicle_position` | 4 | 3 | 4 | 3 | KEEP | Faithful with accepted delta = 1; the in-tool invariant is a copy witness (constant offset, certifies at delta 0); the delta content is the static coverage check | 2 |
| `lit_nahs25_salt_tank` | 3 | 3 | 5 | 3 | KEEP | Faithful Def. 8 value 0 via W; with the key the value does not depend on the attack bound (disclosed) | 4 |
| `rover_ladder_2to3` | 4 | 3 | 4 | 3 | KEEP | Honest ladder rung, no letter; the claim is a plain monotone comparison (slower integrator stays behind), psi never enters a row | 3 |
| `rover_ladder_3to6` | 4 | 3 | 4 | 3 | KEEP | A ladder rung. The relational rows are nearly structural, and the step's new channel (pitch) is a left-only bound. | 3 |
| `rover_ladder_6to8` | 3 | 3 | 4 | 3 | KEEP | As 8to12; also the LTR row at 0.8 is implied by the heading and roll rows (disclosed) | 2 |
| `rover_ladder_8to12` | 3 | 3 | 4 | 3 | KEEP | Relational content is only clearance (v, s); S and I also present with identical ODEs; I rests on a left-only reachable-set guard v <= c | 3 |
| `sat3w_detumble_phases` | 3 | 4 | 4 | 3 | KEEP | Exact energy identity is a good NRA claim; time unit stylized (gain 100x wheel authority), flight period slower than design model | 3 |
| `sat_detumble_phases` | 3 | 4 | 4 | 3 | KEEP | The energy identity through gyroscopic cancellation is real content. Gains and time unit are stylized (disclosed, and the scaled test certifies). | 3 |
| `antenna_track_kvretune` | 4 | 4 | 3 | 4 | POLISH | Clean servo-lag D; STOW row 0.25 is loose (tight 0.085) and not a requirement; header carries suite-history noise and two verdict blocks | 4 |
| `furnace_program_timebase` | 4 | 3 | 4 | 4 | POLISH | clean derivation (6.4 = 0.2 x 32); AMS 2750 Class 3 is spatial uniformity, not run-to-run tracking | 4 |
| `acc_spoof_lag` | 3 | 4 | 4 | 4 | KEEP | exact dominant-mode row, checked by hand; lag tau = 0.375 picked for rational roots (disclosed) | 2 |
| `acc_tune_limp` | 4 | 4 | 4 | 4 | KEEP | A real tune spec (exact at 3/2) plus a LIMP order row. Every letter is explained. The 40 m/s domain top is not justified. | 2 |
| `bottling_fill_strainer` | 4 | 4 | 4 | 4 | KEEP | Offset 1.2 mL exact and derived; S tied to the flow ratio; I is a real mode fact | 4 |
| `lit_csf21_vehicle_thermo` | 4 | 4 | 5 | 4 | KEEP | The source's H-equivalence, faithful. Departures and the cause test (leaky twin declines) are disclosed. | 3 |
| `lit_csf25_salt_tank_hold` | 4 | 4 | 4 | 4 | KEEP | faithful encoding of the source's proof step, tight slopes; start-only left is argued in departure (5) | - |
| `lit_freedm_meter` | 4 | 4 | 4 | 4 | KEEP | the source's Prop. 11 argument, X from a real per-window choice, departures forced and ablated | 3 |
| `lit_gpt10_boost_converter` | 4 | 4 | 4 | 4 | KEEP | The source's condition (3) at the source's precision 2.6. Tight value 2.58 is disclosed. Small wording problems. | - |
| `platoon_latency` | 4 | 4 | 4 | 4 | KEEP | The latency allowance J·τ/kp is derived, scales with τ and is tight. The Q_0.5 row is redundant. | 4 |
| `rover_terrain_4to6` | 3 | 4 | 4 | 4 | KEEP | Good refinement chain with real I; sigma/H at requirement values with tight values reported; zs <= 0.12 and the w floor are tuned for forward invariance | 3 |
| `syringe_relay_prearm` | 4 | 4 | 4 | 4 | KEEP | Real relay hazard (slack take-up, 11.1 min interruption); R and D measured against the cause; header agrees with matrix | 4 |
| `tank_dos_3to1` | 4 | 4 | 4 | 4 | KEEP | DoS hold measured against the requirement (0.72 tight, 0.8 required, 40 s violates it); M and I are real; the left lists one more successor than it needs (harmless) | 4 |
| `watertank` | 4 | 4 | 4 | 4 | KEEP | tolerance = offset, tight both in c and λ; High is start-only on both sides but carries no letter | 3 |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 8 | 28 | 14 | 0 |

Verdicts: KEEP 24, POLISH 16, RETHINK 10, DROP 0. Overall >= 4: 14/50 (28 %). Overall < 3: 8.

## Delta vs previous round

Previous histogram (1..5): 0, 17, 23, 10, 0 over 50; this round: 0, 8, 28, 14, 0 over 50.

Up: `acc_spoof_lag` 2->4, `acc_tune_lag` 2->3, `acc_tune_limp` 2->4, `elevator_start_discbrake` 2->3, `engine_start_highidle` 2->3, `lit_csf21_vehicle_bus` 2->3, `lit_csf21_vehicle_thermo` 3->4, `lit_drl_lane_control` 2->3, `lit_freedm_meter` 3->4, `lit_lz21_vehicle_position` 2->3, `rover_ladder_6to8` 2->3, `rover_terrain_4to6` 3->4, `turbine_startup_gearratio` 2->3, `watertank` 3->4.

Down: `flaps_slow_approach` 4->3, `lit_nahs25_salt_tank` 4->3, `platoon_linkloss` 3->2, `quad_light_lag` 3->2, `quad_light_profiles` 3->2, `train_ato_odometry` 4->3, `ventilator_vc_cuffleak` 4->3.

New in this round: `lit_csf25_salt_tank_hold`, `lit_gpt10_boost_converter`, `rampmeter_poll_2to1`.

Not in this round: `insulin_basal_cgmloss`, `lit_drl_car_stop`, `zone_lightmass_schedule`.

## Reviewer notes by group

### g1

# Review r6, group g1 (10 benchmarks)

Inputs: review-rubric.md, ACCEPTED-LIST.md, suite_v2/<name>/input.txt, matrix.md, letters.md. Read only.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| syringe_relay_prearm | 4 | 4 | 4 | 4 | KEEP | Real relay hazard (slack take-up, 11.1 min interruption); R and D measured against the cause; header agrees with matrix |
| antenna_track_kvretune | 4 | 4 | 3 | 4 | POLISH | Clean servo-lag D; STOW row 0.25 is loose (tight 0.085) and not a requirement; header carries suite-history noise and two verdict blocks |
| bottling_fill_strainer | 4 | 4 | 4 | 4 | KEEP | Offset 1.2 mL exact and derived; S tied to the flow ratio; I is a real mode fact |
| hydro_rejection_gatecal | 4 | 3 | 2 | 2 | POLISH | File's REJECT speed row is 0.07; the header states 0.09 (requirement) in four places |
| sat3w_detumble_phases | 3 | 4 | 4 | 3 | KEEP | Exact energy identity is a good NRA claim; time unit stylized (gain 100x wheel authority), flight period slower than design model |
| lit_nahs25_salt_tank | 3 | 3 | 5 | 3 | KEEP | Faithful Def. 8 value 0 via W; with the key the value does not depend on the attack bound (disclosed) |
| rover_ladder_8to12 | 3 | 3 | 4 | 3 | KEEP | Relational content is only clearance (v, s); S and I also present with identical ODEs; I rests on a left-only reachable-set guard v <= c |
| train_ato_odometry | 4 | 3 | 3 | 3 | POLISH | Good cause/tolerance story; M and B come from cross-level pairings that "same commands" excludes and are not forced; verdict block predates the 10-29 domain change |
| rover_ladder_6to8 | 3 | 3 | 4 | 3 | KEEP | As 8to12; also the LTR row at 0.8 is implied by the heading and roll rows (disclosed) |
| lit_csf21_vehicle_bus | 3 | 3 | 5 | 3 | KEEP | Source's equality claim, trivial by the source's design (accepted #5); negative exhibit carries the content |

## Per benchmark

### syringe_relay_prearm
- Model: two-channel noradrenaline syringe pump in relay mode; deployed relay pre-arms channel 2 (takes up 1 mm driver slack before switchover), validated relay starts it from rest (11.1 min interruption).
- Property: delivered volumes equal up to re-timing in every mode; before switchover C equal and b_R <= b_L; after, C_R <= C_L (the pre-armed relay never leaves less drug in plasma than the validated one at the matched instant).
- Concern (LOW): the comparison is at re-timed instants (right-only segment absorbs 11.1 min), so "no added hypotension risk" is a statement along matched histories, not at equal wall-clock time; the header says "re-timed" but the requirement sentence (l.52-54) reads as a wall-clock claim. Suggest one clause saying so.
- Concern (LOW): "b_R <= b_L + 0.01 DECLINES" (l.51) reads as a weaker row declining; add "(not inductive)" so it is not read as a tightness claim.

### antenna_track_kvretune
- Model: elevation axis, type-1 loop x' = K (c - x), K 30 (commissioned) vs 20 (retuned after gearbox change), over track to LOS then slew to stow.
- Property: TRACK |x_L - x_R| <= 0.035 (a tenth of the 0.36 deg beamwidth) plus right lag envelope; STOW/STOWED 0.25 band.
- Concern (LOW): STOW/STOWED row 0.25 is neither a requirement nor tight (tight 0.085, l.233); its justification "the retuned axis's own following error" bounds x_L - c_L, not x_L - x_R. Either state 0.085 or say plainly it is a chosen post-LOS envelope.
- Concern (LOW): TRACK -> STOWED successor is dead (TRACK keeps c <= 47 < 90); it inflates the handoff count (6/6) but no letter depends on it.
- Concern (LOW): l.267-283 (suite status, reserve history, tunnel_jetfan_pairout, duplicate re-measured verdict block) is process history; cut to one dated verdict block.
- Fix: header only.

### bottling_fill_strainer
- Model: flowmeter-controlled filler, clogged strainer cuts flow to 85 %, the commissioned in-flight correction (8 mL) is kept, so the deployed fill ends 1.2 mL short.
- Property: predicted final volume Psi_L = Psi_R - 1.2 exactly, u_L <= u_R, V_L <= V_R; gives shortfall <= 1.2 mL < 2 mL margin.
- Concern (LOW): FILL has u' = 0, so the load-bearing I atom u >= 1 is a constant mode fact; fine, but worth one phrase that I is "u is the fully open constant", to pre-empt "trivial cut" objections.
- Concern: none substantive.

### hydro_rejection_gatecal
- Model: hydro unit, gate transducer reads 0.02 low; on grid the droop loop holds the load reference, after the breaker opens the gate goes to speed-no-load and the unit accelerates.
- Property: ONGRID w equal, |g_L - g_R| <= 0.027 (3 % power dispatch tolerance); REJECT |w_L - w_R| <= speed band, gate 0.027.
- Strongest concern (HIGH): the file's REJECT row is `w[r] <= w[l] + 0.07 and w[l] <= w[r] + 0.07` (input.txt l.124), but the header states 0.09 in the Property (l.31), the Requirement derivation (l.36, "rounded down to 0.09"), the tightness sentence (l.43) and the D argument (l.50, l.61). 0.07 is neither the requirement (0.09) nor the tight value (about 0.027 at gate 0.027, by l.40-42). Either the header or the row is wrong, and the D measurements "at speed 0.09" may not describe this file.
- Fix: set the REJECT speed constant to 0.09 (the stated requirement) or rewrite the header for 0.07 with its justification; re-measure the uniform-row D claims at the stated value.

### sat3w_detumble_phases
- Model: three-wheel gyrostat (full couplings) vs a decoupled design model, same DETUMBLE/FINE phase logic, flight decision every 2 s vs design 1 s.
- Property: body kinetic energy equal on both sides at every instant (E' = -2kE on both; the coupling terms do no work, checked here by hand: both cubic groups cancel).
- Concern (LOW): letters M, I, X all come from the period ratio and the shared phase logic, not from the refinement (header says so for X and M; true for I too). The 2 s "two-sample debounce" flight period against a 1 s design model is defensible but reads as chosen for M; keep the justification sentence prominent.
- Concern (LOW): gain stylized (about 100x wheel authority; disclosed with a /1000 rescale test). Fine.

### lit_nahs25_salt_tank
- Model: source's brine tank, salt sensor attack bounded by 3, projected exactly onto the level; genuine On iff xp >= 25.
- Property: xp_L = xp_R with both >= 25, at stretch 1 or stutter 0 (genuine waits while the attacked Off holds): the source's Def. 8 forward distance 0.
- Concern (LOW): with the key the value is 0 for every attack bound (0.01 to 10, l.59-61), so as a robustness measure the benchmark does not discriminate attacks; this is faithful to Def. 8 and disclosed. Accepted #4 covers the stutter.
- Concern (LOW): matrix M1 cell says "λ=1 everywhere" while the cover's Off_L pairings are at stretch 0; letters.md records W, so no contradiction, but the matrix row could note stutter.

### rover_ladder_8to12
- Model: 12-DOF rover (heave/roll inertia, tire slip) against the 8-DOF rover, three grade zones, lambda in [1, 1.25] from the timetable.
- Property: clearance v_L <= v_R, s_L <= s_R (the only relational rows), left heading/roll/LTR/lane requirement rows, right plan tolerances.
- Concern (LOW): S and I persist with left ODEs replaced by the right's (l.155-159, 241-243); the step's own dynamics also need S (+0.052 m in 8 s at lambda 1), so S is grounded, but the "earns its place as a ladder rung" sentence is rhetoric; cut it.
- Concern (LOW): I rests on the left-only guard conjunct v <= c (a set point, a reachable-set fact, l.268-275). It excludes no reachable state and is disclosed, but it is a start restriction on the universally quantified side, not controller structure; say "reachable-state start condition" in the mechanisms line.
- Concern (LOW): most rows are unary; the relational claim is clearance only. Acceptable for a refinement ladder.

### train_ato_odometry
- Model: ATO speed loop with wheel-diameter parameter not updated (tachometer reads 0.96), three performance levels switchable every 0.5 s.
- Property: 0 <= v_L - v_R <= 1.11 m/s (ETCS warning margin) against a re-timed design run; tight 1.07, model bound 1.042.
- Concern (LOW, borderline HIGH): the scenario says "same ATO, same levels, same commands" (l.377), but M and B come only from cross-level pairings (PL1_L against PL3_R at 6/5, budget 2, branch 2). Header l.450-451: RELCERT_NO_PAIR_STRETCH=1 certifies at budget 1 with no branching ("S without M and B"). So M and B are properties of the default cover's search order, not forced by the claim; the l.411-412 sentence "PL1_L and PL2_L need stretches above 1" is true only for per-pairing covers. Reword, or state that the certificate also covers an independently commanded design train (a stronger claim).
- Concern (LOW): the S window is narrow, [1.07, 1.13), and S at 1.11 comes only from design-train starts above 26.64 m/s decelerating toward 25 (gap equilibrium 0.04 v_R / 0.96). Physical (section entry above the permitted speed, below the EBI), but say so.
- Concern (LOW): the main verdict block is dated 2026-10-26, before the 2026-10-29 kind-(iii) domain change; only "either single box CERTIFIES" is dated 10-29. Re-date or re-measure the tight 1.07 and the SYNC 1.13 on the current domain.

### rover_ladder_6to8
- Model: 8-DOF rover (yaw and pitch inertia) against the 6-DOF rover, same zones and timetable.
- Property: clearance plus left heading/pitch/roll/LTR rows and right plan tolerances.
- Concern (LOW): the LTR row at 0.8 is implied by the heading and roll rows (0.771, l.565-567, disclosed); it adds nothing to the claim. Either state it at a non-implied value or call it a restatement.
- Concern (LOW): heading rows "any value certifies (0.05 tested)": a unary contracting box, not a tightness result; fine as requirement.
- Same LOW notes as 8to12 on v <= c and the "earns its place" sentence.

### lit_csf21_vehicle_bus
- Model: source's car + thermostat over one bus with acceleration-message priority; attacked thermostat reading.
- Property: d and v equal at every instant (source's {vp}-equivalence).
- Concern: none beyond accepted #5 (bus not load-bearing; content in the negative exhibit, disclosed).

## Findings with severity

| # | benchmark | severity | finding | check |
|---|---|---|---|---|
| 1 | hydro_rejection_gatecal | HIGH | Header number wrong: REJECT speed band is 0.07 in the file (l.124) but 0.09 in the header (l.31, 36, 43, 50, 61) | Read l.124 vs l.31; run the file with 0.09 in both REJECT w rows: expect CERTIFIED; re-run the uniform-row D checks at the constant actually in the file |
| 2 | train_ato_odometry | LOW (borderline HIGH) | M and B come from cross-level pairings the scenario ("same commands") excludes; not forced (NO_PAIR_STRETCH=1 certifies at budget 1, no branch) | RELCERT_NO_PAIR_STRETCH=1: letters S only (header l.450-451 already measured) |
| 3 | train_ato_odometry | LOW | Verdict block dated before the 10-29 domain change | re-run default, SYNC at 1.13, tight 1.07/1.06 on the current file |
| 4 | train_ato_odometry | LOW | S hinges on design-train starts in (26.64, 27.08] m/s; say so | SYNC at 1.11 with right top 26.5 (left 26.5/0.96): expect CERTIFIED |
| 5 | antenna_track_kvretune | LOW | STOW row 0.25 loose (tight 0.085), justification bounds x_L - c_L not x_L - x_R; dead TRACK -> STOWED edge; process history in header | header edit |
| 6 | rover_ladder_6to8, 8to12 | LOW | I rests on left-only reachable-set guard v <= c; S/I persist with identical ODEs; rhetoric "earns its place" | header edit |
| 7 | rover_ladder_6to8 | LOW | LTR row at 0.8 implied by heading+roll rows | header edit or restate |
| 8 | syringe_relay_prearm | LOW | Requirement sentence reads as wall-clock while the claim is re-timed; "b_R <= b_L + 0.01 DECLINES" needs "(not inductive)" | header edit |
| 9 | sat3w_detumble_phases | LOW | M, I, X independent of the refinement cause (period ratio, phase logic) | none; disclosed |
| 10 | lit_nahs25_salt_tank | LOW | value 0 independent of attack bound; matrix M1 shows λ=1 for stutter pairings | none; disclosed |
| 11 | bottling_fill_strainer | LOW | I atom is a constant (u' = 0) mode fact; one phrase to pre-empt "trivial cut" | header edit |

### g2

# Review r6, group g2 (10 benchmarks)

Inputs: rubric, ACCEPTED-LIST, the 10 input.txt files, matrix.md and letters.md rows. Read only; nothing run.
Matrix/letters rows were checked against every header: verdicts, times, covers (λ, budget, branch), pruned edges, handoff counts and letters all agree. No header number contradicts matrix.md or letters.md.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| lit_csf21_vehicle_thermo | 4 | 4 | 5 | 4 | KEEP | The source's H-equivalence, faithful. Departures and the cause test (leaky twin declines) are disclosed. |
| acc_tune_limp | 4 | 4 | 4 | 4 | KEEP | A real tune spec (exact at 3/2) plus a LIMP order row. Every letter is explained. The 40 m/s domain top is not justified. |
| sat_detumble_phases | 3 | 4 | 4 | 3 | KEEP | The energy identity through gyroscopic cancellation is real content. Gains and time unit are stylized (disclosed, and the scaled test certifies). |
| rover_patrol_lag | 4 | 2 | 4 | 2 | RETHINK | The requirement is real-time (1 m waypoint radius), but the certified claim is a re-timed one-sided order. The twin shows the letters come from the slack. |
| platoon_latency | 4 | 4 | 4 | 4 | KEEP | The latency allowance J·τ/kp is derived, scales with τ and is tight. The Q_0.5 row is redundant. |
| lit_gpt10_boost_converter | 4 | 4 | 4 | 4 | KEEP | The source's condition (3) at the source's precision 2.6. Tight value 2.58 is disclosed. Small wording problems. |
| rover_ladder_3to6 | 4 | 3 | 4 | 3 | KEEP | A ladder rung. The relational rows are nearly structural, and the step's new channel (pitch) is a left-only bound. |
| turbine_startup_gearratio | 4 | 3 | 3 | 3 | RETHINK | D comes only from overspeed starts above rated that no run reaches (start-only states). |
| lit_girard08_robot | 4 | 3 | 4 | 3 | KEEP | The source's relation with tight 0.16. Its relational part is the identity w_L = y2_R. The abstraction is enlarged (disclosed). |
| platoon_profiles | 4 | 3 | 3 | 3 | POLISH | The P_0.45 row is implied by the other two rows. The "tight" 3.34 / 1.50 and their derivation from W/kp are not the dynamics' values. |

## Per benchmark

### lit_csf21_vehicle_thermo
- **Model:** the CSF'21 car (d, v, temp). On the left the cabin-temperature reading is attacked (the thermostat is free); on the right the genuine car's thermostat reads the true temperature. Lock step, 6 modes per side (action x thermostat).
- **Property:** d_L = d_R and v_L = v_R at every instant, so the attacker cannot change how the car moves (the source's Fig. 8 equivalence).
- **Strongest concern:** none of substance. The certificate is near-structural, because the d and v flows do not read temp. The header answers this with the leaky negative twin (DECLINED), which is the right cause test.
- LOW: the witness takes the left's action. The header (l.75-77) argues this is the source's claim, which is acceptable.

### acc_tune_limp
- **Model:** a retuned ACC (CRUISE 0.75 /s, plus a latched LIMP map toward 25 m/s) against the stock controller (NORMAL, COMFORT, SPORT, DISENGAGE). λ = 3/2.
- **Property:** CRUISE v_L = v_R at stretch 3/2 (the tune is NORMAL run 1.5x faster). LIMP v_L <= v_R: the limp map never makes the car faster than the reference.
- **Strongest concern (LOW):** the CRUISE row is an exact re-timing identity. That is the property platoon_profiles was changed to avoid ("no tolerance content"). It is acceptable here only because it is stated as the tune's specification. The LIMP row carries the content.
- LOW: the domain top of 40 m/s is not justified as physical (l.215). The LIMP face condition 7.5 - 0.2 v >= 0 fails only above 37.5, so the I letter's LIMP cut exists only because the domain exceeds 37.5.
  - Check: set the domain top to 37.5 on both sides. If RELCERT_NO_CUT=1 then certifies, I depends on that constant.
- LOW: DISENGAGE is dead (the rows force v_R >= 20). No letter is claimed from it.

### sat_detumble_phases
- **Model:** a gyrostat (bilinear couplings) against its decoupled design model, same phase logic. The flight software decides every 2 s, the design model every 1 s.
- **Property:** E_L = E_R in both phases: the design model's energy prediction is exact for the full body.
- **Strongest concern:** the gains are three orders above magnetorquer authority and need isotropic damping. Both points are disclosed, the 1/1000-gain run certifies, and the claim is shown false at realistic x/y gains.
- LOW: the SAFE sink is never an admissible start (the rows force E_R = E_L <= 1), so it is dead structure. No letter is claimed from it (no P).
- LOW: M and I come from a 2:1 period ratio that is a design value of this file. The debounce reading is plausible.

### rover_patrol_lag
- **Model:** a rover with motor lag (τ = 0.1875 s) against its first-order planning model, same zone planner, λ in [1, 3/2].
- **Property:** s_L <= s_R + 1 with the look-ahead strengthening P_L <= P_R + 0.375, against a plan that may be re-timed up to 1.5x and advanced alone.
- **Strongest concern:** the requirement is justified as the 1 m waypoint acceptance radius (l.524-526), which is a real-time statement. The certified claim is explicitly not real time (l.527-530: RELCERT_SYNC=1 declines). With λ up to 1.5 and right-only advances, the matched plan may run faster than the rover in every zone, so "never more than 1 m ahead of the plan" says little.
- The header's own twin (l.566-572) shows that S, M, R and B appear without the lag. They come from the 1 m slack admitting a rover already in the next zone. Only the lead bound (0.75) reads the cause.
- **Fix:** either
  1. justify the slack by a re-timing requirement (schedule tolerance, why 3/2), not the waypoint radius; or
  2. state the λ = 1 claim with the tolerance that certifies synchronously, so that the requirement and the claim match.

### platoon_latency
- **Model:** a CACC follower whose feed-forward is 0.2 s late (Padé lag; predecessor jerk ±J at the ISO limit) against the ideal-link design.
- **Property:** |Δg| <= 4 = Jτ/kp, the static spacing allowance of the latency, with derived modal rows, the deployed's gap and TTC floors, and |e_L| <= Jτ.
- **Strongest concern:** none. I re-derived the forms Q_0.25' = -0.5 Q + e, Q_0.5' = -0.25 Q + e and d/dt(g + 2r) = -0.25(g + 2r - 20) + 2e, and the tight values 4, 1 and 16 follow.
- LOW: |Q_0.5| <= 2 is implied by the other rows, since Q_0.5 = Q_0.25 + 0.25 Δg gives at most 1 + 1. Call it a restatement rather than a derived bound.
- LOW: the header carries a lot of round history (AEB timings, 1.2 s vs 2.0 s) that can be trimmed.

### lit_gpt10_boost_converter
- **Model:** the GPT'10 boost converter (right) against a 48-mode drift model of its lattice abstraction (left), lock step at τ_s = 0.5.
- **Property:** V(x_L - x_R)^2 <= 2.6^2, the source's relation at its precision, in the direction of condition (3).
- **Strongest concern:** none. 2.6 is the source's value, and the header discloses tight 2.58 (l.46-52).
- LOW: the first line ("a converter ... is matched ... by every run of its abstraction") reads as the reverse of the certified direction. The certified direction is that every abstraction run is matched by a converter run.
- LOW: l.32-34 says every abstraction transition "ends a left window". With one constant vertex drift, a single window reaches only 24 displacements. The η-ball is covered only by switching the drift vertex at sub-window boundaries (allowed, since windows are at most ε). The witness keeps p across them because it hops into the left's p. Say so.

### rover_ladder_3to6
- **Model:** the L6 rover (pitch, heave, roll moving) against L3 (attitude frozen), synchronous.
- **Property:** v_L <= v_R, s_L <= s_R, psi_L = psi_R, and |theta_p_L| <= 0.25 (tight 0.23; 0.25 is the tilt-stabilizer requirement).
- **Strongest concern:** the relational rows are nearly structural. v and psi have identical dynamics, and s_L <= s_R follows from the extra loss terms. The step's new content is a unary pitch bound on the left, held by the suspension-travel bound (accepted, item 3).
- R = 3 is acceptable for a ladder rung.
- LOW: l.46-47 does not explain why s_L <= s_R + 1 DECLINES. Presumably the left can then start in the next zone (MODER/FLAT faster) while the right is behind.

### turbine_startup_gearratio
- **Model:** an NREL 5-MW start-up whose controller uses a stale gear ratio (reads 5 % low) against the correct start-up. The domains are the overspeed trip in two reading scales (kind iii, accepted).
- **Property:** w_L <= 1.05 w_R in SPINUP, RAMP and STOP; w_L <= 1.05 w_R + 0.061 in GEN. The deployed never turns faster than 1.05 times a reference start-up.
- **Strongest concern (HIGH):** the GEN tolerance, and therefore D, exists only for GEN pairs above rated speed (w_R > 12.1, w_L > 12.705).
  - No run reaches those states. GEN flows toward 12.705 (left) and 12.1 (right); SPINUP and RAMP exit below 7.245. They exist only as admitted starts (the header's "recoveries from any admitted overspeed", l.128-129).
  - Below rated, the exact GEN row is inductive. On the face w_L = 1.05 w_R, d/dt(1.05 w_R - w_L) = 0.03025 - 0.0025 w_R >= 0 iff w_R <= 12.1.
  - This is the same start-only class as the AEB modes that round 4 removed from the platoon files (D lost there).
- **Fix:** put the rated ceilings into the claim as uniform conjuncts, as platoon_latency did with |e| <= W. Then D goes, or else the header has to say that D is carried by start-only overspeed states.
- LOW: R, P and I are disclosed as properties of the one-sided claim (present at g = 1). That is honest but leaves the cause only in the factor 1.05.

### lit_girard08_robot
- **Model:** the 6-D robot with its dynamic tracking controller (left) against the 2-D planner model (right), six locations, lock step.
- **Property:** w_L = y2_R and the source's quadratic <= 0.16 (precision 0.4), with tight 0.16 equal to β².
- **Strongest concern:** the relational part is an identity. The planner state equals the controller's internal reference, both move at the same heading, and the witness copies w. All the quantitative content is a left-only Lyapunov bound.
  - This is faithful to the source's V (|w - y2| = 0 at V <= 0.4), but the header should say it in one line.
- The enlarged abstraction (extra edges, larger guards) is disclosed as weaker than the source.

### platoon_profiles
- **Model:** a CACC follower in SPORT (kp 0.18, kd 0.85) against the NORMAL design, re-timed by λ = 6/5.
- **Property:** |Δg| <= 3.34, |P_0.4| <= 1.14 and |P_0.45| <= 1.50 on the re-timed pair, plus the deployed's floors.
- **Strongest concern (HIGH):** the stated constants and their "tight" evidence do not describe the dynamics.
  1. P_0.45 = P_0.4 + 0.05 Δg, so |P_0.45| <= 1.14 + 0.05 x 3.34 = 1.307 follows from the other two rows. Rows with 1.49 and with 1.50 are the same relation, yet the header reports 1.49 DECLINED and 1.50 CERTIFIED (l.63). That tightness comes from the tool's proof route, not from the claim.
  2. The cause "W/kp = 0.6/0.18 = 3.33" (l.61) ignores the cap the header itself uses for P_0.4. At Δρ = 0, |r_L| <= 10 gives |r_R| <= 8.33, so w <= 0.5 and the static gap is 2.78.
     - Face check: Δg' = P_0.4 - 0.4 Δg <= 1.14 - 0.4c < 0 for every c > 2.85.
     - The P_0.4 face needs only b >= 1 + 0.04c.
     - So |Δg| <= 2.9 with |P_0.4| <= 1.12 is inductive face by face.
- **Fix:** drop the redundant row or state its implied value, recompute the cause (capped W), and re-bisect jointly. If the tool cannot reach about 2.8, say that 3.34 is the tool's route value.
- LOW: |r| <= 10 is called the "rated closing rate (radar)". It is the CACC engagement spec, which is the guard and is forward invariant. The dependence is legitimate, but the label is wrong.

## Findings with severity

| # | benchmark | sev | finding | exact check |
|---|---|---|---|---|
| 1 | turbine_startup_gearratio | HIGH | Letter D (and the 0.061 GEN tolerance) comes only from GEN states above rated speed that no run reaches. They are admitted starts only (start-only structure). | Set every row to `w_L <= 1.05 w_R and w_L <= 12.705 and w_R <= 12.1` (uniform, exact). Expect CERTIFIED and letters R P I (no D). |
| 2 | platoon_profiles | HIGH | The P_0.45 row is implied by the P_0.4 and Δg rows (bound 1.307). "1.49 declines" (l.63) therefore compares two identical relations, so the stated tight value is not a property of the claim. | (a) Same file with `\|P_0.45\| <= 1.31`: the same relation, expect CERTIFIED. (b) Remove the P_0.45 row: expect CERTIFIED. A DECLINED result in either means the tightness is the tool's route. |
| 3 | platoon_profiles | HIGH | Header number wrong: the cause "W/kp = 3.33 at the rated closing rate" (l.61-62) ignores the r_L cap. The semantic static bound is 2.78, and the joint fixpoint (Δg about 2.8-2.9, P_0.4 about 1.12) is inductive face by face. The stated 3.34 is not tight in the claim's semantics. | Rows `\|Δg\| <= 2.9, \|P_0.4\| <= 1.12`, no P_0.45 row (floors unchanged), λ = 6/5: expect CERTIFIED. |
| 4 | rover_patrol_lag | LOW (borderline) | The waypoint-radius requirement is real-time, but the certified claim is a re-timed one-sided order. The letters come from the slack, per the header's twin. Disclosed, so not false. | n/a (claim reframing) |
| 5 | acc_tune_limp | LOW | The domain top of 40 m/s is unjustified. The LIMP cut is needed only because 40 > 37.5. | Domain top 37.5 on both sides with RELCERT_NO_CUT=1: if CERTIFIED, I hinges on that constant. |
| 6 | acc_tune_limp | LOW | The CRUISE exact row is a pure re-timing identity. That is fine as the tune spec, but inconsistent with platoon_profiles' round-4 reasoning. | n/a |
| 7 | sat_detumble_phases | LOW | The SAFE sink is dead (never admissible). M and I come from a file-chosen 2:1 period ratio. | n/a |
| 8 | platoon_latency | LOW | The Q_0.5 row is implied by the Q_0.25 and Δg rows. History clutter in the header. | n/a |
| 9 | lit_gpt10_boost_converter | LOW | The first line reverses the direction. "Every transition ends a left window" needs sub-window drift switching. | n/a |
| 10 | rover_ladder_3to6 | LOW | The relational rows are near-structural, and the pitch row is left-only. Why s_L <= s_R + 1 declines is unexplained. | n/a |
| 11 | lit_girard08_robot | LOW | The relational part is the identity w_L = y2_R; say so. | n/a |
| 12 | platoon_profiles | LOW | "|r| <= 10, rated closing rate (radar)" is mislabelled: it is the CACC engagement spec (the guard). | n/a |
| 13 | lit_csf21_vehicle_thermo | LOW | The witness takes the left's action. This is argued as the source's claim, so it is acceptable. | n/a |

### g3

# Review r6, group g3 (10 benchmarks)

Inputs: the rubric, ACCEPTED-LIST.md, the 10 input.txt files, the matrix.md and letters.md rows.
Read only; the only computations are plain lock-step Euler simulations (python, dt = 1 ms) of the
file ODEs, used to test real-time readings. They are not tool runs.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| rover_ladder_2to3 | 4 | 3 | 4 | 3 | KEEP | Honest ladder rung, no letter; the claim is a plain monotone comparison (slower integrator stays behind), psi never enters a row |
| rover_terrain_4to6 | 3 | 4 | 4 | 4 | KEEP | Good refinement chain with real I; sigma/H at requirement values with tight values reported; zs <= 0.12 and the w floor are tuned for forward invariance |
| engine_start_highidle | 4 | 3 | 2 | 3 | POLISH | R D I genuine, but the header calls the 4 % bound "a real-time one": in lock step from a normal start the gap reaches 5.5 % |
| rampmeter_poll_2to1 | 3 | 3 | 2 | 3 | POLISH | M B genuine; "tightest 7.00" contradicts the header's own certifying 5.00 (a structural fixed point); k domain is the reachable band, not the 45 capacity limit |
| lit_drl_lane_control | 3 | 3 | 4 | 3 | KEEP | Faithful, fully disclosed dRL Goal 1. Content is static guard inclusion (margin 0 and Rsys = Lsys both certify); Coast stand-in accepted |
| platoon_linkloss | 4 | 4 | 3 | 2 | RETHINK | Rows are good and tight, but the only letter M comes from a single-mode right whose 0.1 s epsilon changes no run |
| h2_refuel_ambientbias | 4 | 3 | 3 | 3 | RETHINK | D and I genuine; R is needed only for TOPOFF_L/STAGE3_R start pairs that no handoff produces; "real-time" wording false for those starts |
| canal_gate_notches | 3 | 4 | 4 | 3 | POLISH | X genuine, tolerance justified, law dependence measured; but RAISE/LOWER are start-only (HOLD band is forward invariant, no disturbance), so the "law dependence" rests on start-only modes |
| lit_lz21_vehicle_position | 4 | 3 | 4 | 3 | KEEP | Faithful with accepted delta = 1; the in-tool invariant is a copy witness (constant offset, certifies at delta 0); the delta content is the static coverage check |
| flaps_slow_approach | 4 | 4 | 3 | 3 | POLISH | Clean per-mode S; the 25/10 tight values come from VFE/VLS (accepted, physical), but the header also says the domain is "not load-bearing" (true only because the guards repeat [130, 200]) |

## Per benchmark

### rover_ladder_2to3
- Model: L3 rover (heading loop psi' = -psi, along-track loss s' = v(1 - psi^2/2)) against the L2 point model, same zoned speed loop, lock step.
- Property: v_L <= v_R and s_L <= s_R (the rover is never faster than or ahead of the reference); offset 0 = equal starts.
- Concern (LOW): the claim follows from (1 - psi^2/2) <= 1 plus set points increasing along s. It is a valid composition rung, but the rung's own content is thin. psi appears in no row, and the header says the former heading row only restricted starts. No letter, matching matrix "no code exercised" and letters "--".
- Concern (LOW): "s_L + 1 <= s_R also certifies" can read as a tighter value. It is a different claim (it excludes equal starts), and saying so would avoid that reading.

### rover_terrain_4to6
- Model: 6-DOF terrain rover (lagged speed command u, heave envelope zh) against the 4-DOF ideal-drive model, three terrain zones.
- Property: v_L <= v_R, s_L <= s_R, slip window v_L <= w_L <= v_L + 0.25, zh_L <= 0.15, plus three auxiliary rows. Tight values 0.21 and 0.13 are reported. The stated values are the traction threshold and the bump stop.
- Concern (LOW): zs in [0, 0.12] is not justified as a physical limit (the reachable sinkage is <= 0.10). It is the value that keeps v' >= 2.5 x 0.05 - zs > 0 at v = 0 in MUD (margin 0.005). Likewise, the wheel floor 0.05 is chosen so that Assumption 1 holds. Both serve Assumption 1, not the claim, so they are not HIGH. Stating zs's upper bound as a modelling choice would help.
- Concern (LOW): "(Renamed ... from rover_terrain_6to8 ...)" and the k_z "bare term" note are history and clutter.

### engine_start_highidle
- Model: turbofan ground start, six sequencer phases incl. low-supply hung start to ABORT; deployed high idle 66 % vs reference 62 %.
- Property: start phases exact (N2_L <= N2_R, timer and supply rows), SELF/IDLE N2_L <= N2_R + 4, up to reference re-timing (R).
- Strongest concern (HIGH): the stretch note says "the requirement is a real-time one", and the Property says the deployed "may exceed the reference start profile by at most the 4 % idle increment". In lock step (both sides deciding every 1 s, no re-timing), a normal rated start from (N2, t, p) = (5, 0, 50) on both sides gives a maximum N2_L - N2_R of 5.51 % at t = 51 s. From equal SELF starts at 50 % the maximum is 5.55 %. The cause is the deployed entering IDLE (gain 0.5) while the reference is still in SELF (gain 0.15). This is the reachable (IDLE_L, SELF_R) pairing. The certified 4 % holds only against a reference that may run ahead alone. The Property says this ("up to the reference's re-timing"), but the "real-time" sentence contradicts it. R itself is genuine, because this pairing is reachable.
- Fix: replace "the requirement is a real-time one" with "lambda 1; the bound is against a reference that may run ahead alone (R); in lock step the gap reaches 5.5 %". State the requirement as a profile comparison.
- LOW: STARTER_LOW's 25.5 % torque limit is set just above light-off so that ABORT becomes reachable (ad hoc but disclosed). The opregion caveat for ABORT_L is fine.

### rampmeter_poll_2to1
- Model: CTM free-flow bottleneck with a six-level traffic-responsive ramp meter; deployed decides every 40 s on polled data, design every 20 s with rate-limited successors.
- Property: equal demand and upstream density, |k_L - k_R| <= 8 veh/mi/ln (derived from HCM LOS bands).
- Strongest concern (HIGH): the header says "Tightest ... 7.00 (6.99 declines)" and "three levels need 7", and calls the certifying 5.00 "a boundary coincidence". The arithmetic says otherwise. At constant 5 the closed rows with the half-open 5-wide bands admit only adjacent levels at a window start, and one extra design update gives two levels, whose largest rate gap is (1800 - 1200)/120 = 5. So 5 is a self-consistent fixed point, and the certifying set is {5} and [7, ...). The tightest certified constant is 5.00, not 7.00. The "claim window [7.00, 11.00), margin 1.00 below" and the cause table (30/40 s: 7.00; 50/60 s: 9.00) come from bisection that cannot see such points.
- LOW: k in [14, 42.5] is the reachable band [min k1 + 4, max k1 + 15], not the physical limit the header itself names (capacity density 45, where free flow holds). The accepted list says to flag a reachable-band domain. It is probably not load-bearing.
- LOW: the requirement was changed "(8, was 10)" and now sits 1 above the 7.00; the header says it was re-derived. Most ablations are from 2026-10-27 at band 10, and the header has two run times (2.2 s and 4.2 s).
- Fix: report the certifying set at 40 s, not a single "tightest". Re-check 50/60 s for isolated points. Widen k to [0, 45].

### lit_drl_lane_control
- Model: sampled dRL lane control, follower Accel/Coast/Brake x leader Accel/Brake; left guarded by Safe_eps, right by Safe.
- Property: identity relation (refinement as reachability inclusion, dRL Goal 1).
- Concern (LOW): the claim's content is the static implication Safe_eps => Safe. The header measures that margin 0 certifies and Rsys = Lsys certifies, so the refinement adds no dynamical content beyond what X shows. This is accepted (item 5) and fully disclosed. The header is very long; the 9-mode variant history could be shortened.
- No HIGH. Letters X = header = SYNC/NO_CHOICE pattern.

### platoon_linkloss
- Model: one CACC link. The deployed switches CACC/ACC under link loss with a 0.2 s decision period; the design is CACC only at 0.1 s.
- Property: 0 <= Delta g <= 15 (tight, the steady offset (h_a - h_c) v_ref), two derived Q-form rows (tight), deployed gap and TTC floors.
- Strongest concern (HIGH): the letter M is an artifact. The right has ONE mode, CACC with next [CACC], and its guard (the operating range) is forward invariant. A 0.1 s run is therefore two back-to-back 0.1 s CACC flows, which is the same trajectory set as one 0.2 s CACC flow. The "multi-cycle matching, budget 2, via CACC" in matrix M2 matches a decision that is never taken. The header itself says equal periods certify with no letter, so the two-message timeout changes neither the claim nor its bounds. After the round-4 AEB removal (D was also start-only), the file has no genuine mechanism.
- Fix: give the design a real per-message decision (e.g., the design also degrades to ACC on a single lost message, so its 0.1 s choices differ from the deployed's held 0.2 s choice), or keep the file as a letter-free tight-tolerance benchmark and stop citing it for M.

### h2_refuel_ambientbias
- Model: one-state staged H2 fill; deployed end pressure 72.4 (sensor +10 K) vs 70.0.
- Property: stage rows p_L <= p_R, top rows p_L <= p_R + 2.9 (2.4 bias + 0.5 certificate slack, disclosed).
- Strongest concern (HIGH): R comes from start-only pairs. R is justified by "the reference may start in STAGE3 while the deployed tops off". No handoff produces that pairing. At STAGE3_L -> TOPOFF_L the stage row gives p_R >= p_L >= 58, so the reference is in TOPOFF or COMPLETE, and its pressure never decreases. The pairing (TOPOFF_L, STAGE3_R with p_R in [55.1, 58)) exists only as an admitted start of the relaxed top row. From such a start the real-time gap reaches 8.83 MPa (lock-step sim, p_L = 58, p_R = 55.1). From a normal fill (both at 0) the real-time maximum is 2.387 MPa. So "the requirement is a real-time one" holds only for reachable pairs. The letter R exists only for these start pairs.
- LOW: D and R also appear at zero bias (s = 0), driven by the 0.5 certificate slack (disclosed). At s = 2.4, D is genuine (stage requirement 0 vs a top shift of 2.4).
- Fix: add p_R >= 58 to the TOPOFF and COMPLETE rows (the handoff guarantees it), then re-measure the letters. If R disappears, report D I.

### canal_gate_notches
- Model: canal pool under a three-position automatic gate (RAISE/HOLD/LOWER, deadband 0.40 to 0.90) against a manual four-notch rule restricting N100 and N25 by level.
- Property: |h_L - h_R| <= 0.15 m (operator tolerance), tight 0.10, law dependence measured (thresholds 0.45/0.85, arbitrary schedule needs 0.20).
- Concern (LOW): HOLD's band [0.40, 0.90) is forward invariant (it contracts to 0.65), and RAISE and LOWER exit to HOLD within one poll. With no inflow disturbance, RAISE and LOWER are entered only from starts. The round-A rationale ("the claim depends on where the automatic controller uses [the extreme positions]") and the law-dependence numbers rest on modes a run never re-enters. X itself is genuine: HOLD_L with N100/N25 admissible needs the hop. The header implies start-only use ("HOLD's flow stays in its band") but does not say it.
- Fix: say explicitly that RAISE/LOWER are start-only, or add a bounded demand disturbance (turnout draw) so the level can leave the deadband. Check: remove RAISE and LOWER; expect X to remain.

### lit_lz21_vehicle_position
- Model: double-integrator vehicle with three input levels; secret run left, non-secret partner right.
- Property: x_R >= 1, |x_L - x_R| <= 1, v_L = v_R (Def. 2 at delta = 1, closed form).
- Concern (LOW): the in-tool invariant is a copy witness (the partner copies the input and keeps its offset). The header measures that it certifies at delta 0, 0.99 and 1, and that x_R >= 1 is invariant because x is nondecreasing. The delta-dependent content (coverage) is the z3 check outside the tool. All of this is disclosed and the departures are accepted (item 5). The rubric still deducts for a copy witness.
- No HIGH.

### flaps_slow_approach
- Model: A320-class flap extension CONF 1+F -> CONF 2 at 0.5 deg/s (one hydraulic system) vs 1 deg/s, autothrust decelerating to F with flap-dependent drag.
- Property: f_L = f_R, V_R <= V_L + 25, V_L <= V_R + 10 against the reference re-timed at lambda 1/2 while extending; tight 25 = (VFE - F)/2 and 10 = (F - VLS)/2.
- Strongest concern (HIGH, header contradicts itself): the Property derives both tight values from the domain ends VFE = 200 and VLS = 130, and says that at placard 190 the tight value is 20. The Domains paragraph says "Not load-bearing now: every bound widened by 20 % of its range CERTIFIES." Both can hold only because every guard repeats V >= 130 and V <= 200. On the evolve domain [116, 214], D = 25 is not inductive (D' = k(-25 + (V_R - 150)/2) > 0 for V_R > 200). The physical placard as a load-bearing tight bound is accepted (item 3). The finding is the false "not load-bearing" sentence.
- Fix: say that the placard range sets the tight values (through the guard copies) and drop "not load-bearing".
- LOW: grid dependence of the stretch is disclosed and fine.

## Findings by severity

HIGH
1. engine_start_highidle: "the requirement is a real-time one" is false for the 4 % bound. Check: lock-step run (no right-only steps) from (N2, t, p) = (5, 0, 50) on both sides; expect max N2_L - N2_R about 5.5 % (python Euler: 5.51 at t = 51 s). The header's own RELCERT_SYNC=1 DECLINED agrees.
2. rampmeter_poll_2to1: header number wrong, "tightest 7.00" while 5.00 certifies (a fixed point: adjacent-level start span, two levels after one update, max gap 5). Check: tolerance 5 -> expect CERTIFIED (header says so); 4.99 -> expect DECLINED; repeat at 50/60 s polling with 5 and 7.
3. platoon_linkloss: letter M from dead structure (single-mode right, next [CACC], forward-invariant guard: the 0.1 s epsilon changes no run). Check: set Rsys epsilon = 0.2 -> expect CERTIFIED with the same tight values and no M.
4. h2_refuel_ambientbias: letter R comes only from start pairs (TOPOFF_L, STAGE3_R) that no handoff produces. Check: add p_R >= 58 to the TOPOFF and COMPLETE rows -> expect CERTIFIED under RELCERT_SYNC=1 and letters D I (no R).
5. flaps_slow_approach: "Not load-bearing: every bound widened by 20 % CERTIFIES" contradicts the tight values 25/10 = placard-derived. Check: widen V to [116, 214] in both evolve and guard lines -> expect DECLINED at 25/10.

LOW
- rover_ladder_2to3: the claim is a thin monotone comparison; "s_L + 1 <= s_R also certifies" should be called a different claim, not a tighter one.
- rover_terrain_4to6: zs <= 0.12 and the w floor 0.05 are set for forward invariance / Assumption 1, not physical limits; history clutter.
- engine_start_highidle: STARTER_LOW's 25.5 % is tuned so that ABORT is reachable.
- rampmeter_poll_2to1: k domain is the reachable band, not 45 (check: widen k to [0, 45], expect CERTIFIED with M B); requirement re-derived "(8, was 10)"; stale ablations at band 10; two run times.
- lit_drl_lane_control: claim content is static guard inclusion (disclosed, accepted); header length.
- h2_refuel_ambientbias: D and R present at zero bias from the 0.5 certificate slack (disclosed).
- canal_gate_notches: RAISE/LOWER start-only, so the law dependence rests on start-only modes (check: remove RAISE and LOWER, expect X unchanged); add a disturbance or say so.
- lit_lz21_vehicle_position: copy witness; the delta content lives in the external coverage check (disclosed).

### g4

# Review r6, group g4 (10 benchmarks)

Inputs: review-rubric.md, ACCEPTED-LIST.md, benchmarks/suite_v2/<name>/input.txt, docs/paper-numbers/matrix.md and letters.md (rows for these names only). Letters below are letters.md; matrix mechanism cells agree with every header's `mechanisms:` line in all ten files.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| elevator_start_discbrake | 3 | 4 | 3 | 3 | POLISH | R and D are real (brake-lift re-timing); header's rest position (19.96 m) is wrong, the trip rests at 20.07 m, 7 cm past the 20 m landing |
| ventilator_vc_cuffleak | 3 | 4 | 4 | 3 | POLISH | Good physics and ISO requirements, D is real; but the domain `V <= 0.404`, `V - 0.4 t <= 0` is a reachable band (one breath from PEEP) and it carries the INSP->EXP handoff |
| watertank_twospeed | 3 | 4 | 3 | 3 | POLISH | Tight rows with cause dependence; P comes from the Fast -> PumpOff edge into a sink that no flow ever enters (start-only); the verdict block predates the 1.5 row |
| acc_spoof_limp | 3 | 3 | 3 | 2 | RETHINK | No letter comes from the spoof (as the header admits); X comes only from LIMP starts above 34.5 m/s, which the header's own 2 s debounce makes unreachable |
| sat_detumble_weak | 4 | 3 | 3 | 3 | POLISH | The exact energy identity is correct (the couplings do no work); header says X comes from the derating but also says X persists at k_L = 0.5; history noise |
| tank_dos_3to1 | 4 | 4 | 4 | 4 | KEEP | DoS hold measured against the requirement (0.72 tight, 0.8 required, 40 s violates it); M and I are real; the left lists one more successor than it needs (harmless) |
| reactor_feed_wireless | 3 | 4 | 3 | 3 | POLISH | Tolerance tight at 8 (two feed levels); B and P are real, but both hold only in a +-2 K window of the coolant range; crude thermal model; two verdict blocks |
| quad_light_lag | 2 | 3 | 3 | 2 | RETHINK | The lag acts only on a constant feedforward, so it never interacts with the loop (built so Psi is conserved); the a bound equals the left's asymptote; the 0.8 tightness comes from the chosen Psi band |
| gantry_speed_zones | 4 | 3 | 4 | 3 | KEEP | A uniform override is a time reparametrization, so S and M are honest; the claim is exact at the file's own range (0.00 certifies), and 0.01 is justified as the clearance requirement; the zone schedule is not load-bearing |
| acc_tune_lag | 3 | 3 | 4 | 3 | POLISH | tau = 0.32 is picked so the exact ratio-2 claim holds; the exact modal rows are correct; row 3's 3.34 is set by the guard/box geometry far outside any reachable state |

## elevator_start_discbrake
- Model: a 20 m elevator up-trip (LIFT/UP/APP/STOP). The deployed disc brake lifts at k=50 and the reference drum brake at k=5. The right is the validated trip.
- Property: equal z and v in every mode up to re-timing, and in LIFT b_R <= b_L. Constant 0, the requirement. R (the reference lifts its brake alone while the deployed is in UP) and D are both real and caused by the brake change.
- Strongest concern (HIGH, header number wrong): the header says "stop at the landing, v' = -4 v (rest at about 19.96 m)" and "STOP comes to rest within 0.1 m of 19.9 m". The file's own dynamics give an STOP entry at z=19.947 and v=0.482, so the rest is z + v/4 = 20.068 m. That is 0.17 m above 19.9 and contradicts 19.96. It also matches the header's own "arrives at about 0.5 m/s" (rest >= 19.9 + 0.125).
- LOW: a 6.8 cm overshoot of the stated 20 m landing is poor levelling (EN 81-20 levelling is +-10 mm), and the brake starts dropping while the car still moves at 0.48 m/s.
- Fix: correct the rest-position numbers, or move the STOP threshold or the APP speed so the car rests at about 20.00 m.

## ventilator_vc_cuffleak
- Model: one volume-controlled breath in an ARDS lung. The deployed has a cuff leak through a correct resistor network (I checked both INSP/EXP fields and the 6.3 mL settling point). The reference has a sealed cuff.
- Property: in INSP, |dV| <= 4 mL + 15 % V_R (ISO delivered-volume accuracy). In EXP, |dV| <= 0.08 L (ISO PEEP +-2 cmH2O). Both are requirement-justified; neither is claimed tight (tight values are 0.104 and 0.0647). D is real (flow integrator vs pressure relaxation).
- Strongest concern (HIGH, a domain does the claim's work): `V <= 0.404` ("the volume one breath can deliver") and `V - 0.4*t <= 0` are not physical limits. They are the reachable set of one breath that starts at PEEP, i.e. an initial condition encoded as a domain.
  - They carry the handoff. INSP hands off |dV| <= 0.004 + 0.15 V_R, which fits under EXP's 0.08 only for V_R <= 0.507. The header's own "tightest EXP 0.0647 = the INSP row at 0.404" shows that the cap sets this.
  - With a physical lung bound (e.g. inspiratory capacity of about 1.5 L) and no clock band, INSP starts at V_R > 0.507 would break the handoff.
- LOW: the INSP row is unsatisfiable for V_R < -0.027 (related negative-volume starts are silently empty).
- Fix: state the band as the breath-start encoding (and get it accepted), or bound V physically and show that the verdict survives.

## watertank_twospeed
- Model: the running example's attacked tank (offset 3, forced full speed) against a two-speed nominal low fill with a latched PumpOff interlock.
- Property: x_L <= x_R + 3 and x_R <= x_L + 1.5 in all modes. Both are tight (2.99 and 1.49 decline), with a measured offset sweep (s, 4.5 - s). The tightness evidence is good.
- Strongest concern (HIGH, letter from dead structure): P is the pruning of Fast -> PumpOff.
  - Fast flows up from 2 (x' = 2 (12.5 - x) > 0), so the edge is never taken; the header itself calls it "dead".
  - PumpOff is a sink no flow ever enters, so it exists only as a start mode.
  - Only Fast declares the edge (Slow, MidEco and MidBoost do not), and successor completeness does not need it. P is then the deadness proof of an edge the model need not declare.
  - If the owner accepts this as running-example heritage, downgrade to LOW.
- LOW: the verdict block says "measured 2026-10-26 with the round-A binary", but the lower row became 1.5 on 2026-10-29. The listed ablations (SYNC, NO_PRUNE, NO_PAIR_STRETCH DECLINE; the rest CERTIFY) are therefore undated for the current claim. The Round-A history paragraph is noise.
- Fix: re-measure and date the verdicts at 1.5. Either drop Fast -> PumpOff (and lose P) or justify the declaration with physics that can reach x < 2 (e.g. a consumer outflow).

## acc_spoof_limp
- Model: a speed-spoofed cruise (settles at 24 m/s) with a latched LIMP (to 22) against the reference driver modes ECO/NORMAL/SPORT plus a pruned DISENGAGE.
- Property: v_L <= v_R (never faster) and 0.7 v_R <= v_L + 4 (AASHTO-derived closing-speed bound). Both are justified by requirements, not tight: row 1 certifies down to -2.40 and row 2's intercept down to -0.20, both disclosed.
- Strongest concern (HIGH, letter from a start-only artifact): X comes only from LIMP entries above the 34.50 m/s ECO crossover.
  - A latch is taken only at a 2 s debounce decision. After one 2 s CRUISE window from the 40 m/s domain top, v <= 24 + 16 e^-1.25 = 28.6 m/s, and LIMP only decelerates.
  - So LIMP states in (34.5, 36] exist only as left start states, i.e. a latch at the instant of attack onset. That contradicts the header's debounce story (the monitor must see 2 s of mismatch).
  - The header's own data confirms that the letter rides on these states: the 10-28 file capped at 30 needed no choice, and NO_CHOICE certifies up to 34.50.
- LOW: "One cause: the spoof" conflicts with M and B coming from "the second difference" (the 2 s period); I persists without the spoof. No letter shows the scenario's cause. LIMP's "entry ceiling 36" sits oddly next to "the plausibility fault is not conditioned on speed".
- Fix: bound LIMP entry by what a debounced latch can reach (<= 28.6 m/s, or derive it), accept letters M B I, and say the spoof shapes the bounds, not the mechanisms. Or replace the debounce argument with a real reason a 35 m/s latch happens.

## sat_detumble_weak
- Model: a derated-actuator gyrostat (k = 0.4, Euler couplings checked: they do no work) against decoupled design profiles NOMINAL 0.5, ECONOMY 0.45 and SURVIVAL 0.42 with a SAFE sink.
- Property: E_L(t) = E_R(0.8 t), an exact energy identity at the pinned stretch 4/5. It is correct and a real "detumble budget x 1.25" requirement, though it reduces to comparing two scalar exponentials.
- Strongest concern (LOW): the header says "S and X come from the derating (the exact scaling and the profile it selects)", but the Letter-window paragraph says that at k_L = 0.5 "RELCERT_NO_CHOICE=1 DECLINES (X persists, from the profile choice)". X comes from the multi-profile reference, not from the derating.
- LOW: the header carries batch/round history (I4, I9, Round 1, the domain changes). M comes from "a design value of this file" (the 2 s duty cycle).
- Fix: correct the attribution of X and cut the history paragraphs.

## tank_dos_3to1
- Model: a tank with 2-5 staged pumps paced by a rising demand w. The deployed staging decision is held for 30 s (DoS drops 2 of 3 polls), the nominal for 10 s.
- Property: h_L <= h_R exactly, h_R <= h_L + 0.8 (submergence requirement; 0.72 tight, 0.71 declines) and w equal. The cause sweep shows 40 s holds violate the requirement. I is real (band-floor mode fact).
- Strongest concern (LOW): left next(P2) = [P2..P5], but within 30 s w rises at most from 10 to 15.4, so P2 cannot reach P5. The header says "can cross two band edges" while the file lists three. This is harmless on the universal side but inconsistent.
- LOW: the certificate is about 5x the simulated transient (disclosed). "Demand only rises" is the scenario premise behind row 1 (stated).

## reactor_feed_wireless
- Model: an exothermic reactor whose feed level is a static map of temperature (F1-F4), first-order thermal. The deployed wireless transmitter publishes every 2 min against the 1 min wired design.
- Property: |T_L - T_R| <= 8 K (two feed levels), tight (7.99 declines). It is justified by a van 't Hoff factor-2 band; the cause sweep is 0 / 8 / 12 for 1 / 2 / 3 min.
- Concerns (all LOW):
  - B (needs p_lo < 17, p_hi > 33) and P (needs p_lo > 13, p_hi < 37) both hang on the coolant range [15, 35] sitting inside a +-2 K window, and the verdict at 8 depends on it (NO_PRUNE needs 12). The range is physical ("winter to summer") and the window is disclosed, but it needs a cited justification (e.g. the cooling-tower design range).
  - T linear in feed with no kinetics is a design model (disclosed). "Continuous stirred-tank reactor" vs "batch sequencer" is mixed wording.
  - Two near-duplicate verdict blocks (10-26 and 10-28); keep one.

## quad_light_lag
- Model: a 20 %-lighter quadrotor climb with a motor lag, against the reference at the pinned stretch 6/5.
- Property: |h_L - h_R| <= 0.8 (PX4 altitude acceptance radius) plus a strengthening band |Psi| <= 0.45 on the conserved steady-climb-altitude gap. The algebra checks (Psi' = 0 at lambda = 6/5; hover Psi = -0.0237).
- Strongest concern (LOW, model shaped to the claim): the lag filters only the constant set-point command, `a' = 10 (a_cmd - a)`, while the feedback `-K w` bypasses it.
  - So a(t) is an exogenous exponential independent of w, and the "lag" never interacts with the loop; this is exactly what makes Psi conserved.
  - A real lagged loop (a' = 10 (a_cmd - K w - a)) gives eigenvalues that do not scale by 6/5.
  - The header discloses it as "a simplification", but it hollows out the benchmark's name.
- LOW: a <= 14.715 is both the left's asymptote a_cmd and 3K (picked so the reference's box is forward invariant at w = 3). The same net-specific-thrust limit is applied to two different masses, which is physically inconsistent. w <= 3 is a set-point limiter, not a plant limit. Neither is load-bearing (20 % widening certifies).
- LOW: "row 2 tight at the requirement 0.80" holds only because the Psi band was widened to 0.45 so that 0.8 is saturated. With hover-related starts the rows certify at 0.36. This is disclosed, but the tightness is made by construction.
- Fix: put the feedback inside the lag. Then either state a toleranced claim with a searched stretch, or drop "lag" from the exhibit and fold it into the lag-free sibling.

## gantry_speed_zones
- Model: a two-axis gantry with independent first-order axis servos. Production overrides of 3/2/1 are zone-scheduled along x; the commissioned run is at 1.
- Property: |dx|, |dy| <= 10 mm (fixture clearance margin) up to a per-mode stretch.
- Concerns (LOW):
  - 0.00 certifies at the file's own lambda range, so 0.01 is not tight. It is justified by the requirement and by grid independence (per-pairing stretch intervals, measured), and the header does not claim it is tight.
  - The arbitrary-schedule run certifies, so the zones are labels, not load-bearing (disclosed).
  - Rename/Round-A history could go.

## acc_tune_lag
- Model: a retuned cruise loop (k = 0.75) against the stock loop (k = 0.5), with the same 0.32 s powertrain lag. One mode per side; the guards are modal-slab envelopes.
- Property: exact equality of the dominant-mode speed u at stretch 2 (checked: u_L - 30 decays at 1.25, u_R at 0.625), plus |v_L - v_R| <= 3.34 (tight, 3.33 declines).
- Concerns:
  - LOW: tau = 0.32 is the unique lag at which the ratio is exactly 2 (a plant constant tuned to the claim). This is disclosed; at 0.30 only a modal tolerance certifies.
  - LOW: row 3 is a derived bound, not a requirement. Its tight value 3.34 is fixed by the left slab envelope clipped by the a box. The envelope's corners (8.6, 28.75) are far from anything an engagement reaches (simulated v in [24.87, 30.47]). The 1 g box is physical and declared load-bearing (accepted list item 3), so this is not HIGH.
- Fix: say in the property paragraph that row 3's value is a geometric consequence of the guard and box, or drop row 3 and keep the exact modal rows.

## Findings with severity

HIGH
1. elevator_start_discbrake: the header's rest position "about 19.96 m" and "within 0.1 m of 19.9 m" contradict the file. The dynamics give an STOP entry at (19.947, 0.482) and a rest at 20.068 m. Check: simulate the right trip from (0, 0, 0) with 0.1 s sampled switching and print z + v/4 at STOP entry. Expect 20.07, not 19.96.
2. ventilator_vc_cuffleak: the domain conjuncts `V <= 0.404` and `V - 0.4*t <= 0.0` are a reachable band (one breath from PEEP), not a physical limit, and they carry the INSP->EXP handoff. Check: replace them in every guard/evolve on both sides by a physical bound (e.g. `V <= 1.5`). Expect DECLINED (the handoff fails for V_R > 0.507) or a wellformed BLOCKING.
3. watertank_twospeed: P comes from the dead edge Fast -> PumpOff into a sink no flow enters (PumpOff is start-only; only Fast declares the edge). Check: delete PumpOff from `Rsys.mode.Fast.next`. Expect CERTIFIED, RELCERT_NO_PRUNE=1 CERTIFIED, letters S M B (P lost).
4. acc_spoof_limp: X comes only from LIMP starts at v in (34.5, 36], which the 2 s debounce makes unreachable (CRUISE from 40 is at <= 28.6 m/s at the first latch decision). Check: set the LIMP guard to `v <= 28.6` (or 34.5). Expect CERTIFIED with RELCERT_NO_CHOICE=1 CERTIFIED, letters M B I (X lost); the header already reports this at 34.50.

LOW
- elevator: the 6.8 cm landing overshoot is poor levelling, and the brake drops while the car moves at 0.48 m/s.
- ventilator: the INSP row is empty for V_R < -0.027.
- watertank_twospeed: the verdict block is dated 10-26, before the 1.5 row (10-29); re-measure the ablations at 1.5. The Round-A history is noise.
- acc_spoof_limp: "One cause" conflicts with M and B from the period difference. "Entry ceiling 36" conflicts with "fault not conditioned on speed". Row 1 constant 0 is not tight (-2.40 certifies; disclosed and requirement-justified).
- sat_detumble_weak: "S and X come from the derating" is contradicted by the header's own k_L = 0.5 run (X persists). Heavy history text.
- tank_dos_3to1: left next(P2) includes P5, which is unreachable in 30 s, while the header says "two band edges". The envelope is about 5x the transient (disclosed).
- reactor_feed_wireless: B and P and the verdict at 8 hinge on the coolant range within a +-2 K window; cite the range. The thermal model is crude. CSTR vs batch-sequencer wording is mixed. Two verdict blocks.
- quad_light_lag: the lag is applied only to the feedforward (the model is shaped so Psi is conserved). The a bound equals the left asymptote and 3K, and the same net-thrust limit is used for both masses. w <= 3 is a set-point limiter. The 0.8 tightness comes from the chosen Psi band (0.36 with hover starts).
- gantry_speed_zones: 0.01 is not tight (0.00 certifies; disclosed and requirement-justified). The zone schedule is not load-bearing. History text.
- acc_tune_lag: tau is tuned to the exact ratio (disclosed). Row 3's 3.34 is set by unreachable guard corners clipped by the box.

### g5

# Review r6, group g5 (10 benchmarks)

Inputs: rubric, ACCEPTED-LIST, the 10 input.txt files, matrix.md and letters.md rows. Read only; nothing run.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| rover_terrain_2to4 | 3 | 3 | 3 | 3 | RETHINK | S M are needed only for wheel-ahead states that no run from a matched start reaches; the real-time form (+ row w_L <= v_R) certifies with I only |
| quad_light_profiles | 3 | 3 | 4 | 2 | RETHINK | B and X come from ECO/SPORT, which the witness never runs (removing them gives S M); the P-only loop ignores PX4's integral term |
| lit_csf25_salt_tank_hold | 4 | 4 | 4 | 4 | KEEP | faithful encoding of the source's proof step, tight slopes; start-only left is argued in departure (5) |
| charger_fast_tapers | 3 | 2 | 2 | 2 | RETHINK | c = 1 is the tool's FULL over-approximation (physical lead 0); S not forced (λ=1 file CERTIFIED); D only from the FULL unit; wrong rate numbers |
| acc_spoof_lag | 3 | 4 | 4 | 4 | KEEP | exact dominant-mode row, checked by hand; lag tau = 0.375 picked for rational roots (disclosed) |
| fuelcell_chp_dos | 3 | 2 | 4 | 2 | RETHINK | P and X come only from start-only LOW_L/HIGH_L windows; the Tin design range sets the verdict; the 7 K claim is weaker than the true 0 |
| watertank | 4 | 4 | 4 | 4 | KEEP | tolerance = offset, tight both in c and λ; High is start-only on both sides but carries no letter |
| lit_freedm_meter | 4 | 4 | 4 | 4 | KEEP | the source's Prop. 11 argument, X from a real per-window choice, departures forced and ablated |
| furnace_program_timebase | 4 | 3 | 4 | 4 | POLISH | clean derivation (6.4 = 0.2 x 32); AMS 2750 Class 3 is spatial uniformity, not run-to-run tracking |
| rover_terrain_6to12 | 3 | 3 | 4 | 3 | POLISH | the route-grade domain theta_p <= 0.02 sets the slip verdict; 3 of the 6 new coordinates are output-only (dim 12 inflated) |

## Per benchmark

### rover_terrain_2to4
- Model: a 4-DOF rover (wheel loop, soil traction, sinkage) on MUD/GRAVEL/PAVED zones against a 2-DOF no-slip plan run at the same 3 /s loop.
- Property: v_L <= v_R and s_L <= s_R against the plan re-timed by λ in [1, 2.7]. A left-only slip window v_L <= w_L <= v_L + 0.25 (tight 0.21; I checked this by hand: 1.47/7).
- Concern (HIGH): header lines 87-90 say runs from matched starts need λ = 1, and S is needed only for admitted states with w_L > v_R. Lines 105-107 say the real-time form with the extra row w[l] <= v[r] certifies at λ 1 with letters I only. So S and M come from the row set's slack (initial states only), not from the physics of a run. The "planner re-initialized from visual odometry while the wheels slip" scenario (lines 108-115) is an argument made after the fact, and the header itself says the stretched form was "chosen as the chain's exhibit" (line 12).
- Concern (LOW): the "time-free" position reading ("a stop line the plan never passes", lines 46, 83) is vacuous. The plan's v_R tends to c_T > 0 in every zone, so it passes every point. The relational content therefore rests on v_L <= v_R under a re-timing of up to 2.7x, which is weak, and the slip row is left-only.
- Concern (LOW): lambda_max 2.7 is 0.06 above the tool's tight 2.64. This is disclosed as rounding of the derived ratio.
- Fix: have the owner choose. Either state the real-time form (letters I), or keep the S M exhibit and record it as an owner decision in the accepted list. Reword the stop-line reading.

### quad_light_profiles
- Model: a 20 % lighter quadrotor under a P velocity loop tuned for the reference mass, against a reference with three pilot-selectable climb profiles (NORMAL/ECO/SPORT).
- Property: altitude within 0.8 m of NORMAL re-timed by 6/5, plus strengthening rows Psi (conserved), 1.2 w_R <= w_L and w_L <= 2.4. I checked by hand that Psi' = 2.4 - 2λ, the Psi offset 0.1 in the file, the d/dt of row 4 and the hover Psi = 0.0163.
- Concern (HIGH): lines 274-277 say ECO and SPORT are never run by the witness: they are admissible starts the cover hops away from at once, and with them removed the file certifies with S M alone. B (lines 279-281) and X therefore both come from structure the witness never uses.
- Concern (LOW): rows 1-3 are not loaded: row 1 certifies at 0.00, and rows 2+3 at 0.0163 from hover. The 0.8 is justified as NAV_MC_ALT_RAD, and the header says so honestly.
- Concern (LOW, P): PX4's vertical velocity loop has an integral term (MPC_Z_VEL_I_ACC) and a hover-thrust estimator. With those, a lighter airframe settles at the set point (2.0 m/s), not at 2.4 m/s. The "mass ratio fixes λ" premise holds only for a P-only loop. The header cites PX4 for K without saying the I term is dropped.
- Fix: either drop ECO/SPORT and claim S M, or give the reference a reason to need them: for example, the claim against "some profile" with a deployed whose profile changes mid-flight. Disclose that the loop is P-only.

### lit_csf25_salt_tank_hold
- Model: the CSF'25 brine tank. One held 3-min attacked window in the stale decision (HoldInc/HoldDec) against the genuine tank re-timed by 1/3 (Prop. 7).
- Property: a band that grows linearly over the hold (Inc 2.1 + 1.25(t-5), Dec 0.5 + 0.23(t-5)) plus the genuine envelope rows. I checked by hand: the row constants at t = 5, the guard images (36.436, 36.921) and [34.705, 36.742), the corner rate 1.247 and the exact worst case 5.47.
- Concern (LOW): both left modes are start-only (guard t = 5; next = itself, and the guard fails afterwards), so the whole left is one window and S, D and I all live in it. Departure (5) argues that this is the source's one-shot threat model, which I accept as substance. The exception to the suite's start-only rule should, however, be added to the accepted list rather than live only in this header.
- Concern (LOW): lambda_min = 0.3333333333, not 1/3. The matrix reports λ = 1/3, so the cover relies on rounding. Also, readings in (34.999, 35) are uncovered (disclosed).

### charger_fast_tapers
- Model: SoC phases (PRECHARGE/BULK/ABSORB/FULL). The deployed has its CC rate raised 25 % and a 2:1 slower decision. The reference profile has two tapers.
- Property: x_L <= x_R + 1 (BULK/ABSORB/FULL) and x_L <= x_R (PRECHARGE), against the profile re-timed by 5/4.
- Concern (HIGH, R): lines 566-578 say the physical re-timed lead is 0.00 and c = 1 is "the FULL pairing's asymptote-against-floor gap of the tool's over-approximation". The stated constant therefore measures the tool, not the charger. Combined with right-only repositioning that lets the profile taper alone to FULL during a deployed BULK window (lines 601-606), the one-sided claim is close to "the reference can get ahead".
- Concern (HIGH, letter S): letters.md has "lambda=1 file: CERTIFIED" for this benchmark and no S_lam1 diagnostic, unlike every other S benchmark in my group. S therefore rests on SYNC alone, and SYNC also removes multi-step and repositioning. The header (line 522, "S comes from the cause"; lines 580-582, "no linear one-sided row is inductive there") does not mention that pinning λ = 1 certifies.
- Concern (HIGH, letter D): D needs every uniform row set to decline. Uniform strict rows decline only because of the FULL unit (lines 585-587), which is the over-approximation above. The mode dependence of the rows is that artifact.
- Concern (HIGH, number): line 543 says "8.5 %/min at 15 %, 2.1 %/min at 79 % on the deployed". Those are the profile's rates (0.1 x 85, 0.1 x 21). The deployed BULK 0.125 gives 10.6 and 2.6 %/min.
- Concern (LOW): matrix M3 lists PRECHARGE, BULK and ABSORB branch=2; the header names only the BULK segment.
- Fix: rethink the claim so the constant is physical. Options: a two-sided band, or a requirement-justified c with FULL handled (for example a hold mode whose floor equals the asymptote's sampling overshoot). Either show S with a λ=1 file that declines or drop S. Fix the two rate numbers.

### acc_spoof_lag
- Model: one cruise loop with a first-order powertrain lag. The speed sensor is spoofed +25 %; the reference is the same loop unspoofed.
- Property: v_L <= v_R and the exact dominant-mode row u_L <= u_R - 6 at λ = 3/2. I checked by hand: the roots (s+1)(s+5/3) and (s+2/3)(s+2), u_L' = 24 - u_L, u_R' = (2/3)(30 - u_R), and both engaged-envelope modal coordinates and corners.
- Concern (LOW): tau = 0.375 s is chosen so that the roots are rational (an ad hoc constant, disclosed). Row 1 at constant 0 is loose (-3.33 certifies); this is stated, and the "Exact" in line 742 refers to row 2 only, which should be said explicitly.
- Concern (LOW): M is a direct consequence of S with equal periods (budget ceil(1.5) = 2). This is genuine but not an independent mechanism.

### fuelcell_chp_dos
- Model: the PEM stack temperature at three current levels. The deployed's selection is held for 20 s by a DoS, against a nondeterministic protocol deciding every 10 s.
- Property: |T_L - T_R| <= 7 and Tin equal. I checked by hand: the excursions 4.30 / 5.83 K, the 7 K margin, the MED reach thresholds 43 / 53 and the pruning flow signs.
- Concern (HIGH, start-only): line 99-101 says LOW_L and HIGH_L occur only after a cold or hot start (MED_L is forward invariant; LOW_L and HIGH_L are re-entered only from themselves). Both P (the LOW->HIGH and HIGH->LOW pruning, lines 64-69) and X (the MED->LOW and MED->HIGH hops, lines 82-85) are needed only in LOW_L and HIGH_L windows. The suite's start-only rule (quoted in lit_csf25 departure (5)) is not addressed here. A hot start at up to 100 degC (the coolant boiling limit) is also not a real operating start.
- Concern (HIGH, domain): Tin in [40, 56] is "a design range of this file" (lines 47-48), and it sets the verdict. [36, 56] and [40, 60] decline at 7 (lines 71-73). The 7 K itself is derived from the same range. This is not a hardware limit.
- Concern (R): the header says the true tolerance is 0 under a 20 s hold (lines 32-38). The 5.00 tight value is "the tool's segment-end obligation, not the attack's effect", and the certified set is non-monotone ([5, 8] and 10). The benchmark measures the certificate's over-approximation, not the attack.
- Fix: make the hold consequential: thresholds or periods at which a held level actually leaves its band, with the claim keyed to that excursion. Get P and X from modes that runs re-enter. State the Tin range as load-bearing, or widen it.

### watertank
- Model: a one-dimensional level controller. The deployed has a +3 dm sensor offset and an aggressive pump (Low gain 2, Mid locked to boost). The reference has Eco and Boost Mid profiles and a PumpOff interlock.
- Property: |x_L - x_R| <= 3 under re-timing λ in [1, 2]. Tight: 2.99 declines and λ_max 1.95 declines. I checked by hand that the Lie derivative on the boundary is neutral.
- Concern (LOW): High is start-only on both sides. Mid tends to its set point (20 on the left, 17 on the right) and never reaches the High guard, and High decays to the set point without crossing it. The Mid<->High edges are dead. No letter depends on them (B is the Low->MidEco/MidBoost retention).
- No fix needed. Optionally say in the header that High is only an overfilled-start mode.

### lit_freedm_meter
- Model: the FREEDM single-transformer batS in sampled form (battery and grid modes for each demand/renewable pair). The public meter E stands in for the draw gr.
- Property: E_L = E_R at every instant, for every pair of secret battery levels (nondeducibility).
- Concern: none substantive. Every departure is listed with a forcing reason and an ablation (literal guards, domain B >= 0, grid-only right, batI gate). X is the source's own per-window argument. The claim follows directly from the always-available grid branch, but that is the source's result.

### furnace_program_timebase
- Model: a setpoint program generator (first-order filter per segment) with a load following at a 5-min lag. The deployed program runs at 80 % rate.
- Property: s_L = s_R and |T_L - T_R| <= 8 under re-timing λ in [0.8, 1], plus the validated load's tracking envelope (s_R - T_R <= 32, T_R <= s_R). I checked by hand: the residual (1 - λ) x 0.2 x 32 gives 6.4, and the cause table 3.2 / 4.8 / 6.4 / 8.0.
- Concern (LOW): 8 degC is justified as AMS 2750 Class 3 (±15 degF). That class bounds spatial uniformity across the work zone in a survey; it is not a tracking tolerance between a slowed and a validated run. The 8 vs the tight 6.40 is stated, not claimed tight.
- Fix: reword the requirement, for example "the profile's qualified tolerance band, set equal to the Class 3 uniformity", or cite a tracking or recipe tolerance.

### rover_terrain_6to12
- Model: the 6-DOF terrain rover with slope load, chassis pitch, second-order heave and a squat-pitch chain added (12-DOF), against the flat 6-DOF model at λ = 1.
- Property: v and s ordering (structural, the slope only slows the rover), auxiliary orderings, and left-only slip (0.25, tight 0.24) and heave (0.15, tight 0.13) bounds.
- Concern (HIGH, domain): the GRAVEL and PAVED guards do not constrain theta_p, so the domain theta_p in [0, 0.02] is what bounds the slope load at a GRAVEL entry. Slip needs sigma >= (1.47 + 9.81 theta_p)/7, which is 0.238 at 0.02 and 0.252 > 0.25 at 0.03. The bound is the route's grade (a scenario constant, a reachable band), not a hardware limit. The Domains paragraph (lines 738-739) does not state it as load-bearing; only the grade discussion (lines 686-690) implies it.
- Concern (LOW): ax, phs and omega_phs are output-only (lines 721-726): 3 of the 6 added coordinates feed nothing and carry no row. "dim 12" in the matrix overstates the refinement. Also, the requirement rows are left-only, so the relational content is the structural v/s ordering.
- Fix: carry the grade bound in the GRAVEL/PAVED entry guards (theta_p <= 0.02, gamma <= 0.02), or state it in the header as a load-bearing route bound. Either drop the squat chain or report dim 9 + 3 output-only.

## Findings with severity

HIGH
1. rover_terrain_2to4: S and M exist only for admitted states with w_L > v_R, which no run from a matched start reaches (header lines 87-90, 105-107). Check: add `w[l] <= v[r]` to all three rows. Expect CERTIFIED at λ 1 with letters I, as the header already measured. Then confirm by RELCERT_DEBUG that every λ > 1 cover pairing starts from w_L > v_R.
2. quad_light_profiles: B and X come from ECO/SPORT, which the witness never runs. Check: remove ECO and SPORT from Rsys and from NORMAL's next. Expect CERTIFIED with letters S M (the header reports this, measured 2026-10-29).
3. charger_fast_tapers, S: S is not forced. Check: set lambda_min = lambda_max = 1.0 with everything else unchanged. Expect CERTIFIED (letters.md "lambda=1 file" column already says CERTIFIED, with no S_lam1 diagnostic).
4. charger_fast_tapers, D and the tolerance: D and c = 1 both come from the FULL over-approximation (the physical lead is 0). Check: set the BULK and ABSORB rows to x_L <= x_R + 0.01 and keep FULL at +1. Expect CERTIFIED, which shows that the only mode-dependent content is the FULL unit. Also check: uniform x_L <= x_R + 0.01 except FULL declines only at FULL.
5. charger_fast_tapers, number: line 543 says "8.5 %/min at 15 %, 2.1 %/min at 79 % on the deployed". Check: 0.125 x (100-15) = 10.6 and 0.125 x (100-79) = 2.6. The quoted values are the profile's 0.1 rates.
6. fuelcell_chp_dos, start-only: P and X are needed only in the LOW_L and HIGH_L windows, which are start-only (header lines 99-101). Check: drop LOW and HIGH from Lsys (only MED_L, with guard [52, 78]). Expect CERTIFIED with letters M B, without P or X.
7. fuelcell_chp_dos, domain: the Tin design range [40, 56] sets the verdict. Check: widen Tin to [40, 60] on every mode of both sides. Expect DECLINED at 7 (the header reports DECLINED).
8. rover_terrain_6to12, domain: the theta_p (and gamma) bound 0.02 does the slip claim's work at GRAVEL entry. Check: widen theta_p's domain to [0, 0.03] on every mode of both sides. Expect DECLINED at sigma 0.25, since (1.47 + 0.294)/7 = 0.252.

LOW
- rover_terrain_2to4: the "stop line the plan never passes" reading is vacuous (the plan passes every point). lambda_max 2.7 vs tight 2.64 (disclosed). The slip row is left-only.
- quad_light_profiles: rows 1-3 are unloaded (0.8 is a requirement, not tight; disclosed). The P-only loop omits PX4's integral and hover-thrust estimation.
- lit_csf25_salt_tank_hold: its start-only exception should be added to the accepted list. lambda_min 0.3333333333 vs 1/3.
- charger_fast_tapers: M3 is in three modes per the matrix, while the header names BULK only.
- acc_spoof_lag: tau chosen for rational roots. "Exact" applies to row 2 only (row 1 is loose by 3.33). M follows from S.
- watertank: High is start-only on both sides and the Mid<->High edges are dead (no letter affected).
- furnace_program_timebase: AMS 2750 Class 3 is a spatial-uniformity class, not a tracking tolerance.
- rover_terrain_6to12: 3 output-only coordinates inflate dim 12. The requirement rows are left-only.
- fuelcell_chp_dos: the certified tolerance set is non-monotone and the 5.00 is the tool's segment-end obligation (disclosed). A hot start at 100 degC is not an operating start.

## Verified HIGH findings and actions (2026-10-30)

Every HIGH finding was treated as a hypothesis and checked by tool runs on scratch copies (frozen binary,
`RELCERT_IMPLIED_CUT=1`, bisection to 0.01, the letters pipeline on scratch suites), by simulation or by Z3
face checks (`tmp/verify-r6/`). 21 HIGH findings from the reviewers, all confirmed (two only partly); the
verifiers found three more of the same classes (marked +). Actions:

| benchmark | finding (verified) | action | letters before -> after |
|---|---|---|---|
| `hydro_rejection_gatecal` | header said the REJECT speed band is 0.09; the file (since round 4) has 0.07 | header | D -> D |
| `turbine_startup_gearratio` | the GEN tolerance 0.061 and D needed only for GEN states above rated speed, which no run reaches (start-only) | uniform rows `w_L <= 1.05 w_R and w_L <= 12.705` (ceiling 12.705 tight, factor 1.05 tight) | R P D I -> R P I |
| `platoon_profiles` | the P_0.45 row is implied by the others (1.49 declining is the tool's route: the rows are proved as a chain); 3.34 is the tool's bound, the semantic fixpoint is 2.80 / 1.12 (Z3 face check) | header (the tool needs the redundant row) | S M -> S (rule M) |
| `platoon_linkloss` | M comes from a single-mode right whose 0.1 s period changes no run (right epsilon 0.2: budget 1) | letter rule M (below); header | M -> none |
| `engine_start_highidle` | "real-time" 4 % bound: in lock step the gap reaches 5.51 % | header (profile comparison against a reference that may run ahead alone) | R D I -> R D I |
| `rampmeter_poll_2to1` | "tightest 7.00": 5.00 also certifies (certifying sets non-monotone, steps of 5) | header (sets per poll period) | M B -> M B |
| `h2_refuel_ambientbias` | R needed only for TOPOFF_L / STAGE3_R start pairs no handoff produces | rows `p_R >= 58` in TOPOFF and COMPLETE (now certifies under SYNC and NO_REPO) | R D I -> D I |
| `flaps_slow_approach` | "domain not load-bearing" false: the placard range sets 25 / 10 (guards repeat it) | header | S -> S |
| `elevator_start_discbrake` | rest position 19.96 m wrong: 20.07 m | header | R D -> R D |
| `ventilator_vc_cuffleak` | domain `V <= 0.404`, `V - 0.4 t <= 0` is the reachable set of one breath and carries the INSP -> EXP handoff | model: the ventilator's inspiratory countdown timer `s` (INSP `s' = -1`, guard `s >= 0.01`; EXP `s' = 0`); physical domain `s >= 0, V >= -0.4`; the delivered-volume bound moved into the claim; Assumption 1 proof adapted | D -> D |
| `watertank_twospeed` | P from the dead edge Fast -> PumpOff (Fast keeps x >= 2) | edge removed (right model; proof's edge list) | S M B P -> S M B |
| `acc_spoof_limp` | X only from LIMP starts at 34.5-36 m/s, unreachable under the 2 s debounce (at most 28.58) | LIMP ceiling 28.6 | M B I X -> M B I |
| `quad_light_profiles` | B and X from ECO / SPORT, which the witness never ran | redesign: the pilot may switch profiles on both sides, each profile its own stretch (1.25 / 1.2 / 1.16), Phi conserved in every matched pairing; SPORT set point 2.4 -> 2.5; Assumption 1 proof adapted | S M B X -> S M B X (now genuine) |
| `rover_terrain_2to4` | S and M needed only for starts with w_L > v_R; w_L <= v_R is forward invariant | real-time form (row `w_L <= v_R`, lambda 1) | S M I -> I |
| `charger_fast_tapers` | S not forced (lambda = 1 file certifies); c = 1 and D from the tool's FULL over-approximation; header rates were the profile's; + the claim does not depend on its cause (an 8x deployed rate certifies) | SKIPPED (`benchmarks/skipped/charger_fast_tapers/SKIPPED.md`); refill `molding_pack_checkring` (reserve, reframed: 2000 bar machine rating as the domain, hold setting in the claim; tight 19.24 = 500 l / (10 + l); D genuine) | S M R B D I -> out; D in |
| `fuelcell_chp_dos` | Tin [40, 56] design band in the domain decides the verdict; P / X in LOW_L / HIGH_L windows | domain = physical (T, Tin in [0, 100]); the design inlet range moved into every guard on both sides (a stated permission condition); P and X decided in LOW_L, the cold-start warm-up of every real start (HIGH_L carries only mirror halves); Assumption 1 proof adapted | M B P X -> M B P X |
| `rover_terrain_6to12` | the route-grade bound theta_p <= 0.02 sets the slip verdict, not stated | header (load-bearing physical route constant, edge 0.028) | I -> I |
| + `acc_tune_limp` | the witness never ran COMFORT / SPORT (every hop into NORMAL): B and X start-only | COMFORT and SPORT removed from the stock controller; Assumption 1 proof adapted | S M B D I X -> S M D I |
| + `acc_spoof_lag`, `acc_tune_lag`, `gantry_speed_zones`, `quad_light_lag` (and the two platoon files above) | M from a single-mode right (the same class as `platoon_linkloss`) | letter rule M | S M -> S |

Letter rule M (`scripts/suite_v2_letters.py`, 2026-10-30): M also needs a right with at least two modes;
with one right mode the cycle boundaries are invisible (a multi-step cover is one continuous right run cut at
epsilon_R), so the matrix still reports the cover shape (M2) but no letter is credited.

Not acted on (LOW): wording items in the per-group notes; `antenna_track_kvretune` STOW row 0.25 (loose
against 0.085, not a requirement); `train_ato_odometry` M and B from cross-level pairings (borderline,
filed LOW by its reviewer); `rampmeter_poll_2to1` k domain = the forward-invariant band [14, 42.5] rather than the
capacity (LOW; measured not load-bearing: with k in [0, 45] it CERTIFIES, 0 UNKNOWN, 0 BLOCKING); `quad_light_lag` lag acting on the feedforward only (RETHINK at 2, a design objection, not a
HIGH class); `rover_patrol_lag` re-timed one-sided order (RETHINK at 2, no HIGH finding).
