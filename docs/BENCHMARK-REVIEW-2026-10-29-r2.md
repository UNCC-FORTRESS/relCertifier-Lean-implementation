# Benchmark review, round 2 (2026-10-29; suite_v2 at 8bdd98e, 50 benchmarks)

Five fresh reviewer agents, 10 benchmarks each, rubric `docs/review-rubric.md` only; the reviewers did not see earlier reviews, scores or fix lists. Findings are reviewer claims; every claim acted on was verified by a tool run first (the round's fix log is in `docs/OVERNIGHT-2026-10-29.md`).

## Ranked table (worst first)

| benchmark | P | R | C | overall | verdict | one-line reason | prev overall |
|---|---|---|---|---|---|---|---|
| `acc_tune_limp` | 2 | 3 | 4 | 2 | RETHINK | LIMP guard v <= 30 (l.27, l.85) is tuned to the claim: at v = 36 SPORT decelerates faster than the limp map, so v_L <= v_R fails if the fault may latch anywhere CRUISE runs; DISENGAGE v' = -0.5 v (l.18) is 10 m/s^2 at the floor | 4 |
| `charger_fast_tapers` | 3 | 2 | 4 | 2 | RETHINK | one-sided re-timed bound is implied by the rate design (deployed rates <= 5/4 x profile rates in every phase) and its constant 2 is, by the header's own account (lines 69-80), two tool artifacts, not charging physics | 2 |
| `lit_lz21_vehicle_position` | 4 | 2 | 5 | 2 | RETHINK | the source's state bound x <= 10 is dropped (l.38-43) and the witness is a pure translation of the left; the certified claim holds for any offset (l.33) | 3 |
| `sat_detumble_phases` | 2 | 4 | 5 | 2 | RETHINK | the x, y actuators are rate dampers of wheel authority (l.21-27) because the claim is false for a real magnetorquer + wheel suite; the header says so, so the plant is chosen to make the identity hold | 3 |
| `engine_start_highidle` | 3 | 3 | 4 | 3 | RETHINK | letter D rests entirely on the unreachable ABORT start (l.28-34, l.38-39); without ABORT the uniform +4 row certifies (l.31-32) | 3 |
| `rover_patrol_lag` | 4 | 3 | 4 | 3 | RETHINK | one-sided rows plus right-only repositioning let the plan run ahead freely; the "registered waypoint" reading (l.38-42) is not operational; the physically interesting direction (rover behind plan) is the one that declines (l.52-54) | 3 |
| `tunnel_jetfan_pairout` | 3 | 3 | 5 | 3 | RETHINK | excellent physics, but the domain floor u >= 3.2 is admittedly not physical and carries the fire requirement by itself (l.44-50, 96-99); FIRE row u_L <= u_R has no smoke-control content; the header's own variant (l.55-59) is the fix | 3 |
| `acc_spoof_limp` | 3 | 4 | 4 | 3 | POLISH | LIMP guard v <= 30 (line 104) is load-bearing for row 1 and only thinly motivated; two "2026-10-29" dates | 3 |
| `acc_tune_lag` | 3 | 3 | 4 | 3 | POLISH | lag tau = 0.32 s picked for rational roots (l.14-17); claim is a modal identity, the measured speed tolerance 3.34 m/s (l.35-37) is left out of the rows | 4 |
| `fuelcell_chp_dos` | 4 | 3 | 5 | 3 | POLISH | certified 7 K is a tool artifact 1 K inside a non-monotone window [5,8] (header admits the physical answer is 0); requirement inference from steady temps (l.24-27) does not follow; future dates | 2 |
| `h2_refuel_ambientbias` | 3 | 3 | 4 | 3 | POLISH | ABORT (l.15, l.132-136) is never enterable (both flows rise at 0.5 MPa, pruned), yet the header cites an aborted reference as the reason the stage rows are exact (l.32-33) and uniform rows decline (l.44-45) | 3 |
| `platoon_profiles` | 3 | 3 | 4 | 3 | POLISH | left AEB is start-only (SPORT->AEB unsat, line 87) so D rests on an unentered mode; unary gap rows; "2026-10-29" dates | 3 |
| `quad_light_lag` | 3 | 4 | 4 | 3 | POLISH | feedback term bypasses the motor lag (l.16-19) and K = g/2 chosen to land lambda on the grid (l.24-26); 0.8 m requirement sourced and tightness measured | 3 |
| `quad_light_profiles` | 3 | 3 | 4 | 3 | POLISH | K = g/2 (l.31) chosen for a round stretch; rows 1-2 have no tightness evidence (l.60 gives Psi = 0.016 m from hover; Psi is conserved, so 0.8 m is a start-set size, not a bound the dynamics produce); ECO/SPORT exist only to earn B, X (l.69-70) | 3 |
| `rover_terrain_2to4` | 4 | 3 | 4 | 3 | POLISH | slip row tight and physical; the re-timed clearance rows are weaker than the real-time form the header says certifies (lines 81-84), and lines 69-75 explain the stretch as faster set-point tracking, which is false from matched starts | 2 |
| `rover_terrain_4to6` | 3 | 4 | 4 | 3 | POLISH | "- zs" drag term (line 16, 77) subtracts wheel radii from m/s^2 with an unstated unit coefficient; rows otherwise tight | 4 |
| `turbine_startup_gearratio` | 3 | 3 | 5 | 3 | POLISH | exemplary candour (letters from claim form, two-sided attempts listed), but unscaled loop gains are an admitted inaccuracy (lines 31-41) and the STOP edges exist only to be pruned (line 24, line 59-60) | 2 |
| `zone_lightmass_schedule` | 4 | 3 | 5 | 3 | POLISH | tight value 0.485 is set by the domain's far bound (l.57-58) and lands 0.015 under the 0.5 K requirement; a 35 degC upper bound would decline; scenario label "model-refinement" misdescribes a plant change | 3 |
| `acc_spoof_lag` | 4 | 3 | 4 | 3 | KEEP | clean linear physics and tight exact rows, but the certified claim is the spoof's mathematical signature (re-timed at 3/2), while the requirement the header names (8 m/s shortfall, lines 55-63) is not a row | 3 |
| `elevator_start_discbrake` | 4 | 3 | 4 | 3 | KEEP | clean retrofit scenario; z,v rows are a copy of identical motion dynamics, content is the right-only lift (R) | 3 |
| `gantry_speed_zones` | 4 | 3 | 5 | 3 | KEEP | exact time reparametrization by construction (tightest 0.00); 10 mm justified by clearance margin; very honest header | 3 |
| `lit_csf21_vehicle_bus` | 3 | 4 | 5 | 3 | KEEP | source-faithful, departures listed; Coast stand-in (v <= 1, v' = 0) lets the car creep into the obstacle forever | 3 |
| `lit_csf21_vehicle_thermo` | 4 | 3 | 5 | 3 | KEEP | faithful source encoding with every departure listed (l.42-57); witness copies the attacked car's action, but that is the source's non-interference claim | 3 |
| `lit_drl_car_stop` | 3 | 3 | 5 | 3 | KEEP | faithful sampled dRL refinement; the witness is the identity by the source's definition, so the content is the guard implication (Goal 1) only, as the header says | 3 |
| `lit_drl_lane_control` | 4 | 3 | 5 | 3 | KEEP | faithful sampled dRL case study with every deviation stated; property is the identity relation whose content is Safe_eps implies Safe (witness copies the left's action pair) | 3 |
| `lit_freedm_meter` | 4 | 3 | 5 | 3 | KEEP | faithful literature nondeducibility with every deviation stated; witness never needs its battery (grid-only right certifies, line 46-47), so the certified content is the source's "grid always available" argument | 3 |
| `rover_ladder_2to3` | 4 | 3 | 4 | 3 | KEEP | honest first rung: clearance rows are a monotone-set-point argument and the heading row is a sublevel set ("every value in [0, 0.6] certifies", line 52); low content by design | 4 |
| `rover_ladder_3to6` | 4 | 3 | 5 | 3 | KEEP | ladder rung with no mechanism; psi row is an identical-dynamics copy and the pitch row is left-only; s row is real | 3 |
| `rover_ladder_6to8` | 4 | 3 | 4 | 3 | KEEP | canonical rover rung; heading rows certify at any value (l.53-54) and the rollover row is implied by heading+roll (l.60-64); clearance rows carry the relational content | 4 |
| `rover_terrain_6to12` | 3 | 3 | 4 | 3 | KEEP | grade pinned by guard+domain (l.67-70, l.103); requirements sourced and tightness measured (l.54-58); header number nit at l.65 | 3 |
| `tank_dos_3to1` | 3 | 4 | 5 | 3 | KEEP | one-directional demand surge (l.13-14) makes h_L <= h_R exact; shortfall 0.8 from a submergence requirement, discriminates 30 s from 40 s holds (l.40-43) | 4 |
| `watertank` | 3 | 3 | 4 | 3 | KEEP | running example; deployed = nominal shifted by the offset and re-timed, so the tight row 3.00 is by construction (l.42-46); lambda range unpinned (l.81) | 3 |
| `watertank_twospeed` | 3 | 4 | 4 | 3 | KEEP | running-example variant, consistent offsets, upper 3 exactly tight and lower 2 justified (1.50 tight); PumpOff (l.150-154) is an unreachable sink, which is the P letter's whole content | 3 |
| `insulin_basal_cgmloss` | 4 | 4 | 4 | 4 | POLISH | sourced physiology, requirement-derived 25/0.5 with tight 20/0.4 shown; line 21's "at most 17.9 mg/dL in 5 min" is the 280 mg/dL band-edge rate, not the domain maximum (27.9 at G = 400) | - |
| `platoon_latency` | 5 | 4 | 4 | 4 | POLISH | best-derived model in the group (W = J tau, rows derived and tight); but D rests on an AEB mode no CACC run reaches on either side (l.90-91), which l.4-5 does not say | 4 |
| `bottling_fill_strainer` | 4 | 4 | 5 | 4 | KEEP | consistent physics (Psi constant in CLOSE), requirement-tied 2 mL, tight 1.20 derived from the in-flight volume; stretch pinned to the grid is disclosed | 4 |
| `flaps_slow_approach` | 4 | 4 | 4 | 4 | KEEP | hardware ratio 1/2 as the stretch, 20 kt from a stated requirement, 17.50 tight with a closed-form explanation; header is complete | 4 |
| `furnace_program_timebase` | 4 | 4 | 4 | 4 | KEEP | sourced requirement (AMS 2750 Class 3), derived residual 6.4 = (1-0.8) x 32, stretch range = recipe allowance; cells agree | 4 |
| `grid_ffr_dos` | 4 | 4 | 4 | 4 | KEEP | realistic swing/FFR model; 0.24 a_R band is the FFR-loss margin, tight and justified (l.36-42); latch encoded as x - 2a (l.16-19) is the only device | 4 |
| `hydro_rejection_gatecal` | 4 | 4 | 4 | 4 | KEEP | genuine mode-dependent requirement (power on grid, speed after rejection), both tolerances requirement-tied, D shown necessary; REJECT governor has no speed feedback (l.18-20), unflagged simplification | 4 |
| `lit_girard08_robot` | 4 | 4 | 4 | 4 | KEEP | tight 0.16 bound, departures disclosed; line 67-68 "inside the enlarged invariant" holds at window starts only | 4 |
| `lit_nahs25_salt_tank` | 4 | 4 | 5 | 4 | KEEP | source's forward distance 3, tight (2.99 declines), direction and slack row stated; deviations listed | 4 |
| `platoon_linkloss` | 4 | 4 | 5 | 4 | KEEP | consistent CACC/ACC/AEB physics (poles, invariant TTC floor, Q_rho contraction all re-derived), tight 0/15 m rows from the time-gap policy; AEB is start-only (lines 44-46), the shared model's known limitation | 3 |
| `reactor_feed_wireless` | 4 | 4 | 5 | 4 | KEEP | sensor-rate robustness with a stated two-sided requirement and tight 8.00; pruning window depends on the coolant range (disclosed l.57-59); structural twin of fuelcell_chp_dos (l.81-84) | 4 |
| `rover_ladder_8to12` | 4 | 4 | 4 | 4 | KEEP | consistent 12-DOF rung, requirement constants sourced, tightest values measured, composition argument stated; runtime 31 s of a 40 s budget (l.126) is the only fragility | 4 |
| `sat3w_detumble_phases` | 4 | 4 | 4 | 4 | KEEP | gyrostat equations and the exact energy identity re-verified; cause dependence shown (line 65-66); design/flight period split (lines 30-38) is the one contrived constant | 3 |
| `sat_detumble_weak` | 4 | 4 | 4 | 4 | KEEP | Euler/gyrostat equations check out and the energy identity is exact; M and B come from a declared 2 s period on a single-mode left that changes no behavior (l.33-39) | 2 |
| `syringe_relay_prearm` | 4 | 4 | 5 | 4 | KEEP | realistic relay (constants check out), tight b and C rows, retiming is the clinical content | 4 |
| `train_ato_odometry` | 4 | 4 | 4 | 4 | KEEP | real miscalibration (806/840), ETCS dV_warning 1.11 as the requirement, tight 1.07 with the model bound 1.042 explained, domains from ETCS EBI | 4 |
| `ventilator_vc_cuffleak` | 4 | 4 | 5 | 4 | KEEP | ISO-derived rows, leak ODEs verified; domain atom V - 0.4 t <= 0 (line 86) is an initial-condition invariant, not a limit | 4 |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 4 | 29 | 17 | 0 |

Verdicts: KEEP 30, POLISH 13, RETHINK 7, DROP 0. Overall >= 4: 17/50 (34 %). Overall < 3: 4.

## Delta vs previous round

Previous histogram (1..5): 0, 5, 25, 19, 0 over 49; this round: 0, 4, 29, 17, 0 over 50.

Up: `fuelcell_chp_dos` 2->3, `platoon_linkloss` 3->4, `rover_terrain_2to4` 2->3, `sat3w_detumble_phases` 3->4, `sat_detumble_weak` 2->4, `turbine_startup_gearratio` 2->3.

Down: `acc_tune_lag` 4->3, `acc_tune_limp` 4->2, `lit_lz21_vehicle_position` 3->2, `rover_ladder_2to3` 4->3, `rover_ladder_6to8` 4->3, `rover_terrain_4to6` 4->3, `sat_detumble_phases` 3->2, `tank_dos_3to1` 4->3.

New in this round: `insulin_basal_cgmloss`.

## Reviewer notes by group

### G1

# Review G1 (independent, rubric RUBRIC.md), 2026-10-28

Sources read: benchmarks/suite_v2/<name>/input.txt (full), the benchmark's rows in docs/paper-numbers/matrix.md (main table, timing table, per-benchmark run record) and docs/paper-numbers/letters.md. No header pointed to docs/SUITE-REDESIGN.md. Mechanism cells in matrix.md / letters.md agree with every header's "mechanisms:" line for all ten files (checked per benchmark below).

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| bottling_fill_strainer | 4 | 4 | 5 | 4 | KEEP | consistent physics (Psi constant in CLOSE), requirement-tied 2 mL, tight 1.20 derived from the in-flight volume; stretch pinned to the grid is disclosed |
| fuelcell_chp_dos | 4 | 3 | 5 | 3 | POLISH | certified 7 K is a tool artifact 1 K inside a non-monotone window [5,8] (header admits the physical answer is 0); requirement inference from steady temps (l.24-27) does not follow; future dates |
| hydro_rejection_gatecal | 4 | 4 | 4 | 4 | KEEP | genuine mode-dependent requirement (power on grid, speed after rejection), both tolerances requirement-tied, D shown necessary; REJECT governor has no speed feedback (l.18-20), unflagged simplification |
| lit_drl_lane_control | 4 | 3 | 5 | 3 | KEEP | faithful sampled dRL case study with every deviation stated; property is the identity relation whose content is Safe_eps implies Safe (witness copies the left's action pair) |
| platoon_latency | 5 | 4 | 4 | 4 | POLISH | best-derived model in the group (W = J tau, rows derived and tight); but D rests on an AEB mode no CACC run reaches on either side (l.90-91), which l.4-5 does not say |
| reactor_feed_wireless | 4 | 4 | 5 | 4 | KEEP | sensor-rate robustness with a stated two-sided requirement and tight 8.00; pruning window depends on the coolant range (disclosed l.57-59); structural twin of fuelcell_chp_dos (l.81-84) |
| rover_patrol_lag | 4 | 3 | 4 | 3 | RETHINK | one-sided rows plus right-only repositioning let the plan run ahead freely; the "registered waypoint" reading (l.38-42) is not operational; the physically interesting direction (rover behind plan) is the one that declines (l.52-54) |
| sat_detumble_weak | 4 | 4 | 4 | 4 | KEEP | Euler/gyrostat equations check out and the energy identity is exact; M and B come from a declared 2 s period on a single-mode left that changes no behavior (l.33-39) |
| tunnel_jetfan_pairout | 3 | 3 | 5 | 3 | RETHINK | excellent physics, but the domain floor u >= 3.2 is admittedly not physical and carries the fire requirement by itself (l.44-50, 96-99); FIRE row u_L <= u_R has no smoke-control content; the header's own variant (l.55-59) is the fix |
| zone_lightmass_schedule | 4 | 3 | 5 | 3 | POLISH | tight value 0.485 is set by the domain's far bound (l.57-58) and lands 0.015 under the 0.5 K requirement; a 35 degC upper bound would decline; scenario label "model-refinement" misdescribes a plant change |

## bottling_fill_strainer

Model: one fill of a flowmeter-controlled filler, FILL (V' = Q u, u = 1) then CLOSE (u' = -25 u, V' = Q u), right Q = 200 mL/s, left Q = 170 mL/s (clogged strainer, 85 %).
Property: with the predicted final volume Psi = V + (Q/25) u, Psi_L = Psi_R - 1.2 exactly, u_L <= u_R, V_L <= V_R, and the deployed fill is short by at most the 2 mL giveaway margin (row 5), FILL paired at lambda 17/20, CLOSE at 1.
Checks: d/dt Psi = Q u - Q u = 0 in CLOSE; in FILL rows (1,2) with u = 1 give V_L = V_R; from (1,2)+(3), V_R - V_L = 6.8 u_L - 8 u_R + 1.2 <= 1.2, so the 1.20 "tightest" of row (5) (l.36) is a consequence of the stated strengthening rows, not an independent measurement (worth one clause in the header). Matrix: M1 FILL 17/20, M6 yes, letters S I: agree with l.6-8.
Strongest concern: the certificate exists only at a grid ratio (0.853 declines, l.44-46) and lambda_min 0.8 is a design value (l.33-35); both are disclosed. None blocking.

## fuelcell_chp_dos

Model: PEM CHP stack T' = (Tin + rise - T)/120 at three current levels; right = overlapping-band protocol deciding every 10 s, left = deterministic thresholds 52/78 held 20 s by a DoS on the supervisory link.
Property: |T_L - T_R| <= 7 and equal return temperatures in every left mode.
Strongest concern (R): the header states (l.28-34, 45-53) that the physical deviation is 0 (the protocol can copy the deployed), that the exact claim is declined under every configuration, that 5.00 is "the tool's segment-end obligation, not the attack's effect", and that the certified window is non-monotone ([5,8] certifies, 8.01-9.9 decline, 10 certifies); the file's 7 sits 1 K inside that window. The requirement inference (l.24-27: 7 K from the protocol's steady temperatures to the [45,85] window) does not follow, since the protocol's permitted trajectories span the domain [40,100] (HIGH is allowed from any T > 70). Pruning depends on Tin in (38,58) (l.65-68), disclosed as a certificate limitation. Matrix: M2 M3 M4 yes, letters M B P X: agree with l.5-7.
Fix (POLISH): reword l.24-27 as a band around a permitted trajectory (drop the window inference) or add the window as a requirement row on T_R; fix the dates "2026-10-29" (l.29, 45, 71, 99), which postdate the review date.

## hydro_rejection_gatecal

Model: hydro unit, gate servomotor g' = (ref - g_meas - 20 w)/4 on the grid (w the shared frequency, constant), after the breaker opens g' = (0.1 - g_meas)/4 and w' = (g - 0.1 - w)/8; left transducer reads 0.02 low.
Property: ONGRID t, w equal and |g_L - g_R| <= 0.027 (dispatch +-3 % of rated power); REJECT |w_L - w_R| <= 0.09 (1.30 overspeed trip minus the commissioned 1.2055 peak) and the same gate band.
Strongest concern (P): in REJECT the governor is an open-loop run-back to the no-load gate with no speed term (l.18-20) although l.12 introduces the 5 % droop as the unit's primary frequency response; a governor keeps acting on speed after a rejection. Acceptable as a test-sequence abstraction but not flagged as a deviation from physics. The speed band 0.09 is 9x the simulated 0.0101 peak gap (l.44-45) but requirement-tied. Matrix: M5 yes 3/3 handoffs, letters D, uniform rows ONGRID/REJECT DECLINED: agree with l.5-7, 47-55.
Fix: none required; one clause at l.18-20 stating the governor simplification would make C a 5.

## lit_drl_lane_control

Model: Loos-Platzer dRL Section 6.4 local lane control in sampled form, d' = v_l - v_f, follower actions {Accel under Safe_eps or Safe, Brake, Coast at v_f <= 1}, leader {A, -B}, six action pairs per side.
Property: identity relation (d, v_f, v_l equal) in every left mode: the time-triggered follower refines the permissive one.
Strongest concern (R): the invariant is the identity and the witness hops into the left's action pair (l.55-57); the entire content is Safe_eps implies Safe (dRL's Goal 1, which "closes automatically", l.15). Non-trivial only through completeness of the right model and the choice mechanism. Deviations (1)-(5) are stated once and the three-valued-leader failure is reported as open (l.32-34). Matrix: all M columns no, letters X: agrees with l.4.
Fix: none; KEEP as the literature anchor it is.

## platoon_latency

Model: CACC follower with a lagged V2V feed-forward (error e' = +-J - e/tau, |e| <= W = 0.5), relative coordinates g, r; right ideal link; shared radar AEB.
Property: |Delta g| <= 4 (= J tau / kp, the static allowance, tight 4.00), two derived modal rows (tight), deployed collision freedom g_L >= 5 and TTC floor g_L + 2 r_L >= 5, design in its operating range; AEB rows exact.
Strongest concern (R/C): l.90-91 state that the CACC operating range is forward invariant on both sides, that the design's CACC -> AEB edge is pruned and the deployed's handoffs are unsat, so AEB is reachable only as a start on either side; the D letter (l.4-5, 102-103, 115) therefore rests on a mode no CACC run enters, and the AEB row is exact only because both AEBs are identical from an exact start. The mechanisms line sells "the 7 handoffs unsat or implied" without saying so. Matrix: M5 yes, M4/M6+ vacuous, letters D: agree.
Fix (POLISH): add to l.4-5 that AEB_L and AEB_R are start-only in this file and that D is the rows differing on a disconnected mode; or (RETHINK-size) allow e beyond W transiently so a deployed AEB entry is reachable and the handoff carries content.

## reactor_feed_wireless

Model: CSTR T' = 0.1 (p + 4k - T) at four feed levels selected by a temperature interlock (partition at 25/35/45), right reading every minute, left every 2 min (WirelessHART burst rate).
Property: |T_L - T_R| <= 9, equal cooling-water temperature; 9 K = margin from the validated envelope [19,51] to boiling (60) and feed accumulation (10).
Strongest concern: the pruning of four live edges holds only for p_lo > 13 and p_hi < 37 and the targets are live only for p_lo < 17, p_hi > 33 (l.57-59, 76-79), so the coolant range [15,35] is inside a narrow window that the certificate needs; the header states the range as winter-to-summer tower supply (l.15), which is plausible. The certified window [8,10] is again non-monotone (l.37-39) and the simulated worst gap is 0.87 K (l.64-65), both disclosed. The file is the positive-association twin of fuelcell_chp_dos (l.81-84) with a deterministic reference (no X). Matrix: M2 M3 M4 yes, letters M B P: agree with l.6-9.
Fix: none required.

## rover_patrol_lag

Model: patrol rover with a first-order motor lag (v' = a, a' = (16/3)(c - v - a)) against the lag-free planning model, same odometer-zone planner (SLOW, MEDIUM_ECO/BRISK, FAST), lambda in [1, 3/2].
Property: the rover is never more than 1 m ahead of the matched plan run (s_L <= s_R + 1), with a look-ahead-odometer strengthening P_L <= P_R + 0.375; both rows one-sided.
Strongest concern (R): both rows let the plan lead without bound, and the witness may advance alone (right-only repositioning, load-bearing: RELCERT_NO_REPO=1 DECLINES, l.62-64) and run 3/2 faster; the requirement reading at l.38-42 ("every waypoint the rover reaches has already been registered in the matched plan run") is not an event of any real planner, since the matched run is re-timed and advanced. The direction a planning-model refinement should guarantee, that the rover does not fall behind the plan, is the one reported to DECLINE (l.52-54). The header itself notes the letters come from the 1 m slack rather than the lag (l.7-10). Matrix: M1 FAST 11/8, M2 B=2 +RO, M3 yes, letters S M R B, NO_REPO DECLINED: agree.
Fix (RETHINK): state the behind-direction bound s_R <= s_L + X (with its own look-ahead strengthening) and admit a plan re-timed slower (lambda in [2/3, 1]) so the plan cannot outrun the rover across zone boundaries; if that declines, report the tightest X and the reason, and demote the present one-sided claim to a stated strengthening.

## sat_detumble_weak

Model: 60 kg microsatellite gyrostat (J = diag(2,4,5), z-wheel) with isotropic rate damping at the derated k_L = 0.4 against the decoupled design model at NOMINAL 0.5 / ECONOMY 0.45 / SURVIVAL 0.42 with a SAFE sink; lambda = 4/5.
Property: body energy E_L = E_R exactly, right re-timed by 4/5 (the detumble budget scales by 1.25).
Checks: the coupling terms cancel in E' (4 w1 w1' + 8 w2 w2' + 10 w3 w3' = -0.8 E), the Euler coefficients match J, and h' = 5 k w3 is the wheel absorbing J3 w3: the identity is physical, not tuned.
Strongest concern (C): the left has a single mode, so its 2 s decision period (l.33-39, "a design value of this file") changes no behavior; M and B (l.77-79) come from that declared period only. Exactness pins lambda to 4/5 (0.79/0.81 decline, l.67-70), disclosed. Dates "2026-10-29" (l.14, 60, 70, 87, 93) postdate the review. Matrix: M1 4/5, M2 B=2 +choice, M3 yes, M4 vacuous, letters S M B X: agree with l.6-10.
Fix: none required; say in l.11 that the period is behaviorally void on a one-mode left.

## tunnel_jetfan_pairout

Model: 1.6 km tunnel air column u' = a n - 0.00171875 u^2 and well-mixed CO c' = e - (u/L) c, ten vs eight jet fans, NORMAL (low speed) until the fire alarm at t = 600 s, then FIRE (full speed, 100 MW fire adding 1.1 ppm/s). All constants reproduce (a = 0.009, steady 3.618/7.236 m/s, 70 ppm, 278 ppm).
Property: NORMAL t equal, u_L <= u_R <= u_L + 0.5, c_R <= c_L <= c_R + 30 (PIARC 70 -> 100 ppm); FIRE t equal, u_L <= u_R.
Strongest concern (P, R): the header states plainly (l.44-50, 96-99) that the domain floor u >= 3.2 "is not a physical limit" (fans off gives u = 0), is the forward-invariant set the certificate needs (load-bearing at 2.54 through the c <= 100 fact), and that the fire requirement (critical velocity 3 m/s) "holds by the domain alone", so the FIRE row carries no smoke-control content (l.43-44). That is exactly the rubric's "bounds that force the property". The I letter persists without the cause (l.86-87). Matrix: M5 3/3, M6 yes, letters D I, uniform FIRE rows CERTIFIED: agree with l.8-12, 70-75.
Fix (RETHINK, already described at l.55-59): install the variant with floor 2.6, FIRE rows u_L >= 3 and u_R <= u_L + 1.56, CO cap 900 and strengthening 0.47, which the header reports CERTIFIED with the same letters; then the FIRE requirement is a stated row and the floor is below the critical velocity.

## zone_lightmass_schedule

Model: lumped zone T' = k (T_set - T), right k = 0.02 (medium EN ISO 13790 class, three set-point levels, nondeterministic), left k = 0.04125 (light prefabricated zone, two-level schedule); lambda = 2 (the design ratio).
Property: |T_L - T_R| <= 0.5 K against the reference trace re-timed by 2 (EN 15500 control accuracy class).
Strongest concern (R): the tight value is 0.00125 x (largest set-point-to-bound distance) / 0.04125 (l.57-58, 65-69), i.e. it is fixed by the domain's far bound, and on [5,30] it is 0.4848, 0.015 under the requirement; with an upper bound of 35 degC (a common overheating value) the distance 16 -> 35 = 19 gives 0.576 and the 0.5 row declines, so the domain choice at l.94-96 decides the verdict. The reachable worst case is 0.057 K (l.60-64), so the claim's content is the 2.0625/2 mismatch. Scenario "model-refinement" (l.7) describes a schedule moved to a different building, a plant change. Matrix: M1 2, M2 B=2 +choice, M3 yes, letters S M B X: agree with l.8-13.
Fix (POLISH): state at l.94-96 the sensitivity of the verdict to the upper bound (30 certifies, 32.5 is the edge, 35 declines) and justify 30 as the sensor span; relabel the scenario (plant-change / degraded-plant).

### G2

# Benchmark review G2 (independent, read-only; 2026-10-28)

Files reviewed: benchmarks/suite_v2/<name>/input.txt, docs/paper-numbers/matrix.md, docs/paper-numbers/letters.md. Line numbers refer to input.txt. Derivations below were re-done by hand (roots, invariance of guard faces, contraction constants); nothing was run.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_spoof_lag | 4 | 3 | 4 | 3 | KEEP | clean linear physics and tight exact rows, but the certified claim is the spoof's mathematical signature (re-timed at 3/2), while the requirement the header names (8 m/s shortfall, lines 55-63) is not a row |
| charger_fast_tapers | 3 | 2 | 4 | 2 | RETHINK | one-sided re-timed bound is implied by the rate design (deployed rates <= 5/4 x profile rates in every phase) and its constant 2 is, by the header's own account (lines 69-80), two tool artifacts, not charging physics |
| furnace_program_timebase | 4 | 4 | 4 | 4 | KEEP | sourced requirement (AMS 2750 Class 3), derived residual 6.4 = (1-0.8) x 32, stretch range = recipe allowance; cells agree |
| insulin_basal_cgmloss | 4 | 4 | 4 | 4 | POLISH | sourced physiology, requirement-derived 25/0.5 with tight 20/0.4 shown; line 21's "at most 17.9 mg/dL in 5 min" is the 280 mg/dL band-edge rate, not the domain maximum (27.9 at G = 400) |
| lit_freedm_meter | 4 | 3 | 5 | 3 | KEEP | faithful literature nondeducibility with every deviation stated; witness never needs its battery (grid-only right certifies, line 46-47), so the certified content is the source's "grid always available" argument |
| platoon_linkloss | 4 | 4 | 5 | 4 | KEEP | consistent CACC/ACC/AEB physics (poles, invariant TTC floor, Q_rho contraction all re-derived), tight 0/15 m rows from the time-gap policy; AEB is start-only (lines 44-46), the shared model's known limitation |
| rover_ladder_2to3 | 4 | 3 | 4 | 3 | KEEP | honest first rung: clearance rows are a monotone-set-point argument and the heading row is a sublevel set ("every value in [0, 0.6] certifies", line 52); low content by design |
| rover_terrain_2to4 | 4 | 3 | 4 | 3 | POLISH | slip row tight and physical; the re-timed clearance rows are weaker than the real-time form the header says certifies (lines 81-84), and lines 69-75 explain the stretch as faster set-point tracking, which is false from matched starts |
| sat3w_detumble_phases | 4 | 4 | 4 | 4 | KEEP | gyrostat equations and the exact energy identity re-verified; cause dependence shown (line 65-66); design/flight period split (lines 30-38) is the one contrived constant |
| turbine_startup_gearratio | 3 | 3 | 5 | 3 | POLISH | exemplary candour (letters from claim form, two-sided attempts listed), but unscaled loop gains are an admitted inaccuracy (lines 31-41) and the STOP edges exist only to be pruned (line 24, line 59-60) |

## acc_spoof_lag

Model: one car, v' = a, a' = (8/3)(a_cmd - a), a_cmd = 0.5(30 - v_meas); left reads v_meas = 1.25 v, right reads v. Both closed loops have the rational roots stated (left (s+1)(s+5/3), right (s+2/3)(s+2)); the modal guard coordinates and their box images ([-3, 8], [-11/3, 12], [40, 66], [44, 62]) re-derive exactly from the engagement box v in [23, 30], |a| <= 2.
Property: with the reference clock run at 3/2, the spoofed car is never faster than the reference (row 1) and its dominant-mode speed u = v + a/r_f is exactly the reference's minus the 6 m/s set-point shift (row 2, equality, tight at -6).
Concern: R. Row 2 is a theorem about two linear loops with proportional gains (the spoof is a gain change), and row 1 is a re-timed comparison no requirement states. The real-time requirement the header itself names (spoofed car at most 8 m/s below, keeps 22 m/s lane minimum, lines 55-63) certifies at lambda 1 but is excluded because it cannot share a file with the lambda 3/2 rows (line 61-62). The guards are forward-invariant hulls of the engagement box, not the controller's own engagement test (lines 65-75); defensible, but it is the tool's shape, not the ACC's.
Fix (optional): none needed for KEEP; if a second file is affordable, the batch-I4 real-time rows (v_R <= v_L + 8 with w = v + 0.5 a strengthening) are the requirement-grade claim and deserve their own suite entry rather than a "consequence" paragraph.

## charger_fast_tapers

Model: 1-D state of charge x (%), phases PRECHARGE 0.2(20 - x), BULK k(100 - x) (right 0.1, left 0.125), tapers 0.05 / 0.07, FULL hold, FAULT x < 10 latched; left decides every 0.012 min, right every 0.006 min; lambda pinned 5/4.
Property: against the profile replayed 1.25x faster, the deployed SoC never leads by more than 2 % (0 in PRECHARGE).
Concerns: (a) R: in every phase the deployed rate is <= 5/4 of the profile's (0.2 <= 0.25, 0.125 = 0.125, 0.05 <= 0.0625, 0 = 0), so the one-sided re-timed bound is a consequence of the rate table, and the header confirms the physical lead is 0.00 (line 53-54) with "the charging pairings themselves hold at any positive c" (line 81). The constant 2 is set by the FAULT x FAULT pairing and the FULL floor (lines 69-80), i.e. by the tool, and is "not a requirement" (line 52). (b) P: the FAULT edges from PRECHARGE/BULK (line 25, model lines 137/142/165/170) target a guard x < 10 that rising flows never reach; they exist to be pruned (line 85-89), and the left period "every other request cycle ... a design value of this file" (lines 39-41) is chosen to produce M. (c) An exponential CC phase (line 32-35) is a known simplification, disclosed.
Fix: state a claim the raised limit is accountable for. Either (i) the real-time benefit, x_R <= x_L + c at lambda 1 (the deployed is never behind the certified profile; the existential right can match the taper), or (ii) keep the re-timed form but remove FAULT on both sides (header line 73-75: c then certifies at 1.00) and name the FULL-floor unit as the sole residual. Either way the header should stop presenting c = 2 as the claim's constant.

## furnace_program_timebase

Model: setpoint generator s approaching each segment target as a first-order filter (kap 0.01 /min validated, 0.008 deployed; SOAK 0.1 / 0.08), furnace load T' = 0.2 (s - T); segments switch on s at 640 and 860. Rates and times re-check (6.3 degC/min initial, 100 min constant).
Property: re-timed by the recipe's permitted rate (lambda in [0.8, 1.0]), the deployed program equals the validated one and the load is within 8 degC (AMS 2750 Class 3) of the validated load; strengthening rows s_R - T_R <= 32, T_R <= s_R re-derive as forward invariant given the implied cuts s <= 650/870.
Concern: none of substance. The tightest 6.40 = (1 - lambda) x 32 is derived and matches; the window and the rate sweep (line 44-47) give the evidence the rubric wants. Minor: an exponential setpoint program (line 10-11) is a modelling choice (real programs ramp linearly and hold); worth one clause.
Fix: none.

## insulin_basal_cgmloss

Model: insulin action X' = (u - X)/55 (Hovorka t_max,I), glucose G' = (120 + 50 (b - X) - G)/60, need b constant in [0.5, 1.3]; nine-level basal table on 30 mg/dL bands; right reads every 5 min, left every 10 min (every other reading lost).
Property: deployed glucose within 25 mg/dL and insulin action within 0.5 U/h of the validated run at equal times. The contraction chain re-checks: two levels apart gives |dX| -> 0.4 and |dG| -> 20, matching the tightest values (line 35).
Concern: line 21 "within 5 min glucose moves at most 17.9 mg/dL" and line 25 "35.8 in 10 min" are the linear rate at the 280 mg/dL band edge (215/60 x 5). The domain maximum is at G = 400, X = 1.6, b = 0.5: 335/60 x 5 = 27.9 (26.8 exponential). The declared successor sets remain correct (27.9 < 30 and from 400 one cannot leave L8), but the sentence is wrong as stated. The 70-180 justification (lines 29-33) is a steady-state argument; transiently the validated run can be anywhere in [40, 400], so the 25 keeps the deployed within the target band only where the validated loop has settled. Fine, but say "at the validated loop's settling points".
Fix: reword line 21/25 to "at a band edge (G = 280) glucose moves at most 17.9 / 35.8; over the domain at most 27.9 / 51.4, still within one band of L8".

## lit_freedm_meter

Model: Bohrer and Platzer (LICS 2018) FREEDM transformer, sampled, one transformer, discrete demand d in {0,1,2} and renewable r in {0,1} as mode choices; battery modes enabled when one period keeps B in [0, 10], grid modes always; meter E' = d - r on grid, 0 on battery.
Property: initial-state nondeducibility of the battery level through the meter: for every left run from any B_L and every B_R there is a right run with E_R = E_L at all times.
Concern: R. The witness uses only grid modes and the header reports that a grid-only right certifies (line 46-47), so the certified fact is "every net draw in {-1, 0, 1, 2} is a grid mode", the source's own Prop. 11 argument. That is faithful to the source, but relative to a 12 x 12 mode model it is a thin claim; the X letter (line 49-52) is real. Deviations (1)-(4) and the leaky negative counterpart (line 53) are exactly what the rubric asks for.
Fix: none required.

## platoon_linkloss

Model: one link, gap g and range rate r behind a constant-speed lead; CACC r' = -0.125 (g - 20) - 0.75 r (poles 0.25, 0.5), radar ACC fallback with set point 35 and the same poles (kd_a = 0.6 re-derives), AEB on g + 2 r < 5 conserving g + 2 r; left decides every 0.2 s (two-message timeout), right every 0.1 s.
Property: the deployed follower is never closer than, and never more than 15 m = (h_a - h_c) v_ref farther behind than, the design follower; both constants tight; AEB rows exact.
Checks: d/dt (g + 2 r) = -0.25 (g + 2 r - 20) under CACC and the Q_rho contractions to 15 rho under (ACC, CACC) re-derive exactly, so the derived rows are what the header says.
Concern: the AEB is reachable only as a start on both sides (design edge pruned, deployed handoffs unsat, lines 44-46 and 92-95), because the lead never brakes; the D letter is therefore carried by a mode no run enters. The kd_a choice "so that the loop keeps the CACC poles" (line 22-23) is a design convenience. Both are disclosed and shared with the other platoon files.
Fix: none.

## rover_ladder_2to3

Model: four-wheel UGV on three odometer zones with speed loop v' = 0.5 (c - v); left adds heading psi' = -psi with along-track loss s' = v (1 - psi^2/2); right pins psi = 0.
Property: the rover is never faster than, nor ahead of, the point model; |psi| <= 0.35 (camera half field of view).
Concern: R. The clearance rows follow from monotone set points along the route (c_L <= c_R whenever s_L <= s_R) and s' <= v, and the heading row is any sublevel set of a contracting scalar loop (line 51-52: every value in [0, 0.6] certifies), so the rung carries little relational content. The header is honest about this (line 4-5, line 82 "no code exercised") and the rung exists to anchor the ladder; the dependence check (a 2x faster left speed loop declines, line 55-57) is good evidence. Domains and requirement constants are sourced.
Fix: none; acceptable as a ladder base.

## rover_terrain_2to4

Model: left 4-DOF rover with wheel loop w' = 3 (c_T - w), ground speed v' = mu_T (w - v) - r_T v - zs, sinkage zs' = 2 (Z_T - zs); right no-slip plan v' = 3 (c_T - v); zones MUD/GRAVEL/PAVED on s.
Property: the rover is never faster than, nor ahead of, the plan re-timed by up to 2.7 (the derived ratio (mu + r)/3 on pavement); slip velocity w - v in [0, 0.25] (traction-controller threshold), tight at 0.21 (the analytic launch bound re-checks: 1.47/7).
Concern: (a) The header reports that adding w[l] <= v[r] certifies the same clearance rows at lambda 1 (lines 81-84), i.e. a strictly stronger real-time claim exists, and the file "keeps the re-timed form deliberately" as an exhibit of S/M. Under the rubric the re-timed rows are then a loose form chosen for the mechanism letters. (b) Lines 69-75 justify the stretch by the rover "responding faster than the plan's 3 /s loop and reaching each set point earlier in its own time"; from matched starts (v = w at a zone entry) the cascade 3 /s then mu /s is slower than the plan's single 3 /s stage, so that sentence is false. What the stretch really buys is admissibility of starts with pre-existing slip (w_L > v_R), where v_L' = mu (w - v) can exceed 3 (c - v_R); the (mu + r)/3 ratio is exactly that bound. (c) P: the wheel floor w >= 0.15 (line 51-53, model line 115) is introduced so that v' > 0 at v = 0; "creep floor" is the justification, but it reads as a domain chosen for invariance.
Fix (header): rewrite lines 69-75 to state that the allowance covers starts where the wheel already leads the plan (slip up to sigma), not faster set-point tracking, and say in the mechanisms paragraph that the real-time form with the auxiliary row is the stronger claim. If the chain's exhibit of a stretched claim is wanted, keep the file; otherwise adopt the real-time form.

## sat3w_detumble_phases

Model: 60 kg microsatellite, J = diag(2, 4, 5), three axis-aligned wheels absorbing the body rates (h_i' = k J_i w_i); left the full gyrostat (Euler and wheel cross terms re-verified coefficient by coefficient), right the decoupled design model; DETUMBLE k = 0.5 on E <= 1, FINE k = 0.3 on E <= 0.125 (= J1 (0.25)^2), SAFE sink on the design model; flight decides every 2 s, design every 1 s.
Property: body energy E = w . J w equal on both sides at every instant through the phase handovers (exact; no tolerance).
Concern: the identity E' = -2 k E holds on both sides because the gyroscopic and wheel terms do no work, so the claim is physics-exact, and the cause dependence (removing one wheel term breaks it, line 65-66) shows it is not vacuous. The contrived part is the period split, a 2 s flight debounce against a 1 s design-model cycle (lines 30-38), which produces M and I; it is stated as the batch-I9 change (line 9-10). FINE is a lower-gain rate loop, not a pointing loop (no attitude states), which the header calls "fine pointing through the same actuators" (line 42); fine as an abstraction, but say so. The right-only momentum band (lines 96-101) is an initial-state restriction the left does not carry; disclosed.
Fix: none.

## turbine_startup_gearratio

Model: NREL 5-MW rotor speed w (rpm), first-order phases SPINUP 0.03 (9 - w), RAMP 0.04 (7.5 - w), GEN 0.05 (12.1 - w), STOP -0.1 w; left thresholds and loop targets scaled by 1.05 (stale 97:1 ratio against a 92.4:1 gearbox), free-spin 9 rpm and brake unchanged, gains unchanged.
Property: w_L <= 1.05 w_R in every mode (deployed never faster than 1.05 x a reference start-up; existential reference may run ahead); exactly 1.05 certifies, 1.049 and 1.06 decline.
Concerns: (a) P: lines 31-41 admit that a proportional loop on the measured error has gain 0.04/1.05 and 0.05/1.05 in true speed, that this variant declines on [0, 16] and certifies only on the reachable band, and that the switch is deferred. The file therefore ships a model the header says is wrong. (b) P: SPINUP and RAMP declare STOP (line 24, model lines 123/129/151/157) although both flows rise at 2 rpm (line 59-60); the edges are never taken and exist to be pruned. (c) R: the one-sided claim against an existential reference that may already be in GEN is close to a unary bound (w_L <= 12.705 in GEN follows from the left's own contraction); the header says so itself (lines 55-69) and lists the failed two-sided forms (lines 70-84). The honesty is exemplary; the relational content is modest.
Fix: switch to the scaled gains with the forward-invariant start-up band (left w <= 12.705, right w <= 12.1) as the header schedules, state the band as "a start-up begins below rated" (physical, not tuned), and either drop the STOP edges or add one clause that they are the parking logic's declared edges, unreachable at rated wind.

### G3

# Review G3 (independent, rubric RUBRIC.md; 10 benchmarks of benchmarks/suite_v2)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_spoof_limp | 3 | 4 | 4 | 3 | POLISH | LIMP guard v <= 30 (line 104) is load-bearing for row 1 and only thinly motivated; two "2026-10-29" dates |
| elevator_start_discbrake | 4 | 3 | 4 | 3 | KEEP | clean retrofit scenario; z,v rows are a copy of identical motion dynamics, content is the right-only lift (R) |
| gantry_speed_zones | 4 | 3 | 5 | 3 | KEEP | exact time reparametrization by construction (tightest 0.00); 10 mm justified by clearance margin; very honest header |
| lit_csf21_vehicle_bus | 3 | 4 | 5 | 3 | KEEP | source-faithful, departures listed; Coast stand-in (v <= 1, v' = 0) lets the car creep into the obstacle forever |
| lit_girard08_robot | 4 | 4 | 4 | 4 | KEEP | tight 0.16 bound, departures disclosed; line 67-68 "inside the enlarged invariant" holds at window starts only |
| platoon_profiles | 3 | 3 | 4 | 3 | POLISH | left AEB is start-only (SPORT->AEB unsat, line 87) so D rests on an unentered mode; unary gap rows; "2026-10-29" dates |
| rover_ladder_3to6 | 4 | 3 | 5 | 3 | KEEP | ladder rung with no mechanism; psi row is an identical-dynamics copy and the pitch row is left-only; s row is real |
| rover_terrain_4to6 | 3 | 4 | 4 | 3 | POLISH | "- zs" drag term (line 16, 77) subtracts wheel radii from m/s^2 with an unstated unit coefficient; rows otherwise tight |
| syringe_relay_prearm | 4 | 4 | 5 | 4 | KEEP | realistic relay (constants check out), tight b and C rows, retiming is the clinical content |
| ventilator_vc_cuffleak | 4 | 4 | 5 | 4 | KEEP | ISO-derived rows, leak ODEs verified; domain atom V - 0.4 t <= 0 (line 86) is an initial-condition invariant, not a limit |

## acc_spoof_limp
Model: one-state speed loop; left CRUISE reads a 25 % high speed (settles at 24 m/s) and may latch LIMP (set 22, gain 0.3); right is the unspoofed ACC with ECO/NORMAL/SPORT set speeds and a latched DISENGAGE below 20 m/s.
Property: the spoofed car is never faster than the reference (v_L <= v_R) and the reference traffic's closing speed stays absorbable (0.7 v_R <= v_L + 4, an AASHTO-derived chord).
Concern: the LIMP guard `v <= 30.0` (line 104, motivated at lines 31-32 only by "at or below the nominal set speed") is tuned to the claim: with LIMP admitted up to 40, from v_L = v_R = 38 LIMP decelerates at 4.8 m/s^2 while ECO decelerates at 5.5, so row 1 fails (crossover at 34.5 m/s); a plausibility monitor has no reason to stop latching above 30 m/s, and CRUISE admits starts up to 40 (line 99) from which a latch is a decision away. Also lines 51 and 81 cite a measurement dated 2026-10-29, after today.
Fix: either bound CRUISE to the same band (guard v <= 30, "ACC engaged at or below the nominal set speed", and say so for both modes) or keep LIMP wide and weaken row 1 above 30 m/s; correct the dates. Matrix/letters (M B I; M2 M3 M6) agree with lines 5-6.

## elevator_start_discbrake
Model: 20 m up-trip (z, v, brake lift b) with LIFT/UP/APP/STOP; the deployed brake lifts at k = 50 /s, the validated one at 5 /s; z, v dynamics identical and independent of b except through the UP guard b >= 0.95.
Property: positions and speeds equal in every mode (the validated profile up to re-timing of the lift), plus b_R <= b_L in LIFT (the reference has not started first).
Concern: the motion rows are a copy of identical dynamics (b does not enter z', v'), so the relational content is entirely the right-only lift and the LIFT ordering row; the header discloses this (lines 48-54). Minor: the brake drop rate in STOP is 5 /s on both sides (lines 109, 137) although the retrofit is a different brake; line 25 "the lift time is the only difference" should state the drop rate is assumed unchanged. Domains are physical (pit buffer, overhead, rated speed). Matrix M5 7/7 and RO path agree with R D.

## gantry_speed_zones
Model: two independent first-order axis servos toward (0.5, 0.3); the production program scales both gains by 3, 2, 1 by x-zone, the commissioned program runs at gain 1 everywhere.
Property: each axis within 10 mm of the commissioned path, up to a per-left-mode stretch in [1, 3].
Concern: a uniform gain scaling of an autonomous first-order loop is exactly a time reparametrization, so the claim holds by construction (header line 42: tightest tolerance 0.00) and the witness is the re-timed copy; the 10 mm comes from a stated clearance requirement (lines 36-38), the grid dependence of round A is disclosed (lines 10-13, 44-49). Acceptable as the S M exhibit; nothing to fix. Matrix M1/M2 cells (FREE 3/B=3, APPROACH 2/B=2) agree with lines 58-60.

## lit_csf21_vehicle_bus
Model: CSF'21 Fig. 11/12 car with thermostat on a shared bus; left attacked (thermostat free, 6 modes), right genuine (12 modes split by message type); d' = -v, v' in {1, 0, -1}, temp' = +-1.
Property: d and v equal in every left mode, i.e. owning the cabin-temperature reading cannot change the motion.
Concern: the stand-in for braking to rest, Coast at v <= 1 with v' = 0 (lines 38-39, 86-95), lets a car at 0 < v <= 1 creep forward indefinitely with d unbounded below (no d >= 0 anywhere); the source's plant stops at v = 0. It does not affect the relational verdict (both sides identical) but is a physics departure that the departures list should name as such, not only as "stand-in". The right's witness copies the left's action every cycle (line 47-50), which is the source's theorem, so acceptable. Letters X agree with line 5.

## lit_girard08_robot
Model: Girard et al. 2008 planar robot (6-D, in tracking-error coordinates e, z, w) vs its 2-D kinematic planner over a six-location hexagonal patrol at 0.2 m/s; planner edges and guards enlarged beyond Fig. 3 (departure 2).
Property: planner position equals the robot's controller reference w and e^2 + 100 z^2 <= 0.16, i.e. |y1 - y2| <= 0.4, the source's precision; tight (0.1599 declines, line 42).
Concern: departure (3)'s argument (lines 67-68) that the planner stays inside the enlarged invariant within a window is off by the robot's own 0.2 m overshoot of departure (6) (line 77): w may be 0.4 outside the Fig. 2 invariant at a window start and move 0.2 further, i.e. 0.2 outside the Fig. 3 strip. Since the planner's evolve domain is the whole plane (line 149 etc.) no verdict depends on it, but the sentence should say "at window starts". Departure (2) honestly states the certified abstraction is more permissive than the source. Relational part (w_L = y2_R) is a copy once the heading is chosen; the content is the unary simulation-function bound, as in the source. Letters X agree.

## platoon_profiles
Model: one CACC link (gap g, range rate r); left SPORT profile with gains scaled (kp x 1.44, kd x 1.2), right NORMAL; both with the same latched AEB; operating range 5 <= g + 2r <= 60, |r| <= 10.
Property: SPORT rows are the exact re-timing g_L(t) = g_R(1.2 t), r_L = 1.2 r_R at lambda 6/5, plus g_L >= 5 and g_L + 2 r_L >= 5; AEB rows exact at lambda 1.
Concern: (a) the left AEB mode is never entered from SPORT (line 87: "reachable only as a start", the SPORT guard is forward invariant and SPORT->AEB is unsat), so the D letter and the lambda-1 pairing rest on a mode no SPORT run reaches; (b) g_L + 2 r_L >= 5 (line 142) is the SPORT guard itself and g_L >= 5 is a left-only forward-invariant fact, so the requirement rows are unary; (c) lines 68 and 101 cite measurements dated 2026-10-29. Rows are exact by the gain construction (lines 65-67), as disclosed.
Fix: justify AEB starts physically (a cut-in at the window start) in the header or drop the left AEB mode and claim S M only; move the dates. Matrix (M1 SPORT 6/5, M2 B=2, M5 3/3) agrees with lines 6-9.

## rover_ladder_3to6
Model: UGV ladder rung L3 -> L6 over three odometer zones; the left adds pitch (settling to grade + 0.5 z), heave (pure decay) and roll (cross-slope + 0.015 v r), with slip/crabbing losses in s'; the right pins them at 0.
Property: v_L <= v_R, s_L <= s_R (clearance), psi_L = psi_R, |theta_p_L| <= 0.25 (tilt-stabilizer range; tightest 0.23, line 52).
Concern: psi' = -psi is identical on both sides (lines 99, 121) so the psi row is a copy; the pitch row depends only on left coordinates (theta_p, z) and is a unary invariant; the only relational content is s_L <= s_R (and v ordering across zones), which the header's evidence (lines 46-47) supports. Heave z' = -z (line 19) has no excitation, so the "heave kick" is only an initial-condition effect; acceptable for a rung. Mechanisms "none" is honest and matrix shows no code exercised. Keep as a composition rung.

## rover_terrain_4to6
Model: terrain rover MUD/GRAVEL/PAVED; right has an ideal wheel-speed loop (4 coords), left adds a lagged motor state u and a heave envelope zh excited by roughness x speed.
Property: never faster or ahead of the ideal-drive model; slip window v <= w <= v + 0.25 (tight 0.21); heave envelope zh <= 0.15 (tight 0.13); auxiliary ordering rows w_L <= w_R, zs_R <= zs_L, w_L <= u_L each needed (line 29).
Concern: the ground law v' = mu_T (w - v) - r_T v - zs (line 16, used at lines 77-111) subtracts a sinkage in wheel radii from an acceleration in m/s^2 with an implicit coefficient of 1 m/s^2 per radius that is nowhere stated; u is called a "torque state" (line 17) but has speed units. The guard entry conditions u <= c_T / w <= c_T (lines 42-45) are justified as unreachable from the ordered route. Slip and heave rows are unary but tight and requirement-backed.
Fix: state the sinkage-drag coefficient (e.g. "sinkage drag 1 m/s^2 per wheel radius") in the system paragraph and rename u a lagged speed command. Letters I and M6 "yes" agree with lines 6-7.

## syringe_relay_prearm
Model: two-channel syringe pump relay of noradrenaline (0.05 mL/min, 1 mm driver slack taken up at 0.09 mm/min = 11.1 min, plasma half-life 2.4 min); the deployed relay pre-arms channel 2 at 5 mL left, the validated one starts it from rest at the switchover.
Property: each syringe delivers the validated volume history up to re-timing; before syringe 2 delivers, equal plasma concentration and b_R <= b_L (tight, +0.01 declines, line 50); after, C_R <= C_L (tight, -0.01 declines, line 53): no added hypotension risk.
Concern: none of substance. The constants check (26.6 mm ID gives 0.09 mm/min; k = ln 2 / 2.4 = 0.29). TAKEUP2_L is reachable only from a late PREARM start (a 100 min pre-arm window against an 11.1 min take-up), which lines 82-84 acknowledge via the 49.4 mL variant. Matrix M5 13/13 and the RO path agree with R D.

## ventilator_vc_cuffleak
Model: one volume-controlled ARDS breath (lung volume V above PEEP, clock t): constant flow 0.4 L/s for 1 s, then passive expiration at PEEP; the deployed side adds a cuff leak of conductance 0.002 L/s/cmH2O at the trachea (both leak ODEs re-derived from the resistor network: 0.376 - 0.0495 V and -1.942 V - 0.0122 check out).
Property: INSP |V_L - V_R| <= 4 mL + 15 % V_R (ISO 80601-2-12 delivered-volume accuracy), EXP |V_L - V_R| <= 0.08 L (ISO PEEP accuracy x compliance); clocks equal.
Concern: the domain atom V - 0.4 t <= 0 (lines 86-87, 102-103) is a start condition plus invariant ("no more than delivered since breath start"), not a physical limit; it is what makes V <= 0.404 forward invariant. Line 61 states it, so it is disclosed, but it belongs with the start set rather than the physical range. Applying the tidal-volume accuracy to the running delivered volume (line 35) is a stated extrapolation of the standard. Tightness 0.104 vs 0.15 and 0.0647 vs 0.08 is justified by the standard. Letters D and M5 3/3 agree with lines 6-8.

### G4

# Review G4 (independent, read-only; rubric RUBRIC.md)

Benchmarks: acc_tune_lag, engine_start_highidle, grid_ffr_dos, lit_csf21_vehicle_thermo, lit_lz21_vehicle_position, quad_light_lag, rover_ladder_6to8, rover_terrain_6to12, tank_dos_3to1, watertank. Line numbers refer to `benchmarks/suite_v2/<name>/input.txt`.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_tune_lag | 3 | 3 | 4 | 3 | POLISH | lag tau = 0.32 s picked for rational roots (l.14-17); claim is a modal identity, the measured speed tolerance 3.34 m/s (l.35-37) is left out of the rows |
| engine_start_highidle | 3 | 3 | 4 | 3 | RETHINK | letter D rests entirely on the unreachable ABORT start (l.28-34, l.38-39); without ABORT the uniform +4 row certifies (l.31-32) |
| grid_ffr_dos | 4 | 4 | 4 | 4 | KEEP | realistic swing/FFR model; 0.24 a_R band is the FFR-loss margin, tight and justified (l.36-42); latch encoded as x - 2a (l.16-19) is the only device |
| lit_csf21_vehicle_thermo | 4 | 3 | 5 | 3 | KEEP | faithful source encoding with every departure listed (l.42-57); witness copies the attacked car's action, but that is the source's non-interference claim |
| lit_lz21_vehicle_position | 4 | 2 | 5 | 2 | RETHINK | the source's state bound x <= 10 is dropped (l.38-43) and the witness is a pure translation of the left; the certified claim holds for any offset (l.33) |
| quad_light_lag | 3 | 4 | 4 | 3 | POLISH | feedback term bypasses the motor lag (l.16-19) and K = g/2 chosen to land lambda on the grid (l.24-26); 0.8 m requirement sourced and tightness measured |
| rover_ladder_6to8 | 4 | 3 | 4 | 3 | KEEP | canonical rover rung; heading rows certify at any value (l.53-54) and the rollover row is implied by heading+roll (l.60-64); clearance rows carry the relational content |
| rover_terrain_6to12 | 3 | 3 | 4 | 3 | KEEP | grade pinned by guard+domain (l.67-70, l.103); requirements sourced and tightness measured (l.54-58); header number nit at l.65 |
| tank_dos_3to1 | 3 | 4 | 5 | 3 | KEEP | one-directional demand surge (l.13-14) makes h_L <= h_R exact; shortfall 0.8 from a submergence requirement, discriminates 30 s from 40 s holds (l.40-43) |
| watertank | 3 | 3 | 4 | 3 | KEEP | running example; deployed = nominal shifted by the offset and re-timed, so the tight row 3.00 is by construction (l.42-46); lambda range unpinned (l.81) |

## acc_tune_lag
Model: one car, speed v and realised acceleration a, cruise loop a_cmd = k(30 - v) through a 0.32 s powertrain lag; left gain 0.75 /s (retune), right 0.5 /s (stock), 0.1 s decision period.
Property: the retuned car's dominant-mode speed u = v + a/r_fast equals the stock car's at twice the elapsed time (exact, two rows, stretch 2).
Concern (P): tau = 0.32 s is chosen so that both closed loops have rational real roots (l.14-17), i.e. a constant tuned to the tool's arithmetic, not a measured powertrain lag; the modal-coordinate guards (l.80, l.88) are forward-invariant hulls, defensible as engaged envelopes but not a controller check.
Concern (R): the exact modal identity is a mathematical consequence of the two linear systems (dominant roots 1.25 = 2 x 0.625) and only the dominant mode is "twice as fast" (fast roots 1.875 vs 2.5); the operational tolerance |v_L - v_R| <= 3.34 m/s (l.35-37) is measured but not claimed.
Fix: add the measured row |v_L - v_R| <= 3.34 (l.35-37) to the claim so the property says something about speed; pin lambda_min = lambda_max = 2 (l.72-73) as the header l.34 says the factor 2 is the specification.

## engine_start_highidle
Model: core speed N2 through STARTER / LIGHTOFF / SELF / IDLE first-order phases (CFM56-class numbers), left idle 66 %, right 62 %; ABORT (N2 < 5) latched run-down.
Property: N2_L <= N2_R exactly below starter cut-out; N2_L <= N2_R + 4 above (the idle increment); mode-dependent rows.
Concern (P, R): ABORT is unreachable by any transition (both edges pruned, l.15-17) and exists only as an admissible start; the header states that the exact low rows are "forced by the ABORT start, not by the start physics" (l.28) and that without ABORT the uniform row N2_L <= N2_R + 4 certifies (l.31-32), so the letter D is an artefact of an unreachable mode, not of the controller change. The +4 row is the set-point difference and trivially inductive (d' = 0.15(4 - d) in SELF).
Minor (C): header time 0.8 s (l.67) vs matrix 522 ms / letters 0.4 s; measurement dates 2026-10-29 (l.19, l.31) are after today's date.
Fix: make the abort physical, a light-off time-out via a sequencer clock (the header l.18-19 reports it already certifies with R D I); then D rests on reachable behaviour. If the clock is not wanted, drop ABORT on both sides and report the file as R I with the uniform row.

## grid_ffr_dos
Model: island-grid swing equation x' = 6.25(0.1a - d) - 2.625x (H = 4 s, 5 % droop, damping 1), FFR battery ramps a with 0.2 s time constant once x <= -0.4 Hz, generator trip at -1.5 Hz on the right; left decisions held 0.3 s (DoS), right 0.1 s.
Property: attacked frequency never above nominal, never more than 0.24 a_R Hz below it, FFR never activated earlier, same incident d.
Concern: the latch is encoded as the guard x - 2a <= -0.4 (l.16-19, l.98), a modeling device whose coefficient 2 has no physical meaning (it only needs to make the guard flow-invariant); the left omits its trip relay (l.27-30), justified by invariance of x >= -1.5. The 0.24 band is tight for the certifier and equals the no-FFR support, so the claim does not distinguish a 0.3 s hold from total FFR loss (l.44-46); the header says so.
No fix needed; optionally state the latch coefficient as such in l.16.

## lit_csf21_vehicle_thermo
Model: Xiang/Fulton/Chong CSF'21 car (d' = -v, v' = a, temp' = thermo) with A = B = 1, eps = 1, modes action x thermostat; left thermostat reads an attacked temperature (free), right reads the true one.
Property: d_L = d_R and v_L = v_R in every left mode, the source's H-equivalence (the cabin-temperature attacker cannot move the car).
Concern (R): the witness is the genuine car hopping into the attacked car's action each window (l.59-62), a copy of the left; the content is that the action guards do not read temp, which is exactly the source's claim, and the leaky counterpart declines (l.75). Departure (1) narrows the universally quantified side (Brk only from v >= 1, l.43-50), stated.
No fix needed.

## lit_lz21_vehicle_position
Model: Liu/Zamani L-CSS'21 vehicle x' = v, v' = u with u in {-0.05, 0, 0.05} held 1 s, v in [0, 0.1]; left secret run, right partner.
Property: v_L = v_R and x_R = x_L + 1 (partner 1 m ahead copies the input forever).
Concern (R): the source's state set X = [0, 10] is dropped (l.38-43) precisely because the copying partner would block at 10; what remains is translation invariance of a double integrator, which the header concedes holds for any offset (l.33) and needs nothing of the dynamics. Of the source's two difficulties (stay in X, stay within delta) the first is removed and the second is trivial for a copying witness. Rubric: witness trivially copies the left.
Fix: restore x <= 10 on both sides (the source's X) and give the partner a non-copy policy at the top of the range (lead by up to 1 m, then hold at 10 while the secret run closes the gap), with rows x_L <= x_R <= x_L + 1; if the tool's Assumption 1 cannot admit a partner that stops at 10, say so in the header and keep the file as a documented literature row rather than a mechanism exhibit.

## quad_light_lag
Model: altitude h, climb rate w, net specific thrust a with motor lag a' = 10(a_cmd - a), w' = a - K w; left airframe 20 % lighter (a_cmd and K scaled by 1.25); stretch 6/5.
Property: |h_L(t) - h_R(1.2 t)| <= 0.8 m (PX4 NAV_MC_ALT_RAD) with a conserved steady-climb gap |Psi| <= 0.16 as strengthening rows.
Concern (P): the set-point part of the thrust command passes through the motor lag but the feedback part K w does not (l.16-19), an inconsistent plant (the header calls it a simplification, l.18-19); K = 4.905 = g/2 is chosen so that lambda = 6/5 lies on the stretch grid (l.24-26), while the PX4 default K = 4 /s is reported to certify at lambda = 1.24525 with the same letters (l.25-26).
Fix (POLISH): switch to K = 4.0 /s with lambda pinned at 1.24525 (l.77-78) so no constant is grid-tuned; carry the split-lag simplification as a one-line limitation, or (later round) route the whole command through the lag.

## rover_ladder_6to8
Model: canonical rover, 8-DOF left (yaw and pitch inertia) against 6-DOF right (omega_psi, omega_theta pinned) over STEEP / MODER / FLAT zones on the odometer, 1 s decisions.
Property: v_L <= v_R, s_L <= s_R against a re-timed reference (lambda 11/10 within a 1.25 timetable margin); heading, pitch, roll, LTR requirement rows on the left; plan-tolerance rows on the right.
Concern (R): the heading rows certify at any constant (l.53-54, the yaw loop has no disturbance input, l.146), and the rollover row is implied by the heading and roll rows (l.60-64), so of the eleven left rows the dynamics load only pitch (0.23 of 0.25) and roll (0.14 of 0.2); the deployed guards carry v <= c as a load-bearing start condition (l.108-114, l.147).
No fix needed; optional: drop the rollover row (implied) to keep the certificate to load-bearing rows.

## rover_terrain_6to12
Model: terrain rover, 6-DOF right (u, w, v, zs, zh, s) against 12-DOF left adding the ramp grade, chassis pitch, slope load, second-order heave, filtered acceleration and squat pitch; MUD / GRAVEL / PAVED zones.
Property: sloped compliant rover never faster or further than the flat model; slip window 0.25 m/s, heave <= 0.15, chassis pitch + squat <= 0.15 rad; derived auxiliary orderings.
Concern (P): the ramp grade is pinned by the MUD guard gamma >= 0.02 against the domain gamma <= 0.02 (l.67-70, l.103-104), a device for a constant input rather than a plant feature; theta_p's domain [0, 0.02] (l.63) is justified by the dynamics but reads as tuned.
Minor (C): l.65 says |v'| <= 5.6 on the boxes; PAVED with w = 0.8, v = 0 gives v' = 6.4 (still inside the ax domain 6.5, so not load-bearing); dates 2026-10-29 (l.16-19) are after today.
No fix needed beyond the l.65 number.

## tank_dos_3to1
Model: tank level h' = 0.005 n - 0.001 w h with a demand-paced four-stage pump station (n by demand band), demand surge w' = 0.02(22 - w) on both sides; left poll held 30 s (DoS), right 10 s.
Property: h_L <= h_R exactly and h_R <= h_L + 0.8 (outlet submergence margin), same demand.
Concern (P): the demand only rises (l.13-14), so a stale staging decision is always a lower stage; with a falling demand the exact row h_L <= h_R would fail, so the scenario is cut to the direction the claim needs (declared as a surge). The inductive envelope is about five times the simulated worst shortfall (l.48-50), stated.
No fix needed; the hold-length dependence (0.72 at 30 s, 0.84 at 40 s, l.40-43) is the kind of evidence other files should carry.

## watertank
Model: 1-dim tank level with proportional pump modes (Low / Mid / High, two Mid profiles on the right, PumpOff interlock), left thresholds and set points shifted by a 3 dm sensor offset with doubled Low gain and locked Mid profile.
Property: |x_L - x_R| <= 3 in every left mode (the true levels differ by at most the sensor offset).
Concern (R): the deployed controller is the nominal one shifted by exactly the offset and re-timed by the gain ratio, so the tight row (3.00, l.41-46) is neutral by construction; the second row is slack to 1.50 (l.46-47). The deployed side omits its own dry-run interlock (l.32-34). lambda_max = 6 (l.81) is unpinned while the header l.53-54 says only lambda = 2 matches, unlike the audited files.
Fix (optional, header/constant): pin lambda_max to 2 and say the second row keeps the symmetric band by choice; it is the paper's running example and stays.

Cross-cutting: several headers cite measurements dated 2026-10-29 (engine_start_highidle l.19, l.31; quad_light_lag l.26; rover_terrain_6to12 l.16, l.19), one day after today's date.

### G5

# Review G5 (independent, rubric RUBRIC.md): acc_tune_limp, flaps_slow_approach, h2_refuel_ambientbias, lit_drl_car_stop, lit_nahs25_salt_tank, quad_light_profiles, rover_ladder_8to12, sat_detumble_phases, train_ato_odometry, watertank_twospeed

Line numbers refer to benchmarks/suite_v2/<name>/input.txt. Mechanism cells were checked against docs/paper-numbers/matrix.md and letters.md; all ten agree with their headers.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_tune_limp | 2 | 3 | 4 | 2 | RETHINK | LIMP guard v <= 30 (l.27, l.85) is tuned to the claim: at v = 36 SPORT decelerates faster than the limp map, so v_L <= v_R fails if the fault may latch anywhere CRUISE runs; DISENGAGE v' = -0.5 v (l.18) is 10 m/s^2 at the floor |
| flaps_slow_approach | 4 | 4 | 4 | 4 | KEEP | hardware ratio 1/2 as the stretch, 20 kt from a stated requirement, 17.50 tight with a closed-form explanation; header is complete |
| h2_refuel_ambientbias | 3 | 3 | 4 | 3 | POLISH | ABORT (l.15, l.132-136) is never enterable (both flows rise at 0.5 MPa, pruned), yet the header cites an aborted reference as the reason the stage rows are exact (l.32-33) and uniform rows decline (l.44-45) |
| lit_drl_car_stop | 3 | 3 | 5 | 3 | KEEP | faithful sampled dRL refinement; the witness is the identity by the source's definition, so the content is the guard implication (Goal 1) only, as the header says |
| lit_nahs25_salt_tank | 4 | 4 | 5 | 4 | KEEP | source's forward distance 3, tight (2.99 declines), direction and slack row stated; deviations listed |
| quad_light_profiles | 3 | 3 | 4 | 3 | POLISH | K = g/2 (l.31) chosen for a round stretch; rows 1-2 have no tightness evidence (l.60 gives Psi = 0.016 m from hover; Psi is conserved, so 0.8 m is a start-set size, not a bound the dynamics produce); ECO/SPORT exist only to earn B, X (l.69-70) |
| rover_ladder_8to12 | 4 | 4 | 4 | 4 | KEEP | consistent 12-DOF rung, requirement constants sourced, tightest values measured, composition argument stated; runtime 31 s of a 40 s budget (l.126) is the only fragility |
| sat_detumble_phases | 2 | 4 | 5 | 2 | RETHINK | the x, y actuators are rate dampers of wheel authority (l.21-27) because the claim is false for a real magnetorquer + wheel suite; the header says so, so the plant is chosen to make the identity hold |
| train_ato_odometry | 4 | 4 | 4 | 4 | KEEP | real miscalibration (806/840), ETCS dV_warning 1.11 as the requirement, tight 1.07 with the model bound 1.042 explained, domains from ETCS EBI |
| watertank_twospeed | 3 | 4 | 4 | 3 | KEEP | running-example variant, consistent offsets, upper 3 exactly tight and lower 2 justified (1.50 tight); PumpOff (l.150-154) is an unreachable sink, which is the P letter's whole content |

## acc_tune_limp
Model: one speed coordinate; left = aftermarket ACC tune (CRUISE v' = 0.75(30 - v), fault-latched LIMP v' = 0.3(25 - v)); right = stock ACC with driver-selectable NORMAL/COMFORT/SPORT gains and a DISENGAGE below 20 m/s.
Property: in CRUISE the tuned speed equals the stock NORMAL speed at stretch 3/2 (exact); in LIMP the tuned car is never faster than the stock car (v_L <= v_R).
Concern (P): the LIMP guard v in [20, 30] (l.27-28, l.85) is justified as "the fault latches while the ACC is engaged at or below the set speed"; a drivetrain fault is not conditioned on speed. The bound is load-bearing: with v_L = v_R = 36 (inside CRUISE's guard, l.80) SPORT decelerates at 0.6 x 6 = 3.6 m/s^2 and the limp map at 0.3 x 11 = 3.3 m/s^2, so v_L > v_R after the handoff and the LIMP row fails; the guard excludes exactly the starts where the claim is false. Secondary: DISENGAGE v' = -0.5 v (l.18, l.107) is a 10 m/s^2 deceleration at the 20 m/s floor (harder than emergency braking) for a "hand back to the driver"; it is pruned, so it does not affect the verdict, but it is an ad hoc constant.
Concern (R): the CRUISE exact row holds by construction (0.75 = 1.5 x 0.5, same set point: the tuned loop is the stock loop re-timed), so the row is an identity of first-order linear systems; the non-trivial content is the LIMP row and the X/D interplay.
Fix: widen the LIMP guard to CRUISE's range [20, 36] and give LIMP a measured tolerance (v_L <= v_R + c, c from bisection; the handoff from v_L = v_R then starts with a lead the SPORT pairing creates), or model the limp map as torque limiting (no active deceleration above the set point: v' = min(0, ...) is not expressible, so v' = -0.02 v above 25 would need a fourth left mode). Replace the DISENGAGE field by a coast (v' = -0.3, or -0.02 v). Re-measure D and X after the change.

## flaps_slow_approach
Model: flap angle f and airspeed V on approach, CONF 1+F to CONF 2; left flaps at 0.5 deg/s (one hydraulic system lost), right at 1 deg/s; the autothrust decelerates toward F = 150 kt with flap-dependent drag on both.
Property: at equal flap angle (stretch 1/2 while the flaps move, 1 once set) the FLAPS SLOW aircraft is never faster and at most 20 kt slower than the normal extension.
Concern: none of substance. The flap rows are exact by construction at the stretch (0.5 deg/s is the re-timed 1 deg/s), so the content is the speed row, whose 17.50 = (1 - 1/2)(S - F) is explained in closed form (l.39-41) and whose requirement (l.33-36) is sourced. Nits: the header's "about 0.6 s" (l.89) against matrix 325 ms; the flap rate 1 deg/s is "assumed" (l.21), which is stated.

## h2_refuel_ambientbias
Model: tank pressure p under a staged exponential pressure ramp (gain 0.05 /s, stages toward 20/40/60 MPa, top-off toward end + 0.5), COMPLETE and ABORT frozen; left end pressure 72.4 MPa (ambient sensor 10 K high), right 70.0.
Property: in the ramp stages the biased fill never leads (p_L <= p_R, exact); in TOPOFF/COMPLETE/ABORT it leads by at most 2.9 MPa (2.4 bias shift + 0.5 certificate slack).
Concern (P, R): ABORT (l.15-16, l.132-136, l.172-176) is declared from STAGE1 and STAGE2 only, with guard p < 0.5 while both flows rise at p = 0.5, so it is never entered (the header prunes it, l.63-64). The header nevertheless uses an aborted reference as the reason the stage rows are exact (l.32-33: "a reference already aborted below 0.5 MPa becomes an admissible start") and as the reason the uniform row declines (l.44). A frozen ABORT is also not a leak (pressure would fall). The staged exponential ramp is a design value, not J2601's APRR, and is disclosed (l.22-23). The 0.5 MPa of the 2.9 is a certificate artifact (the top-off's exit cannot be used), disclosed (l.47-51).
Concern (C): the header carries measurement dates of 2026-10-29 (l.39, l.73, l.75, l.77), after today's date.
Fix: drop ABORT (or make it a leak mode p' = -0.1 p reachable from every stage) and re-measure; the stage boundary already forces the stage rows exact (a 0.01 lead grows when the leading tank enters the next stage first), so restate l.32-33 and l.44-45 with that reason and confirm D still holds. Fix the dates.

## lit_drl_car_stop
Model: x, v car with a = +1 / 0 / -1; left Accel guarded by the time-triggered Safe_eps, right by the event condition Safe; identical plants, both sampled at 1 s.
Property: the conservative controller refines the permissive one: identical x and v at every window (dRL refinement at the identity relation).
Concern (R): the witness copies the left's action at every window (l.57-59); the certified content reduces to Safe_eps implies Safe over identical plants, which the header states (l.35-38). Faithful to the source as sampled, with every deviation listed (l.31-53).
Nit (C): the Accel guards carry v <= 9.0 (l.86, l.104), a cap keeping one period of acceleration inside the domain; it is not in the deviations list (l.43-53, which mention only the top speed 10). One clause would close it. KEEP.

## lit_nahs25_salt_tank
Model: salt mass xp in a 100 gal brine tank; On xp' = 0.1(25 - xp), Off xp' = 0; left thresholds widened by the attack magnitude 3 (On at xp >= 22, Off at xp < 28), right genuine (On iff xp >= 25).
Property: the attacked and genuine tanks stay within 3 lb of salt of each other and both above 25.
Concern: none of substance. The upper row is tight at the paper's distance (l.29-30), the slack row is stated (l.31-32), the rows xp >= 25 restrict the claim to the source's invariant region, which makes the genuine Off never admissible (l.60); that mirrors the source's proof invariant (l.17). The missing evolve domain (l.36-38, l.78) is a deliberate match to the source. KEEP.

## quad_light_profiles
Model: altitude h and climb rate w under a P velocity loop; left airframe 20 % lighter than the reference's model (w' = 14.715 - 6.13125 w); right NORMAL/ECO/SPORT set points 2.0/1.6/2.4 m/s, selectable at every 1 s cycle.
Property: the light airframe's altitude is within 0.8 m (PX4 NAV_MC_ALT_RAD) of the NORMAL reference's altitude at time 1.2 t, plus two strengthening rows (conserved gap Psi <= 0.8, 1.2 w_R <= w_L).
Concern (P): K = 4.905 = g/2 (l.31) is picked so the terminal rates are 2.0/2.4 and the stretch is exactly 6/5; PX4's default 4.0 is mentioned as also certifying at 1.24525 (l.32-33), so the round value is cosmetic but still an ad hoc constant.
Concern (R): no tightness evidence for rows 1-2. Psi is conserved at the stretch (l.53-54) and from hover Psi = 0.016 m (l.60); the invariant Psi <= 0.8 therefore holds for any constant at or above the start set's Psi, so 0.8 m measures the admitted start set, not a gap the dynamics produce. ECO and SPORT are never run by the witness and removing them keeps the file certifying with S M (l.69-70): B and X are carried by right modes that exist only to earn them.
Concern (C): dates of 2026-10-29 (l.33, l.70, l.90).
Fix: state the tightest certifying constant for rows 1-2 over the declared domain (or state that rows 1-2 are implied by row 3 from any start with |Psi| <= 0.8 and that 0.8 is the requirement's radius, not a measured bound); either use PX4's K = 4.0 with lambda = 1.24525 or justify g/2; fix the dates.

## rover_ladder_8to12
Model: 12-DOF rover (speed, odometer, heading/pitch/heave/roll with their rates, tire slip and its rate) over three zones; right = the 8-DOF rung with heave/roll rates and slip pinned at 0.
Property: the 12-DOF rover is never ahead of the re-timed 8-DOF reference (v_L <= v_R, s_L <= s_R), with heading, roll, LTR and lane requirements on the left and the previous rung's plan tolerances on the right.
Concern: the left guards carry v <= c (l.152, l.158, l.164; discussed l.110-116) as a start condition on the deployed side only; it is load-bearing (without it DECLINED) and excludes a rover entering STEEP faster than 3 m/s. The header argues every reachable state satisfies it along the route; a reviewer should note that a start above the set point is a real scenario the file excludes. Runtime 31 s of the 40 s budget (l.126-128) and 280 s needed for the tightness runs (l.136) make the benchmark fragile under a slower machine. Mechanism cells (S M I; M1 M2 M6) agree. KEEP.

## sat_detumble_phases
Model: gyrostat Euler equations (J = diag(2,4,5), z-wheel momentum h) with isotropic rate damping on all three axes, DETUMBLE k = 0.5 and FINE k = 0.3, flight period 2 s; right = the design model with the couplings dropped, period 1 s, plus a SAFE sink.
Property: the full body's energy E = 2 w1^2 + 4 w2^2 + 5 w3^2 equals the design model's at every instant through the phase handovers (exact both ways).
Concern (P): the header states (l.21-27) that with magnetorquer-scale x, y gains and a wheel on z the claim is false (E_L - E_R = +0.067 at 2 s), so the x, y actuators are "modeled as rate dampers of the same authority as the wheel". The plant is therefore chosen so the identity holds, not the plant of a microsatellite with the stated actuator suite; the time unit is stylized by three orders of magnitude (l.28-31). SAFE (l.152-156) is a mode never entered (pruned, l.95-97). The 2 s period (l.44-47) is a "design value of this file" that produces M.
Concern (R): none: exact, non-trivial (needs the cubic cancellation), cause-dependent (l.79-81).
Fix: give the satellite three reaction wheels (states h1, h2, h3, h_i' = k J_i w_i, body couplings -(w x h)); the wheel torques are internal, so E' = -2 k E still holds exactly, the damping can take a real wheel gain (the file already certifies at k/1000, l.31-34), and the actuator suite matches a microsat ADCS. Dimension 6; re-measure M I X. Drop SAFE or make it enterable.

## train_ato_odometry
Model: one speed coordinate under the ATO's first-order loop in three performance levels (k = 0.05/0.045/0.04 /s) toward 25 m/s; left reads 0.96 of the true speed (wheel-diameter parameter 806 mm against new 840 mm wheels).
Property: the miscalibrated train is never slower than, and never more than 1.11 m/s (ETCS dV_warning) faster than, the calibrated design run re-timed per pairing in [0.75, 1.25].
Concern: the S letter depends on the chosen tolerance lying in [1.07, 1.13) (l.53-54): at 1.13 the real-time claim certifies by a choice hop. Since 1.11 is the ETCS value, this is legitimate, but the window is narrow and should be read as such. Domains come from the ETCS EBI margin (l.65-69) and widen without harm (l.72-74). Mechanism cells (S M B; M1 M2 M3) agree. KEEP.

## watertank_twospeed
Model: one tank level under proportional pump modes; right nominal with a two-speed low fill (Fast gain 2 below 7 dm, Slow gain 1 to 10 dm), two mid profiles, High and a PumpOff interlock; left = the running example's attacked controller (thresholds and set points 3 dm higher, full speed forced).
Property: the attacked level is at most 3 dm above and at most 2 dm below the nominal level, in every mode.
Concern (P): PumpOff (l.18, l.150-154) is unreachable (Fast rises from 2; pruned, l.69-73); it exists only to carry the P letter, which the header calls the running example's dead edge. lambda_max = 6.0 (l.91) while no cover exceeds 2 (l.82-84): an unused range (h2_refuel pinned its own). The gain 2.0 /min toward 15.5 dm for a 2.5 m tank is a toy rate but consistent on both sides.
Concern (R): none: upper 3 is exactly tight both ways (l.50-52), lower 2 is justified by the interlock margin with 1.50 measured (l.52-54), cause dependence tabulated (l.55-59).
Nit (C): l.8-11 is change history, not a claim statement. KEEP (pin lambda_max to 2 if a polish pass is made).
