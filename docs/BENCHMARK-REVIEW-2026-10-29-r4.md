# Benchmark review, round 4 (2026-10-29; suite_v2 at 50ab23f, branch benchmark-fixes tip af37eb3, 50 benchmarks)

Five fresh reviewer agents, 10 benchmarks each in alphabetical order (G1 `acc_spoof_lag` .. `flaps_slow_approach`, G2 `fuelcell_chp_dos` .. `lit_drl_car_stop`, G3 `lit_drl_lane_control` .. `quad_light_profiles`, G4 `reactor_feed_wireless` .. `sat3w_detumble_phases`, G5 `sat_detumble_phases` .. `zone_lightmass_schedule`). Each saw only `docs/review-rubric.md`, its ten `input.txt` files, `docs/paper-numbers/matrix.md` and `docs/paper-numbers/letters.md`; no earlier review, score, overnight report or fix list. Nothing in the suite was changed this round.

Verification column: every RETHINK, every overall 2, and every claim that a file certifies only through a domain/model artifact or that a header number is wrong was checked once where a single edit tests it. `CONFIRMED (run)` = `./.lake/build/bin/relcert` with `RELCERT_IMPLIED_CUT=1` (plus the ablation variable named) on a scratch copy in `tmp/verify-r4/` (file name in parentheses); `(arith)` / `(inspection)` = checked by hand against the file; `UNCHECKED` = not run (reason given). No tested claim was refuted.

## Ranked table (worst first)

| benchmark | P | R | C | overall | verdict | one-line reason | r3 overall | verification |
|---|---|---|---|---|---|---|---|---|
| `acc_tune_lag` | 2 | 3 | 2 | 2 | RETHINK | tau = 0.32 is the unique lag that makes the claim realisable (l.14-18), and the a-box is load-bearing (l.67-69). The left guard l.96 reaches abs(a) = 28.75 at its far corners, so l.72 "envelope's own acceleration range is well inside it" is false. | 3 | CONFIRMED (run): a box widened to +-30 DECLINED (atl_a30); arith: left guard corner (v, a) = (8.6, 28.75), so l.72 'well inside' is false |
| `charger_fast_tapers` | 2 | 2 | 3 | 2 | RETHINK | c = 2 is a tool artifact by the header's own account (l.52-57, 69-81), and the physical lead is 0. FAULT (x < 10) cannot be entered from PRECHARGE or BULK, so P rests on pruning dead edges. l.12 attributes P to "the raised limit", which contradicts l.85-89. | 2 | CONFIRMED (run): FAULT removed from the four next lists, RELCERT_NO_PRUNE=1 CERTIFIED (chg_nofault), so P rests on dead edges |
| `engine_start_highidle` | 2 | 3 | 4 | 2 | RETHINK | ABORT is reached only from STARTER starts whose timer is already near 30 s (l.17-18). A sequence started at t = 0 reaches 25 % N2 by 16.1 s. The D letter and the low-row tightness (l.31-33, 37) rest on those starts. | 4 | CONFIRMED (run): ABORT and t < 30 removed, uniform n_L <= n_R + 4 in every mode CERTIFIED (eng_noabort), so D and the STARTER/LIGHTOFF rows rest on ABORT |
| `grid_ffr_dos` | 3 | 2 | 4 | 2 | RETHINK | The 0.24 a_R band is the whole FFR contribution (0.625/2.625 = 0.238). It certifies for a 1 s hold and for an FFR that never fires (l.44-46), so the claim does not depend on the attack. Instantaneous droop (l.9) removes the nadir that FFR exists for. | 3 | CONFIRMED (run): left FFR a' = 0 (FFR never fires) CERTIFIED at 0.24 (grid_noffr); left epsilon 3.0 UNCHECKED (run exceeded 600 s) |
| `platoon_profiles` | 4 | 2 | 4 | 2 | RETHINK | SPORT gains are an exact bandwidth scaling (kp x1.44, kd x1.2), so the rows are an identity with no tolerance content (any slack C certifies, l.69-75); D start-only (l.10-11) | 3 | CONFIRMED (run): SPORT forms +-5 slack plus right TTC floor CERTIFIED (pp_slack5f); without the floor DECLINED (pp_slack5), as the header says |
| `quad_light_lag` | 2 | 4 | 3 | 2 | RETHINK | Motor lag acts only on the set-point part of the thrust, feedback K w is lag-free (l.16-19): not a physical plant; Psi constant 0.16 derived from removed envelopes (l.50-52) | 3 | CONFIRMED (inspection + run): l.101/109 lag only on the set point (w' = a - K w); Psi constant 0.45 CERTIFIED, 0.46 DECLINED (ql_psi45/46), so the stated 0.16 is far from tight |
| `rover_ladder_2to3` | 3 | 2 | 4 | 2 | RETHINK | Clearance is pure monotonicity (s_L' = v(1-psi^2/2) <= v_L <= v_R, l.99 vs l.121); the heading row is a start restriction ("every value in [0, 0.6] certifies", l.51-52); no mechanism | 3 | CONFIRMED (run): heading bound 0.35 -> 100 CERTIFIED (l23_psi100), the heading row is not load-bearing |
| `rover_patrol_lag` | 3 | 2 | 4 | 2 | RETHINK | Header's own twin test (l.7-10, 85-91): S M R B come from the 1 m slack, not the lag. Claim is one-sided against a plan re-timed 1.5x and moved alone; the tight 0.75 is set by the a >= -2 box (l.50-52) | 3 | UNCHECKED (header's own no-lag twin test, l.7-11, l.85; not re-run) |
| `rover_terrain_2to4` | 4 | 2 | 4 | 2 | RETHINK | Keeps a weaker claim on purpose: the plan's clock may run 2.7x faster when a real-time form certifies at lambda 1 (l.101-105); S/M come only from slip-ahead pairs the rows admit (l.87-92) | 2 | CONFIRMED (run): w_L <= v_R added, lambda_max 1.0 CERTIFIED (t24_rt) |
| `turbine_startup_gearratio` | 3 | 2 | 3 | 2 | RETHINK | One-sided w_L <= 1.05 w_R against a reference that may run ahead. R, P and I appear even at g = 1 (l.85-89), and a weaker factor (1.06) DECLINES (l.67-68). The STOP edges are dead, and the real hazard (left trip at 13.9755 > 13.31) is admitted by the claim | 2 | CONFIRMED (run): base CERTIFIED, factor 1.05 -> 1.06 (weaker claim) DECLINED (turb_106): non-monotone |
| `lit_drl_lane_control` | 3 | 2 | 4 | 2 | POLISH | Right = left with weaker accel guard (l.115 vs l.82), same flows; claim reduces to Safe_eps => Safe (dRL Goal 1 only, l.43-44); a strict-superset 9-mode leader variant DECLINES "cause not identified" (l.32-34), which is a red flag | 3 | CONFIRMED (inspection): left/right flows identical (l.81 vs l.114), guards differ only by the Safe_eps margin; 9-mode decline is the header's own statement (not re-run) |
| `lit_lz21_vehicle_position` | 3 | 2 | 5 | 2 | KEEP | Pure translation invariance with an input copy (any offset certifies, l.31-34); x <= 10 dropped for the witness (l.38-51); honest, but no relational content beyond X | 2 | CONFIRMED (run): offset 1.0 -> 5.0 in all rows CERTIFIED (lz21_off5) |
| `acc_spoof_lag` | 3 | 3 | 3 | 3 | POLISH | The modal identity is right (roots 1, 5/3 vs 2/3, 2; ratio 3/2), but row 1 (re-timed overspeed, l.31) is not a requirement anyone states. tau = 0.375 was picked so the roots come out rational. The left guard l.103 is a modal parallelogram with corners (6.5, 25.5) and (46.5, -25.5) that only the domain clips. | 3 | - |
| `acc_spoof_limp` | 4 | 4 | 3 | 3 | POLISH | The physics and the AASHTO-derived row 2 check out (l.58-61). But the LIMP ceiling of 36 m/s (l.121) contradicts "fault not conditioned on speed" (l.35), and the existential reference driver is what produces X. | 4 | UNCHECKED |
| `acc_tune_limp` | 4 | 3 | 4 | 3 | POLISH | The CRUISE identity holds by construction (0.75 = 1.5 x 0.5, l.36-38), and D exists only because the stated CRUISE row is stronger. The LIMP crossovers 35 and 37.5 check out. l.65 "leads by at most 7.00" is a certificate bound; the true sup is about 5.6. | 3 | - |
| `bottling_fill_strainer` | 4 | 3 | 3 | 3 | POLISH | The physics checks out (Psi conserved, 8 vs 6.8 mL in flight). But requirement row (5), V_R - V_L <= 2, follows algebraically from rows (1)-(3), so "tightest 1.20 (1.19 declines)" (l.36) measures the hard-coded -1.2 offset, not the dynamics. | 4 | CONFIRMED (run): row (5) R_V <= L_V + 2 deleted, CERTIFIED (bot_norow5) |
| `elevator_start_discbrake` | 3 | 3 | 3 | 3 | POLISH | The brake never feeds back into z or v, so the conformance holds by construction apart from the lift delay. l.17 "rest at about 19.96 m" is wrong: the car arrives at about 0.5 m/s (l.68), so it rests near 20.03 m. | 3 | UNCHECKED (rest position 20.03 vs 19.96 is a simulation claim) |
| `flaps_slow_approach` | 4 | 3 | 3 | 3 | POLISH | The gap ODE (l.35) is correct, and its tolerance is exactly (Vmax - F)/2 with Vmax = 200 taken from the guards (l.127, 141). So l.84 "not load-bearing" holds only because the guards repeat V <= 200, and the stated 25 kt exceeds the 20 kt requirement the header itself cites (l.40-46). | 4 | CONFIRMED (run): V <= 200 -> 214 in guards and evolves DECLINED at 25 (flaps_214): the bound is set by the copied V limits |
| `fuelcell_chp_dos` | 3 | 3 | 3 | 3 | POLISH | Physics checks out (4.30 K / 5.83 K hold drift, pruning flows at 60/70 degC). But the true gap is 0 (l.31-37), the 7 K is window-derived and the certified window is non-monotone [5,8] then 10 (l.53-56). The 111-line header buries this. | 3 | CONFIRMED (run): 9.0 DECLINED, 10.0 CERTIFIED (fc_9/fc_10): non-monotone window, as disclosed |
| `furnace_program_timebase` | 3 | 4 | 4 | 3 | POLISH | The stretch arithmetic is right: residual (1-0.8) x 32 = 6.40 and lag window E >= 30 from 0.01(630-E) <= 0.2E (l.41-43). But 8 degC is AMS 2750 *uniformity*, a spatial class reused as a run-to-run tolerance (l.29-31), and SOAK has no dwell (l.15). | 4 | - |
| `gantry_speed_zones` | 3 | 3 | 3 | 3 | POLISH | Uniform gain scaling makes the claim an exact time reparametrization. The tightest is 0.00 at lambda_max 3 (l.42) and an arbitrary zone schedule certifies (l.54-57), so the zones carry no weight. History lines 8-13 are noise. | 3 | - |
| `h2_refuel_ambientbias` | 3 | 3 | 2 | 3 | POLISH | 72.43 MPa and the stage times (~45/48/48/64 s) check. But the exact stage rows and D come from the start-only ABORT mode (l.33-38, 49-52). l.51-52 "letters R I" without ABORT conflicts with the letters.md D rule. | 3 | CONFIRMED (run): ABORT removed: CERTIFIED; uniform 2.9 CERTIFIED (drops the stated stage rows), uniform p_L <= p_R DECLINED, so by the D_rows rule D stays and the header's 'letters R I' (l.52) conflicts with the rule (letters script not re-run) |
| `hydro_rejection_gatecal` | 3 | 4 | 3 | 3 | POLISH | The keyed rows are well motivated and the peak 0.2055 reproduces from settled on-grid gates. A start at g = 1 near t = 20 peaks at 0.223, so the margin is 0.077, not 0.0945 (l.34-36). Torque g-0.1 (l.101) contradicts P = (g-0.1)/0.9 (l.33). | 4 | CONFIRMED (run): speed band 0.09 -> 0.07 CERTIFIED (hydro_007): 0.09 is not tight; torque/power mismatch UNCHECKED |
| `lit_csf21_vehicle_bus` | 4 | 3 | 4 | 3 | POLISH | Faithful encoding of CSF'21 Sec. VI-C with deviations listed. Same claim and only X as in vehicle_thermo; the six *T right modes are never used (l.50). "batch I8" (l.53) is internal jargon. | 3 | - |
| `quad_light_profiles` | 3 | 3 | 4 | 3 | POLISH | Psi conserved at 6/5 (checked, hover Psi = 0.0163); B and X come only from ECO/SPORT starts the cover leaves at once (l.84-89); row 1 certifies at 0.00 (l.74-75) | 3 | CONFIRMED (run): w_L <= 2.4 dropped DECLINED (qp_nowl): a load-bearing start restriction |
| `reactor_feed_wireless` | 3 | 3 | 4 | 3 | POLISH | 8.00 tight is right (2 levels x 4 K), but the 9 K "boil / accumulate" justification (l.31-39) is vacuous: the domain T in [15,60] (l.86-88) already excludes both, so the left alone meets it | 3 | CONFIRMED (run): 9 K band replaced by unary 10 <= T_L <= 60 CERTIFIED (reac_unary) |
| `rover_ladder_3to6` | 3 | 3 | 4 | 3 | POLISH | Pitch row tight and model-reading (0.15+0.5x0.15=0.225, l.52-53), but unary; header l.81-83 calls roll a requirement the next rung relies on, yet no roll row here | 4 | - |
| `rover_ladder_6to8` | 3 | 3 | 3 | 3 | POLISH | S/I come from the right plan-tolerance rows (header l.5-9 says so); the LTR row is implied (0.771 < 0.8, l.62-63); composed 1.21 rests on the cover, not on lambda_max = 1.25 (l.146) | 4 | UNCHECKED (lambda_max 1.25 vs cover 1.1 is a header claim) |
| `rover_ladder_8to12` | 3 | 3 | 3 | 3 | POLISH | The rung adds heave inertia (z' = omega_z - z, l.161) but drops the left pitch rows; "heave row" in l.110-114 does not exist; same lambda_max composition gap (l.153) | 4 | UNCHECKED |
| `rover_terrain_4to6` | 3 | 3 | 3 | 3 | POLISH | Ordering rows are sound and real-time; but w,u in [0.15,0.8] (l.81) contradicts the "exactly 2to4's left" composition claim (l.15, 51), since 2to4 now has w in [0,0.8] | 3 | CONFIRMED (run): w, u floors 0.15 -> 0 CERTIFIED (t46_floor0): floors not needed, composition with 2to4 restorable |
| `rover_terrain_6to12` | 3 | 3 | 3 | 3 | POLISH | Tight values check out (sigma 0.24, H 0.13, Theta 0.13), but 4 of 6 new coordinates are output-only filters (vz, ax, phs, omega_phs), and "/v'/<= 5.6" (l.65) is wrong: 8 x 0.8 = 6.4 | 4 | CONFIRMED (run + arith): Theta/ax/omega_phs rows deleted CERTIFIED (t612_noout); PAVED v' = 8 x 0.8 = 6.4 > header's 5.6 (l.65) |
| `sat3w_detumble_phases` | 3 | 4 | 4 | 3 | POLISH | Gyrostat equations and E' = -2kE check out exactly; the stated gains are ~100x real authority (l.60-63), and the header says the 1/1000-gain variant certifies the same, so use it | 4 | - |
| `sat_detumble_weak` | 3 | 3 | 3 | 3 | POLISH | The RK4 example at l.62 starts at w = (0.5, 0.3, 0.2), where E = 1.06 > 1, outside the DETUMBLE guard on l.133. Its B letter comes only from the ECONOMY/SURVIVAL successors (l.143), which are answered by a hop back to NOMINAL. Exact only at the pinned 0.8 | 3 | CONFIRMED (arith): E(0.5, 0.3, 0.2) = 1.06 > 1 = DETUMBLE guard (l.133), RK4 example start outside the guard |
| `ventilator_vc_cuffleak` | 4 | 3 | 3 | 3 | POLISH | Resistor-network derivation checks (0.376238 - 0.049505 V; -1.9419 V - 0.0122; 32.9 mL loss). The EXP tight value 0.0647 comes from the V <= 0.404 / V - 0.4t <= 0 reachable-set domain, not from PEEP accuracy. Header gives the tight fraction as 0.104 (l.37) and 0.105 (l.56) | 4 | CONFIRMED (run): 0.104 CERTIFIED, 0.103 DECLINED (vent_0104/0103): l.37 right, l.56 '0.105 at 500' stale; domain claim UNCHECKED |
| `watertank` | 3 | 3 | 3 | 3 | POLISH | The deployed model omits its own dry-run interlock (l.32-34: "no dry-run mode"), though only the sensor and pump are attacked. lambda in [1, 6] (l.80-81) is not justified. The requirement (l.37-40) reads as real time, but the claim is re-timed by 2 | 3 | CONFIRMED (run): lambda_max 6 -> 2 CERTIFIED (wt_l2); interlock claim UNCHECKED |
| `watertank_twospeed` | 3 | 3 | 4 | 3 | POLISH | The lower-row "underflow margin" justification is vacuous: x_R <= x_L + 2 with x_R >= 2 gives x_L >= 0, which is already the domain floor. Tight is 1.5 (l.52-54). P rests on a dead Fast->PumpOff edge, and the same missing left interlock as watertank | 3 | CONFIRMED (run): lower row 2 -> 1.5 CERTIFIED (wt2_15); interlock claim UNCHECKED |
| `zone_lightmass_schedule` | 3 | 3 | 4 | 3 | POLISH | 0.5 K certifies only because the range is 5..30 (tight 0.4848 = 0.00125 x 16 / 0.04125); header l.62-65 admits that 4 degC or 33 degC declines. Upper 30 degC is low for a lightweight zone's summer air. B is degenerate (l.95-97) | 3 | CONFIRMED (run): T <= 30 -> 33 DECLINED at 0.5 (zone_33), as disclosed |
| `insulin_basal_cgmloss` | 3 | 3 | 4 | 3 | KEEP | Rate and band arithmetic verified (27.9, 17.9, 55.8, 35.8; equilibria 125/L2 and 155/L3). The tolerance is a chain-depth artifact (20 vs simulated 1.4 mg/dL), and the header says so. | 4 | - |
| `lit_csf21_vehicle_thermo` | 4 | 3 | 5 | 3 | KEEP | psi = v^2+4v+2 at A=B=eps=1 checks, and the deviations (1)-(3) are explicit. The non-interference holds because temp is structurally decoupled from (d, v), so R is the source's. | 3 | - |
| `lit_drl_car_stop` | 4 | 3 | 5 | 3 | KEEP | Safe_eps = x+v^2/2+2v+1 checks (FM'11 eq. 7 at A=B=eps=1). The sampled form reduces the refinement to guard inclusion (Goal 1), and the header says so plainly (l.31-41). | 3 | - |
| `lit_freedm_meter` | 4 | 3 | 5 | 3 | KEEP | Faithful sampled form of Prop. 11; the witness ignores the secret entirely (grid-only right certifies, l.46-47), which is the source's own argument; negative leaky twin exists (l.53) | 3 | - |
| `sat_detumble_phases` | 3 | 4 | 4 | 3 | KEEP | Euler/gyrostat coefficients check out ((J2-J3)/J1 = -0.5, 0.75, -0.4, h/J2 = 0.25) and E' = -2kE holds exactly, but the claim needs equal damping k on all three axes, which is not physical; header l.23-36 says the claim fails at magnetorquer gains | 3 | - |
| `tank_dos_3to1` | 3 | 4 | 4 | 3 | KEEP | Tight 0.72 (= 10/14) under a stated 0.8 requirement, with a cause sweep. h_L <= h_R rests on demand that only rises (w' = 0.02(22-w), l.85). A 50 s "morning surge" (l.14) and a 2.5 m tank that 5 pumps fill in about 100 s are stylized | 4 | CONFIRMED (run): 0.72 CERTIFIED, 0.71 DECLINED (tank_72/71), header tight value right; falling-demand claim UNCHECKED |
| `train_ato_odometry` | 4 | 3 | 4 | 3 | KEEP | 806/840, 26.04 m/s, ETCS 4 km/h and 7.5 km/h are all correct. S rests on the narrow tolerance window [1.07, 1.13) (l.53): SYNC with choice certifies at 1.13, only 0.02 m/s above the 1.11 requirement | 3 | CONFIRMED (run): RELCERT_SYNC=1 at 1.13 CERTIFIED, 1.12 DECLINED (train_12/13) |
| `platoon_latency` | 4 | 4 | 4 | 4 | POLISH | Lag/Q-form/TTC arithmetic all check (W/kp = 4, 1, 2, 20 - 8W = 16); only letter D lives on AEB pairs reachable only as starts (l.5-9); header time 2.0 s (l.136) vs matrix 984 ms | 4 | CONFIRMED (run): AEB removed on both sides CERTIFIED (plat_noaeb): D only from AEB; base run 1.1 s vs header 2.0 s (l.136) |
| `platoon_linkloss` | 4 | 4 | 4 | 4 | POLISH | Good requirement (0 <= Delta g <= (h_a - h_c) v_ref = 15, checked); D again start-only (l.43-46); M manufactured by the 0.2 s timeout period (l.9), disclosed | 4 | - |
| `syringe_relay_prearm` | 4 | 4 | 4 | 4 | POLISH | Physics is sound (26.6 mm bore gives 0.09 mm/min; k = ln2/2.4 gives 0.29; e^{-3.2} gives 4 %). Header l.32 says "100 min before the switchover", but (49.5-45)/0.05 = 90 min | 3 | CONFIRMED (arith): (49.5 - 45) / 0.05 = 90 min, header l.32 says 100 |
| `antenna_track_kvretune` | 4 | 4 | 4 | 4 | KEEP | Lags 0.7/K and 5/K check out. The pointing row is tied to beamwidth/10 (0.12 dB, l.35-36), and the D argument (command rate changes, requirement only while tracking) is genuine. The header carries a duplicated verdict block (l.68-91). | new | - |
| `lit_girard08_robot` | 4 | 4 | 5 | 4 | KEEP | Error-coordinate change checked (z' = -z/2 - e/200), tight 0.16 checked (Lie derivative -Q - 2 e.v); planner made more permissive than Fig. 3 (l.53-64), disclosed | 3 | - |
| `lit_nahs25_salt_tank` | 5 | 4 | 5 | 4 | KEEP | Attack projection exact (On iff xp >= 22, Off iff xp < 28, l.20-22); band 3 tight (checked: L holds below 28, R decays to 25); I load-bearing (matrix NO_CUT DECLINED) | 4 | - |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| r3 (4b5d052) | 0 | 4 | 29 | 17 | 0 |
| r4 (50ab23f) | 0 | 12 | 32 | 6 | 0 |

Verdicts r4: KEEP 11, POLISH 29, RETHINK 10, DROP 0 (r3: KEEP 32, POLISH 12, RETHINK 6, DROP 0). Overall >= 4: 6/50 (12 %, r3 34 %). Overall < 3: 12 (r3 4).

## Delta vs r3

The r3 set had `tunnel_jetfan_pairout` (3, now skipped); r4 has `antenna_track_kvretune` (new, 4). Of the 49 shared files 26 keep their overall, 2 go up, 21 go down.

Up: `lit_girard08_robot` 3->4, `syringe_relay_prearm` 3->4.

Down: `engine_start_highidle` 4->2, `acc_tune_lag` 3->2, `grid_ffr_dos` 3->2, `lit_drl_lane_control` 3->2, `platoon_profiles` 3->2, `quad_light_lag` 3->2, `rover_ladder_2to3` 3->2, `rover_patrol_lag` 3->2, and 4->3 for `acc_spoof_limp`, `bottling_fill_strainer`, `flaps_slow_approach`, `furnace_program_timebase`, `hydro_rejection_gatecal`, `insulin_basal_cgmloss`, `rover_ladder_3to6`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_terrain_6to12`, `sat3w_detumble_phases`, `tank_dos_3to1`, `ventilator_vc_cuffleak`.

Still at 2 from r3: `charger_fast_tapers`, `lit_lz21_vehicle_position`, `rover_terrain_2to4`, `turbine_startup_gearratio` (the turbine and terrain files were edited since r3; the reviewers still found the same core issue).

Reading the delta: this round's reviewers scored harder on R (twelve files at R = 2) and ran their own "is this row load-bearing" arithmetic; most of the downgrades are a new concrete finding, not drift. In the 4->3 group the finding is mostly a header or constant issue (POLISH). Only `engine_start_highidle` lost two points, for the start-only ABORT. The same start-only-fallback pattern was already noted in r3 for `h2_refuel_ambientbias` and the platoon files.

## Per-group notes

- G1 (ACC, antenna, bottling, charger, elevator, engine, flaps). Three RETHINK: `acc_tune_lag` (the lag constant is solved so that the claim holds, and the a box clips the left guard parallelogram, whose corner reaches a = 28.75), `charger_fast_tapers` (c = 2 is a tool artifact over a physical lead of 0; P comes from dead FAULT edges) and `engine_start_highidle` (ABORT is reachable only from pre-elapsed timer starts and carries D). `antenna_track_kvretune` is the only KEEP and scores 4. In `flaps_slow_approach` and `bottling_fill_strainer` the "tight" values are set by copied guard limits or by an implied row.
- G2 (fuel cell, furnace, gantry, grid, h2, hydro, insulin, csf21 x2, drl car). One RETHINK: `grid_ffr_dos`, where the 0.24 a_R band certifies with an FFR that never fires, so the DoS hold is not what the claim distinguishes. The others are POLISH or KEEP at 3: non-monotone tolerance windows (fuelcell, also turbine and charger), the AMS 2750 uniformity class reused as a run-to-run tolerance (furnace), and an untight hydro speed band (0.07 also certifies).
- G3 (literature x5, platoon x3, quad x2). Two RETHINK: `platoon_profiles` (the rows are exact by the gain construction; any slack certifies) and `quad_light_lag` (the lag sits on the set-point part only, and the Psi constant 0.16 is far from the tight 0.45). Two literature files are at 2 but kept or polished: `lit_lz21_vehicle_position` (any offset certifies) and `lit_drl_lane_control` (the claim reduces to Safe_eps => Safe). In all three platoon files D sits on start-only AEB modes.
- G4 (reactor, rover ladder x4, rover patrol, rover terrain x3, sat3w). No KEEP. RETHINK: `rover_ladder_2to3` (the heading row is not load-bearing; the clearance row is monotonicity), `rover_patrol_lag` (the letters come from the 1 m slack, not the lag; the header itself says so) and `rover_terrain_2to4` (the real-time form certifies at lambda 1, but the file keeps the 2.7x form). The ladder 6to8/8to12 files state lambda_max 1.25 while the cover uses 1.1. In `rover_terrain_6to12` four of the six added coordinates are output-only and the header's |v'| <= 5.6 should be 6.4.
- G5 (sat x2, syringe, tank, train, turbine, ventilator, watertank x2, zone). One RETHINK: `turbine_startup_gearratio` (one-sided claim, non-monotone in the factor, dead STOP edges). Mostly header numbers: syringe 100 -> 90 min, the sat_detumble_weak RK4 start outside its guard, ventilator 0.105 vs 0.104, watertank lambda_max 6 unused. Both watertanks omit the deployed side's own dry-run interlock (unchecked).

## Verified actionable items (ranked by impact)

1. Start-only fallback modes manufacture D and force exact rows (verified on three files, alleged on two more). `engine_start_highidle`: without ABORT the uniform n_L <= n_R + 4 certifies in every mode. `platoon_latency`: without AEB it certifies, so D comes only from AEB. `h2_refuel_ambientbias`: without ABORT, uniform 2.9 certifies but drops the stated stage rows, while uniform p_L <= p_R declines. By the D_rows rule D then stays, which contradicts the header's "letters R I" (l.52). `platoon_linkloss` and `platoon_profiles` are reported with the same AEB pattern but were not run. Fix: either give ABORT/AEB a guard reachable from the operating range (a real trigger) or drop them and their D claim. This moves the D letter count, which is a paper number.
2. Claimed relational rows that carry no content (verified on six files). `rover_ladder_2to3`: the heading row certifies at 100. `reactor_feed_wireless`: the 9 K band can be replaced by unary limits. `bottling_fill_strainer`: row (5) is implied. `rover_terrain_6to12`: the three output-only rows can be deleted. `lit_lz21_vehicle_position`: offset 5 certifies. `platoon_profiles`: +-5 slack certifies. Fix: drop or restate each row, or (platoon_profiles) perturb the SPORT kd, e.g. 0.85, so that the exact rows break and a real tolerance can be bisected.
3. Letters or verdicts resting on dead or artificial structure (verified on two files). `charger_fast_tapers`: P comes from FAULT edges no run takes; NO_PRUNE certifies once they are removed. `grid_ffr_dos`: the band certifies with an FFR that never fires, so the DoS claim is not what is checked. Fix (charger): give FAULT a real trigger or remove it and the P claim. Fix (grid): make the band depend on the hold, or tie it to the FFR-active regime.
4. Domain or guard bounds that set the "tight" value (verified on four files; acc_tune_lag l.72 calls the guard's a range 'well inside' the box, flaps l.84 calls the widening not load-bearing). `acc_tune_lag`: the a box at +-30 declines, and the left guard reaches a = 28.75, so l.72's "well inside" is false. `flaps_slow_approach`: V <= 214 declines at 25. `quad_light_profiles`: dropping w_L <= 2.4 declines. `zone_lightmass_schedule`: 33 degC declines. Fix: state each as a load-bearing start or domain restriction with its physical justification, or move the bound to a physical limit and re-bisect.
5. Loose constants presented as derived or tight, and weaker-than-available claims (verified on six files). `quad_light_lag`: Psi 0.45 certifies against the stated 0.16. `hydro_rejection_gatecal`: 0.07 certifies against the stated 0.09. `watertank_twospeed`: the lower row certifies at 1.5 against the stated 2. `watertank`: lambda_max 2 suffices against the stated 6. `rover_terrain_2to4`: the real-time form w_L <= v_R certifies at lambda_max 1. `rover_terrain_4to6`: the 0.15 creep floors can go to 0, which restores the composition with 2to4. Fix: re-bisect and state the tight value, or switch to the stronger form.

Header-number fixes (verified, POLISH only):
- `syringe_relay_prearm` l.32: 100 min should be 90 min.
- `sat_detumble_weak` l.62: the RK4 start has E = 1.06 > 1.
- `ventilator_vc_cuffleak` l.56: 0.105 should be 0.104 (0.103 declines).
- `rover_terrain_6to12` l.65: |v'| <= 5.6 should be 6.4.
- `platoon_latency` l.136: 2.0 s should be about 1.1 s.

## Reviewer notes by group

### G1

#### Review G1 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_spoof_lag | 3 | 3 | 3 | 3 | POLISH | The modal identity is right (roots 1, 5/3 vs 2/3, 2; ratio 3/2), but row 1 (re-timed overspeed, l.31) is not a requirement anyone states. tau = 0.375 was picked so the roots come out rational. The left guard l.103 is a modal parallelogram with corners (6.5, 25.5) and (46.5, -25.5) that only the domain clips. |
| acc_spoof_limp | 4 | 4 | 3 | 3 | POLISH | The physics and the AASHTO-derived row 2 check out (l.58-61). But the LIMP ceiling of 36 m/s (l.121) contradicts "fault not conditioned on speed" (l.35), and the existential reference driver is what produces X. |
| acc_tune_lag | 2 | 3 | 2 | 2 | RETHINK | tau = 0.32 is the unique lag that makes the claim realisable (l.14-18), and the a-box is load-bearing (l.67-69). The left guard l.96 reaches abs(a) = 28.75 at its far corners, so l.72 "envelope's own acceleration range is well inside it" is false. |
| acc_tune_limp | 4 | 3 | 4 | 3 | POLISH | The CRUISE identity holds by construction (0.75 = 1.5 x 0.5, l.36-38), and D exists only because the stated CRUISE row is stronger. The LIMP crossovers 35 and 37.5 check out. l.65 "leads by at most 7.00" is a certificate bound; the true sup is about 5.6. |
| antenna_track_kvretune | 4 | 4 | 4 | 4 | KEEP | Lags 0.7/K and 5/K check out. The pointing row is tied to beamwidth/10 (0.12 dB, l.35-36), and the D argument (command rate changes, requirement only while tracking) is genuine. The header carries a duplicated verdict block (l.68-91). |
| bottling_fill_strainer | 4 | 3 | 3 | 3 | POLISH | The physics checks out (Psi conserved, 8 vs 6.8 mL in flight). But requirement row (5), V_R - V_L <= 2, follows algebraically from rows (1)-(3), so "tightest 1.20 (1.19 declines)" (l.36) measures the hard-coded -1.2 offset, not the dynamics. |
| charger_fast_tapers | 2 | 2 | 3 | 2 | RETHINK | c = 2 is a tool artifact by the header's own account (l.52-57, 69-81), and the physical lead is 0. FAULT (x < 10) cannot be entered from PRECHARGE or BULK, so P rests on pruning dead edges. l.12 attributes P to "the raised limit", which contradicts l.85-89. |
| elevator_start_discbrake | 3 | 3 | 3 | 3 | POLISH | The brake never feeds back into z or v, so the conformance holds by construction apart from the lift delay. l.17 "rest at about 19.96 m" is wrong: the car arrives at about 0.5 m/s (l.68), so it rests near 20.03 m. |
| engine_start_highidle | 2 | 3 | 4 | 2 | RETHINK | ABORT is reached only from STARTER starts whose timer is already near 30 s (l.17-18). A sequence started at t = 0 reaches 25 % N2 by 16.1 s. The D letter and the low-row tightness (l.31-33, 37) rest on those starts. |
| flaps_slow_approach | 4 | 3 | 3 | 3 | POLISH | The gap ODE (l.35) is correct, and its tolerance is exactly (Vmax - F)/2 with Vmax = 200 taken from the guards (l.127, 141). So l.84 "not load-bearing" holds only because the guards repeat V <= 200, and the stated 25 kt exceeds the 20 kt requirement the header itself cites (l.40-46). |

##### acc_spoof_lag
- Model: one car with a first-order powertrain lag (tau = 0.375 s). Left reads speed 25 % high, so it settles at 24 m/s; right is the unspoofed loop. Both run at 0.1 s with lambda = 3/2.
- Property: the dominant-mode speeds satisfy u_L <= u_R - 6 under 3/2 re-timing. I checked this: u_L - 24 decays at 1, u_R - 30 at 2/3, and 2/3 x 3/2 = 1, so the gap is inductive. Row 1 (v_L <= v_R, re-timed) rides along.
- Concern 1: row 1 compares the spoofed car at t with the reference at 1.5 t. That is not an overspeed requirement; the real-time one is relegated to "consequence" (l.33-37).
- Concern 2: l.40 "Row 2 holds with equality" is only true from equal starts. The row is an inequality whose gap decays.
- Concern 3: the left envelope (l.103) is an interval box in modal coordinates, with corners at v = 6.5, a = 25.5 and v = 46.5, a = -25.5. Only the domain removes them, yet l.79-80 asserts "not load-bearing" without a measurement.
- Fix: keep row 2 as the claim, and either drop row 1 or motivate it. Reword l.40. Report the left envelope's span and measure the domain claim (see Checkable claims).

##### acc_spoof_limp
- Model: a 1-D speed loop. Left is CRUISE spoofed to 24 m/s with a latched LIMP at 22 m/s and a 2 s debounce. Right has driver-selectable ECO 27, NORMAL 30 and SPORT 33, plus a latched DISENGAGE, at 1 s.
- Property: never faster than the reference, and the closing speed v_R - v_L <= 4 + 0.3 v_R. I checked the AASHTO derivation: -8.5 + sqrt(72.25 + 13.6 v_R) gives 10.05 and 16.32, and the linear bound lies below the chord.
- Concern 1: the LIMP guard (l.121) caps entry at 36 m/s although l.35 says the fault "is not conditioned on speed". CRUISE runs up to 40, and the header admits the cap is not load-bearing (l.37). The cap only borrows acc_tune_limp's resume ceiling.
- Concern 2: X exists because the reference driver is existential, and ECO at 36 m/s decelerates faster than LIMP. The universal-driver claim holds up to 34.5 m/s.
- Concern 3: l.53 "the spoof keeps the car at least 2.4 m/s slower" is an inductive bound given the start relation, not a reachable-gap fact.
- Fix: set the LIMP guard to v >= 20 and v < 40, matching CRUISE. State plainly that X is the existential driver commitment above the 34.5 m/s crossover. Reword l.53.

##### acc_tune_lag
- Model: the same lagged car with gain 0.75 against 0.5, tau = 0.32 s, lambda = 2 pinned.
- Property: exact equality of the dominant modes, u_L(t) = u_R(2t), plus abs(v_L - v_R) <= 3.34. I checked the roots: (1.25, 1.875) against (0.625, 2.5), and the ratio-2 equation holds at p = 25/8.
- Concern 1 (P): the plant lag was solved for so that the specification is exactly realisable. At 0.30 s it declines (l.22), so the plant was tuned to the claim.
- Concern 2: the left guard (l.96) is a parallelogram in modal coordinates. Its far corners are (v, a) = (8.6, 28.75) and (46.4, -28.75), since a = 3X - 2Y over the box [-8.25, 2] x [-11.375, 2]. It is far from the "engaged envelope".
- Concern 3: the domain abs(a) <= 10 is therefore what removes those states, and the header confirms it is load-bearing (5 % widening declines, l.67-69). l.72's justification is factually wrong for the left side; the right envelope has a in [-7.5, 7.5].
- Fix: replace the left guard with a tighter forward-invariant polytope (for example add facets from simulated hulls), or drop row 3, which is a consequence rather than a requirement, and re-measure whether the a-box still matters. Correct l.72.

##### acc_tune_limp
- Model: 1-D tuned CRUISE (0.75 toward 30) with a latched LIMP (0.3 toward 25). Right has NORMAL, COMFORT and SPORT gains plus DISENGAGE, all at 0.1 s.
- Property: CRUISE v_L = v_R at stretch 3/2; LIMP v_L <= v_R at stretch 1.
- Concern 1: the CRUISE row is an algebraic identity of two first-order loops with gain ratio 1.5, so the only verification content is LIMP and the handoff.
- Concern 2: D counts only because the stated CRUISE row is stronger than the uniform v_L <= v_R that certifies.
- I checked the crossovers: 35 for SPORT and 37.5 for NORMAL are correct.
- Fix: say at l.65 that 7.00 is the inductive bound. The analytic reachable sup from equal starts is about 5.3 against NORMAL and 5.6 against SPORT.

##### antenna_track_kvretune
- Model: a type-1 elevation loop x' = K(c - x) following the same pass program (TRACK at -0.7 deg/s, then STOW at +5 deg/s, then STOWED), with K = 20 against 30.
- Property: the pointing difference stays within 0.035 deg while tracking and 0.25 deg after LOS, with the reference's own lag envelope as strengthening.
- I checked the numbers: lags 0.035 vs 0.023 and 0.25 vs 0.167, and 12 (0.1)^2 = 0.12 dB.
- Concern: none substantive. The header repeats its verdict block (l.68-73 and l.86-91), and the TRACK -> STOWED edge is unreachable (c is about 5 at t = 60).
- Fix (optional): merge the two verdict blocks.

##### bottling_fill_strainer
- Model: a volumetric filler. FILL is V' = Q, then CLOSE with u' = -25u and V' = Qu; Q = 170 against 200 mL/s, FILL at lambda 17/20.
- Property: the predicted final volumes are offset exactly by 1.2 mL, plus u_L <= u_R, V_L <= V_R, and V_R - V_L <= 2 (the giveaway requirement).
- Concern 1: V_R - V_L = 1.2 + 6.8 u_L - 8 u_R <= 1.2 - 1.2 u_R <= 1.2 follows from rows (1)-(3). So requirement row (5) is redundant at any constant >= 1.2, and its "tight" 1.20 is the offset written into rows (1,2).
- Concern 2: lambda_min = 0.8 doubles as a filling-sector time requirement through the tool's stretch range, not through a row.
- Fix: either state the requirement as Psi_R - Psi_L <= 2, one-sided, and report what certifies, or present rows (1,2) as the claim (shortfall exactly 1.2 mL) and drop row (5). Move the sector-time reading into prose as a disclosed encoding.

##### charger_fast_tapers
- Model: 1-D SoC phases (PRECHARGE, BULK, ABSORB, FULL, FAULT). The deployed raises the BULK rate 25 % and runs at half the decision rate; the reference has two tapers. lambda = 5/4.
- Property: re-timed x_L <= x_R + 2 (exact in PRECHARGE).
- Concern 1 (R): the header says c = 2 is the tool's over-approximation (one unit from FAULT x FAULT, one from the FULL floor at 99), not a requirement. The physical lead is 0, and the certifying window [2, 5] is non-monotone. The claim therefore says nothing about the charger.
- Concern 2 (P): FAULT is entered only at x < 10, yet the PRECHARGE and BULK flows are increasing at x >= 10. The edges at l.137, 142, 165 and 170 are dead, so P is manufactured by declaring impossible edges, and FAULT exists only as a start.
- Concern 3 (C): l.12 says "P from the raised limit", which contradicts l.85-89.
- Fix: make a cell fault a real event (FAULT reachable from every charging mode at any SoC, which is what a cell fault is), or drop FAULT. Restate the claim at a tolerance derived from a requirement (for example exact BULK equality at 5/4 plus one-sided rows elsewhere at c = 0 if attainable). Fix l.12.

##### elevator_start_discbrake
- Model: elevator trip phases LIFT, UP, APP, STOP. Brake lift rate is k = 50 against 5, and the brake gates only LIFT -> UP.
- Property: z and v equal in every mode after right-only repositioning of the reference's slower lift; in LIFT, b_R <= b_L.
- Concern 1: b never enters the z or v dynamics, so the conformance claim holds by construction except for the dwell. The retrofit's real risk, brake drop at the stop, is modelled identically on both sides (b' = -5b in STOP).
- Concern 2: the APP phase arrives at 19.9 m at about 0.5 m/s. I computed this from v = 0.25 + 1.35 e^{-0.8t} over 1.9 m, and it matches l.68. The car therefore rests near 20.03 m, not "19.96" (l.17). The initial stop deceleration of 2 m/s^2 is harsh for passengers.
- Fix: correct l.17 and l.58. Optionally give the disc brake its faster drop in STOP and couple the stop deceleration to b, so the relational claim has content beyond the delay.

##### engine_start_highidle
- Model: N2 start phases (STARTER, LIGHTOFF, SELF, IDLE, ABORT), with high idle 66 against ground idle 62. The timer runs only in STARTER.
- Property: exact (one-sided) in STARTER and LIGHTOFF with the timer row t_R <= t_L; N2_L <= N2_R + 4 above cut-out.
- I checked the physics: 5 -> 25 % at 0.1(30 - N2) takes 16.1 s, and 25 -> 50 at 0.08(55 - N2) takes 22.4 s, which is plausible.
- Concern 1: ABORT (t >= 30, N2 < 25) is reachable only from STARTER starts whose timer is pre-elapsed. From a sequence start at t = 0 and N2 >= 5, STARTER exits by 16.1 s and never aborts.
- Concern 2: both D (uniform +4 declines "because of the reachable abort", l.37) and the forced timer row and 0.0 constant (l.31-33) rest on those starts. The STARTER and LIGHTOFF dynamics are identical on both sides, so without the abort the low rows are trivial. "Light-off timer" is also a misnomer: it times motoring before fuel-on.
- Fix: make the abort a physical failure path, for example a hung-start or weak-starter branch, or a start condition tying t to N2. Otherwise disclose that D comes from timer-offset starts only.

##### flaps_slow_approach
- Model: flap extension 10 -> 15 deg at 0.5 against 1 deg/s, with an autothrust speed loop V' = -(0.02 + 0.001 f)(V - 150). Stretch 1/2 in EXT and 1 in CONF2.
- Property: equal flap angle, and the speed gap within [-10, +25] kt.
- I checked the gap ODE: D' = -kD + (k/2)(V_R - F) gives sup D = (Vmax - F)/2 = 25 and inf = (Vmin - F)/2 = -10. Both constants are therefore exactly functions of the V bounds.
- Concern 1: those bounds are copied into the EXT and CONF2 guards (l.127, 132, 141, 146). The l.84 claim "every bound widened by 20 % CERTIFIES" can hold only if the guards were not widened.
- Concern 2: the stated 20 kt requirement (l.40-46) is not met by the certified 25 kt, so the claim falls short of the requirement it cites.
- Fix: describe V <= 200 as the CONF 2 selection condition (a physical guard), not a non-load-bearing domain. Either restrict selection to <= 190 kt and claim 20 (meeting the requirement), or state openly that 25 = (VFE - F)/2 is the placard-derived bound.

##### Checkable claims
- acc_spoof_lag (a): the left guard (l.103) admits states with abs(a) up to 25.5 that only the a-domain removes. Test: widen `a >= -10.0 and a <= 10.0` to +-30 on l.104 and l.112. The header (l.79-80) predicts CERTIFIED; if it declines, the domain is load-bearing.
- acc_spoof_lag (b): tight row 1 at -3.33 (l.33) and stretch 1.45 declining (l.51). Test: set row 1 to `(<= L_v (- R_v 3.34))` on l.115 and expect DECLINED; set lambda_min = lambda_max = 1.45 on l.95-96 and expect DECLINED.
- acc_spoof_lag (c): row 1 is not load-bearing for row 2. Test: delete `(<= L_v R_v)` from l.115 and expect CERTIFIED.
- acc_spoof_limp (a/c): the LIMP ceiling is not load-bearing and X survives without it. Test: set l.121 to `v >= 20.0 and v < 40.0`. Expect CERTIFIED, still DECLINED under RELCERT_NO_CHOICE=1.
- acc_spoof_limp (c): X is produced by the ceiling. Test: set l.121 to `v <= 34.5`. Expect CERTIFIED under RELCERT_NO_CHOICE=1, which removes X (header l.39-41).
- acc_tune_lag (a): row 3 rests on the a-domain clipping the left parallelogram, not on rows 1-2. Test 1: delete the two 3.34 rows on l.108 and widen the a-domain on l.97 and l.105 to +-30; expect CERTIFIED. Test 2: keep row 3 with the same widening; expect DECLINED (header l.67-69).
- acc_tune_lag (b): l.72 "envelope's own acceleration range is well inside" the a-box is false for the left guard. Test: run --wellformed on the left with the a-domain removed (l.97); the reachable guard spans abs(a) up to 28.75, at the corner (v, a) = (8.6, 28.75).
- acc_tune_lag (a): the plant lag is tuned to the claim. Test: set 3.125 to 1/0.30 = 3.3333 on l.95 and l.103 with matching rows; header l.22 says DECLINED.
- acc_tune_limp (c): the CRUISE exactness row creates D. Test: set CRUISE on l.129 to `(<= L_v R_v)`; header says CERTIFIED with D gone.
- antenna_track_kvretune (b): the tight values. Test: TRACK 0.012 and STOW 0.084 on l.144-146 should give DECLINED; 0.0125 and 0.085 should give CERTIFIED.
- bottling_fill_strainer (c): row (5) is implied by rows (1)-(3). Test: delete `(<= R_V (+ L_V 2))` from l.120 and l.121 and expect CERTIFIED. Also set it to 1.19 and expect DECLINED from the empty CLOSE start set at u = 0, not from the dynamics.
- bottling_fill_strainer (b): the requirement can be stated directly. Test: replace the two exact Psi rows with `(<= (- (+ R_V (* 8 R_u)) (+ L_V (* 6.8 L_u))) 2)` and see whether it certifies. If it declines, the exactness is a tool need and should be stated as such.
- charger_fast_tapers (c): P comes only from dead FAULT edges. Test: remove FAULT from `next` on l.137, l.142, l.165 and l.170, and run RELCERT_NO_PRUNE=1. Expect CERTIFIED, so P vanishes.
- charger_fast_tapers (b): non-monotone tolerance. Test: set l.193-196 to +5.01 and expect DECLINED (header l.55). Set them to +1.99 and expect DECLINED.
- charger_fast_tapers (b): FAULT is responsible for one unit. Test: delete FAULT on both sides and set c = 1.0 on l.193-195; header says CERTIFIED.
- elevator_start_discbrake (b): the rest position is about 20.03 m, not 19.96 (l.17). This is a model computation, not a tool run; simulate APP from z = 18, v = 1.6 to z = 19.9 and get v of about 0.50.
- elevator_start_discbrake (c): the LIFT conjunct is load-bearing. Test: delete `and b[r] <= b[l]` from l.143; header says DECLINED.
- engine_start_highidle (a/c): D and the timer row exist only because of pre-elapsed-timer starts. Test: delete ABORT on both sides, the `t < 30.0` atom (l.88, l.122) and ABORT from `next` (l.90, l.124). Expect uniform `n[l] <= n[r] + 4.0` in every mode CERTIFIED, so D disappears.
- engine_start_highidle (b): tight 4.00. Test: set l.153-155 to 3.99 and expect DECLINED. Set the l.151 constant to 0.01 and expect DECLINED (header l.31).
- flaps_slow_approach (a): the bounds 25 and 10 are set by the guard copies of the V limits. Test 1: change `V <= 200` to `V <= 214` in both guards and evolve (l.127, 128, 132, 133, 141, 142, 146, 147); expect DECLINED at 25, with the tight value moving to about 32. Test 2: change `V >= 130` to `V >= 116` in the same lines; expect DECLINED at 10, with the tight value moving to about 17.
- flaps_slow_approach (b): the l.84 "every bound widened by 20 % CERTIFIES" is reproducible only if the guards are left untouched. Test: widen only the evolve lines (l.128, 133, 142, 147); expect CERTIFIED, which contrasts with Test 1 above.

### G2

#### Review G2 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| fuelcell_chp_dos | 3 | 3 | 3 | 3 | POLISH | Physics checks out (4.30 K / 5.83 K hold drift, pruning flows at 60/70 degC). But the true gap is 0 (l.31-37), the 7 K is window-derived and the certified window is non-monotone [5,8] then 10 (l.53-56). The 111-line header buries this. |
| furnace_program_timebase | 3 | 4 | 4 | 3 | POLISH | The stretch arithmetic is right: residual (1-0.8) x 32 = 6.40 and lag window E >= 30 from 0.01(630-E) <= 0.2E (l.41-43). But 8 degC is AMS 2750 *uniformity*, a spatial class reused as a run-to-run tolerance (l.29-31), and SOAK has no dwell (l.15). |
| gantry_speed_zones | 3 | 3 | 3 | 3 | POLISH | Uniform gain scaling makes the claim an exact time reparametrization. The tightest is 0.00 at lambda_max 3 (l.42) and an arbitrary zone schedule certifies (l.54-57), so the zones carry no weight. History lines 8-13 are noise. |
| grid_ffr_dos | 3 | 2 | 4 | 2 | RETHINK | The 0.24 a_R band is the whole FFR contribution (0.625/2.625 = 0.238). It certifies for a 1 s hold and for an FFR that never fires (l.44-46), so the claim does not depend on the attack. Instantaneous droop (l.9) removes the nadir that FFR exists for. |
| h2_refuel_ambientbias | 3 | 3 | 2 | 3 | POLISH | 72.43 MPa and the stage times (~45/48/48/64 s) check. But the exact stage rows and D come from the start-only ABORT mode (l.33-38, 49-52). l.51-52 "letters R I" without ABORT conflicts with the letters.md D rule. |
| hydro_rejection_gatecal | 3 | 4 | 3 | 3 | POLISH | The keyed rows are well motivated and the peak 0.2055 reproduces from settled on-grid gates. A start at g = 1 near t = 20 peaks at 0.223, so the margin is 0.077, not 0.0945 (l.34-36). Torque g-0.1 (l.101) contradicts P = (g-0.1)/0.9 (l.33). |
| insulin_basal_cgmloss | 3 | 3 | 4 | 3 | KEEP | Rate and band arithmetic verified (27.9, 17.9, 55.8, 35.8; equilibria 125/L2 and 155/L3). The tolerance is a chain-depth artifact (20 vs simulated 1.4 mg/dL), and the header says so. |
| lit_csf21_vehicle_bus | 4 | 3 | 4 | 3 | POLISH | Faithful encoding of CSF'21 Sec. VI-C with deviations listed. Same claim and only X as in vehicle_thermo; the six *T right modes are never used (l.50). "batch I8" (l.53) is internal jargon. |
| lit_csf21_vehicle_thermo | 4 | 3 | 5 | 3 | KEEP | psi = v^2+4v+2 at A=B=eps=1 checks, and the deviations (1)-(3) are explicit. The non-interference holds because temp is structurally decoupled from (d, v), so R is the source's. |
| lit_drl_car_stop | 4 | 3 | 5 | 3 | KEEP | Safe_eps = x+v^2/2+2v+1 checks (FM'11 eq. 7 at A=B=eps=1). The sampled form reduces the refinement to guard inclusion (Goal 1), and the header says so plainly (l.31-41). |

##### fuelcell_chp_dos
- Model: a PEM CHP stack settles a fixed rise above the heating return, T' = (Tin + rise - T)/120. The deployed's deterministic level selection is held 20 s by a DoS, against the protocol's overlapping bands decided every 10 s.
- Property: |T_L - T_R| <= 7 and Tin equal, justified as the margin between the [45, 85] window and the [52, 78] settled band.
- I re-checked the hold drift (40 -> 44.30, 100 -> 94.17), the MED invariance (Tin+17 in [57, 73]), both pruning flows ((68-70)/120 < 0, (62-60)/120 > 0) and the live-target thresholds (Tin < 43, Tin > 53). All correct.
- Strongest concern: the header says the physical gap is 0 (l.31-37), and the certificate needs 5 because of a segment-end obligation. The certified window is non-monotone ([5, 8] certifies, 8.01-9.995 declines, 10 certifies; l.53-56). That is a tool-completeness oddity the benchmark exposes, not a property of the plant. P holds only for Tin in (38, 58) (l.69-76).
- Fix: cut the header to scenario, requirement, tight value and letters, and move the 30 lines of variant measurements (l.69-92) to a note. Say in one sentence that 7 is a requirement-derived tolerance on a claim whose physical value is 0.

##### furnace_program_timebase
- Model: a first-order program generator (kap 0.01/min validated, 0.008 deployed) drives a 5-min-lag load, with segments PREHEAT/HEAT/SOAK.
- Property: s equal and |T_L - T_R| <= 8 up to stretch 4/5, with the validated-lag envelope s_R - T_R <= 32, T_R <= s_R.
- The arithmetic is consistent. D' = -0.2D + 0.2(1-lambda)(s_R - T_R) gives (1-lambda)E = 6.4, and the rate scaling (0.9: 3.2, 0.75: 8.0) is linear as claimed.
- Concerns:
  - AMS 2750 Class 3 (+-8 degC) is a temperature-uniformity class (spatial spread in the work zone), not a tolerance between a deployed and a validated run (l.29-31).
  - Real programmers run linear ramps plus timed dwells. The exponential approach plus a SOAK with no dwell or exit (l.15) makes the PREHEAT plus HEAT program about 12 h for a "light load in a small furnace".
- Fix (header): justify 8 degC as a profile-tracking tolerance, for example the load-thermocouple tolerance of the qualified profile, or say plainly that the uniformity class is being reused. Optionally note that the ramp shape is a design choice.

##### gantry_speed_zones
- Model: a two-axis first-order point-to-point servo. The production program scales both axis gains by a zone override 3/2/1; the right is the commissioning run at gain 1.
- Property: per-axis position within 10 mm up to a per-mode stretch.
- Successor reach checks (0.5 - 0.2e^-0.6 = 0.390; 0.5 - 0.05e^-0.4 = 0.466).
- Concern: uniform gain scaling is an exact time reparametrization by construction. The exact claim certifies (l.42), and an arbitrary zone schedule certifies too (l.54-57), so the zone structure carries no weight in the claim, and S/M are the only content. A first-order servo also has unbounded jerk at the start (3 m/s instantaneous at x = 0).
- Fix (header): drop the renaming and Round-A history (l.8-13). State in the claim paragraph that the relation holds for any schedule of uniform overrides, so the benchmark exercises S and M, not the zone law.

##### grid_ffr_dos
- Model: an aggregated swing equation (H = 4, droop 5 %, instantaneous) with a latched 0.1 pu battery FFR. A DoS holds the supervisor decision 0.3 s against 0.1 s.
- Property: x_L <= x_R <= x_L + 0.24 a_R, a_L <= a_R, same d.
- The model coefficients check (6.25, 2.625, settling -d/0.42, flow +2.06 Hz/s at -1.5 Hz, d = 0.3).
- Strongest concern: 0.24 = 0.625/2.625 is the steady effect of losing the *whole* FFR.
  - The header shows it certifies for a 1 s hold and for an FFR that never activates (l.44-46), so the hold length is not load-bearing for the bound.
  - "0.23 declines" comes from row states with a_L = 0 and a_R near 1. My boundary check gives 1.15 - 1.171 a_R + 0.625 a_L < 0 at a_R > 0.982. A 0.3 s hold cannot reach those states: a_R(0.3 s) = 0.78 while a_L is still 0.
  - With instantaneous droop the frequency has no nadir, which is the reason FFR exists. TRIP is therefore dead for d <= 0.63 by construction, and the P letter prunes a mode that can never be reached.
- Fix (RETHINK):
  - Add a governor lag state (for example a first-order turbine power with T = 2-5 s) so the FFR delay changes the nadir.
  - Make the band depend on the hold, either with a row tying a_L to a_R (1 - a_L <= e^{5 eps_L}(1 - a_R)) or with a constant tolerance derived from the simulated attacked-vs-nominal nadir gap.
  - The tightest value should then move with eps_L.

##### h2_refuel_ambientbias
- Model: a staged 0.05/s pressure-ramp fill to the J2601 end pressure. The ambient sensor reads 10 K high, giving 70 x (1 + 10/288) = 72.43 MPa.
- Property: the deployed may not lead in the stages (exact) and may lead by at most 2.9 MPa at top-off and after (2.4 bias + 0.5 certificate slack).
- Stage durations check (45.5, 48.0, 48.0, 64.4 s, about 3.4 min).
- Concerns:
  - By the header's own account (l.33-38, 49-52), the exact stage rows and the D letter rest entirely on ABORT. ABORT is a start-only mode no fill enters (l.16-17); without it every stage lead tried certifies and uniform 2.9 certifies. Physically this is a real threshold discontinuity at 0.5 MPa (a tank at 0.495 is refused, one at 0.5 is filled), but the header sells it as a "stage requirement".
  - l.51-52 reports "letters R I" without ABORT. Under the D rule in letters.md, uniform p_L <= p_R still declines on the top rows and uniform 2.9 drops the stated stage row, so D should survive the ABORT removal. Either the header or the letter script is out of step with the rule.
  - The 0.5 MPa of the 2.9 is certificate slack (l.40-42). The adiabatic fill heating that motivates J2601 tables is not modeled (acceptable, but unstated).
- Fix (header): restate the stage rows as the abort-threshold discontinuity (two tanks on either side of 0.5 MPa diverge), not as "stages identical so the deployed may not lead". Re-run the letter script on the ABORT-less variant and reconcile l.51-52 with the 2026-10-27 D rule.

##### hydro_rejection_gatecal
- Model: a governor with droop on the grid (speed frozen at the grid's |w| <= 0.004). After the breaker opens at t = 20 the gate closes to speed-no-load and the unit accelerates on the excess gate. The deployed's gate transducer reads 0.02 low.
- Property: on the grid equal t and w with gate within 0.027 (+-3 % power); after rejection the speed within 0.09 and the gate within 0.027.
- I reproduced the peaks: commissioned 0.2055 from w = -0.004 at settled gate, deployed peak gap 0.0101, settled gap 0.02.
- Concerns:
  - The rows admit a start at any t < 20 with any g in [0, 1]. A start with g = 1 at t near 20 peaks at 0.223, so the "every on-grid start" margin (l.34-36) is 1.30 - 1.223 = 0.077, and a 0.09 band could reach 1.313 > 1.30.
  - The REJECT torque is g - 0.1 (l.101, 117), but l.33 says P = (g - 0.1)/0.9. With the 1/0.9 factor the commissioned peak rises to about 0.228.
  - There is no speed feedback after rejection (l.19-20), so the deployed unit sits at 1.02 pu indefinitely. This is stated as "not modeled", but it is what sets the tightest 0.02.
- Fix: set the REJECT speed band to 0.07 (the tightest is 0.02, so this costs nothing), or restrict the margin derivation to t0 = 0 starts and say so. Make the torque scaling consistent with l.33 (w' = ((g-0.1)/0.9 - w)/8) and recompute the peak and band.

##### insulin_basal_cgmloss
- Model: a linear insulin-action/glucose cascade (55 min, 60 min, 50 mg/dL per U/h) with a 9-level glucose-band basal table, read every 5 min (reference) or every 10 min (Bluetooth loss).
- Property: |G_L - G_R| <= 25, |X_L - X_R| <= 0.5, b equal.
- Verified: band-skip rates (27.9, 17.9, 55.8, 35.8), the two-band jump from L7 at 250 (30.8 > 30, so L7 -> L5 is declared), and equilibria 125 (L2) and 155 (L3).
- Concern: the 25 mg/dL justification only covers the validated settling points (l.35-38), and the certificate's 20 mg/dL is a cover chain-depth artifact against a simulated 1.4 mg/dL. Both are stated, so this is acceptable.
- None blocking.

##### lit_csf21_vehicle_bus
- Model: the CSF'21 internal-bus car. One bus message per cycle changes either the action or the thermostat; the genuine side has 12 modes (action x setting x message type).
- Property: d and v equal (non-interference of the cabin-temperature attack).
- The deviation list (1)-(4) is careful, including the source's quirk of writing the accel value into thermo at temps = T.
- Concerns: the claim and the mechanism (X only) duplicate lit_csf21_vehicle_thermo. The six *T right modes are never needed by the cover (l.50). l.53 cites "batch I8", which a reader cannot resolve.
- Fix (header): replace "the same pattern as batch I8's unrestricted Coast" with the actual verdicts under the unrestricted Coast. Add one line on what this file adds over vehicle_thermo (the one-message-per-cycle successor restriction).

##### lit_csf21_vehicle_thermo
- Model: the CSF'21 car with thermostat, A = B = eps = 1, psi = 2d > v^2 + 4v + 2. The attacked thermostat is free; the genuine one is gated on temp vs 20.
- Property: d_L = d_R, v_L = v_R at every instant.
- Concern: the property holds because temp does not enter the (d, v) dynamics, so the content is the mode-product bookkeeping that X resolves. That is the source's claim, and the header is exemplary on deviations (Coast stand-in, top speed, thermo values) and on direction. "batch I8" (l.65) is minor jargon.
- None blocking.

##### lit_drl_car_stop
- Model: a sampled dRL stop-sign car. The left accelerates under Safe_eps = x + v^2/2 + 2v + 1 <= 50, the right under Safe = x + v^2/2 <= 50; both have Brake (v >= 1) and Coast (v <= 1).
- Property: x and v equal (reachability-inclusion refinement at stretch 1).
- Concern: in sampled form the certificate reduces to Safe_eps => Safe on v >= 0 (Goal 1). The header states this and gives the correct counterexample region v < -1/2 for the domain-free variant (l.38-41). As a benchmark it exercises only X.
- None blocking.

##### Checkable claims
- fuelcell_chp_dos (b): the certified tolerance window is non-monotone. Set 7.0 -> 9.0 on l.164-166: header says DECLINED. Set it to 10.0: header says CERTIFIED. Set it to 0.0: header says DECLINED although the physical gap is 0.
- fuelcell_chp_dos (a): P depends on the return-temperature domain, not on the property. Change `Tin <= 56` to `Tin <= 60` in every guard/evolve line (l.125-160): header says DECLINED at 7 (l.71-72).
- furnace_program_timebase (b): the tightest tolerance equals 0.2 x envelope. Set the envelope 32.0 -> 31.5 on l.118-120: expect tightest 6.30 (6.29 declines). Set it to 30.0: expect 6.00. Set it to 29.0: expect DECLINED at every tolerance (below the lag window of 30).
- gantry_speed_zones (c): the zone guards and the mode law are not load-bearing. Set left guards l.91/97/103 to the whole workspace and every `next` to [FREE, APPROACH, PLACE]: header says CERTIFIED (l.54-57). Set the tolerance on l.118-120 to 0.0: header says CERTIFIED at lambda_max 3, so 0.01 is not tight.
- grid_ffr_dos (c): the attack is not load-bearing for the band. Set the left epsilon on l.88 to 3.0: expect CERTIFIED at 0.24 (header measured 1.0). Set the left FFR to `a' = 0` (l.97): header says CERTIFIED.
- grid_ffr_dos (b): "0.23 declines" comes from states the hold cannot reach. Add `(<= R_a (+ L_a 0.78))` to the rows on l.125-126 and lower 0.24 to 0.20: if CERTIFIED (or if the added row is the only non-inductive part), the band can be made hold-dependent. Currently untested.
- grid_ffr_dos (a): TRIP is unreachable only because the incident range is small (instantaneous droop). Set `d <= 0.3` to `d <= 0.65` in every guard/evolve line: header says DECLINED (l.57).
- h2_refuel_ambientbias (c): D and the exact stage rows rest on the start-only ABORT. Delete ABORT on both sides (l.140-144, 180-184, 192, and ABORT in `next` on l.114, 120, 154, 160), set the stage rows to `p[l] <= p[r] + 1.0`: header says CERTIFIED. Then run scripts/suite_v2_letters.py on that file: header says R I, but the letters.md D rule predicts D (uniform `p[l] <= p[r]` declines on the top rows, uniform 2.9 drops a stated row). One of the two is wrong.
- h2_refuel_ambientbias (b): set 2.9 -> 2.899 on l.190-192: header says DECLINED. Set it to 2.4: DECLINED.
- h2_refuel_ambientbias (c): P is not load-bearing. RELCERT_NO_PRUNE=1: header and matrix say CERTIFIED.
- hydro_rejection_gatecal (b): the 0.09 speed band exceeds the requirement margin for g = 1 starts. Set 0.09 -> 0.07 on l.124: expect CERTIFIED (tightest 0.02, l.40-42).
- hydro_rejection_gatecal (b): the torque scaling is inconsistent. Replace `(- (- g 0.1) w)` with `(- (* 1.1111 (- g 0.1)) w)` on l.101 and l.117: expect the tightest speed band to rise to about 0.022 and the commissioned peak (simulation) to about 0.228.
- insulin_basal_cgmloss (b): G 20 / X 0.4 on l.210-218: header says CERTIFIED. G 19.5 / X 0.5: DECLINED. Left epsilon 15 (l.95) at 25/0.5: DECLINED.
- lit_csf21_vehicle_bus (c): the *T right modes are not load-bearing. Delete AccCoolT, AccHeatT, CoastCoolT, CoastHeatT, BrkCoolT, BrkHeatT and their `next` entries: expect CERTIFIED.
- lit_csf21_vehicle_thermo / lit_csf21_vehicle_bus / lit_drl_car_stop (c): X is the only load-bearing letter. RELCERT_NO_CHOICE=1: header says DECLINED; every other ablation CERTIFIED.
- lit_drl_car_stop (a): the top speed is not load-bearing. Drop `v <= 10.0` / `v <= 9.0` from l.86-115: header says CERTIFIED. Drop `v >= 0.0` from the evolve domains (l.87, 92, 97, 105, 110, 115): expect DECLINED (Goal 1 fails at v < -1/2).

### G3

#### Review G3 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| lit_drl_lane_control | 3 | 2 | 4 | 2 | POLISH | Right = left with weaker accel guard (l.115 vs l.82), same flows; claim reduces to Safe_eps => Safe (dRL Goal 1 only, l.43-44); a strict-superset 9-mode leader variant DECLINES "cause not identified" (l.32-34), which is a red flag |
| lit_freedm_meter | 4 | 3 | 5 | 3 | KEEP | Faithful sampled form of Prop. 11; the witness ignores the secret entirely (grid-only right certifies, l.46-47), which is the source's own argument; negative leaky twin exists (l.53) |
| lit_girard08_robot | 4 | 4 | 5 | 4 | KEEP | Error-coordinate change checked (z' = -z/2 - e/200), tight 0.16 checked (Lie derivative -Q - 2 e.v); planner made more permissive than Fig. 3 (l.53-64), disclosed |
| lit_lz21_vehicle_position | 3 | 2 | 5 | 2 | KEEP | Pure translation invariance with an input copy (any offset certifies, l.31-34); x <= 10 dropped for the witness (l.38-51); honest, but no relational content beyond X |
| lit_nahs25_salt_tank | 5 | 4 | 5 | 4 | KEEP | Attack projection exact (On iff xp >= 22, Off iff xp < 28, l.20-22); band 3 tight (checked: L holds below 28, R decays to 25); I load-bearing (matrix NO_CUT DECLINED) |
| platoon_latency | 4 | 4 | 4 | 4 | POLISH | Lag/Q-form/TTC arithmetic all check (W/kp = 4, 1, 2, 20 - 8W = 16); only letter D lives on AEB pairs reachable only as starts (l.5-9); header time 2.0 s (l.136) vs matrix 984 ms |
| platoon_linkloss | 4 | 4 | 4 | 4 | POLISH | Good requirement (0 <= Delta g <= (h_a - h_c) v_ref = 15, checked); D again start-only (l.43-46); M manufactured by the 0.2 s timeout period (l.9), disclosed |
| platoon_profiles | 4 | 2 | 4 | 2 | RETHINK | SPORT gains are an exact bandwidth scaling (kp x1.44, kd x1.2), so the rows are an identity with no tolerance content (any slack C certifies, l.69-75); D start-only (l.10-11) |
| quad_light_lag | 2 | 4 | 3 | 2 | RETHINK | Motor lag acts only on the set-point part of the thrust, feedback K w is lag-free (l.16-19): not a physical plant; Psi constant 0.16 derived from removed envelopes (l.50-52) |
| quad_light_profiles | 3 | 3 | 4 | 3 | POLISH | Psi conserved at 6/5 (checked, hover Psi = 0.0163); B and X come only from ECO/SPORT starts the cover leaves at once (l.84-89); row 1 certifies at 0.00 (l.74-75) |

##### lit_drl_lane_control
Model: follower/leader on a lane in gap coordinates (d, v_f, v_l), six (follower action, leader action) modes per side, time-triggered follower (guard Safe_eps) on the left, permissive follower (guard Safe) on the right, both sampled at 1 s.
Property: identity relation (d, v_f, v_l equal), i.e. reachability inclusion, the dRL refinement pattern.
Concern: the right model is the left model with one guard weakened (l.82/87 vs l.115/120; arithmetic of Safe_eps = v_f^2/2 - v_l^2/2 + 2 v_f + 1 checked), so the certificate is the guard implication of dRL Goal 1 and nothing else (l.43-44 says so). The 9-mode leader {A, 0, -B} is the same construction with superset guards and should certify by the same argument; its DECLINED with "cause not identified" (l.32-34) points at a tool incompleteness or a guard slip in that variant. Also unstated: the leader below v_l = 1 is forced to accelerate (AccelL is its only enabled action there, l.87/102 guards vl >= 1 for braking).
Fix: resolve the 9-mode decline (find the failing segment with RELCERT_DEBUG; if it is a tool gap, record it; if a guard slip, fix and adopt the 9-mode file as the faithful {A, 0, -B} leader) and add the low-speed leader restriction to deviation (2).

##### lit_freedm_meter
Model: one FREEDM transformer, battery level B (secret) and grid meter E (public), demand {0,1,2} and renewable {0,1} as 12 modes on each side.
Property: nondeducibility of B through the meter, E_L = E_R, every pair of B an admissible start.
Concern: none beyond triviality; the right never uses its battery (grid modes realise every net draw -1..2, checked), which is exactly Prop. 11's argument. Deviations (meter instead of draw, one transformer, finite inputs, sampling) are well argued (l.18-39).

##### lit_girard08_robot
Model: 6-D robot (double integrator plus dynamic tracking controller, in coordinates e, z, w) against the 2-D planner y2' = v, six heading locations each.
Property: w_L = y2_R and e^2 + 100 z^2 <= 0.16 on the robot, hence |y1 - y2| <= 0.4 (the source's precision).
Concern: the relational part is a copy of w; the precision is a left-only quadratic invariant (honestly the source's construction). The planner automaton is strictly more permissive than Fig. 3 (extra edges, target-invariant guards, l.53-64), so what is certified is weaker than the source, disclosed. Nit: matrix M7 cell reads "dim 6+-4" while letters.md reads 6/2.

##### lit_lz21_vehicle_position
Model: double integrator (x, v) in [0, inf) x [0, 0.1], three input levels per side, secret run left, partner right.
Property: v_L = v_R and x_R = x_L + 1 (partner 1 m ahead, so non-secret, outputs within delta = 1).
Concern: the claim is translation invariance under a copied input; the offset is free (0, 0.5, 2, 5, 9, 50, -1 all certify, l.32-33), and the source's X upper bound 10 is dropped to keep the copy unblocked (l.38-51). The header already calls it "a literature row, not a mechanism exhibit". No fix inside the encoding (any right model with x <= 10 and inputs held per level blocks, l.47-50); keep only as opacity-class coverage.

##### lit_nahs25_salt_tank
Model: brine tank xp' = 0.1 (25 - xp) (On, r = 10) or 0 (Off), attacked controller (reading error in [-3, 3]) vs genuine controller.
Property: |xp_L - xp_R| <= 3 with both tanks at or above 25 (the source's invariant from pre xp = 50).
Concern: none serious. The lower bounds xp >= 25 are start conditions taken from the source's invariant and are load-bearing (below 25 the attacked On rises while the genuine Off holds, so the gap exceeds 3); this is faithful, but say in the header that they are load-bearing.

##### platoon_latency
Model: CACC follower with a V2V feed-forward delayed by tau = 0.2 s (first-order lag, error e' = +-J - e/tau) vs the ideal-link CACC, shared radar AEB.
Property: |Delta g| <= 4 = J tau / kp, the two modal forms within 2W, 4W, deployed gap and TTC floors, |e_L| <= W; AEB pairs exact.
Concern: every constant checks (Q_0.25' = -0.5 Q + e, Q_0.5' = -0.25 Q + e, d/dt(g + 2r) = 2e - 0.25(g + 2r - 20)). The only letter D comes from AEB pairs that no CACC run reaches (l.5-9, l.103-108): with AEB removed there is no letter at all. The tau sweep (l.91-96) predates the one-domain change; timing 2.0 s (l.136) disagrees with the matrix (984 ms).
Fix: mark D as "start-only" in letters.md / the paper table (or report the file under "--"), re-measure the tau sweep on the current domain, and replace the 2.0 s with the matrix time.

##### platoon_linkloss
Model: CACC follower that falls back to radar ACC (h_a = 1.2 s) when the V2V link drops, with a 0.2 s link-loss decision period, vs the always-up design at 0.1 s.
Property: 0 <= Delta g <= 15, modal forms in [0, 15 rho], deployed gap/TTC floors, design TTC floor; AEB pairs exact.
Concern: the arithmetic checks (ACC differs from CACC only in the set point 35 vs 20, Q forms settle at 3.75 and 7.5). D is start-only exactly as in platoon_latency (l.43-46); M exists only because the deployed period was doubled in batch I9 (l.9), a plausible but constructed story.
Fix: same D annotation as platoon_latency; state in the header that M is by construction of the period ratio (equal periods give D only).

##### platoon_profiles
Model: SPORT CACC (kp 0.18, kd 0.9) vs NORMAL CACC (kp 0.125, kd 0.75) at lambda 6/5, shared AEB at lambda 1.
Property: g_L = g_R, r_L = 1.2 r_R at re-timed instants (exact), deployed floors; AEB exact.
Concern: the SPORT gains are chosen as the exact bandwidth scaling, so the rows hold by construction (re-timing identity checked); any slack certifies (l.69-75), so there is no tight constant and the claim says nothing a reader could not derive. Related starts need r_L = 1.2 r_R, so the same physical state is related only at r = 0. D is start-only (l.10-11, l.96-98).
Fix: give SPORT a realistically tuned, not exactly scaled, gain pair (e.g. kd = 0.85 instead of 0.9 on l.128) and state the re-timed rows with a tolerance that is tight (bisect), or switch to the real-time claim with its tight 4.00 (l.74-75) and drop S.

##### quad_light_lag
Model: lighter and reference quadrotor climb with a 0.1 s first-order motor lag, h' = w, w' = a - k w, a' = 10 (a_cmd - a).
Property: |h_L - h_R| <= 0.8 at times t and 1.2 t, strengthened by |Psi| <= 0.16 (the conserved steady-climb gap).
Concern: the lag filters only the constant set-point part of the thrust while the feedback -k w acts instantly (l.16-19); a real motor lag filters the whole command. Psi's constant 0.16 is "0.8 less the transient term of the earlier per-side envelopes" (l.50-52), envelopes that were removed, so it has no current derivation (Psi certifies up to 0.45 / 0.58, l.62-63). Domain coincidence: thrust limit 14.715 = left's a_cmd = 3 x 4.905 (l.71-75), harmless (20 % widening certifies).
Fix: put the lag on the full command, w' = a, a' = 10 (14.715 - 6.13125 w - a) (left) and a' = 10 (9.81 - 4.905 w - a) (right); Phi = h + w/k + a/(10 k) still has Phi' = a_cmd/k, so Psi stays exactly conserved at 6/5; widen a's domain below 0 (the loop is underdamped, zeta about 0.64 and 0.71) and re-derive the Psi constant from a stated requirement.

##### quad_light_profiles
Model: lag-free lighter quadrotor climb (terminal 2.4 m/s) vs a reference with pilot-selectable ECO/NORMAL/SPORT set points (1.6/2.0/2.4 m/s), lambda 6/5.
Property: |h_L - h_R| <= 0.8 at t and 1.2 t, with Psi <= 0.8, 1.2 w_R <= w_L, w_L <= 2.4.
Concern: all arithmetic checks (Psi' = 2.4 - 2 lambda; d/dt(w_L - 1.2 w_R) = 0.5886 - 0.2943 w_R on the face). B and X exist only because ECO/SPORT are admissible starts that the cover leaves at its first decision (l.84-89); with them removed the file is S M. Row 1 is unloaded (certifies at 0.00) and 0.8 is the admitted start set, not a dynamic gap (l.73-79).
Fix: annotate B and X as start-only in letters.md, or remove ECO/SPORT and claim S M; either way say in the claim that 0.8 bounds the admitted starts.

##### Checkable claims
- lit_drl_lane_control (b): the 9-mode leader {A, 0, -B} variant (l.32-34) has right guards that contain the left guards and identical flows; expect CERTIFIED. Build it (add AccelLCoast, CoastLCoast, BrakeLCoast with vl' = 0 on both sides, rows identical); if it still DECLINES, the decline is a tool incompleteness worth isolating.
- lit_drl_lane_control (c): the certificate is only the guard implication: replace the right's Accel guards (l.115, l.120) with the left's Safe_eps (l.82, l.87); expect CERTIFIED (identical systems), and RELCERT_NO_CHOICE=1 still DECLINED.
- lit_freedm_meter (c): delete the six Bat* modes from Rsys (l.133-162) and from the next lists; header says CERTIFIED (the secret is never used by the witness).
- lit_girard08_robot (b): set 0.16 to 0.1599 on l.183-188; expect DECLINED (my check: invariance of Q <= c needs sqrt(c) >= 0.4 |v|/0.2, i.e. c >= 0.16).
- lit_girard08_robot (a): restore the source's planner edges (l -> l, l+1) on l.150-180; header says DECLINED, so the certified abstraction depends on the extra edges.
- lit_lz21_vehicle_position (c): change the offset 1.0 to 5.0 in all three rows (l.139-141); header says CERTIFIED (translation invariance only).
- lit_lz21_vehicle_position (a): add x <= 10.0 to the right evolve domains (l.123, 129, 135) and run RELCERT_WELLFORMED_STRICT=1; header says DECLINED (the dropped source bound is what keeps the copying partner well-formed).
- lit_nahs25_salt_tank (b): set 3.0 to 2.99 in xp[l] <= xp[r] + 3.0 (l.104-105); expect DECLINED.
- lit_nahs25_salt_tank (a): drop xp[l] >= 25.0 and xp[r] >= 25.0 from both rows (l.104-105); expect DECLINED (L On rises from 22 while R Off holds below 25). Justified start condition (source pre xp = 50), but load-bearing.
- platoon_latency (c): remove AEB from both sides (l.159 next = [CACC_UP, CACC_DN], drop l.165-169, l.177 next = [CACC], drop l.178-182 and row l.186); header (measured before the one-domain change) says CERTIFIED with no letter, so D is start-only. Re-measure on the current file.
- platoon_latency (b): header timing "CERTIFIED (2.0 s)" (l.136) vs matrix 984 ms; also re-run the tau sweep l.91-96 (tau = 0.75 CERTIFIED with |Delta g| <= 15, tau = 0.8 DECLINED) on the one domain.
- platoon_latency (b): |Delta g| 3.99 (l.184-185), Q rows 0.99 / 1.99, TTC floor 16.01, |e_L| 0.49: all predicted DECLINED by my arithmetic (W/kp = 4, 2W, 4W, 20 - 8W, J tau).
- platoon_linkloss (c): remove AEB on both sides (l.130/135 next without AEB, drop l.136-140, l.148 next = [CACC], drop l.149-153 and row l.157); expect CERTIFIED with M only.
- platoon_linkloss (c): set the left epsilon 0.2 to 0.1 (l.125); header l.9 says CERTIFIED with D only (M is the period ratio).
- platoon_linkloss (b): Delta g <= 14.99 or Delta g >= 0.01 on l.155-156; expect DECLINED (steady ACC/CACC offset is exactly 15; equal starts give 0).
- platoon_profiles (c): widen the four SPORT equalities by +-5 (l.151, keep the floors); header says CERTIFIED, so the exact rows carry no tolerance content.
- platoon_profiles (c): drop AEB_L (l.131 next = [SPORT], drop l.132-136 and row l.152); header says CERTIFIED with S M (D start-only).
- platoon_profiles (proposed): set SPORT kd 0.9 to 0.85 (l.128); expect the exact rows to DECLINE, giving a tolerance that can be bisected.
- quad_light_lag (b): the Psi constant 0.16 (l.268, 6.13125 x 0.16) has no current derivation; with rows 1, 2 at 0.8, set it to 0.45 (header: certifies) and to 0.46 (header: declines) to confirm.
- quad_light_lag (a, mild): raise the a bound 14.715 to 17.658 (1.8 g) in l.102-103, l.110-111; expect CERTIFIED (header: 20 % widening certifies), so the coincidence a_max = a_cmd,L = 3 K is not load-bearing.
- quad_light_lag (proposed): full-command lag a' = 10 (14.715 - 6.13125 w - a), w' = a (left) and a' = 10 (9.81 - 4.905 w - a), w' = a (right), a domain [-9.81, 14.715], Psi rows rewritten with Phi = h + w/k + a/(10 k); expect CERTIFIED at lambda 1.2 (Psi conserved), with a re-bisected Psi bound.
- quad_light_profiles (c): delete ECO and SPORT from Rsys (l.144-154, NORMAL next = [NORMAL]); header says CERTIFIED with S M only (B and X are start-only).
- quad_light_profiles (c): set row 1 (R_h - L_h <= 0.8, l.156) to 0.0; header says CERTIFIED (row 1 unloaded).
- quad_light_profiles (a): drop w_L <= 2.4 (l.156); expect DECLINED (row 5 is a start restriction that bounds w_R <= 2 through row 4).

### G4

#### Review G4 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| reactor_feed_wireless | 3 | 3 | 4 | 3 | POLISH | 8.00 tight is right (2 levels x 4 K), but the 9 K "boil / accumulate" justification (l.31-39) is vacuous: the domain T in [15,60] (l.86-88) already excludes both, so the left alone meets it |
| rover_ladder_2to3 | 3 | 2 | 4 | 2 | RETHINK | Clearance is pure monotonicity (s_L' = v(1-psi^2/2) <= v_L <= v_R, l.99 vs l.121); the heading row is a start restriction ("every value in [0, 0.6] certifies", l.51-52); no mechanism |
| rover_ladder_3to6 | 3 | 3 | 4 | 3 | POLISH | Pitch row tight and model-reading (0.15+0.5x0.15=0.225, l.52-53), but unary; header l.81-83 calls roll a requirement the next rung relies on, yet no roll row here |
| rover_ladder_6to8 | 3 | 3 | 3 | 3 | POLISH | S/I come from the right plan-tolerance rows (header l.5-9 says so); the LTR row is implied (0.771 < 0.8, l.62-63); composed 1.21 rests on the cover, not on lambda_max = 1.25 (l.146) |
| rover_ladder_8to12 | 3 | 3 | 3 | 3 | POLISH | The rung adds heave inertia (z' = omega_z - z, l.161) but drops the left pitch rows; "heave row" in l.110-114 does not exist; same lambda_max composition gap (l.153) |
| rover_patrol_lag | 3 | 2 | 4 | 2 | RETHINK | Header's own twin test (l.7-10, 85-91): S M R B come from the 1 m slack, not the lag. Claim is one-sided against a plan re-timed 1.5x and moved alone; the tight 0.75 is set by the a >= -2 box (l.50-52) |
| rover_terrain_2to4 | 4 | 2 | 4 | 2 | RETHINK | Keeps a weaker claim on purpose: the plan's clock may run 2.7x faster when a real-time form certifies at lambda 1 (l.101-105); S/M come only from slip-ahead pairs the rows admit (l.87-92) |
| rover_terrain_4to6 | 3 | 3 | 3 | 3 | POLISH | Ordering rows are sound and real-time; but w,u in [0.15,0.8] (l.81) contradicts the "exactly 2to4's left" composition claim (l.15, 51), since 2to4 now has w in [0,0.8] |
| rover_terrain_6to12 | 3 | 3 | 3 | 3 | POLISH | Tight values check out (sigma 0.24, H 0.13, Theta 0.13), but 4 of 6 new coordinates are output-only filters (vz, ax, phs, omega_phs), and "|v'| <= 5.6" (l.65) is wrong: 8 x 0.8 = 6.4 |
| sat3w_detumble_phases | 3 | 4 | 4 | 3 | POLISH | Gyrostat equations and E' = -2kE check out exactly; the stated gains are ~100x real authority (l.60-63), and the header says the 1/1000-gain variant certifies the same, so use it |

##### reactor_feed_wireless
- Model: a 4-level feed interlock on a first-order CSTR temperature, T' = 0.1(p + 4k - T), with a 2 min wireless publish period (left) against a 1 min wired one (right), lambda 1.
- Property: |T_L - T_R| <= 9 and p_L = p_R in every mode. It is tight and inductive: at the band edge the gap derivative is 0.1(4 dk - d), so d >= 8 for |dk| <= 2. The branching and pruning arithmetic in l.41-56 all checks out.
- Concern: the stated requirement (no boiling above 60, no feed accumulation below 10, l.31-35) is already guaranteed by the left model alone. The domain T in [15,60] is forward invariant and excludes both, and every level settles in [19,51]. So the 9 K band transfers nothing the deployed side does not already have. Minor: the file says "batch sequencer" (l.23) but models a continuous reactor (l.1). A positive-feedback feed law is unusual, but l.16-18 justifies it.
- Fix: justify 9 K by a relational spec, e.g. the validated temperature profile's product-quality band (max deviation from the validated run), not by absolute limits the domain already enforces; and fix the batch/continuous wording.

##### rover_ladder_2to3
- Model: the 3-state rover (v, s, psi, with psi' = -psi) against the 2-state point model (psi frozen), on a three-zone route, lambda 1.
- Property: v_L <= v_R, s_L <= s_R, and |psi_L| <= 0.35.
- Concern: the clearance follows from s_L' = v_L(1 - psi^2/2) <= v_L <= v_R plus increasing set points. The heading row is unary and contracting, so any constant certifies (l.51-52): it only restricts starts. The rung exercises no mechanism and claims nothing about how much the heading costs.
- Fix: replace the heading row by a two-sided lag bound so the rung states a quantity, e.g. s_R - s_L + 2 psi_L^2 <= d with the derived d (the integral of v psi^2/2 is at most 8 psi0^2/4). Or state in the header that it is a composition-only base rung and drop the heading row.

##### rover_ladder_3to6
- Model: L6 (pitch, heave, roll with slip losses in s') against L3, lambda 1.
- Property: clearance, psi_L = psi_R, and |theta_p_L| <= 0.25. The tight 0.23 matches the analytic 0.225, and the z <= 0.15 bump stop is honestly declared load-bearing.
- Concern: every relational row is structural: the losses are squares, so the clearance is monotone. The only quantitative row is unary. The roll dynamics this rung adds (cross-slope + 0.015 a) carry no row, although l.81-83 says the next rung's plan tolerances are "the heading, pitch and roll requirements" on this model. Slip constants 0.3 / 0.2 are ad hoc.
- Fix: add |phi_r_L| <= 0.2. It should certify: the bound is 0.1 + 0.015 x 8 x 0.6 = 0.172. Report its tight value.

##### rover_ladder_6to8
- Model: L8 (yaw and pitch inertia in cascade charts) against L6, lambda in [1, 1.25]; the cover uses 11/10 with budget 2.
- Property: clearance; left heading, pitch, roll and LTR rows; right plan tolerances.
- Checked: roll tight 0.14 matches 0.1 + 0.015 x 3 x 0.7 = 0.1315, which uses the STEEP guard v <= 3. Stretch need 1/0.912 = 1.0965 is correct. The LTR implication 0.771 is correct.
- Concern: the header itself says S and I come from the claim form, not the refinement. The heading row is non-binding ("any value certifies"). The LTR row is implied by the other rows. l.110 says "the heave row's envelope", but there is no heave row: it is the pitch row. The 1.21 <= 1.25 timetable argument uses the certificate's 1.1, while the stated range would compose to 1.5625.
- Fix: set lambda_max to about 1.11 so the declared range itself composes (1.11^2 = 1.23 <= 1.25); call the LTR row a restated consequence; fix "heave row" to "pitch row".

##### rover_ladder_8to12
- Model: L12 (heave and roll inertia, tire slip y) against L8, lambda in [1, 1.25].
- Property: clearance; left heading, roll, LTR and lane rows; right plan tolerances.
- Checked: roll tight 0.15 matches 0.1 + 0.015 x (2.1 + 0.75 + 0.122) = 0.1446. Lane tight 0.20 matches 0.03 x (6.5 x 0.7 + 9.81 x 0.2) = 0.195 in FLAT. "Other rows bound LTR by 0.87" checks out.
- Concern: the step makes heave second order, and heave drives pitch (omega_theta' has 0.5 z). Yet the left pitch rows are dropped, so the 12-DOF rover's pitch requirement is never certified anywhere in the ladder. Also: "heave row" wording (l.113); same lambda_max composition gap as 6to8. The v <= 8 load-bearing claim is plausible only through the right's roll plan tolerance, since the right has no v <= c guard (0.1 + 0.015 x 9.6 x 0.7 = 0.2008 > 0.2); the header should say this.
- Fix: add |theta_p_L|, |omega_theta_L| <= 0.25; set lambda_max to about 1.11; say which row makes v <= 8 load-bearing.

##### rover_patrol_lag
- Model: a rover with a first-order motor lag (tau = 3/16 s) against a no-lag plan, four zone modes, lambda in [1, 1.5].
- Property: s_L <= s_R + 1, plus a look-ahead strengthening P_L <= P_R + 0.375. Both look-ahead derivatives are exactly c, which I verified.
- Concern: the plan may be re-timed and advanced alone, and "may lead by any amount" (l.45-48), so the claim is weak. By the header's own no-lag twin, all four letters come from the slack. The only lag-dependent number (0.75) is the row-2 offset plus tau x 2, i.e. it is set by the traction box a >= -2, not by reachable lag dynamics (0.59 with the reachable band). The left box is not forward invariant: runs are cut at v = 1.6 (l.29-35).
- Fix: either recast the claim so the lag causes the stretch (state row (1) at the tight lag lead and show the no-lag twin certifies synchronously at the same offsets), or keep the file as an explicit claim-form exhibit and drop the lag story from its framing.

##### rover_terrain_2to4
- Model: a 4-state slip/sinkage rover against a no-slip plan, three terrain zones, lambda in [1, 2.7].
- Property: v_L <= v_R, s_L <= s_R, and slip window 0 <= w - v <= 0.25.
- Checked: sigma tight 0.21 = 1.47/7. The ratios 2.637 and 1.294 check out.
- Concern: the header says a strictly stronger real-time form exists (add w[l] <= v[r], certifies at lambda 1 with SYNC), and that 2.7 was derived from what the cover needs, not from a requirement. The stretch is only needed for pairs (v_L = v_R with full slip ahead) that matched runs never reach. Composition claim (l.75-77) is stale against 4to6's w domain.
- Fix: adopt the real-time form as the file (letters I), or tie 2.7 to a dispatcher requirement and say the S exhibit is a claim-form choice.

##### rover_terrain_4to6
- Model: the 4-DOF terrain rover plus drive lag u and a heave envelope zh, against the 4-DOF model, lambda 1.
- Property: ordering rows, slip window, and zh <= 0.15. Tight H 0.13 matches rho_MUD c_MUD = 0.125.
- Concern: the domain w, u >= 0.15 ("creep floor", l.40) is a controller start restriction that excludes standstill. It differs from 2to4's w in [0, 0.8], so the "right = 2to4's left" claim (l.15, l.51) is no longer literal. Composition is still sound in this direction, because 4to6's runs are a subset of 2to4's. zh feeds nothing back.
- Fix: lower the floors to 0 (as 2to4 did) or justify the creep floor as a physical limit and say whether it is load-bearing.

##### rover_terrain_6to12
- Model: the 6-DOF terrain rover plus ramp grade, chassis pitch (slope load), filtered acceleration, squat pitch and second-order heave, against the 6-DOF model, lambda 1.
- Property: ordering rows, slip window, heave, and nose-up pitch theta_p + phs <= 0.15, with derived auxiliary rows.
- Checked: sigma 0.24 = (1.47 + 0.196)/7. Grade window 0.028 / 0.029 is right. Theta 0.12 declines because of the lag term 2v(gamma - theta_p) <= 0.028 in PAVED, not the stated "analytic 0.12" (l.56); the real inductive need is 0.128.
- Concern: only theta_p feeds back into v. vz, ax, phs and omega_phs are output filters, and gamma is a pinned scenario constant, so the "12-DOF" is padded. l.65's "|v'| <= 5.6" is wrong: at v = 0, w = 0.8 in PAVED, v' = 6.4. ax in [-6.5, 6.5] still contains it, but barely. Same creep-floor issue as 4to6.
- Fix: correct 5.6 to 6.4 and the Theta explanation (0.128); state which coordinates are output-only.

##### sat3w_detumble_phases
- Model: a three-wheel gyrostat (J = diag(2,4,5), wheels absorbing k J w) against a decoupled design model. Phase logic DETUMBLE / FINE; flight decides every 2 s, design every 1 s.
- Property: E_L = E_R exactly (tolerance 0). I verified all three Euler components and the h' coefficients. E' = -2kE holds exactly, and the claim depends on the cause (removing one coupling term declines, l.75-76).
- Concern: physically stylized. k = 0.5 /s means about 1 N m wheel torque, about 100x microsat authority (l.60-63); there is no wheel saturation. The header says the 1/1000-gain variant certifies with the same pattern, so the stylization is unnecessary. The matrix cells (M2, M6, M4 vacuous) agree with the letters M I X.
- Fix: make the 1/1000-gain variant the stated file (physical gains, SI seconds), or move the stylization remark to the header's first lines.

##### Checkable claims
- reactor_feed_wireless (claim: the requirement needs no band). Replace the |T_L - T_R| <= 9 conjuncts on l.172-175 by unary T[l] <= 60.0 and T[l] >= 10.0, keeping the p rows. Expect CERTIFIED: the boiling and accumulation limits hold for the left alone.
- reactor_feed_wireless (header numbers). Set 9.0 to 7.99 on l.172-175: header says DECLINED. Set it to 11.0: header says DECLINED (non-monotone window). Set it to 12.0: header says CERTIFIED.
- rover_ladder_2to3 (heading row not load-bearing). Set 0.35 to 0.0 on l.139-141, or delete the psi conjuncts. Expect CERTIFIED.
- rover_ladder_3to6 (missing roll row). Add (<= L_phi_r 0.2) and (<= (- 0 0.2) L_phi_r) to l.149-151. Expect CERTIFIED, tight near 0.18.
- rover_ladder_3to6 (header number). Widen z <= 0.15 to 0.21 on every evolve (l.111-145). Header says DECLINED.
- rover_ladder_6to8 (stated range should compose). Set lambda_max 1.25 to 1.11 on l.146. Expect CERTIFIED: cover 1.1, need 1.0965.
- rover_ladder_8to12 (same). Set lambda_max 1.25 to 1.11 on l.153. Expect CERTIFIED.
- rover_ladder_6to8 (LTR row not load-bearing). Delete the LTR conjunct on l.194-196. Expect CERTIFIED, since the other rows plus the domain imply it at 0.771.
- rover_ladder_6to8 (roll tight value uses the guard v <= 3). Set the roll row to 0.13 on l.194-196: header says DECLINED. Separately, setting STEEP's set point to 2.5 (l.154 and l.176) should let 0.13 certify.
- rover_ladder_8to12 (missing pitch rows). Add |L_theta_p|, |L_omega_theta| <= 0.25 to l.201-203. Expect CERTIFIED (0.15 + 0.5 x 0.15 = 0.225).
- rover_ladder_8to12 (v <= 8 is load-bearing only through the right). Widen v <= 8.0 to 9.6 on the right evolves only (l.185, 191, 197): expect DECLINED. Widen it on the left evolves only (l.163, 169, 175): expect CERTIFIED, because the left guard v <= c caps v_L.
- rover_patrol_lag (tight value set by the box). Add 0 <= a + 4v <= 6.4 to the left evolves (l.122-137). Header says the tight row (1) returns to 0.59. Set row (1) to 0.74 on l.163-166: header says DECLINED.
- rover_patrol_lag (letters not lag-caused). Set row (1) to 0.75 on l.163-166 and run RELCERT_SYNC=1: expect DECLINED. Run the header's no-lag twin with the same 0.75 / 0.375 offsets under RELCERT_SYNC=1: expect DECLINED too, confirming that the slack, not the lag, causes S.
- rover_terrain_2to4 (stronger real-time form). Add "and w[l] <= v[r]" to l.174-176 and set lambda_max to 1.0 on l.126. Header says CERTIFIED, with RELCERT_SYNC=1 certifying too.
- rover_terrain_2to4 (header number). Set lambda_max to 2.63 on l.126: header says DECLINED. Set it to 2.64: header says CERTIFIED.
- rover_terrain_4to6 (creep floor). Lower w >= 0.15 and u >= 0.15 to 0.0 on l.81-115. Expect CERTIFIED. If it declines, the floor is a load-bearing start restriction that the header does not declare.
- rover_terrain_6to12 (creep floor). The same edit on l.104-138. Expect CERTIFIED.
- rover_terrain_6to12 (output-only rows not load-bearing for the requirement). Delete theta_p[l] + phs[l] <= 0.15, ax[l] <= 2.0 and omega_phs[l] <= 0.1 from l.142-144. Expect CERTIFIED: those coordinates do not feed v, s, w.
- rover_terrain_6to12 (header "|v'| <= 5.6" is wrong). Shrink ax to [-5.7, 5.7] on l.104-138. Expect relcert --wellformed to report a domain exit on the ax face, since v' reaches 6.4 at v = 0, w = 0.8 in PAVED.
- rover_terrain_6to12 (Theta header number). Set 0.15 to 0.12 on l.142-144: header says DECLINED. Set PAVED's set point to 0.45 (l.114, 136): I predict 0.12 then certifies, since the need becomes 0.118.
- sat3w_detumble_phases (physical gains). Divide k by 1000 on both sides (l.129-147: -0.5 to -5e-4, -0.3 to -3e-4, and the h' coefficients scaled to match). Header says CERTIFIED, with NO_CHOICE and NO_CUT declining.
- sat3w_detumble_phases (box not load-bearing). Widen |w_i| <= 1 to 2 on all evolves (l.131-154). Expect CERTIFIED, because E <= 1 bounds every rate below 0.71.

### G5

#### Review G5 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| sat_detumble_phases | 3 | 4 | 4 | 3 | KEEP | Euler/gyrostat coefficients check out ((J2-J3)/J1 = -0.5, 0.75, -0.4, h/J2 = 0.25) and E' = -2kE holds exactly, but the claim needs equal damping k on all three axes, which is not physical; header l.23-36 says the claim fails at magnetorquer gains |
| sat_detumble_weak | 3 | 3 | 3 | 3 | POLISH | The RK4 example at l.62 starts at w = (0.5, 0.3, 0.2), where E = 1.06 > 1, outside the DETUMBLE guard on l.133. Its B letter comes only from the ECONOMY/SURVIVAL successors (l.143), which are answered by a hop back to NOMINAL. Exact only at the pinned 0.8 |
| syringe_relay_prearm | 4 | 4 | 4 | 4 | POLISH | Physics is sound (26.6 mm bore gives 0.09 mm/min; k = ln2/2.4 gives 0.29; e^{-3.2} gives 4 %). Header l.32 says "100 min before the switchover", but (49.5-45)/0.05 = 90 min |
| tank_dos_3to1 | 3 | 4 | 4 | 3 | KEEP | Tight 0.72 (= 10/14) under a stated 0.8 requirement, with a cause sweep. h_L <= h_R rests on demand that only rises (w' = 0.02(22-w), l.85). A 50 s "morning surge" (l.14) and a 2.5 m tank that 5 pumps fill in about 100 s are stylized |
| train_ato_odometry | 4 | 3 | 4 | 3 | KEEP | 806/840, 26.04 m/s, ETCS 4 km/h and 7.5 km/h are all correct. S rests on the narrow tolerance window [1.07, 1.13) (l.53): SYNC with choice certifies at 1.13, only 0.02 m/s above the 1.11 requirement |
| turbine_startup_gearratio | 3 | 2 | 3 | 2 | RETHINK | One-sided w_L <= 1.05 w_R against a reference that may run ahead. R, P and I appear even at g = 1 (l.85-89), and a weaker factor (1.06) DECLINES (l.67-68). The STOP edges are dead, and the real hazard (left trip at 13.9755 > 13.31) is admitted by the claim |
| ventilator_vc_cuffleak | 4 | 3 | 3 | 3 | POLISH | Resistor-network derivation checks (0.376238 - 0.049505 V; -1.9419 V - 0.0122; 32.9 mL loss). The EXP tight value 0.0647 comes from the V <= 0.404 / V - 0.4t <= 0 reachable-set domain, not from PEEP accuracy. Header gives the tight fraction as 0.104 (l.37) and 0.105 (l.56) |
| watertank | 3 | 3 | 3 | 3 | POLISH | The deployed model omits its own dry-run interlock (l.32-34: "no dry-run mode"), though only the sensor and pump are attacked. lambda in [1, 6] (l.80-81) is not justified. The requirement (l.37-40) reads as real time, but the claim is re-timed by 2 |
| watertank_twospeed | 3 | 3 | 4 | 3 | POLISH | The lower-row "underflow margin" justification is vacuous: x_R <= x_L + 2 with x_R >= 2 gives x_L >= 0, which is already the domain floor. Tight is 1.5 (l.52-54). P rests on a dead Fast->PumpOff edge, and the same missing left interlock as watertank |
| zone_lightmass_schedule | 3 | 3 | 4 | 3 | POLISH | 0.5 K certifies only because the range is 5..30 (tight 0.4848 = 0.00125 x 16 / 0.04125); header l.62-65 admits that 4 degC or 33 degC declines. Upper 30 degC is low for a lightweight zone's summer air. B is degenerate (l.95-97) |

##### sat_detumble_phases
- Model: a 4-state gyrostat (rigid body plus z-wheel) under isotropic rate damping, with a 2 s phase decision, against a decoupled design model with a 1 s decision. Shared DETUMBLE/FINE phase logic; the design model adds a SAFE sink.
- Property: body energy E_L = E_R exactly in both phases (two rows, l.165-166). It holds because the gyroscopic and wheel couplings do no work, which Z3 must establish by cubic cancellation.
- I checked the arithmetic: the coefficients follow from J = diag(2, 4, 5), h' = k J3 w3 gives 2.5 / 1.5, and the FINE envelope bounds (0.25, 0.177, 0.158) are right.
- Strongest concern: the claim exists only under equal k on all three axes, i.e. x/y actuators with wheel authority. The header admits that magnetorquer-scale gains DECLINE and the claim is false there (l.24-29). The header is cluttered with batch and date history.
- Verdict: keep. A good NRA refinement exhibit with an honest disclosure. Optionally move the batch history out of the header.

##### sat_detumble_weak
- Model: the gyrostat on actuators derated to 80 % (k = 0.4, 2 s decision) against a 1 s design model with three ground-selectable profiles (k = 0.5 / 0.45 / 0.42) plus SAFE.
- Property: E_L(t) = E_R^NOM(0.8 t) exactly, at a pinned lambda = 4/5. I checked: -0.8 = 0.8 x (-1.0); ECONOMY gives 0.72 = 0.9 x 0.8 and SURVIVAL gives 0.672 = 0.84 x 0.8.
- Concerns:
  - (1) The RK4 example (l.62-64) starts at E = 2(0.25) + 4(0.09) + 5(0.04) = 1.06, outside the engagement guard E <= 1 (l.133). The numbers themselves are consistent: 1.06 e^{-1.6} = 0.21401.
  - (2) B (branch 2) comes only from NOMINAL's declared ECONOMY/SURVIVAL successors (l.143). They are covered by an immediate hop back into NOMINAL, so the branch is degenerate. zone_lightmass_schedule discloses the same pattern; this header does not.
  - (3) An exact rate ratio is brittle (0.79 and 0.81 decline), and the ECONOMY/SURVIVAL values look chosen to generate X and B.
- Fix:
  - Restart the RK4 example inside E <= 1, e.g. w = (0.5, 0.3, 0.1) with E = 0.91, and re-measure.
  - Disclose B as degenerate, the way the zone header does, or drop B from the letters.

##### syringe_relay_prearm
- Model: a two-channel noradrenaline syringe-pump relay (volumes, plasma fraction C, driver slack b). The deployed relay pre-arms channel 2 at v1 = 45; the validated relay takes up 1 mm of slack from rest at the switchover.
- Property:
  - Volumes are equal up to re-timing (the right-only take-up absorbs the 11.1 min interruption).
  - C is equal before the switchover and C_R <= C_L after it (no added hypotension). Both are tight.
  - The b_R <= b_L ordering row is load-bearing (D).
- I checked: area pi(13.3)^2 = 555.7 mm^2, so 0.05 mL/min gives 0.090 mm/min. 1/0.09 = 11.1 min. ln2/2.4 = 0.289. e^{-0.29 x 11.1} = 0.040.
- Strongest concern: a header arithmetic slip. Pre-arm at v1 = 45 is (49.5 - 45)/0.05 = 90 min before the switchover, not 100 min (100 min is the time to empty at 50). Otherwise a strong benchmark.
- Fix: change "100 min before the switchover" to "90 min" on l.32.

##### tank_dos_3to1
- Model: tank level h and network demand conductance w. The pump stage is n = band(w); nominal polls every 10 s, the DoS-held decision every 30 s; same staging law on both sides.
- Property: h_L <= h_R (a stale stage is never higher), h_R <= h_L + 0.8 (outlet submergence requirement), equal w.
- I checked:
  - Equilibria 5n/w lie in [1.0, 1.67] per band.
  - Demand moves at most 3.2 per 10 s (< 4, the band width).
  - In 30 s, w(30) from 9.99 reaches 15.41, which crosses two band edges, as declared.
  - The tight 10/14 = 0.714 matches the 0.72 measurement.
- Strongest concern:
  - The scenario hard-codes monotone rising demand (w' = 0.02(22 - w) on every mode). The exact row h_L <= h_R is a property of the surge only; during falling demand the stale stage is higher.
  - A 50 s time constant is not a "morning surge" (l.14).
- Verdict: keep. Optionally drop "morning surge" from l.14 (keep "fire-flow draw") and say explicitly that the claim is a surge-only claim.

##### train_ato_odometry
- Model: a first-order ATO speed loop at three performance levels. The deployed train has an uncorrected wheel diameter (tachometer reads 0.96 v), so it holds 26.04 m/s with a 4 % slower loop.
- Property: 0 <= v_L - v_R <= 1.11 m/s (the ETCS warning margin), against a design run re-timed per pairing in [0.75, 1.25].
- I checked:
  - 806/840 = 0.9595. 25/0.96 = 26.042 (93.75 km/h).
  - 90 + 7.5 km/h = 27.08 m/s, and 27.08/0.96 = 28.21.
  - The stretch table (39/40, 43/40, 6/5, 7/8, 11/10, 31/40) matches 0.96 k_i/k_j snapped to the 0.025 grid.
  - The SYNC tolerance 1.042 + 0.0417 x 2.08 = 1.129 is right.
- Strongest concern: S rests on the requirement 1.11 lying in the window [1.07, 1.13) (l.53). That window is set by the domain top 27.08 and the stretch grid, so S is genuine but marginal (0.02 m/s). Re-timing a speed claim is harmless here.
- Verdict: keep (already disclosed).

##### turbine_startup_gearratio
- Model: an NREL 5-MW start-up in four first-order phases (SPINUP free-spin toward 9 rpm, RAMP, GEN, STOP). The deployed controller reads rotor speed 5 % low (97/92.4), which scales thresholds and targets by 1.05 and divides the loop gains by 1.05.
- Property: w_L <= 1.05 w_R (+0.061 in GEN) against a reference that may run ahead. I checked the GEN tolerance: d >= (0.0025 w_R - 0.03025)/0.047619 at w_R = 13.252 gives 0.0604.
- Concerns:
  - (1) The claim is close to unary. A reference allowed to run ahead upper-bounds the deployed trivially. The header itself shows R, P and I appear at g = 1 (identical systems), every two-sided form fails or is near-vacuous (d >= 4.86 rpm), and a WEAKER claim (factor 1.06) DECLINES (l.67-68), so the rows act as a start relation rather than a requirement.
  - (2) The real hazard of the stale ratio is that the deployed's protection trips at a true 13.9755 rpm, above the 13.31 limit. The claim admits that (GEN row up to the trip) instead of exposing it.
  - (3) SPINUP->STOP and RAMP->STOP are declared but physically dead (both flows rise at 2 rpm). P rests on pruning edges that should not be declared; STOP is a start-only mode.
- Fix (RETHINK): state the claim the cause actually breaks. One option is a same-phase (no ahead reference) GEN-only relation w_L - 1.05 w_R in [-d, 0.061] with admissible start restricted to the deployed's phase. Another is to keep the file as a pure "one-sided existential" exhibit, drop the gear-error framing, and drop R/P/I as cause-driven letters. Remove the dead STOP successors or give SPINUP a low-wind deceleration so that STOP is reachable.

##### ventilator_vc_cuffleak
- Model: one volume-controlled breath (INSP flow-controlled, EXP pressure-controlled) in an ARDS lung (C = 0.04, R = 5 + 8). The deployed side has a 500 cmH2O.s/L cuff leak at the trachea.
- Property:
  - INSP: |V_L - V_R| <= 4 mL + 15 % V_R (ISO delivered-volume accuracy applied pointwise).
  - EXP: |V_L - V_R| <= 0.08 L (ISO PEEP accuracy +-2 cmH2O times C).
- I checked:
  - (0.4 - 0.002(10 + 25V))/1.01 = 0.376238 - 0.049505 V.
  - The node balance gives -(127V + 0.8)/65.4 = -1.94190 V - 0.012232, settling at -6.3 mL.
  - INSP end gap 0.4 - 7.6(1 - e^{-0.0495}) = 32.9 mL.
- Concerns:
  - The EXP tight value 0.0647 = 0.004 + 0.15 x 0.404 is the INSP row carried across the handoff. It is fixed by the reachable-set domain V <= 0.404 together with V - 0.4t <= 0 (l.86-109), not by a physical capacity. The PEEP requirement is met with margin.
  - The header gives the tight fraction as 0.104 (l.37) and as 0.105 (l.56).
  - Applying a per-breath ISO tidal-volume tolerance at every instant of inspiration is a reinterpretation (disclosed).
- Fix: reconcile 0.104/0.105. Say explicitly that V - 0.4t <= 0 and V <= 0.404 are reachable-set facts of one breath from V = 0 (not physical limits), and whether the EXP row depends on them (see the checkable claims).

##### watertank
- Model: a 1-D proportional level controller with Low / Mid (Eco, Boost) / High / PumpOff. The deployed side has a -3 dm sensor offset plus a doubled low-fill gain and is locked to Boost.
- Property: |x_L - x_R| <= 3 (the offset) against the reference re-timed by lambda = 2 in Low and Mid. Tight at 3.00.
- Concerns:
  - (1) The deployed controller is the nominal one with a biased sensor, so it should keep the dry-run interlock at reading < 2 (true x < 5). The header asserts that it "has no dry-run mode" (l.32-34), and that omission is what keeps PumpOff out of the claim.
  - (2) lambda_max = 6 (l.81) is unexplained; the cover uses 2.
  - (3) The requirement "the attack may not move the true level by more than the offset" reads as an equal-time claim, but it holds only up to a factor-2 re-timing.
  - (4) A "fill pump" that drains in High (x' = 17 - x) is stylized.
- Fix:
  - Disclose the left interlock as a coverage gap (or add it and report the verdict).
  - Pin lambda to [1, 2], or justify 6.
  - Restate the requirement as a claim on the level history up to re-timing.

##### watertank_twospeed
- Model: the running example's attacked tank against a nominal controller whose low fill has Fast (gain 2) and Slow (gain 1) stages.
- Property: x_L <= x_R + 3 (tight; the offset) and x_R <= x_L + 2 (tight value 1.5). I checked that from just below 7, Fast reaches 12.5 - 5.5e^{-2} = 11.76.
- Concerns:
  - The stated justification for the lower row ("while the reference runs, x_R >= 2, the deployed tank is not empty") is implied by the domain x_L >= 0. The constant 2 is therefore justified by nothing; it is 0.5 above the tight 1.5.
  - The upper bound is non-monotone (3.01 declines), so "tight" here is a start-admissibility effect.
  - P rests on the physically dead Fast->PumpOff edge.
  - Same missing left interlock as watertank.
- Fix: give the lower row a real requirement or use the tight 1.5, and say that 3 is fixed by start admissibility. lambda_max = 6 (l.91): pin or justify.

##### zone_lightmass_schedule
- Model: lumped zone air under a load-compensated bidirectional proportional terminal. The deployed zone (EN ISO 13790 very-light, 80 kJ/m^2K) runs 165/80 = 2.0625 times faster than the commissioned medium zone; a two-level schedule runs against a three-level strategy.
- Property: |T_L - T_R| <= 0.5 K against the reference re-timed by 2 (EN 15500 control accuracy).
- Concerns:
  - The tight value is D = 0.00125 x 16 / 0.04125 = 0.4848, set entirely by the range 5..30 degC (l.54-65). By the header's own numbers, 33 degC or 4 degC declines the requirement row. A room sensor span is typically 0..40 or 0..50, and a lightweight zone in summer exceeds 30 degC, so this is a domain that decides the claim.
  - The reachable worst gap is 0.057 K, so 0.5 is driven by admitted starts at the range edge.
  - B is the degenerate hop-back branch on the never-used STANDBY (l.95-97). It is disclosed, but it is still counted in the letters.
- Fix: take the sensor span 0..40 and state the tight 0.73 K, with the requirement derived from it (or a claim on the comfort band only, with the domain named as such). Drop B from the letters, or mark it degenerate in letters.md.

##### Checkable claims
- (b) sat_detumble_weak l.62-64: the RK4 start w = (0.5, 0.3, 0.2) has E = 1.06 > 1 = DETUMBLE guard (l.133). This needs only arithmetic, not a tool run. Re-run the RK4 check from w = (0.5, 0.3, 0.1) (E = 0.91).
- (c) sat_detumble_weak B is not load-bearing: set NOMINAL next on l.143 to [NOMINAL, SAFE] (keep ECONOMY/SURVIVAL next unchanged). Expect CERTIFIED with M3 = no (branching 0), S M X unchanged.
- (b) syringe_relay_prearm l.32: "100 min before the switchover" should be 90 min ((49.5-45)/0.05). Arithmetic only.
- (b) tank_dos_3to1 l.43: set 0.8 to 0.71 on l.137-140. Expect DECLINED; 0.72 should give CERTIFIED.
- (a) tank_dos_3to1: h_L <= h_R depends on monotone rising demand. Change w' target 22.0 to 6.0 on every mode (l.85-131; falling demand), reverse the right next lists to downward stages, and leave the left lists as [Pn, ..., P2]. Expect DECLINED for the row h_L <= h_R.
- (b) train_ato_odometry l.49-53: with RELCERT_SYNC=1 and the tolerance 1.11 set to 1.13 on l.146-148, expect CERTIFIED; with 1.12, expect DECLINED. This confirms that S hinges on a 0.02 m/s window.
- (c) turbine_startup_gearratio, R/P/I are artifacts of the claim form: replace the left modes (l.161-183) with the right's (l.189-211) and set the rows to w_L <= w_R. Expect RELCERT_SYNC=1, RELCERT_NO_PRUNE=1 and RELCERT_NO_CUT=1 each DECLINED (header l.85-87).
- (b) turbine_startup_gearratio non-monotone rows: set 1.05 to 1.06 in SPINUP/RAMP/STOP (l.214, 215, 217) and to 1.06 w_R + 0.061 in GEN (l.216). The claim is weaker, yet the header says DECLINED.
- (a) turbine_startup_gearratio P stands on dead edges: delete STOP from SPINUP and RAMP next (l.165, 171). Expect CERTIFIED under RELCERT_NO_PRUNE=1 (P disappears).
- (a) ventilator_vc_cuffleak: the EXP row stands on a reachable-set domain. Drop "V - 0.4*t <= 0.0" and widen V <= 0.404 to V <= 0.8 in every guard/evolve (l.86-109). Expect DECLINED, because the INSP->EXP handoff needs 0.004 + 0.15 V_R <= 0.08, i.e. V_R <= 0.507. Widening only V <= 0.404 to 0.8 (keeping V - 0.4t <= 0) should stay CERTIFIED.
- (b) ventilator_vc_cuffleak l.37 vs l.56: set 0.15 to 0.104 in both INSP inequalities on l.113. Header l.37 says CERTIFIED; header l.56 implies DECLINED (tight 0.105). One of them is wrong.
- (a) watertank: add the deployed's own interlock: Lsys mode PumpOff (guard x < 5.0, x' = 0, next [PumpOff]), PumpOff in Low next (l.92), and a row PumpOff = same as l.141. Expect DECLINED (a latched deployed against a filling reference in Low). The omission is then load-bearing.
- (c) watertank lambda range: set lambda_max = 6.0 (l.81) to 2.0. Expect CERTIFIED with the same letters (the range [2, 6] is unused).
- (a) watertank_twospeed: the same added left PumpOff (guard x < 5.0) as above. Expect DECLINED.
- (b) watertank_twospeed lower row: set +2 to +1.5 on l.157-159. Expect CERTIFIED (the header says 1.50 is tight). The stated "underflow margin" requirement holds through the domain alone.
- (a) zone_lightmass_schedule: widen 5 <= T <= 30 to 0 <= T <= 40 on l.135-159. Expect DECLINED at 0.5 and CERTIFIED at 0.73 (header l.62, l.75). Use 5 <= T <= 33 for DECLINED at 0.5.
- (c) zone_lightmass_schedule B: remove STANDBY from the next lists of COMFORT and ECONOMY on l.150 and l.160. Expect CERTIFIED with M3 = no (branch 1) and S M X kept.

