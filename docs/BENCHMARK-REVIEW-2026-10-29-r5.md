# Benchmark review, round 5 (2026-10-29; suite_v2 at 36e736d, 50 benchmarks)

Five fresh reviewer agents, 10 benchmarks each in alphabetical order (G1 `acc_spoof_lag` .. `engine_start_highidle`, G2 `flaps_slow_approach` .. `lit_drl_car_stop`, G3 `lit_drl_lane_control` .. `quad_light_profiles`, G4 `reactor_feed_wireless` .. `sat_detumble_phases`, G5 `sat_detumble_weak` .. `zone_lightmass_schedule`). Each saw only `docs/review-rubric.md`, its ten `input.txt` files, `docs/paper-numbers/matrix.md` and `docs/paper-numbers/letters.md`; no earlier review, score, report or fix list. Nothing in the suite was changed this round (the suite is fix round 4's, commit 404b0ab).

Verification column: every RETHINK, every overall 2 and every artifact or number claim was checked once where a single edit tests it. `CONFIRMED (run)` = `./.lake/build/bin/relcert` with `RELCERT_IMPLIED_CUT=1` on a scratch copy in `tmp/verify-r5/` (file name in parentheses); `(inspection)` / `(arith)` = checked by hand against the file, `letters.md` or `matrix.md`; `UNCHECKED` = not run (reason given). A weaker claim certifying is not a finding; only a stronger claim certifying, or a stated claim failing, is.

## Ranked table (worst first)

| benchmark | P | R | C | overall | verdict | one-line reason | r4 overall | verification |
|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | 3 | 2 | 3 | 2 | RETHINK | A re-timed comparison (attacked car at t vs reference at 3/2 t) is not a sensor-attack requirement. The real-time claims are moved to prose. The lag 0.375 s is chosen so the claim comes out exact. | 3 | CONFIRMED (inspection): the stronger row v_L <= v_R - 3.33 certifies by the header's own measurement (l.32-33); the 'not a requirement' point is a framing judgment |
| `acc_spoof_limp` | 2 | 3 | 4 | 2 | RETHINK | The reference has driver set-speed modes and a period the attacked car lacks, so every letter comes from padding, not from the spoof. The overspeed row holds only by committing the reference driver out of ECO. | 3 | UNCHECKED (reduced right model not built); row 1 slack (-2.40 certifies) is the header's own measurement (l.51) |
| `acc_tune_lag` | 2 | 3 | 4 | 2 | RETHINK | The lag tau = 0.32 s is the unique knife-edge value that makes the exact claim true (0.30 declines). Row 3's tight 3.34 comes from the +-10 m/s^2 domain clipping unreachable guard corners. | 2 | CONFIRMED (inspection + r4 run): tau 0.30 declines per header l.22; a box at +-30 DECLINED (r4 atl_a30) |
| `acc_tune_limp` | 3 | 2 | 4 | 2 | RETHINK | The CRUISE witness NORMAL is the left ODE time-scaled (it copies the left). The LIMP overspeed row is false against a SPORT driver and is rescued by an existential choice. COMFORT/SPORT exist only to produce B and X. | 3 | CONFIRMED (inspection): letters.md D is D_rows only, uniform v_L <= v_R certifies (header l.45-46) |
| `charger_fast_tapers` | 3 | 2 | 4 | 2 | RETHINK | The one-sided bound against a replay at 5/4 that dominates every phase is trivially true. The tight c = 1 is a tool artifact (any c up to 100 certifies). D and M/B come from that artifact and from an invented 2:1 period. | 2 | CONFIRMED (run): FULL threshold 99 -> 99.5 makes c tight at 0.50 (0.49 declines; chg_995): c measures 100 minus the threshold, not the charger |
| `elevator_start_discbrake` | 3 | 2 | 3 | 2 | RETHINK | The brake does not enter the motion dynamics, so "same motion up to re-timing" is the identical ODE replayed (R is needed even at k_L = k_R). The stated rest position is wrong. | 3 | CONFIRMED (inspection): R needed at k_L = k_R per header l.51-53; rest position 20.03 vs 19.96 UNCHECKED (simulation) |
| `engine_start_highidle` | 3 | 2 | 4 | 2 | RETHINK | The start-phase rows compare identical dynamics. The +4 row is the equilibrium shift. R exists only because the one-sided SELF row admits a lagging reference. The STARTER_LOW aim 25.5 is tuned to make abort reachable. | 2 | CONFIRMED (run): exact start rows (n, t two-sided in STARTER, STARTER_LOW, LIGHTOFF) CERTIFY (eng_exact), a stronger claim than the stated one-sided rows; 'R only from the one-sided SELF row' NOT confirmed (two-sided SELF/IDLE rows DECLINE, eng_twoside); aim threshold 26.05 CONFIRMED (arith) |
| `fuelcell_chp_dos` | 3 | 2 | 4 | 2 | RETHINK | The exact claim is true. 7 K sits in a non-monotone tool-artifact window [5, 8]. The Tin range and the 45 degC floor are tuned so that P and 7 work. | 3 | REFUTED in part (run): the exact rows (7.0 -> 0.0) DECLINE (fc_exact), so 7 is the tool's value, the semantic exactness UNCHECKED; non-monotone window CONFIRMED in r4 (fc_9/fc_10) |
| `lit_csf21_vehicle_bus` | 3 | 2 | 4 | 2 | RETHINK | The cover never uses the genuine car's thermostat-message modes, so the bus adds nothing over lit_csf21_vehicle_thermo (same constants, claim and letter X). | 3 | CONFIRMED (inspection): header l.50 states the six *T right modes are never used by the cover |
| `lit_drl_car_stop` | 3 | 2 | 5 | 2 | RETHINK | The sampled form reduces the dRL refinement to a single guard inclusion (Goal 1). The event-triggered content (Goals 2, 3) is gone and the right copies the left. | 3 | CONFIRMED (inspection): left Accel guard implies the right's on v >= 0; Coast and Brake identical; the header says the claim is Goal 1 |
| `lit_drl_lane_control` | 3 | 2 | 4 | 2 | RETHINK | identity refinement with identical ODEs and weaker right guards: the copy witness is immediate, the only content is Safe_eps => Safe; unguarded Coast lets the follower collide; 3-valued leader declines unexplained | 2 | CONFIRMED (inspection, r4): identical flows, guards differ by the Safe_eps margin; collision run UNCHECKED |
| `lit_lz21_vehicle_position` | 3 | 2 | 4 | 2 | RETHINK | right = left, witness copies the input, rows certify for every offset; the opacity content (partner non-secret) is not in the claim | 2 | CONFIRMED (run): adding x_R >= 1.0 (the partner non-secret) to every row CERTIFIES (lz_xr1): the opacity condition can be stated in the claim |
| `rover_patrol_lag` | 3 | 2 | 4 | 2 | RETHINK | All four letters S M R B come from the 1 m slack and appear unchanged in the no-lag twin; lambda_max 3/2 is "not a mission requirement" (15/11 rounded); order property with the plan advanced alone | 2 | UNCHECKED (header's own no-lag twin, l.7-11, l.85-91; not re-run) |
| `turbine_startup_gearratio` | 3 | 2 | 4 | 2 | RETHINK | the header admits R P I come from the one-sided claim (present at g = 1.00); the overspeed requirement follows from the left alone; STOP is start-only; the claim is called "real-time" but uses right-only repositioning | 2 | CONFIRMED (inspection): R P I at g = 1.00 per header l.85-89 |
| `zone_lightmass_schedule` | 3 | 2 | 4 | 2 | RETHINK | the 0.5 K row clears the inductive bound set by the domain by only 0.015, so it certifies because the domain is 5..30 (0..30 or 5..33 decline); it is 9x the reachable gap; B and X come from the claim's form | 3 | CONFIRMED (run): domain 0 <= T <= 30 DECLINES at 0.5 (zone_0_30): the tolerance is set by the domain floor |
| `hydro_rejection_gatecal` | 4 | 4 | 2 | 2 | POLISH | A good D exhibit, but the REJECT speed row in the file is 0.07 (l.124) while the header claims and justifies 0.09 everywhere. | 3 | CONFIRMED (inspection): the row is 0.07 (l.124) but the header still says 0.09 (l.31, 36, 43, 50, 61): a fix-round-4 omission (the header edit was prepared, not installed) |
| `rover_ladder_6to8` | 3 | 2 | 4 | 2 | POLISH | LTR row implied by the heading and roll rows (header admits it); heading rows "any value certifies" (the reason 2to3 dropped its heading row); S/I come from the plan-tolerance claim form, not the step | 3 | CONFIRMED (inspection, r4): LTR row implied (0.771 < 0.8, header l.61-63) |
| `quad_light_profiles` | 4 | 3 | 3 | 3 | RETHINK | B and X come from ECO/SPORT modes that are start-only for the witness (removing them leaves S M), the pattern removed from platoon_* in round 4; rows 1-3 not loaded | 3 | CONFIRMED (inspection): header l.87 states S M without ECO/SPORT |
| `canal_gate_notches` | 3 | 4 | 4 | 3 | POLISH | A good refinement scenario with a requirement tolerance. But HOLD is absorbing: no withdrawal disturbance, so the deadband law is never exercised after the start. | - | CONFIRMED (arith): HOLD's flow 0.006 (0.65 - h) stays in [0.4, 0.9), so RAISE and LOWER are entered only from starts |
| `gantry_speed_zones` | 4 | 3 | 4 | 3 | POLISH | A uniform override is a time reparametrization by construction. The exact claim certifies and so does an arbitrary zone schedule, so the 10 mm rows and the zone logic are not load-bearing. | 3 | CONFIRMED (run): rows at 0.00 CERTIFY (gz_000) |
| `h2_refuel_ambientbias` | 3 | 3 | 4 | 3 | POLISH | Plausible bias-to-end-pressure story. The top tolerance 2.9 = 2.4 bias + 0.5 certificate artifact has no requirement behind it, and the stage rows are one-sided where equality holds. | 3 | CONFIRMED (run): two-sided exact stage rows p_L = p_R in STAGE1-3 CERTIFY (h2_eqstage) |
| `insulin_basal_cgmloss` | 3 | 3 | 3 | 3 | POLISH | Without a meal input, glucose falls everywhere above 185, so L5-L8 are start-only. The header's "glucose can go either way from every level" is false for L4+. The certificate (20) is about 10x the simulated gap. | 3 | UNCHECKED (arithmetic reachability claims, not run) |
| `platoon_linkloss` | 3 | 4 | 3 | 3 | POLISH | ACC law drops a_pred (cruising lead assumed silently), so link loss is only a 20 -> 35 m set-point switch; M exists only by the 0.2/0.1 period ratio | 4 | - |
| `platoon_profiles` | 3 | 3 | 4 | 3 | POLISH | SPORT kd 0.85 chosen to break the exact re-timing; S is a framing choice (a lambda-1 tolerance exists and is not reported); tolerance scales with the |r| <= 10 domain | 2 | UNCHECKED (lambda-1 tolerance not bisected; the header's [1, 1.2] range certifies) |
| `quad_light_lag` | 3 | 4 | 4 | 3 | POLISH | the feedback K w bypasses the motor lag (only the set-point thrust is lagged), a non-physical loop; Psi band tight, row 1 slack | 2 | - |
| `reactor_feed_wireless` | 3 | 3 | 4 | 3 | POLISH | Good sampling-rate scenario, but the van 't Hoff argument for 8 K cites T-dependent kinetics the linear model lacks; 8 K equals the tightest value (moved from 9 on 10-29) and is ~9x the simulated 0.87 K gap | 3 | - |
| `rover_ladder_3to6` | 3 | 3 | 4 | 3 | POLISH | The "new channel" pitch row is a unary left invariant that the clearance rows do not need; psi_L = psi_R is an identity row | 3 | CONFIRMED (run): pitch conjunct deleted CERTIFIES (l36_nopitch); a unary requirement row not needed by the others |
| `rover_ladder_8to12` | 3 | 3 | 4 | 3 | POLISH | Rows are meaningful (LTR not implied, lane tight 0.20), but "lane" bounds only the tire-slip offset y and ignores cross-track drift from heading; S/I from claim form; 31 s of a 40 s budget | 3 | - |
| `rover_terrain_2to4` | 3 | 3 | 4 | 3 | POLISH | lambda up to 2.7 is derived from the worst start the rows admit (tight 2.64), and a stronger real-time form certifies; the re-timed form is "chosen as the chain's exhibit" | 2 | CONFIRMED (r4 run t24_rt): the real-time form certifies at lambda 1 (letters I only); the header states why the re-timed form is kept |
| `rover_terrain_4to6` | 3 | 3 | 4 | 3 | POLISH | Heave row zh_L <= 0.15 bounds an output-only coordinate (no feedback into v, s, w): the same reason 6to12 deleted its pitch rows | 3 | CONFIRMED (run): zh row deleted CERTIFIES (t46_nozh); zh is output-only |
| `rover_terrain_6to12` | 3 | 3 | 3 | 3 | POLISH | "12-DOF" is padded: ax, phs, omega_phs feed nothing and no row reads them; zh/vz heave rows output-only as in 4to6 | 3 | CONFIRMED (inspection): ax, phs, omega_phs feed no other field and no row reads them (stated in the header since fix round 4) |
| `sat3w_detumble_phases` | 3 | 4 | 4 | 3 | POLISH | exact, tight energy identity with correct gyrostat terms; but the stylized gain is ~100x actuator authority, "fine pointing" is rate damping with no attitude state, and M and I come from giving the design model a different period | 3 | - |
| `sat_detumble_phases` | 3 | 3 | 4 | 3 | POLISH | Exact energy equality is a textbook identity (couplings do no work) that holds only for isotropic damping, which the header says was chosen because the claim needs it; SAFE unreachable | 3 | - |
| `sat_detumble_weak` | 3 | 3 | 3 | 3 | POLISH | M and B come from a 2 s period on a one-mode left that has no decision to make; two differences between the sides (derating and couplings); the SI-unit claim with a ~100x stylized gain is not disclosed here (sat3w discloses it) | 3 | CONFIRMED (run): left epsilon 2 -> 1 CERTIFIES with letters S X (sdw_eps1): M and B come from the period ratio |
| `watertank` | 3 | 3 | 3 | 3 | POLISH | running example: the attack gains are chosen so that ratio 2 matches exactly; tolerance = offset is nearly circular; High and PumpOff are entered only from initial states; line 73 is stale | 3 | CONFIRMED (inspection): l.73 'cuts load-bearing in watertank_twospeed' is false (letters.md: S M B P, no I) |
| `watertank_twospeed` | 3 | 4 | 3 | 3 | POLISH | a better attack story than watertank (the full-speed pump matches Fast) and a tight lower row; but lambda_max = 6 is unexplained, verdicts are dated before the 1.5 change, and High/PumpOff are start-only | 3 | CONFIRMED (run): lambda_max 6 -> 2 CERTIFIES (wt2_l2); verdict block predates the 1.5 row |
| `lit_csf21_vehicle_thermo` | 3 | 3 | 5 | 3 | KEEP | A faithful literature replica. Non-interference holds by syntax (d, v ignore temp; the right can always pick a thermostat), but that is the source's claim. | 3 | - |
| `lit_freedm_meter` | 3 | 3 | 5 | 3 | KEEP | faithful to Prop. 11, but the secret B occurs in no grid guard, so security is immediate and the right's six battery modes are dead weight | 3 | - |
| `lit_girard08_robot` | 4 | 3 | 5 | 3 | KEEP | relational part is an exact copy (w_L = y2_R); the content is a robot-only Lyapunov sublevel (tight 0.16), which is the source's structure; certified abstraction weaker than Fig. 3 (disclosed) | 4 | - |
| `rover_ladder_2to3` | 3 | 3 | 4 | 3 | KEEP | Honest rung with no mechanism; clearance follows from a one-line comparison (same v loop, s'_L <= v) | 2 | - |
| `flaps_slow_approach` | 4 | 4 | 4 | 4 | POLISH | Hardware-ratio stretch on placard domains with tight 25/10 kt. The 25 kt exceeds the stated 20 kt requirement (disclosed). Stale suite-status note about insulin (l.101-102). | 3 | - |
| `antenna_track_kvretune` | 4 | 4 | 4 | 4 | KEEP | Real servo retune with a requirement-derived pointing band (a tenth of the beamwidth). D is physically motivated. Only a dead TRACK->STOWED edge and some history clutter. | 4 | - |
| `bottling_fill_strainer` | 4 | 4 | 4 | 4 | KEEP | Clean cause and a regulatory requirement. The 1.2 mL offset is exact and tight (1.19 and 1.21 decline). The model is simple but faithful. | 3 | - |
| `furnace_program_timebase` | 4 | 4 | 5 | 4 | KEEP | Clean S+I exhibit: exact program rows, a load residual (1-λ)·32 = 6.4 with a tight bisection, and an 8 degC requirement from AMS 2750. | 3 | - |
| `lit_nahs25_salt_tank` | 4 | 4 | 5 | 4 | KEEP | source model exactly, tight distance 3, I letter genuine; only nit: the genuine Off is excluded by the rows | 4 | - |
| `platoon_latency` | 4 | 4 | 4 | 4 | KEEP | derived and bisected tolerance J tau / kp, convex jerk extremes; header cluttered with round history | 4 | - |
| `syringe_relay_prearm` | 4 | 4 | 4 | 4 | KEEP | real clinical hazard (slack take-up start-up delay), tight one-sided C row, honest D disclosure; TAKEUP2_L is a corner case only reachable from late-start states | 4 | - |
| `tank_dos_3to1` | 4 | 4 | 4 | 4 | KEEP | requirement-tied 0.8 against tight 0.72, cause sweep over hold lengths; the model covers only a rising-demand surge, which is what makes h_L <= h_R hold | 3 | - |
| `train_ato_odometry` | 4 | 4 | 4 | 4 | KEEP | correct odometry physics and ETCS margin, tight 1.07 against the 1.11 requirement, cause sweep; S lives in a narrow tolerance window [1.07, 1.13) and the performance levels are a gain stylization | 3 | - |
| `ventilator_vc_cuffleak` | 4 | 4 | 4 | 4 | KEEP | resistor-network leak model checks out, ISO-tied tolerances, tight values given, D argued from flow vs pressure control | 3 | - |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 17 | 23 | 10 | 0 |

Verdicts: KEEP 13, POLISH 21, RETHINK 16, DROP 0. Overall >= 4: 10/50 (20 %). Overall < 3: 17.

## Delta vs previous round

Previous histogram (1..5): 0, 12, 32, 6, 0 over 50; this round: 0, 17, 23, 10, 0 over 50.

Up: `bottling_fill_strainer` 3->4, `flaps_slow_approach` 3->4, `furnace_program_timebase` 3->4, `platoon_profiles` 2->3, `quad_light_lag` 2->3, `rover_ladder_2to3` 2->3, `rover_terrain_2to4` 2->3, `tank_dos_3to1` 3->4, `train_ato_odometry` 3->4, `ventilator_vc_cuffleak` 3->4.

Down: `acc_spoof_lag` 3->2, `acc_spoof_limp` 3->2, `acc_tune_limp` 3->2, `elevator_start_discbrake` 3->2, `fuelcell_chp_dos` 3->2, `hydro_rejection_gatecal` 3->2, `lit_csf21_vehicle_bus` 3->2, `lit_drl_car_stop` 3->2, `lit_girard08_robot` 4->3, `platoon_linkloss` 4->3, `rover_ladder_6to8` 3->2, `zone_lightmass_schedule` 3->2.

New in this round: `canal_gate_notches`.

Not in this round: `grid_ffr_dos`.

## Verdicts and delta, in short

Histogram (overall 1..5): r4 0 / 12 / 32 / 6 / 0, r5 0 / 17 / 23 / 10 / 0. Verdicts r5: KEEP 13, POLISH 21, RETHINK 16, DROP 0 (r4: KEEP 11, POLISH 29, RETHINK 10, DROP 0). Overall >= 4: 10/50 (20 %, r4 12 %). Overall < 3: 17 (r4 12).

Fix-round-4 files: up `bottling_fill_strainer` 3->4, `ventilator_vc_cuffleak` 3->4, `platoon_profiles` 2->3, `quad_light_lag` 2->3, `rover_ladder_2to3` 2->3, `rover_terrain_2to4` 2->3; unchanged `engine_start_highidle` 2, `charger_fast_tapers` 2, `acc_tune_lag` 2, `platoon_latency` 4, `syringe_relay_prearm` 4, `h2_refuel_ambientbias`, `reactor_feed_wireless`, `rover_terrain_4to6`, `rover_terrain_6to12`, `sat_detumble_weak`, `watertank`, `watertank_twospeed` 3; down `hydro_rejection_gatecal` 3->2 (the header was not updated with its row, a fix-round-4 omission), `platoon_linkloss` 4->3 (new finding: the ACC law drops the predecessor acceleration). The refill `canal_gate_notches` scored 3. Most downgrades among unedited files are new concrete findings by a stricter reviewer (G1 rated four ACC files 2 for re-timed claims, existential padding and knife-edge constants; G2 rated the two literature files at 2 for guard-inclusion-only content).

## Verified actionable items (ranked by impact)

1. Stronger claims certify than the files state (verified on six files). `engine_start_highidle`: exact two-sided start rows certify (eng_exact), so the one-sided start rows state less than the identity. `h2_refuel_ambientbias`: exact stage rows certify (h2_eqstage). `gantry_speed_zones`: 0.00 certifies (gz_000). `lit_lz21_vehicle_position`: the partner's non-secret condition `x_R >= 1` can be added to every row and certifies (lz_xr1). `watertank_twospeed`: lambda_max 2 certifies (wt2_l2). `acc_spoof_lag` / `acc_spoof_limp`: stronger rows certify by the headers' own measurements. Fix: state the stronger claim (or say why the weaker one is the requirement).
2. Tolerances that measure the tool or the domain, not the plant (verified on three files). `charger_fast_tapers`: c tracks the FULL threshold (99.5 gives tight 0.50, chg_995), physical lead 0. `zone_lightmass_schedule`: the domain floor 0 instead of 5 DECLINES at 0.5 (zone_0_30). `fuelcell_chp_dos`: 7 K lies in a non-monotone tool window (the exact rows decline, fc_exact). Fix: restate as tool-bound values or redesign the claim so the plant sets the number.
3. Mechanism letters from period ratios or start-only modes (verified on four files). `sat_detumble_weak`: equal periods leave S X (M B gone, sdw_eps1). `canal_gate_notches`: RAISE/LOWER only from starts (HOLD absorbing). `quad_light_profiles`: B X only from ECO/SPORT starts (header l.87). `acc_tune_limp`: D is D_rows only. Fix: give the start-only modes a reachable trigger (canal: a withdrawal disturbance) or drop the letter claim.
4. Header out of sync with the model (verified on three files). `hydro_rejection_gatecal`: row 0.07, header 0.09 throughout (fix-round-4 omission). `watertank` l.73 (twospeed has no I). `watertank_twospeed`: verdict block predates the 1.5 row. Fix: header edits only.
5. Output-only coordinates and unary rows (verified on three files). `rover_terrain_4to6` zh row and `rover_ladder_3to6` pitch row are not needed by the relational rows (t46_nozh, l36_nopitch); `rover_terrain_6to12` keeps three output-only coordinates. Fix: drop the coordinates, or state the unary rows as requirements of the refined channel explicitly.

## Reviewer notes by group

### G1

# Review G1 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

Sources: the rubric, the ten input.txt files, matrix.md and letters.md rows. Mechanism letters in every header agree with letters.md (acc_spoof_lag S M; acc_spoof_limp M B I X; acc_tune_lag S M; acc_tune_limp S M B D I X; antenna D; bottling S I; canal X; charger S M R B D I; elevator R D; engine R D I) and with the matrix M-cells. My own side checks used z3 (as an LP solver) and a 10-line Euler simulation, not the tool.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_spoof_lag | 3 | 2 | 3 | 2 | RETHINK | A re-timed comparison (attacked car at t vs reference at 3/2 t) is not a sensor-attack requirement. The real-time claims are moved to prose. The lag 0.375 s is chosen so the claim comes out exact. |
| acc_spoof_limp | 2 | 3 | 4 | 2 | RETHINK | The reference has driver set-speed modes and a period the attacked car lacks, so every letter comes from padding, not from the spoof. The overspeed row holds only by committing the reference driver out of ECO. |
| acc_tune_lag | 2 | 3 | 4 | 2 | RETHINK | The lag tau = 0.32 s is the unique knife-edge value that makes the exact claim true (0.30 declines). Row 3's tight 3.34 comes from the +-10 m/s^2 domain clipping unreachable guard corners. |
| acc_tune_limp | 3 | 2 | 4 | 2 | RETHINK | The CRUISE witness NORMAL is the left ODE time-scaled (it copies the left). The LIMP overspeed row is false against a SPORT driver and is rescued by an existential choice. COMFORT/SPORT exist only to produce B and X. |
| antenna_track_kvretune | 4 | 4 | 4 | 4 | KEEP | Real servo retune with a requirement-derived pointing band (a tenth of the beamwidth). D is physically motivated. Only a dead TRACK->STOWED edge and some history clutter. |
| bottling_fill_strainer | 4 | 4 | 4 | 4 | KEEP | Clean cause and a regulatory requirement. The 1.2 mL offset is exact and tight (1.19 and 1.21 decline). The model is simple but faithful. |
| canal_gate_notches | 3 | 4 | 4 | 3 | POLISH | A good refinement scenario with a requirement tolerance. But HOLD is absorbing: no withdrawal disturbance, so the deadband law is never exercised after the start. |
| charger_fast_tapers | 3 | 2 | 4 | 2 | RETHINK | The one-sided bound against a replay at 5/4 that dominates every phase is trivially true. The tight c = 1 is a tool artifact (any c up to 100 certifies). D and M/B come from that artifact and from an invented 2:1 period. |
| elevator_start_discbrake | 3 | 2 | 3 | 2 | RETHINK | The brake does not enter the motion dynamics, so "same motion up to re-timing" is the identical ODE replayed (R is needed even at k_L = k_R). The stated rest position is wrong. |
| engine_start_highidle | 3 | 2 | 4 | 2 | RETHINK | The start-phase rows compare identical dynamics. The +4 row is the equilibrium shift. R exists only because the one-sided SELF row admits a lagging reference. The STARTER_LOW aim 25.5 is tuned to make abort reachable. |

## acc_spoof_lag
- **Model:** a two-state ACC with a first-order lag. The left reads a speed spoofed 25 % high, so it settles at 24 m/s instead of 30; both sides share the 0.1 s period.
- **Property:** at stretch 3/2, the attacked car's speed and dominant-mode speed stay at or below the reference's at 3/2 the elapsed time, with the mode speed 6 m/s lower (row 2 exact).
- **Concern:**
  - The re-timed reading (l.31-32, "never faster than the unspoofed reference at time 3/2 t") is not something a sensor-attack analyst cares about. The meaningful real-time overspeed and shortfall claims (l.33-37, l.55-63) certify at lambda 1 but are relegated to prose.
  - Row 1's constant 0 is loose by 3.33 m/s (l.32-33).
  - tau = 0.375 (l.19-22) is picked so that the slow-root ratio is exactly 3/2, which is what makes row 2 exact.
  - The header is a palimpsest: batch I4/I9 history, two strengthening coordinates u (0.6) and w (0.5), and a "Consequence" paragraph.
  - It duplicates acc_tune_lag's S M pattern in a scenario where re-timing has no requirement behind it.
- **Fix:** make the file's claim the real-time requirement at lambda 1 (v_L <= v_R with the w rows, and the 8 m/s shortfall), accepting letter I. Or drop the file as redundant with acc_tune_lag. Strip the batch history.

## acc_spoof_limp
- **Model:** a first-order speed loop. The left is spoofed CRUISE with a latched LIMP (22 m/s) and a 2 s period. The right is unspoofed NORMAL/ECO/SPORT (27/30/33 m/s) with a 1 s period, plus DISENGAGE.
- **Property:** no faster than the reference (v_L <= v_R), and the closing speed stays below an AASHTO-derived bound (0.7 v_R <= v_L + 4). The row 2 derivation is good.
- **Concern:**
  - Apples and oranges. The left has a fixed 30 m/s set speed, yet it is compared against a driver who may pick ECO or SPORT. The periods differ (2 s vs 1 s).
  - The header admits that no letter comes from the spoof (l.25-31): M and B come from the period, X from LIMP vs ECO above 34.5 m/s.
  - Row 1 is false against a reference driver in ECO above 34.5 m/s (l.39-42). It certifies only because the existential choice hops ECO->NORMAL, which hides a real violation of the stated overspeed requirement.
  - Row 1 is loose by 2.4 (l.51).
- **Fix:** take the reference as the unspoofed controller at the same set speed (NORMAL only, plus DISENGAGE), and either use the same period or justify the period difference as part of the scenario. If driver modes stay, the overspeed claim must quantify the driver on both sides (the same selection), not existentially on the right.

## acc_tune_lag
- **Model:** a lagged ACC loop. The left is retuned to k = 0.75 and the right is stock at k = 0.5. The lag is tau = 0.32 s on both sides.
- **Property:** at stretch 2, the dominant-mode speeds are equal (exact), and |v_L - v_R| <= 3.34.
- **Concern:**
  - tau = 0.32 is "the unique powertrain lag" at which the exact claim holds (l.14-18). At 0.30 it declines and at 0.35 the retune is underdamped (l.22-24): the plant is tuned to the claim.
  - The a-box is load-bearing (l.66-76): widened by 5 % the file declines. Row 3's tight 3.34 is set by clipping guard corners such as (8.6, 28.75), while runs from the engagement box stay in v in [24.87, 30.47] with small |a|.
  - The "1 g tyre limit" defence is physical, but the property hinges on unreachable states that only the domain removes.
- **Fix:** keep the exact modal rows but drop row 3, or bound a in the left guard by an invariant engaged-envelope conjunct rather than through the domain. Alternatively use the physical tau = 0.30 with the measured modal tolerance (0.35 at lambda 7/4) and say why that stretch.

## acc_tune_limp
- **Model:** a first-order speed loop. The left is a tuned CRUISE (0.75) with a latched LIMP map. The right is stock NORMAL/COMFORT/SPORT plus DISENGAGE.
- **Property:** in CRUISE, v_L = v_R exactly at stretch 3/2. In LIMP, v_L <= v_R.
- **Concern:**
  - The CRUISE witness is NORMAL, which is literally the left ODE scaled by 1.5 (l.96 vs l.109). The exact row is the identity of time scaling, so the witness copies the left.
  - The LIMP overspeed row is false against a driver holding SPORT at v in (35, 36] (l.58-61). The committed hop SPORT->NORMAL hides it (NO_CHOICE declines, l.76).
  - COMFORT and SPORT exist to generate B and X.
  - D holds only under the 2026-10-27 "drops a stated row" rule. A uniform v_L <= v_R certifies (l.45-46), and letters.md has no D_strict.
  - Mixing lambda 3/2 in CRUISE with lambda 1 in LIMP means the LIMP comparison is against a time-shifted reference. The header never says what that composite claim means.
- **Fix:** state the composite timing semantics. Either restrict the reference to the mode the tune claims to mirror (NORMAL), or make the driver choice shared, not existential. Report the SPORT counterexample as a finding rather than covering it with X.

## antenna_track_kvretune
- **Model:** a type-1 elevation loop (K = 20 vs 30 /s) over a descending pass at 0.7 deg/s, then a 5 deg/s slew to stow.
- **Property:** pointing within 0.035 deg (a tenth of the 0.36 deg beamwidth) while tracking, and the slew-lag envelope 0.25 deg after LOS.
- **Concern (minor):**
  - TRACK->STOWED (l.107, l.129) is never taken: TRACK ends near c = 5 deg and STOWED needs c >= 90.
  - The TRACK band is 2.8x the tight 0.0125, but that is justified by the requirement.
  - The "Suite status" history (l.75-91) is clutter.

## bottling_fill_strainer
- **Model:** a flowmeter-controlled filler with a clogged strainer (170 vs 200 mL/s), a pre-close at 994 mL and a 40 ms valve closing time.
- **Property:** the predicted final volumes differ by exactly 1.2 mL (tight), with the deployed fill never ahead. This bounds the shortfall within the 2 mL giveaway (Directive 76/211/EEC).
- **Concern (minor):**
  - In FILL the rows reduce to V_L = V_R, u = 1 (a re-timed identity). The content is the CLOSE phase.
  - lambda_min 0.8 is "a stated design value of this benchmark" (l.37-39).

## canal_gate_notches
- **Model:** a linear pool (h' = 0.006 (Q/2 - h)). The left is a three-position deadband controller. The right is a manual rule with four notches, the extremes restricted by level.
- **Property:** |h_L - h_R| <= 0.15 m, the operator's level tolerance; the tight value is 0.10.
- **Concern:**
  - With no turnout withdrawal or inflow disturbance, HOLD's flow toward 0.65 m never leaves [0.4, 0.9). The declared HOLD->RAISE and HOLD->LOWER edges (l.102) are dead, and RAISE and LOWER occur only as start modes.
  - The "law window" analysis (l.39-48) therefore concerns start states only.
- **Fix:** add a withdrawal disturbance (a demand mode or a bounded outflow term) so the deadband law cycles. At minimum, state in the header that HOLD is absorbing.

## charger_fast_tapers
- **Model:** a SoC phase model. The deployed has its CC rate raised 25 % and decides every other cycle. The profile is replayed at 5/4 with a slow or fast taper.
- **Property:** the deployed SoC never exceeds the replayed profile's by more than 1 % (0 % in PRECHARGE).
- **Concern:**
  - At lambda 5/4 the replay is at least as fast in every phase: PRECHARGE 0.25 vs 0.2, BULK 0.125 vs 0.125, tapers 0.0625 and 0.0875 vs 0.05. The bound is a monotone-comparison triviality; the physical lead is 0 (l.55-58).
  - c = 1 is "the tool's tight value, not a physical lead" (l.55, l.60-64), and every c up to 100 certifies. The tolerance has no requirement behind it.
  - D exists only because of that FULL artifact (l.74-76).
  - M and B come from a 2:1 period that is "a design value of this file" (l.40-41).
- **Fix:** rebuild the claim around a requirement, for example an equal-time bound on the deployed lead (the CC-phase 7 % lead, l.58) with a tolerance tied to a cell or BMS limit, or a two-sided re-timed band. Otherwise drop.

## elevator_start_discbrake
- **Model:** a 20 m elevator up-trip. The left has a fast disc brake (k = 50) and the right the original drum brake (k = 5). The brake lift b gates LIFT->UP only.
- **Property:** equal position and speed in every mode up to the reference's lone brake lift; in LIFT, b_R <= b_L.
- **Concern:**
  - b never enters the z, v dynamics. After the lift both sides run the same ODE, so the claim is "the same ODE gives the same motion" with the reference shifted in time, and the witness copies the left.
  - The header concedes that R is needed even at k_L = k_R (l.51-53), so R and D come from the claim form, not from the retrofit.
  - l.17 "rest at about 19.96 m" and l.58 "within 0.1 m of 19.9 m" are wrong. The car arrives at about 0.5 m/s, so z + v/4 is about 20.03 m, past the 20 m landing.
- **Fix:** give the brake a physical role, such as drag torque while b < 1 in UP, so the retrofit changes the motion. Then bound the deviation with a requirement-derived tolerance (levelling accuracy). Correct the rest-position text.

## engine_start_highidle
- **Model:** a turbofan start sequence (STARTER, STARTER_LOW, LIGHTOFF, SELF, IDLE, ABORT). The left aims at 66 % idle, the right at 62 %.
- **Property:** in the start phases the deployed is never ahead and its timer is never behind. Above cut-out the deployed exceeds the reference by at most 4 % N2.
- **Concern:**
  - The start phases have identical ODEs and guards (l.104-120 vs l.144-160), so their rows are the identity witness, stated one-sided.
  - The +4 row is just the equilibrium difference (d' = 0.15 (4 - d)).
  - R exists because the one-sided SELF/IDLE row (l.184-185) admits a reference still in LIGHTOFF behind a deployed in SELF (l.56-59). That is a looseness of the row, not a behaviour of high idle.
  - The STARTER_LOW aim 25.5 (l.111) sits 0.5 % above light-off. It was added on 2026-10-29 to make ABORT reachable, and the hung start from rest exists only for aims below about 26.05.
- **Fix:** state the start phases as exact equality. Bound SELF/IDLE two-sided (0 <= N2_L - N2_R <= 4) and report whether R survives. Justify the low-supply torque limit from a source, or model the hung start through a physical torque-versus-pressure law.

##### Checkable claims
- **acc_spoof_lag, l.115 row 1:** not tight. `v_L <= v_R - 3.33` certifies (header l.32-33), so constant 0 is 3.33 m/s loose.
- **acc_spoof_lag, l.102/110:** row 2 is exact only at a'-coefficient 8/3 (tau 0.375). With 2.5 (tau 0.4) the slow-root ratio is not 3/2, and `u_L <= u_R - 6` at lambda 1.5 should DECLINE.
- **acc_spoof_lag, l.103:** the left guard's corner (v, a) = (6.5, 25.5) lies outside the a-domain [-10, 10]. The guard is far larger than the engaged region (runs stay in v in [22.6, 30.6]).
- **acc_spoof_lag, l.33-37:** the real-time requirement (v_L <= v_R plus the w-strengthening at lambda 1) certifies as its own file. A lambda-1 file with the actual requirement exists.
- **acc_spoof_limp, l.149 row 1 in LIMP:** fails against a reference held in ECO. At v_L = v_R = 36, LIMP gives v' = 0.3 (22 - 36) = -4.2 and ECO gives 0.5 (27 - 36) = -4.5, so v_L overtakes. It certifies only via the ECO->NORMAL hop; RELCERT_NO_CHOICE=1 DECLINES (l.98).
- **acc_spoof_limp, l.127-146:** with Rsys reduced to NORMAL + DISENGAGE (the left's 30 m/s set speed), the file should certify without B and X.
- **acc_spoof_limp, l.113:** with left epsilon 1.0 only I remains (header l.23-24). M and B are period artifacts.
- **acc_spoof_limp, l.148-149 row 1:** not tight. `v_L <= v_R - 2.40` certifies (l.51).
- **acc_tune_lag, l.98/106:** tau = 0.32 (3.125) is a knife edge. At tau 0.30 (3.333...) the exact rows DECLINE (l.22).
- **acc_tune_lag, l.100 (a in [-10, 10]):** load-bearing. Every bound widened by 5 % DECLINES (l.67-69). The left guard corner (v, a) = (8.6, 28.75) of l.99 lies outside the box. Expected: adding a reachable engaged-acceleration conjunct to the left guard (e.g. |a| <= 3) tightens row 3 below 3.34 and removes the domain dependence.
- **acc_tune_limp, l.96 vs l.109:** the CRUISE witness NORMAL is the left ODE time-scaled exactly (0.75 = 1.5 x 0.5). The exact CRUISE row is the time-scaling identity.
- **acc_tune_limp, l.130 LIMP row:** fails against a reference held in SPORT for v in (35, 36]: at 36, SPORT gives 0.6 (30 - 36) = -3.6 and LIMP gives 0.3 (25 - 36) = -3.3. RELCERT_NO_CHOICE=1 DECLINES (l.76).
- **acc_tune_limp, l.113-122:** with COMFORT and SPORT removed from Rsys, the file should certify without B and X.
- **acc_tune_limp, l.129-130 (D):** uniform `v_L <= v_R` in both modes CERTIFIES (l.45-46). D is D_rows only (letters.md, no D_strict).
- **canal_gate_notches, l.102:** HOLD->RAISE and HOLD->LOWER are unreachable from HOLD's flow 0.006 (0.65 - h) on [0.4, 0.9). Non-connection certificates for both edges should exist, and RAISE and LOWER are start-only modes after the first switch.
- **charger_fast_tapers, l.133-171:** at lambda 5/4 every replayed rate is at least the deployed's (0.25 >= 0.2, 0.125 = 0.125, 0.0625/0.0875 >= 0.05). Row `x_L <= x_R` holds by comparison, with physical lead 0 (l.55-58).
- **charger_fast_tapers, l.149/177:** the tight c = 1 equals 100 minus the FULL threshold 99. With the FULL threshold at 99.5 (and the ABSORB guards at < 99.5) the tight c should become 0.5. The constant measures the over-approximation, not the charger.
- **charger_fast_tapers, l.182-184:** every c in [1, 100] certifies (l.60). No requirement fixes c.
- **charger_fast_tapers, l.131/154:** with equal periods (both 0.006 or both 0.012) M and B should vanish. They come from the "design value" 2:1 period (l.40-41).
- **elevator_start_discbrake, l.97/103 vs l.125/131:** the z, v dynamics are identical and independent of b. R is needed even at k_L = k_R (l.51-53), so R and D come from the claim form.
- **elevator_start_discbrake, l.17 and l.58:** APP from (z, v) = (18, 1.6) reaches 19.9 m at t ~ 2.10 s with v ~ 0.50 m/s, so the rest position z + v/4 is about 20.03 m (20.07 m if the switch comes one period late). This contradicts "rest at about 19.96 m" and "within 0.1 m of 19.9 m" (my Euler simulation).
- **engine_start_highidle, l.181-183:** STARTER, STARTER_LOW and LIGHTOFF have identical ODEs and guards on both sides. Exact rows (n_L = n_R, t_L = t_R, p_L = p_R) in those modes should certify, so the one-sided rows state less than the trivial identity.
- **engine_start_highidle, l.184-185:** with SELF/IDLE rows two-sided (`n_R <= n_L` added), check whether RELCERT_NO_REPO=1 still DECLINES. If it certifies, R is an artifact of the one-sided row.
- **engine_start_highidle, l.111/151:** the hung start from rest (n = 5, t = 0) exists only for a STARTER_LOW aim A < (25 - 5e^-3)/(1 - e^-3) ~ 26.05. At aim 26.5 every start from t = 0 with n0 >= 5 lights off within 30 s (26.5 - 21.5e^-3 ~ 25.43). ABORT would again be reachable only from starts whose timer is already advanced, which is the defect the 2026-10-29 revision fixed.

### G2

# Review G2 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

Sources used: docs/review-rubric.md, the ten input.txt files, docs/paper-numbers/matrix.md (rows 15-24, mechanism index 58-66), docs/paper-numbers/letters.md (rows 13-22). Line numbers below are input.txt lines.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| flaps_slow_approach | 4 | 4 | 4 | 4 | POLISH | Hardware-ratio stretch on placard domains with tight 25/10 kt. The 25 kt exceeds the stated 20 kt requirement (disclosed). Stale suite-status note about insulin (l.101-102). |
| fuelcell_chp_dos | 3 | 2 | 4 | 2 | RETHINK | The exact claim is true. 7 K sits in a non-monotone tool-artifact window [5, 8]. The Tin range and the 45 degC floor are tuned so that P and 7 work. |
| furnace_program_timebase | 4 | 4 | 5 | 4 | KEEP | Clean S+I exhibit: exact program rows, a load residual (1-λ)·32 = 6.4 with a tight bisection, and an 8 degC requirement from AMS 2750. |
| gantry_speed_zones | 4 | 3 | 4 | 3 | POLISH | A uniform override is a time reparametrization by construction. The exact claim certifies and so does an arbitrary zone schedule, so the 10 mm rows and the zone logic are not load-bearing. |
| h2_refuel_ambientbias | 3 | 3 | 4 | 3 | POLISH | Plausible bias-to-end-pressure story. The top tolerance 2.9 = 2.4 bias + 0.5 certificate artifact has no requirement behind it, and the stage rows are one-sided where equality holds. |
| hydro_rejection_gatecal | 4 | 4 | 2 | 2 | POLISH | A good D exhibit, but the REJECT speed row in the file is 0.07 (l.124) while the header claims and justifies 0.09 everywhere. |
| insulin_basal_cgmloss | 3 | 3 | 3 | 3 | POLISH | Without a meal input, glucose falls everywhere above 185, so L5-L8 are start-only. The header's "glucose can go either way from every level" is false for L4+. The certificate (20) is about 10x the simulated gap. |
| lit_csf21_vehicle_bus | 3 | 2 | 4 | 2 | RETHINK | The cover never uses the genuine car's thermostat-message modes, so the bus adds nothing over lit_csf21_vehicle_thermo (same constants, claim and letter X). |
| lit_csf21_vehicle_thermo | 3 | 3 | 5 | 3 | KEEP | A faithful literature replica. Non-interference holds by syntax (d, v ignore temp; the right can always pick a thermostat), but that is the source's claim. |
| lit_drl_car_stop | 3 | 2 | 5 | 2 | RETHINK | The sampled form reduces the dRL refinement to a single guard inclusion (Goal 1). The event-triggered content (Goals 2, 3) is gone and the right copies the left. |

## flaps_slow_approach
- Model: an A320-family flap extension CONF 1+F -> CONF 2. The deployed side has one hydraulic motor lost (0.5 deg/s against 1 deg/s), with first-order autothrust deceleration toward F = 150 kt and flap-dependent drag.
- Property: equal flap angle (stretch 1/2 while extending, 1 once set), and the FLAPS SLOW aircraft is at most 25 kt slower or 10 kt faster than the normal one.
- Strongest concern: the requirement cited is a 20 kt window (l.40-46), but the claim states 25 because the placard domain admits selections up to 200 kt. The constant is tight but exceeds the requirement it cites. The lower 10 kt comes from starts below F at VLS (l.38-39), a selection speed the procedure (CONF 2 at S = 185) never uses. These points are disclosed, so they are not fatal.
- C: l.101-102 says insulin_basal_cgmloss is "in the reserve since batch I9", but it is in suite_v2 and in letters.md row 19. The header is also padded with audit history (l.46-50, 82-85, 97-104).
- Fix: delete or correct the suite-status paragraph (l.97-103). Optionally say in one sentence that 25 kt is the envelope and the 20 kt requirement holds only for selections <= 190 kt.

## fuelcell_chp_dos
- Model: a PEM CHP stack at three current levels with a first-order thermal response. The deployed level selection is held 20 s by a DoS attack, against the nondeterministic 10 s maker's protocol.
- Property: |T_L - T_R| <= 7, Tin equal, i.e. the attacked stack stays within 7 K of some protocol-permitted trajectory.
- Strongest concern: the header shows the physical answer is 0. The hold never leaves the band (l.31-37), so the protocol can copy the deployed exactly. The 7 K is therefore not a property of the attack but a point in a non-monotone certificate window ([5, 8] certifies, (8, 10) declines, 10 certifies; l.53-57). Its justification depends on a floor of 45 degC that the file sets itself (l.42-44). P (pruning) also depends on a Tin range that the header admits is a certificate limitation (l.69-80: [36, 56] and [40, 60] decline at 7). In effect the domains are tuned to the claim.
- LOW_L and HIGH_L occur only as starts (l.98-100).
- Fix: make the attack consequential, e.g. move the deployed thresholds to the band edges or use a longer hold so the deployed actually leaves the protocol band. State a tolerance from a real requirement that the certificate meets, or reframe the file as an explicit incompleteness exhibit outside the headline suite.

## furnace_program_timebase
- Model: a first-order program setpoint generator, where the deployed runs at 80 % rate, and a load with a 5 min lag. Segments PREHEAT/HEAT/SOAK.
- Property: exact program rows at λ = 4/5, |T_L - T_R| <= 8 degC, plus stated right-side lag-envelope rows.
- Strongest concern: minor. The AMS 2750 Class 3 tolerance is a spatial uniformity tolerance, used here as a tracking tolerance against the validated profile (l.29-31), which is a reasonable but loose reading. The tightest value is 6.40 (l.41), so 8 has a 1.6 degC margin, justified by the requirement. The cause-sweep (l.44-48) is exemplary.
- Fix: none needed. Optionally reword l.29-31 to say the uniformity class is used as the acceptance band.

## gantry_speed_zones
- Model: two independent first-order axis servos. Production runs zone-scheduled uniform speed overrides (3, 2, 1) against commissioning at override 1.
- Property: per-axis position within 10 mm of the commissioned path, up to a per-zone time stretch.
- Strongest concern: a uniform override that scales both axis gains is exactly a time reparametrization (l.32-33). So the path claim is exact by construction: 0.00 certifies at λmax = 3 (l.42). An arbitrary zone schedule also certifies (l.54-57), so neither the 10 mm rows nor the zone guards carry content. The 10 mm only buys grid robustness. A 300 % override is also unusual: overrides are normally <= 100 % of the programmed speed.
- Fix: make the tolerance load-bearing with real per-axis non-uniformity, e.g. the y axis saturating at its velocity limit under override 3. The header says a non-uniform FREE declines at 0.01 (l.53-54), so measure and state the tolerance that then certifies. At minimum, say up front that the relation is exact and the 10 mm is margin.

## h2_refuel_ambientbias
- Model: a one-state staged-ramp H70 fill. The deployed side's ambient sensor reads 10 K high, so the end pressure is 72.4 against 70.0 MPa.
- Property: stage rows p_L <= p_R; top rows p_L <= p_R + 2.9.
- Strongest concern: 2.9 = 2.4 (bias) + 0.5, where the 0.5 is the certificate's top-off set-point artifact, needed even at zero bias (l.39-48, 55-59). No requirement selects 2.9. The real hazard of a high-reading ambient sensor is overfill (SOC > 100 % at the true gas temperature), and the header only notes "well inside 87.5 MPa" (l.43-44). The stage requirement is one-sided ("may not lead", l.33-38) although the stages are identical, so p_L = p_R holds there physically. The staged ramp is a design of the file, not J2601 (l.20-22).
- Fix: state the top tolerance from an SOC or overfill requirement (e.g. the end-pressure error a 10 K bias may cause under the protocol), and test whether two-sided stage rows certify.

## hydro_rejection_gatecal
- Model: a Francis-type unit with a 0.02-stroke gate-transducer offset. ONGRID uses droop with a fixed grid frequency; REJECT drives the gate to speed-no-load with first-order speed dynamics.
- Property: ONGRID has equal speeds and a gate gap <= 0.027 (3 % power). REJECT has a speed gap <= 0.09 (overspeed margin) and a gate gap <= 0.027.
- Strongest concern: the file's REJECT row uses 0.07 (l.124), but the header states, derives and measures 0.09 (l.31, 36, 43, 50, 61). Either the header or the row is wrong, so the matrix and letters were measured on an unstated claim. Physically, the post-rejection governor has no speed loop (l.18-22, disclosed). The model is otherwise sound, with a strong D argument (l.47-60).
- Fix: make l.124 and the header agree (0.09, or re-derive 0.07) and re-measure the D rule and the tight values.

## insulin_basal_cgmloss
- Model: a basal-only insulin pump with a 9-level glucose table and a minimal-model glucose. The CGM drops every other reading (10 min hold against 5 min).
- Property: |G_L - G_R| <= 25 mg/dL, |X_L - X_R| <= 0.5 U/h, equal need b.
- Strongest concern: without a meal or glucose-appearance input, the steady state is 120 + 50(b - X) <= 185. Glucose therefore strictly falls for G >= 185, so L5-L8 (G >= 190) are entered only as starts and every upward edge from L4 up is unreachable. The header's "from every level the glucose can go either way" (l.47-50) is false above L3, so part of the branching is time-free over-approximation. The two-level deployed successors (l.28-30) exist only from L8, and the other two-level edges are unreachable within a 10-min hold. The 25 mg/dL requirement holds only "at the validated loop's settling points" (l.35-38). The certificate's 20 is far from the simulated 1.4 mg/dL gap (l.61-63). Unit slip: "50 mg/dL per U" (l.14) multiplies a U/h difference.
- Fix: add a bounded meal disturbance (or a constant appearance term in [0, d]) so the high levels are reachable from ordinary runs, or say that L5-L8 are start-only. Correct l.47-50 and l.14.

## lit_csf21_vehicle_bus
- Model: the CSF'21 car plus thermostat sharing one bus message per cycle. The attacked car has 6 modes; the genuine car has 12 (action x setting x message type).
- Property: d and v equal at every instant (thermostat attack non-interference).
- Strongest concern: per the header (l.50) the genuine car never needs a thermostat-message mode, so the cover uses only the six xtA modes. Those carry no temperature guard, so the genuine thermostat logic is irrelevant to the proof. Same constants, claim, letter X and cover idea as lit_csf21_vehicle_thermo. The bus (the source's point, Fig. 11-12) imposes nothing that the thermo file does not.
- Fix: model the bus effect that differs from thermo, e.g. a thermostat message occupying the slot that delays an acceleration change by one cycle, with a tolerance claim on d and v. Otherwise drop it as a duplicate of the thermo file.

## lit_csf21_vehicle_thermo
- Model: the CSF'21 car (A = B = 1, eps = 1, psi guard) with an attacked cabin-temperature reading, plus Coast at v <= 1 and a 40 m/s cap.
- Property: d_L = d_R and v_L = v_R at every instant.
- Strongest concern: the claim holds by syntactic independence. The d and v ODEs do not read temp, the action guards are identical, and for every temp at least one genuine setting is enabled, so the witness copies the left's action. That is the source's own claim, so the score reflects the source. temp' = ±1 degC/s is unphysical but irrelevant. Departures are well stated (l.42-57).
- Fix: none required.

## lit_drl_car_stop
- Model: sampled car stop-line controllers. The deployed uses the time-triggered Safe_eps; the reference uses Safe tested at each sample; the plants are identical.
- Property: identity refinement (x and v equal).
- Strongest concern: with identical plants and periods, the claim reduces to Safe_eps => Safe on v >= 0 (l.36-41), a single implication (2v + 1 >= 0). The right copies the left. The dRL content (an event-triggered plant with runs of any length, Goals 2 and 3) is not represented (l.31-38).
- Fix: represent the event-triggered side's freedom, e.g. a right side with a variable period via a stretch range or a right-only reposition, so that Goals 2 and 3 enter the obligation. Otherwise relabel it as a guard-inclusion sanity check, not a dRL reproduction.

##### Checkable claims
- fuelcell_chp_dos: the exact claim (rows at l.164-166 with 7.0 -> 0.0) is semantically true. A 20 s hold keeps each held level inside its protocol band (header l.31-37), so the 7 K is a certificate artifact.
- fuelcell_chp_dos: constant 7.0 (l.164-166) is not tight; 5.00 certifies (l.48), and 8.5 declines while 10 certifies (l.53-57).
- fuelcell_chp_dos: the Tin domain [40, 56] (l.125-160) is load-bearing for the claim. At 7, Tin in [36, 56] and in [40, 60] DECLINE (l.69-72).
- fuelcell_chp_dos: LOW_L and HIGH_L (l.123-127, 135-139) are unreachable from MED_L, since MED_L is forward invariant (l.98-100), so they are start-only.
- gantry_speed_zones: the 0.01 rows (l.118-120) are not tight at λmax = 3; 0.00 certifies (l.42, 74).
- gantry_speed_zones: the zone guards (l.91, 97, 103) are not load-bearing. With every left guard = workspace and every mode a successor of every other, the file CERTIFIES (l.54-57).
- h2_refuel_ambientbias: the top rows p_L <= p_R + 2.9 (l.179-180) include 0.5 MPa that the certificate needs at zero bias. At s = 0 the tightest value is 0.50 (l.54-59).
- h2_refuel_ambientbias: test whether two-sided stage rows p_L = p_R on STAGE1-3 (l.176-178) certify. The stages are identical (l.111-127 vs 145-161).
- hydro_rejection_gatecal: the REJECT speed rows in the file are 0.07 (l.124), while the header states 0.09 (l.31, 36-37, 43, 50, 61).
- insulin_basal_cgmloss: for G >= 185, G' = (120 + 50(b - X) - G)/60 < 0 for all X in [0, 1.6] and b in [0.5, 1.3] (ODEs l.98-146). So the edges L4->L5, L5->L6, L6->L7, L7->L8 (left next l.125, 131, 137, 143; right l.183, 189, 195, 201) are unreachable, and L5-L8 are reachable only as starts.
- insulin_basal_cgmloss: the two-level edges SUSP_L->L2 (l.101), L1_L->L3 (l.107), L3_L->L1 (l.119) and L4_L->L2 (l.125) are unreachable within a 10-min hold. Example: from G < 70, G(10) <= 185 - 115·e^{-1/6} ≈ 87.6 < 100. Only L8_L->L6 is reachable, contradicting l.28-30's "reach two levels" as a general statement.
- insulin_basal_cgmloss: the header's "from every level the glucose can go either way" (l.47-50) is false for L4-L8, where upward motion is impossible.
- insulin_basal_cgmloss: the certified tightest value (G 20, X 0.4, l.40) is about 14x the simulated worst gap of 1.4 mg/dL at 10 min (l.61-63).
- lit_csf21_vehicle_bus: the cover uses no xtT right mode (header l.50). With the six *T right modes (l.119-123, 131-135, 143-147, 155-159, 167-171, 179-183) removed, the file still CERTIFIES with the same cover.
- lit_csf21_vehicle_thermo: for every temp, AccCool_R (temp >= 20, l.129) or AccHeat_R (temp <= 20, l.135) is enabled whenever psi holds, and likewise for Coast and Brk. The d and v ODEs (l.88-120, 128-160) do not read temp, so the identity rows hold by syntactic independence.
- lit_drl_car_stop: the left Accel guard (l.86) implies the right Accel guard (l.104) on v >= 0, since 2v + 1 > 0. Coast and Brake are identical on both sides (l.89-98 vs 107-116), so the claim is guard inclusion over identical plants.

### G3

# Review G3 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

Sources used: the ten `input.txt` files, `docs/paper-numbers/matrix.md` (rows 25-34 and the detail
sections), `docs/paper-numbers/letters.md`. Line numbers below are `input.txt` lines.
The mechanism letters in letters.md agree with every header (drl_lane X, freedm X, girard X,
lz21 X, nahs I, latency none, linkloss M, profiles S M, quad_lag S M, quad_profiles S M B X), and
the matrix cells (M1/M2/M3/M6/M6+) agree with them.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| lit_drl_lane_control | 3 | 2 | 4 | 2 | RETHINK | identity refinement with identical ODEs and weaker right guards: the copy witness is immediate, the only content is Safe_eps => Safe; unguarded Coast lets the follower collide; 3-valued leader declines unexplained |
| lit_freedm_meter | 3 | 3 | 5 | 3 | KEEP | faithful to Prop. 11, but the secret B occurs in no grid guard, so security is immediate and the right's six battery modes are dead weight |
| lit_girard08_robot | 4 | 3 | 5 | 3 | KEEP | relational part is an exact copy (w_L = y2_R); the content is a robot-only Lyapunov sublevel (tight 0.16), which is the source's structure; certified abstraction weaker than Fig. 3 (disclosed) |
| lit_lz21_vehicle_position | 3 | 2 | 4 | 2 | RETHINK | right = left, witness copies the input, rows certify for every offset; the opacity content (partner non-secret) is not in the claim |
| lit_nahs25_salt_tank | 4 | 4 | 5 | 4 | KEEP | source model exactly, tight distance 3, I letter genuine; only nit: the genuine Off is excluded by the rows |
| platoon_latency | 4 | 4 | 4 | 4 | KEEP | derived and bisected tolerance J tau / kp, convex jerk extremes; header cluttered with round history |
| platoon_linkloss | 3 | 4 | 3 | 3 | POLISH | ACC law drops a_pred (cruising lead assumed silently), so link loss is only a 20 -> 35 m set-point switch; M exists only by the 0.2/0.1 period ratio |
| platoon_profiles | 3 | 3 | 4 | 3 | POLISH | SPORT kd 0.85 chosen to break the exact re-timing; S is a framing choice (a lambda-1 tolerance exists and is not reported); tolerance scales with the |r| <= 10 domain |
| quad_light_lag | 3 | 4 | 4 | 3 | POLISH | the feedback K w bypasses the motor lag (only the set-point thrust is lagged), a non-physical loop; Psi band tight, row 1 slack |
| quad_light_profiles | 4 | 3 | 3 | 3 | RETHINK | B and X come from ECO/SPORT modes that are start-only for the witness (removing them leaves S M), the pattern removed from platoon_* in round 4; rows 1-3 not loaded |

## Per benchmark

**lit_drl_lane_control.** Follower/leader on a lane, three states (gap, two speeds), six
(follower, leader) action modes per side; left guards Accel by Safe_eps, right by the weaker Safe.
Property: identity relation (dRL refinement as reachability inclusion). Strongest concern: with
identical ODEs and left guards contained in right guards (82 vs 115, 87 vs 120), the copy witness
is a one-line argument; the rubric's "witness trivially copies the left" applies in full, and the
tool-level content is only Safe_eps => Safe (header 43-44 admits Goals 2, 3 are not represented).
Physics: Coast (92, 97) has no gap guard and braking is forbidden below 1 m/s (102), so the
modeled follower can drive into the leader, which neither FM 2011 nor dRL allows. The
three-valued leader declining with "cause not identified" (32-34) on what should be the same
trivial copy is an open incompleteness. Fix: either reframe as a pure literature row (not a
mechanism exhibit) and diagnose the 9-mode decline, or give Coast a gap guard (Safe at a = 0) and
let the follower brake from any v_f > 0 so the model is collision-free like the source.

**lit_freedm_meter.** Battery/grid source selection with discrete demand and renewable inputs;
public meter E, secret battery level B. Property: nondeducibility, E_L = E_R from every pair of B
levels. Concern: every grid mode's guard is B >= 0 and B <= 10 (163-192), so for each left meter
rate in {-1, 0, 1, 2} a B-independent grid mode exists; the header itself says the grid-only right
certifies (46-47). This is exactly the source's argument, so the claim is faithful but shallow; the
leaky negative counterpart is what gives it teeth. Units of B, E, d, r are abstract (1 unit/period).
KEEP; optionally drop the right battery modes or state that they are never used by the witness.

**lit_girard08_robot.** 6-D robot with dynamic tracking controller (error coordinates) vs 2-D
planner point mass, six hexagon locations. Property: w_L = y2_R plus e^2 + 100 z^2 <= 0.16 on the
robot, i.e. |y1 - y2| <= 0.4. Concern: the relational rows are a copy (w' = v identical in matched
modes, 107 vs 147), and the non-trivial row (183) mentions only left variables; it is a unary
invariant of the robot. That is the source's simulation function (second term 0), and the tight
0.16 / 0.1599 evidence is good. The planner is more permissive than Fig. 3 (63-64), disclosed.
KEEP.

**lit_lz21_vehicle_position.** Double integrator with three input levels on both sides.
Property: v_L = v_R and x_R = x_L + 1 forever. Concern: Rsys is a verbatim copy of Lsys (98-114 vs
120-136); the header admits every offset certifies (31-34), so the claim is translation
invariance under a copied input. The opacity content (the partner starts outside Xs = [0, 1]) is
not stated anywhere in the rows, and the source's position bound 10 is dropped (38-51). Fix: add
the row x[r] >= 1.0 (partner non-secret, invariant since v >= 0) so the claim carries the opacity
requirement, and list the file as a literature reproduction only, not as an X exhibit.

**lit_nahs25_salt_tank.** Brine tank, attacked controller (reading in [xp-3, xp+3]) vs genuine.
Property: |xp_L - xp_R| <= 3 with both >= 25. Tight 3.00 / 2.99, lower side slack (0 suffices,
stated 31-32). Flow and guards are the source's Fig. 7 exactly. Nit: the lower-bound rows exclude
the genuine Off (99) altogether, so that mode is never entered (stated 60-61). KEEP.

**platoon_latency.** CACC follower with lagged feed-forward error e driven by predecessor jerk
+-J, vs ideal-link CACC. Property: |Delta g| <= J tau / kp = 4, two modal forms, deployed gap/TTC
floors, |e_L| <= 0.5. Constants derived and bisected, scan over tau given (82-88), domain widening
robust. Concern: no mechanism letter, so it is a baseline tolerance row; the header carries round
history (6-10, 75-80, 90-106) that a reader does not need. KEEP (optionally trim history).

**platoon_linkloss.** Deployed follower switching CACC <-> radar ACC on link loss (0.2 s
decisions) vs CACC (0.1 s). Property: 0 <= Delta g <= 15 = (h_a - h_c) v_ref plus modal forms and
floors. Concern: the ACC has no feed-forward, so its true law is r' = a_pred - kp (g - 35) - 0.75 r;
line 125 drops a_pred, which is right only if the predecessor never accelerates (line 16 says the
lead cruises, but line 22 writes the CACC with a general a_pred). Under that assumption the link
loss has no disturbance effect and the benchmark is a set-point switch between two equilibria with
no overshoot. M is by construction of epsilon 0.2 (118), disclosed. Fix: state a_pred = 0 at the
ACC explicitly, or (better) add bounded predecessor-acceleration modes to ACC_L as in
platoon_latency and re-derive the tolerance (it should grow by A / kp).

**platoon_profiles.** SPORT CACC (kp 0.18, kd 0.85) vs NORMAL (0.125, 0.75), compared at
stretch 6/5. Property: |Delta g| <= 3.34 at re-timed instants, two modal forms, floors. Concern:
kd = 0.85 is chosen so the exact re-timing fails (12-16), i.e. tuned to create tolerance content;
"critical damping" is a post hoc label (ratio 1.002). Both loops share the equilibrium (20, 0),
so a real-time (lambda 1) tolerance also exists; the header reports only that SYNC declines at
the stated constants, not what lambda 1 would need, so the value of S is unquantified. The
tolerance is set by the |r| <= 10 domain (93-97). Fix: report the bisected lambda-1 tolerance next
to the lambda-6/5 one (that comparison is the argument for S), and cite a source for the SPORT gains
or derive kd from a stated spec.

**quad_light_lag.** Climb loop of a lighter and a reference quadrotor, both with a 0.1 s motor lag.
Property: |h_L - h_R| <= 0.8 (PX4 altitude radius) at t vs 1.2 t, plus a conserved steady-climb gap
Psi in [-0.45, 0.45]. Concern: the model lags only the set-point thrust while K w acts unlagged
(16-19, 102, 110): in a real multicopter the whole thrust command goes through the ESC/motor lag.
Psi is conserved for any stable linear loop at the terminal-rate ratio, so the physical model is
within reach. Row 1 slack (0.67), Psi band tight (0.45 / 0.46), the stretch derived. Fix: model
w' = a, a' = 10 (a_cmd - k w - a) per airframe, rebuild Psi, re-bisect.

**quad_light_profiles.** Lighter quadrotor at the NORMAL set point vs a reference with three pilot
profiles, compared at stretch 6/5. Property: |Delta h| <= 0.8, Psi <= 0.8, 1.2 w_R <= w_L,
w_L <= 2.4. Concern 1: ECO and SPORT are never run by the witness; they exist only as right starts
that the cover hops out of (84-89), and removing them leaves S M. B and X are therefore produced by
start-only modes, the same pattern round 4 removed from platoon_* (AEB start-only D letters).
Concern 2: rows 1-3 are not loaded by the dynamics (73-79: row 1 certifies at 0.00, rows 2, 3 at
any common constant >= 0.0163), so 0.8 is a start-set width, not a tolerance. Fix: either drop
ECO/SPORT (S M, then the file duplicates quad_light_lag's letters) or give the left a pilot
profile switch too (left modes ECO/NORMAL/SPORT on the light airframe), so the reference must
follow the left's selection and B/X come from runs, not starts.

##### Checkable claims

- lit_drl_lane_control, lines 115/120 vs 82/87, 144-149: replacing the right's Accel guards by the
  left's Safe_eps (Rsys = Lsys) still CERTIFIES with the same cover; the certificate uses nothing
  beyond guard inclusion and the copy hop.
- lit_drl_lane_control, lines 92, 97, 102: the left reaches d < 0 from a Safe_eps start
  (d = 3.5, v_f = 1, v_l = 0): the follower Coasts at 1 m/s while the leader alternates
  AccelL/BrakeL around 0.5 m/s; no mode can brake at v_f < 1 and Coast has no gap guard.
- lit_drl_lane_control, lines 32-34: the nine-mode variant with leader {A, 0, -B} should certify
  by the same copy argument; its DECLINE at AccelLCoast is a tool or encoding incompleteness to
  diagnose (e.g. RELCERT_DEBUG=1 on that mode).
- lit_freedm_meter, lines 163-192 and 46-47: no right grid guard mentions B beyond the box; a right
  model with the six grid modes only CERTIFIES (header), so the six right battery modes (133-162)
  are never used by the witness.
- lit_girard08_robot, line 183: the conjunct ex^2 + ey^2 + 100 (zx^2 + zy^2) <= 0.16 is inductive for
  the robot alone (a unary invariant under each of the six headings); the w rows hold by copy
  (wx', wy' identical in matched modes, 107-137 vs 147-177).
- lit_lz21_vehicle_position, lines 98-136, 139-141: Rsys is identical to Lsys and the rows certify
  for every offset (header 31-34); adding the row x[r] >= 1.0 (partner outside Xs) CERTIFIES since
  v >= 0 makes it forward invariant.
- platoon_linkloss, line 125 (ACC r'): adding predecessor-acceleration modes a_pred = +-A to ACC_L
  (r' += a_pred, CACC unchanged since the feed-forward cancels it) makes 0 <= Delta g <= 15 (138-139)
  DECLINE; the upper constant must grow by about A / kp.
- platoon_linkloss, line 118: with epsilon 0.1 on the left the file certifies with no letter
  (header 8-9): M is a property of the stated period ratio only.
- platoon_profiles, line 125: with kd 0.9 the exact rows certify (header 13-15); kd 0.85 is a
  detuning chosen to make the tolerance non-trivial.
- platoon_profiles, lines 118-119, 138: at lambda_min = lambda_max = 1 the same row shapes certify
  with some |Delta g| bound c < 60 (the real-time disturbance is about 0.055 (g_R - 20) + 0.1 r_R,
  suggesting c near 18 m); this number is what S buys and is not reported.
- platoon_profiles, lines 93-97: with |r| <= 14 the stated rows DECLINE and the scaled ones certify:
  every constant of row 138 is a function of the rated closing-rate bound.
- quad_light_lag, lines 102, 110: with the full command lagged (w' = a, a' = 10 (a_cmd - k w - a),
  a_cmd = 14.715 / 9.81 rescaled to the hover-plus-set-point thrust) a rebuilt Psi is conserved at
  lambda 6/5 and the 0.8 rows should certify.
- quad_light_lag, line 115: row 1 (h_R - h_L <= 0.8) certifies down to 0.67 (header 64); only row 2
  is tight.
- quad_light_profiles, lines 145-154: ECO and SPORT are start-only for the witness; deleting both
  modes CERTIFIES with letters S M only (header 87), so B and X are artefacts of right starts.
- quad_light_profiles, line 156: row 1 certifies with constant 0.0, and rows 2 and 3 with any common
  constant >= 0.0163 (header 74-77): 0.8 is not a dynamics-produced gap.

### G4

# Review G4 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

Sources used: the rubric, the ten input.txt files, matrix.md and letters.md (rows grepped). Line numbers below are input.txt lines.
Letters/matrix agreement: all ten headers agree with letters.md and the matrix cells (reactor M B P = M2 M3 M4; ladder 2to3/3to6 none; 6to8/8to12 S M I = M1 M2 M6; patrol S M R B = M1 M2(+RO) M3; terrain_2to4 S M I = M1 M2 M6; 4to6/6to12 I = M6; sat M I X = M2(+choice) M6, M4 vacuous). No C deduction for mismatches; C deductions below are about content.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| reactor_feed_wireless | 3 | 3 | 4 | 3 | POLISH | Good sampling-rate scenario, but the van 't Hoff argument for 8 K cites T-dependent kinetics the linear model lacks; 8 K equals the tightest value (moved from 9 on 10-29) and is ~9x the simulated 0.87 K gap |
| rover_ladder_2to3 | 3 | 3 | 4 | 3 | KEEP | Honest rung with no mechanism; clearance follows from a one-line comparison (same v loop, s'_L <= v) |
| rover_ladder_3to6 | 3 | 3 | 4 | 3 | POLISH | The "new channel" pitch row is a unary left invariant that the clearance rows do not need; psi_L = psi_R is an identity row |
| rover_ladder_6to8 | 3 | 2 | 4 | 2 | POLISH | LTR row implied by the heading and roll rows (header admits it); heading rows "any value certifies" (the reason 2to3 dropped its heading row); S/I come from the plan-tolerance claim form, not the step |
| rover_ladder_8to12 | 3 | 3 | 4 | 3 | POLISH | Rows are meaningful (LTR not implied, lane tight 0.20), but "lane" bounds only the tire-slip offset y and ignores cross-track drift from heading; S/I from claim form; 31 s of a 40 s budget |
| rover_patrol_lag | 3 | 2 | 4 | 2 | RETHINK | All four letters S M R B come from the 1 m slack and appear unchanged in the no-lag twin; lambda_max 3/2 is "not a mission requirement" (15/11 rounded); order property with the plan advanced alone |
| rover_terrain_2to4 | 3 | 3 | 4 | 3 | POLISH | lambda up to 2.7 is derived from the worst start the rows admit (tight 2.64), and a stronger real-time form certifies; the re-timed form is "chosen as the chain's exhibit" |
| rover_terrain_4to6 | 3 | 3 | 4 | 3 | POLISH | Heave row zh_L <= 0.15 bounds an output-only coordinate (no feedback into v, s, w): the same reason 6to12 deleted its pitch rows |
| rover_terrain_6to12 | 3 | 3 | 3 | 3 | POLISH | "12-DOF" is padded: ax, phs, omega_phs feed nothing and no row reads them; zh/vz heave rows output-only as in 4to6 |
| sat_detumble_phases | 3 | 3 | 4 | 3 | POLISH | Exact energy equality is a textbook identity (couplings do no work) that holds only for isotropic damping, which the header says was chosen because the claim needs it; SAFE unreachable |

## Per benchmark

**reactor_feed_wireless.** Model: a 4-level feed interlock on a first-order jacket-cooled reactor, T' = 0.1 (p + 4k - T). The deployed side reads temperature every 2 min and the design side every 1 min.
Property: the deployed temperature stays within 8 K of a validated run from the same state, with equal coolant temperature.
Strongest concern: the requirement argument (l.34-37, a factor of 2 per 10 K in reaction rate) relies on temperature-dependent kinetics. The model has none: the heat release 4k is independent of T (l.124-142), so "exothermic" acts only through the interlock. The stated 8 K is exactly the tightest certifying value and was lowered from 9 K on 10-29 (l.40-41). The certified window is non-monotone ([8, 10] certifies, 10.01-11.99 declines, l.42-43), and the simulated worst gap is 0.87 K (l.70). So the tightness evidence describes the uniform-band certificate shape, not the plant. Minor: l.1 says "continuous stirred-tank", l.23 says "batch sequencer".
Fix: tie 8 K to a requirement the model can express, or say plainly that it is the tool's tightest band. Add the 0.87 K vs 8 K gap to the claim summary. Make CSTR vs batch consistent.

**rover_ladder_2to3.** Model: the L3 rover (decaying heading error psi with along-track loss v(1 - psi^2/2)) against the L2 point model, over three odometer zones.
Property: the rover is never faster than and never ahead of the point model (offset 0 is structural).
Strongest concern: the property is nearly immediate. In a shared zone, d(v_R - v_L)/dt = -0.5 (v_R - v_L) and s'_L <= v_L <= v_R = s'_R. Behind the reference, set points only rise. No mechanism is exercised, and the right psi is a dead coordinate. It is acceptable as the first rung. Removing the heading row (l.54-60) was correct.

**rover_ladder_3to6.** Model: L6 (pitch/heave/roll suspension, slip and crabbing losses in s') against L3.
Property: clearance, plus psi_L = psi_R, plus |theta_p_L| <= 0.25.
Strongest concern: the pitch row (l.51-55) is a single-system invariant of the left. At theta_p = 0.25, theta_p' <= -0.25 + 0.15 + 0.075 < 0 for z <= 0.15, so it is not relational. The clearance rows do not need it: with psi equal, s'_L <= s'_R pointwise. The psi row is an identity: identical loops, synchronous cover (l.48-50). Heave has no terrain input (z' = -z), so the "load-bearing" z <= 0.15 (l.69-73) only restricts the start.
Fix: label the pitch row as a unary requirement carried alongside the relational clearance claim, and state that the clearance rows certify without it.

**rover_ladder_6to8.** Model: L8 (second-order yaw and pitch in the cascade chart) against L6, with a timetable re-timing <= 1.25 (cover 11/10).
Property: clearance against the re-timed reference; |psi|, |omega_psi| <= 0.35; |theta_p|, |omega_theta| <= 0.25; |phi_r| <= 0.2; LTR <= 0.8; plan tolerances on the right.
Strongest concern, three items:
- The LTR row is implied by the other rows (l.61-65: 8 x 0.7/9.81 + 0.2 = 0.771 < 0.8).
- The heading rows "certify at any value (0.05 tested)" because the loop contracts (l.54-55). This is exactly why 2to3 deleted its heading row (2to3 l.54-56), so the two files apply opposite policies.
- S and I persist with the left ODEs replaced by the right's (l.7-9, l.88-90). The headline mechanisms therefore come from the plan-tolerance rows, which admit a worst-attitude reference beside a level rover, not from the refinement.

Fix: drop the LTR row, or state it at its tight 0.22 against a requirement. Justify keeping the heading rows (they are load-bearing for roll through a = v r), or align the policy with 2to3. Report S as claim-form-driven in the paper's mechanism table.

**rover_ladder_8to12.** Model: L12 (heave/roll inertia and tire slip y) against L8, with re-timing 11/10.
Property: clearance, heading, roll (tight 0.15), LTR including slip (tight 0.35, not implied), lane |y| <= 0.25 (tight 0.20), and plan tolerances equal to 6to8's left rows.
Strongest concern: the lane requirement (l.65-68) bounds only the slip offset y. The model has no cross-track state, although a heading error of 0.35 rad at 8 m/s drifts sideways at about 2.8 m/s, which dwarfs the 0.25 m margin. So "lane" overclaims. S/I again come from the claim form (l.7-9, l.91-93). The run takes 31.4 s (matrix) to 33 s (l.136) of the 40 s default budget, which is fragile.
Fix: rename the row to a slip-offset requirement, or add a cross-track coordinate e' = v psi. Note the timing headroom.

**rover_patrol_lag.** Model: a rover with a first-order motor lag (tau = 3/16 s, chosen to make the roots rational) against its lag-free planning model, with the same zone planner.
Property: in matched runs (plan re-timed by up to 3/2 and advanced alone), the rover is never more than 1 m ahead (tight 0.75), with a look-ahead-odometer strengthening.
Strongest concern: by the header's own cause test (l.7-10, l.85-91), every mechanism letter comes from the 1 m slack and not from the lag. lambda_max is "not a mission requirement" and is 15/11 rounded up to make it certify (l.79-81). The certified statement is an order property in which the plan may be advanced alone. The lag contributes only the 0.75 m number.
Fix: restate the claim so the lag drives it. Either use the exact offset-0 rows with an explicit lag allowance at lambda 1, or tie the slack to same-zone starts so SYNC can certify. Alternatively, retitle the file as a claim-form exhibit and stop presenting it as a lag refinement.

**rover_terrain_2to4.** Model: the 4-DOF rover (wheel loop, soil traction, drag, sinkage) against the no-slip plan, over MUD/GRAVEL/PAVED.
Property: never faster or ahead of the plan re-timed by lambda <= 2.7, plus the slip window [0, 0.25] (tight 0.21, analytic).
Strongest concern: the plan clock may run 2.7x faster. That value is the worst admitted pre-slip start's rate ratio rounded (tight 2.64, l.92-101), so the allowance is derived from the claim's own start set. Adding one auxiliary row gives a stronger real-time form that certifies at lambda 1 (l.104-106). The header says the re-timed form was "chosen as the chain's exhibit" (l.11). The compaction term subtracts zs (in wheel radii) directly from the acceleration (l.38-39), which is ad hoc but stated.
Fix: make the real-time form the claim, or give the 2.7 allowance an operational source (for example a planner re-initialized from visual odometry) and present it as the requirement rather than as a derived ratio.

**rover_terrain_4to6.** Model: adds the drive's lagged command u and a heave envelope zh' = rho_T v - zh to the 4-DOF terrain model.
Property: clearance, slip window (tight 0.21), heave zh_L <= 0.15 (tight 0.13), and three auxiliary orderings.
Strongest concern: zh is output-only. It appears only in its own ODE (l.89, 95, 101) and never in v, s, w, u or zs. The heave row (l.29-30) is therefore a unary left bound with no relational content, which is the stated reason 6to12 deleted its body-pitch rows (6to12 l.50-55). The I letter and clearance rows are fine.
Fix: drop the zh row, or label it as a unary requirement consistently in both files.

**rover_terrain_6to12.** Model: adds the ramp grade, chassis pitch (with a slope load on v), second-order heave, and a filtered body acceleration driving squat pitch.
Property: as 4to6, plus u_L <= u_R and vz_L <= 0.15. Sigma is tight at 0.24.
Strongest concern: ax, phs and omega_phs (l.110) feed no other coordinate, and since 10-29 no row reads them (l.50-55). The model is effectively 9-DOF for the claim, yet matrix and letters report dim 12/12. The zh/vz rows are output-only, as in 4to6. Grade and pitch are genuine: they enter v' and raise the tight sigma from 0.21 to 0.24.
Fix: remove the dead squat-pitch chain or report the effective dimension. Treat the heave rows as in 4to6.

**sat_detumble_phases.** Model: gyrostat Euler equations with isotropic rate damping against a decoupled design model. DETUMBLE/FINE phases are decided every 2 s on the flight side and every 1 s on the design side.
Property: E_L = E_R exactly (tolerance 0) in matched phases.
Strongest concern: both sides obey E' = -2kE (l.37-40), so the claim is the textbook fact that gyroscopic terms do no work, plus phase matching. It holds only because damping is isotropic, which the header says was chosen because the claim needs it (l.23-29). With realistic magnetorquer x/y gains the claim is false. The stylized gains (l.30-35) are not load-bearing (they also certify scaled down by 1000). The right SAFE mode is unreachable (pruned, NO_PRUNE certifies, l.97-99).
Fix: justify isotropic damping by a real actuator set (three wheels, as in sat3w) rather than "x, y actuators at wheel authority". State that SAFE is unreachable from invariant pairs.

##### Checkable claims

- reactor_feed_wireless l.124-142 vs l.34-37: the model's heat term p + 4k is independent of T, so the van 't Hoff rate argument has no counterpart in the dynamics (inspection).
- reactor_feed_wireless l.42-43, l.70: tolerance 10.5 DECLINES while 8.0 and 12.0 CERTIFY. The certified 8 K is about 9x the simulated worst gap of 0.87 K. A per-(left, right)-level row set may certify a band below 8.
- reactor_feed_wireless l.40-41: the stated value 8.00 equals the tightest certifying value (7.99 declines), and the requirement was changed from 9 to 8 on 2026-10-29.
- rover_ladder_2to3 l.107/129, l.147-149: in a shared zone, (v_R - v_L)' = -0.5 (v_R - v_L) and s'_L <= v_L <= v_R = s'_R. The rows are preserved by a one-line comparison argument.
- rover_ladder_3to6 l.149-151: deleting the pitch conjunct |theta_p_L| <= 0.25 still CERTIFIES. With psi_L = psi_R, s'_L <= s'_R pointwise.
- rover_ladder_3to6 l.51-53: |theta_p_L| <= 0.25 is inductive for the left alone (theta_p' <= -0.025 at theta_p = 0.25 for z <= 0.15), so it is a unary invariant.
- rover_ladder_6to8 l.61-63, l.194-196: the LTR conjunct is implied by |omega_psi - psi| <= 0.7, v <= 8 and |phi_r| <= 0.2 (bound 0.771 < 0.8). Removing it leaves the verdict unchanged.
- rover_ladder_6to8 l.54-55 vs rover_ladder_2to3 l.54-56: the heading rows are start restrictions of a contracting loop (any bound >= 0.05 certifies), the same pathology for which 2to3 removed its heading row.
- rover_ladder_6to8 l.7-9, l.88-90 and rover_ladder_8to12 l.7-9, l.91-93: with the left ODEs replaced by the right's, RELCERT_SYNC=1 still DECLINES. S does not come from the refinement step.
- rover_ladder_8to12 l.65-68, l.161: no cross-track coordinate. |v sin psi| reaches about 2.8 m/s within the heading row, so the lane margin of 0.25 m is not a lane-keeping claim.
- rover_ladder_8to12 l.136: CERTIFIED at 31.4-33 s against the 40 s default budget, so a 25 % slower machine may DECLINE.
- rover_patrol_lag l.7-10, l.85-91: the no-lag twin with this file's rows yields the same letters S M R B and the same covers.
- rover_patrol_lag l.79-81: lambda_max 1.25 DECLINES, and 3/2 is 15/11 rounded with no stated requirement behind it.
- rover_terrain_2to4 l.92-101: lambda_max 2.64 CERTIFIES and 2.63 DECLINES. The allowance equals the rate ratio from the worst start that the slip row admits.
- rover_terrain_2to4 l.104-106: adding w[l] <= v[r] certifies at lambda 1 under RELCERT_SYNC=1, a strictly stronger real-time claim on its start set.
- rover_terrain_4to6 l.89/95/101, l.129-131: zh appears in no ODE but its own. Deleting the conjunct zh[l] <= 0.15 leaves the other rows certifying.
- rover_terrain_6to12 l.110-122, l.150-152: ax, phs and omega_phs are read by no other ODE and no row. Deleting them (dimension 9) leaves the verdict unchanged, so matrix "dim 12" overstates the model.
- rover_terrain_6to12 l.150-152: zh and vz are output-only. Deleting zh[l] <= 0.15 and vz[l] <= 0.15 leaves the remaining rows certifying.
- sat_detumble_phases l.37-40, l.137-158: on both sides, in each phase, (sum J_i w_i^2)' = -2k (sum J_i w_i^2) holds identically. The relation reduces to a scalar identity plus phase agreement.
- sat_detumble_phases l.23-28: with non-isotropic gains (x, y at 5e-4, z at 0.5) the claim is false (E_L - E_R = +0.067 at t = 2 s).
- sat_detumble_phases l.97-99, l.161: Rsys SAFE (E > 1) is unreachable from any pair satisfying the rows (E_R = E_L <= 1 and E' < 0), and NO_PRUNE CERTIFIES.

### G5

# Review G5 (10 benchmarks of benchmarks/suite_v2, branch benchmark-fixes)

Sources: the rubric, the ten input.txt files, docs/paper-numbers/matrix.md and letters.md. Line numbers are file lines of benchmarks/suite_v2/<name>/input.txt. Header letters agree with letters.md for all ten.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| sat_detumble_weak | 3 | 3 | 3 | 3 | POLISH | M and B come from a 2 s period on a one-mode left that has no decision to make; two differences between the sides (derating and couplings); the SI-unit claim with a ~100x stylized gain is not disclosed here (sat3w discloses it) |
| sat3w_detumble_phases | 3 | 4 | 4 | 3 | POLISH | exact, tight energy identity with correct gyrostat terms; but the stylized gain is ~100x actuator authority, "fine pointing" is rate damping with no attitude state, and M and I come from giving the design model a different period |
| syringe_relay_prearm | 4 | 4 | 4 | 4 | KEEP | real clinical hazard (slack take-up start-up delay), tight one-sided C row, honest D disclosure; TAKEUP2_L is a corner case only reachable from late-start states |
| tank_dos_3to1 | 4 | 4 | 4 | 4 | KEEP | requirement-tied 0.8 against tight 0.72, cause sweep over hold lengths; the model covers only a rising-demand surge, which is what makes h_L <= h_R hold |
| train_ato_odometry | 4 | 4 | 4 | 4 | KEEP | correct odometry physics and ETCS margin, tight 1.07 against the 1.11 requirement, cause sweep; S lives in a narrow tolerance window [1.07, 1.13) and the performance levels are a gain stylization |
| turbine_startup_gearratio | 3 | 2 | 4 | 2 | RETHINK | the header admits R P I come from the one-sided claim (present at g = 1.00); the overspeed requirement follows from the left alone; STOP is start-only; the claim is called "real-time" but uses right-only repositioning |
| ventilator_vc_cuffleak | 4 | 4 | 4 | 4 | KEEP | resistor-network leak model checks out, ISO-tied tolerances, tight values given, D argued from flow vs pressure control |
| watertank | 3 | 3 | 3 | 3 | POLISH | running example: the attack gains are chosen so that ratio 2 matches exactly; tolerance = offset is nearly circular; High and PumpOff are entered only from initial states; line 73 is stale |
| watertank_twospeed | 3 | 4 | 3 | 3 | POLISH | a better attack story than watertank (the full-speed pump matches Fast) and a tight lower row; but lambda_max = 6 is unexplained, verdicts are dated before the 1.5 change, and High/PumpOff are start-only |
| zone_lightmass_schedule | 3 | 2 | 4 | 2 | RETHINK | the 0.5 K row clears the inductive bound set by the domain by only 0.015, so it certifies because the domain is 5..30 (0..30 or 5..33 decline); it is 9x the reachable gap; B and X come from the claim's form |

## sat_detumble_weak
- Model: a derated gyrostat (k = 0.4, z-wheel) against a decoupled design model with three power profiles (k = 0.5 / 0.45 / 0.42). The left decides every 2 s and the right every 1 s.
- Property: E_L(t) = E_R^NOMINAL(0.8 t) exactly (two rows). Tight: lambda 0.79/0.81 decline.
- Strongest concern: the left has one mode with next = [DETUMBLE] (l.135), so its epsilon = 2.0 (l.130) changes nothing about its trajectories. The "power-saving duty cycle" period (l.36-38, "a design value of this file") exists only to produce M and B. There is a second issue too. The sides differ in two things, the derating and the couplings (l.53-56), and the letters were measured on the design-model left (l.88-90), so the couplings are decoration. Line 19 says "SI units", but k = 0.4/s commands about 0.9 N m (100x a microsat wheel), and unlike sat3w (l.60-66) this file does not disclose it. The mission-planning requirement (l.65-67, "1.25 T s") depends on that time unit.
- Fix: disclose the stylized time unit as sat3w does. Either drop the M/B claim or give the left a real decision (for example a SAFE/derate fallback mode), so that the period matters. State that the pair has two differences, or drop the couplings.

## sat3w_detumble_phases
- Model: a 3-wheel gyrostat against a decoupled design model, with DETUMBLE (k = 0.5) and FINE (k = 0.3) phases. I checked the gyrostat coefficients against J w' = -w x (J w + h) - h' and they are correct.
- Property: E_L = E_R in both phases (tolerance 0, tight by construction; it declines when one wheel term is removed).
- Strongest concern: physical stylization. The gain is ~100x actuator authority (disclosed l.60-66, with a /1000 re-check, which is good). "Fine pointing" (l.45) is rate damping at a lower gain with no attitude state. The 2 s vs 1 s period difference (l.33-36) is a second cause stacked on the model refinement, and M and I come only from it (l.9-10; the equal-period file kept only X).
- Fix: call FINE a low-power rate-hold phase (or say that pointing is abstracted to rate damping). State that the debounce period is a deliberate second difference.

## syringe_relay_prearm
- Model: a two-channel syringe relay. The deployed pre-arms channel 2's driver slack 90 min before the switchover. The validated relay takes up the slack from rest (11.1 min interruption, C falls to 4 %).
- Property: equal volumes up to re-timing; equal C before the switchover and C_R <= C_L after (tight at 0); a strengthening b row.
- Strongest concern: minor. TAKEUP2_L (l.138-142) is reached from PREARM only if the pre-arm starts within 11.1 min of the switchover (v1 > ~48.9 at b = 0), so ordinary runs never enter it. The C keying is expressiveness only (disclosed l.72-75).

## tank_dos_3to1
- Model: a 4-pump station with demand-band staging. The left's decision is held up to 30 s (DoS); the right polls every 10 s; the demand surge is the same on both sides.
- Property: h_L <= h_R <= h_L + 0.8 and w_L = w_R. 0.8 comes from the submergence requirement; the tightest value is 0.72, swept over hold lengths.
- Strongest concern: the demand only rises (w' = 0.02 (22 - w), and the successor sets only step up). That is what makes "a stale decision is always a lower stage" true. A falling-demand (night) episode, where a stale decision overfills, is outside the model, and the header does not list it as a coverage gap. The 0.95 m nominal floor in the requirement chain (l.35-36) is simulated, not certified.

## train_ato_odometry
- Model: an ATO first-order speed loop at three performance levels. In the deployed, the stale wheel diameter makes the tachometer read 0.96 of the true speed.
- Property: 0 <= v_L - v_R <= 1.11 (the ETCS warning margin), with a per-pairing stretch in [0.75, 1.25]. The tightest value is 1.07, the model bound is 1.042, and a cause sweep over c is given.
- Strongest concern: S holds only for tolerances in [1.07, 1.13) (l.53), so the letter rests on the requirement happening to fall in a 0.06 window. Modeling performance levels as 100/90/80 % loop gain is a stylization; PLs usually scale acceleration limits. Both are disclosed or minor.

## turbine_startup_gearratio
- Model: an NREL 5-MW start-up (SPINUP / RAMP / GEN / STOP). The deployed's controller reads the rotor speed 5 % low (stale gearbox ratio), so its thresholds and targets are x1.05 and its gains /1.05.
- Property: one-sided, w_L <= 1.05 w_R (+0.061 in GEN), against an existential reference that may run ahead alone.
- Strongest concern: the relational content is weak. (1) The header says R, P and I appear at g = 1.00 (l.85-89), so three of the four letters come from the claim's form, not the cause. (2) The stated overspeed requirement (l.54-57) already follows from the deployed alone: GEN_L converges to 12.705 < 13.31. (3) Every two-sided form declines or needs d >= 4.86 rpm (l.93-107). (4) l.132-133 calls the requirement "a real-time one", but the cover advances the reference alone with the left frozen (R), so the comparison is not at equal clock times. (5) STOP (l.179-183, 207-211) is entered only as an initial state (pruned edges).
- Fix: either find a claim the cause pins, for example a same-phase relation with a time-dependent band, or keep the file as a disclosed claim-form exhibit for R/P/I and stop presenting it as a gear-error benchmark. Remove the "real-time" sentence.

## ventilator_vc_cuffleak
- Model: one VC breath with a cuff leak at the trachea. I re-derived both INSP and EXP fields from the resistor network and they match (0.376 - 0.0495 V; -1.942 V - 0.0122).
- Property: INSP |V_L - V_R| <= 0.004 + 0.15 V_R; EXP |V_L - V_R| <= 0.08; equal clocks.
- Strongest concern: minor. ISO's "15 % of set volume" is applied to the running V_R, so the INSP band is empty for V_R < -0.027 L (inside the stated domain V >= -0.4). The PEEP-accuracy translation to alveolar volume via C is an interpretation. Both are acceptable with a one-line disclosure.

## watertank
- Model: a set-point level controller. The left has a 3 dm sensor offset plus a pump attack (Low gain doubled, Mid locked to boost). The right has two Mid profiles and a dry-run PumpOff sink.
- Property: |x_L - x_R| <= 3 against a reference re-timed by lambda in [1, 2]. The upper row is tight at 3.00; the lower row is slack (1.50).
- Strongest concern: the constants are reverse-engineered. The deployed Low gain 2.0 and Mid gain 1.0 are exactly 2x the nominal Low and MidEco, so lambda = 2 is an exact identity (l.53-54). The requirement "tolerance = the offset the operator tolerates" (l.39-40) is close to circular. Left High (l.105-109) and right High and PumpOff (l.133-143) are entered only from initial states: the Mid flows approach 20 / 17 asymptotically, and PumpOff is pruned. "Pumps" drain in High. C: l.73 says "The cuts are load-bearing in watertank_twospeed", which contradicts watertank_twospeed l.12 and its matrix row (NO_CUT CERTIFIED). Verdicts are dated 2026-10-26 (l.75), but lambda_max changed on 2026-10-29 (l.55); matrix.md shows CERTIFIED at [1, 2], so only the date is stale.
- Fix: delete or correct l.73, re-date the verdicts, and add one sentence saying High is an overfill-start mode.

## watertank_twospeed
- Model: the watertank attacked controller against a nominal one whose low fill has Fast (gain 2) and Slow (gain 1) stages.
- Property: x_L <= x_R + 3 (tight; the PumpOff exclusion) and x_R <= x_L + 1.5 (tight, 17 - 15.5); cause sweep (s, 4.5 - s).
- Strongest concern: lambda_max = 6.0 (l.95), while every per-pairing stretch is <= 2 (l.86-87). watertank removed the same unused top on 2026-10-29 (watertank l.55), and this file did not. Verdicts are "measured 2026-10-26 with the round-A binary" (l.81), but the lower row became 1.5 on 2026-10-29 (l.9); matrix.md confirms CERTIFIED. High and PumpOff are start-only, as in watertank.
- Fix: set lambda_max = 2.0, re-measure, and re-date the verdict block.

## zone_lightmass_schedule
- Model: a lumped zone under a load-compensated proportional law. The deployed is a light zone (rate 0.04125) and the reference a medium zone (rate 0.02); the right has three set-point levels, the left two.
- Property: |T_L - T_R| <= 0.5 K (EN 15500 CA) against the reference re-timed by lambda = 2.
- Strongest concern: the header shows (l.54-65) that the tight value is 0.0303 x (the largest set-point-to-bound distance) = 0.4848 on 5..30, so the 0.5 requirement certifies only because of the domain choice. 0..30 (0.64) and 5..33 (0.52) decline. The "room sensor span" justification (l.100-101) is weak: common room sensors span 0..50 degC, which needs about 1.03. The reachable gap is <= 0.057 K (l.66-70), so 0.5 is neither tight nor reachable-relevant. B is degenerate and X is forced by the claim's form (l.88-97). This is a domain-tuned tolerance, which the rubric names directly.
- Fix: state the tolerance as the derived bound for a declared, justified range, or replace the constant band with a band relative to the set-point step (the true mismatch is (a - 2b)/a = 3 % of the step). Either way, drop the claim that 0.5 K "is fixed by the requirement and not by a domain".

##### Checkable claims
- sat_detumble_weak l.130/l.135: the left has one mode with next = [DETUMBLE]; with Lsys epsilon = 1.0 the file still CERTIFIES and the cover has budget 1 with no joint step (M and B vanish), while the left's trajectories are unchanged.
- sat_detumble_weak l.19 vs l.49: "SI units" with k_L = 0.4/s gives a wheel torque k J3 w3 of about 0.9 N m at the E = 1 envelope (|w3| <= 0.45), about 100x a microsat wheel. No stylized-unit disclosure, unlike sat3w l.60-66.
- sat_detumble_weak l.23-26, l.88-90: with the couplings removed from the left (left = decoupled at k = 0.4), the file CERTIFIES with letters S M B X; the couplings are not load-bearing.
- sat3w_detumble_phases l.127 vs l.140: with Rsys epsilon = 2.0 (equal periods), M and I disappear (only X), per l.9-10.
- sat3w_detumble_phases l.133-137: FINE has no attitude state; its field is DETUMBLE's with k = 0.3.
- turbine_startup_gearratio l.85-89: at g = 1.00 (left = right) the claim w_L <= w_R shows R, P and I (SYNC, NO_PRUNE, NO_CUT all DECLINE).
- turbine_startup_gearratio l.173-177 with l.54-57: from any GEN_L start w <= 12.705, w_L <= 12.705 < 13.31 holds for the deployed alone (unary invariant), so the requirement needs no reference.
- turbine_startup_gearratio l.179-183, l.207-211: STOP is never entered from SPINUP/RAMP: the flows are positive at their floors (0.03 (9 - 2.1) > 0; RAMP_L 0.038 (7.875 - 5.25) > 0), and the edges are pruned.
- turbine_startup_gearratio l.132-133: "the requirement is a real-time one" conflicts with the cover's right-only step (SPINUP_L, l.143-144; RELCERT_NO_REPO=1 DECLINES).
- turbine_startup_gearratio l.93-101: two-sided rows certify only with d >= 4.86 rpm (GEN only) or 6.85 (RAMP+GEN), >= 40 % of the 12.1 rpm range.
- watertank l.73: "The cuts are load-bearing in watertank_twospeed" is false; matrix.md watertank_twospeed NO_CUT, NO_IMPLIED_CUT and NO_LINEAR_CUT all CERTIFIED, and watertank_twospeed l.12 says I was lost.
- watertank l.105-109, l.133-137: Mid_L (toward 20) never reaches x >= 20 and MidEco/MidBoost (toward 17) never reach x >= 17, so the Mid -> High edges never fire; High is entered only from initial states. Right PumpOff (l.139-143) likewise (Low -> PumpOff pruned).
- watertank l.94/l.100 vs l.116/l.122: the deployed gains 2.0 and 1.0 are exactly 2x the nominal Low (1.0) and MidEco (0.5), so at lambda = 2 the fields coincide up to the shift by 3.
- watertank l.75 vs l.55: the verdict block is dated 2026-10-26, but lambda_max = 2 was set on 2026-10-29.
- watertank_twospeed l.95: lambda_max = 6.0 is unused; with lambda_max = 2.0 the file CERTIFIES with the same letters S M B P (every per-pairing stretch in l.86-87 is <= 2).
- watertank_twospeed l.81 vs l.9 and l.161-163: the verdict block (2026-10-26, round-A binary) predates the lower row 1.5 (2026-10-29).
- zone_lightmass_schedule l.135-136, l.148-159: with the domain 0 <= T <= 30 the 0.5 row DECLINES (inductive bound 0.64); with 5 <= T <= 33 it DECLINES (0.52); with 0 <= T <= 50 it needs about 1.03.
- zone_lightmass_schedule l.162-163: 0.49 certifies and 0.48 declines (l.54), so 0.5 is 0.015 above the domain-set bound and about 9x the simulated reachable gap 0.057 K (l.66-69).
- zone_lightmass_schedule l.95-97: B is degenerate (an off-level selection is answered by a zero-time hop back).
