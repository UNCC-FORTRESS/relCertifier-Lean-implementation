# Benchmark review, round 7 (2026-10-30; suite_v2 at bd7c608, 23 benchmarks)

Three fresh reviewer agents, 7 or 8 benchmarks each, rubric `docs/review-rubric.md` plus the accepted list of decided structural choices (below); the reviewers did not see earlier reviews, scores or fix lists. Every finding carries a severity (HIGH: claim false, letter from an artifact, domain doing the claim's work, stronger claim certifies, header number wrong; LOW otherwise). Findings are reviewer claims; every claim acted on was verified by a tool run first (the fix log is in `docs/OVERNIGHT2-2026-10-30.md`).

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
| `fuelcell_chp_dos` | 3 | 2 | 4 | 2 | RETHINK | attack is physically inert (exact claim true); 7 K is neither tight (5.00) nor sourced (45 degC floor is "a design value of this file"); certifying set non-monotone | 2 |
| `turbine_startup_gearratio` | 4 | 2 | 3 | 2 | RETHINK | the overspeed requirement is met by the unary ceiling alone, and the relational row needs that ceiling pinned at the deployed's asymptote | 3 |
| `acc_spoof_lag` | 3 | 3 | 2 | 2 | POLISH | rows are true, but the header's "Reading" and "Row 2 holds with equality" are false as stated (only the dominant mode matches); row 1's constant 0 is 3.33 m/s slack | 4 |
| `acc_tune_limp` | 4 | 4 | 2 | 2 | POLISH | M is credited on a joint step whose path never leaves NORMAL (DISENGAGE dead in every cover); otherwise clean | 4 |
| `acc_spoof_limp` | 3 | 4 | 3 | 3 | POLISH | row 2 well sourced; "one cause" contradicts the header's own account (period and right-only profiles also differ) | 2 |
| `acc_tune_lag` | 3 | 3 | 3 | 3 | POLISH | lag tau = 0.32 chosen so the exact claim holds; the left "hull" guard is a loose modal box reaching a = 28.75 | 3 |
| `molding_pack_checkring` | 3 | 3 | 4 | 3 | POLISH | D is real, but x_R <= 500 leaves out the switchover above hold pressure that the header itself calls common; 25 bar is self-chosen | - |
| `platoon_profiles` | 4 | 3 | 4 | 3 | POLISH | clean derivation; the "Requirement" 3.34 m is the tool's route value (header: semantic tightest 2.78), and the TTC row's 5 is not tight (19.44 certifies) | 3 |
| `quad_light_lag` | 3 | 4 | 4 | 3 | POLISH | Psi conservation claim is sound and sourced (0.8 m NAV_MC_ALT_RAD); the state `a` is mislabeled "net specific thrust", and its bound 14.715 equals the left set point and 3 K_R, both fixed by the contrived K = g/2 | 2 |
| `quad_light_profiles` | 4 | 4 | 2 | 3 | POLISH | good property; the header's system equation has a -K w term the file does not have | 2 |
| `rover_terrain_6to12` | 3 | 3 | 3 | 3 | POLISH | relational rows are a monotone comparison; the numeric rows are left-only, and heave is output-only, the same reason the pitch rows were removed | 3 |
| `elevator_start_discbrake` | 4 | 3 | 4 | 3 | KEEP | genuine R (reference lifts alone) and D; claim is true by construction (z, v dynamics identical, b never feeds motion), so its content is the re-timing mechanism | 3 |
| `engine_start_highidle` | 4 | 3 | 4 | 3 | KEEP | realistic start sequence, genuine R D I and a reachable abort; with free right-only run-ahead the SELF/IDLE row is close to the unary bound N2_L <= 66 | 3 |
| `gantry_speed_zones` | 4 | 3 | 4 | 3 | KEEP | Clean S exhibit; the claim is exact (tolerance 0 certifies) because a uniform override is a time reparametrization, so the 10 mm comes from a requirement, not from tightness | 3 |
| `h2_refuel_ambientbias` | 3 | 3 | 4 | 3 | KEEP | Honest header; the top 2.9 is 2.4 of cause plus 0.5 of certificate slack, and the stage "requirement" (lead 0) holds by construction | 3 |
| `rover_terrain_2to4` | 3 | 4 | 4 | 3 | KEEP | Tight sigma checked analytically; the left guard conjunct w <= c_T is a reachability restriction presented as a guard, and the I cut that carries the no-skid row rests on it | 3 |
| `lit_gpt10_boost_converter` | 4 | 4 | 3 | 4 | POLISH | Faithful to the source at eps 2.6 (tight 2.58); the inclusion argument ("{G w} covers the ball") holds only for the convex hull or for sub-window mixing, and the header does not say this | 4 |
| `ventilator_vc_cuffleak` | 4 | 4 | 3 | 4 | POLISH | Network constants reproduce; D is well motivated; the header's I explanation (INSP guard s >= 0.01) does not name the kept atom matrix.md reports (L.EXP s <= 0.01 closure, M6+) | 3 |
| `flaps_slow_approach` | 4 | 4 | 4 | 4 | KEEP | sound per-mode stretch, tight constants derived from placards; the claim (25) is wider than the requirement (20), as the header says | 3 |
| `hydro_rejection_gatecal` | 4 | 4 | 4 | 4 | KEEP | Real governor/turbine constants, requirement-derived tolerances, tight values given; D comes from a real shared-grid premise | 2 |
| `platoon_linkloss` | 4 | 4 | 5 | 4 | KEEP | Every constant tight with a physical reading; a baseline with no letters, disclosed | 2 |
| `rampmeter_poll_2to1` | 4 | 4 | 5 | 4 | KEEP | real CTM + table metering; 8 from HCM LOS bands, tight set {5} and [7, ...) measured and explained; cause dependence swept | 3 |
| `watertank_twospeed` | 4 | 5 | 4 | 4 | KEEP | Both rows tight with a clear cause law; several declared successor edges are dead (only Fast -> PumpOff was removed) | 3 |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 4 | 12 | 7 | 0 |

Verdicts: KEEP 10, POLISH 11, RETHINK 2, DROP 0. Overall >= 4: 7/23 (30 %). Overall < 3: 4.

## Delta vs previous round

Previous histogram (1..5): 0, 8, 28, 14, 0 over 50; this round: 0, 4, 12, 7, 0 over 23.

Up: `acc_spoof_limp` 2->3, `flaps_slow_approach` 3->4, `hydro_rejection_gatecal` 2->4, `platoon_linkloss` 2->4, `quad_light_lag` 2->3, `quad_light_profiles` 2->3, `rampmeter_poll_2to1` 3->4, `ventilator_vc_cuffleak` 3->4, `watertank_twospeed` 3->4.

Down: `acc_spoof_lag` 4->2, `acc_tune_limp` 4->2, `turbine_startup_gearratio` 3->2.

New in this round: `molding_pack_checkring`.

Not in this round: `antenna_track_kvretune`, `bottling_fill_strainer`, `canal_gate_notches`, `charger_fast_tapers`, `furnace_program_timebase`, `lit_csf21_vehicle_bus`, `lit_csf21_vehicle_thermo`, `lit_csf25_salt_tank_hold`, `lit_drl_lane_control`, `lit_freedm_meter`, `lit_girard08_robot`, `lit_lz21_vehicle_position`, `lit_nahs25_salt_tank`, `platoon_latency`, `reactor_feed_wireless`, `rover_ladder_2to3`, `rover_ladder_3to6`, `rover_ladder_6to8`, `rover_ladder_8to12`, `rover_patrol_lag`, `rover_terrain_4to6`, `sat3w_detumble_phases`, `sat_detumble_phases`, `sat_detumble_weak`, `syringe_relay_prearm`, `tank_dos_3to1`, `train_ato_odometry`, `watertank`.

Round 7 reviewed only the 23 files edited after round 6 (three fresh reviewers, the same rubric and accepted list plus the M rule); the other 27 keep their round-6 scores.

## Reviewer notes by group

### g1

# Review r7, group g1 (8 benchmarks)

Inputs used: rubric, ACCEPTED-LIST, the 8 `input.txt` files, `docs/paper-numbers/matrix.md`, `docs/paper-numbers/letters.md`.
I spot-checked header numbers by hand against the file constants (all reproduced, see per-benchmark notes). Header letters match letters.md for all 8, and the mechanism cells match matrix.md (one wording gap noted for the ventilator).

## Table

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| hydro_rejection_gatecal | 4 | 4 | 4 | 4 | KEEP | Real governor/turbine constants, requirement-derived tolerances, tight values given; D comes from a real shared-grid premise |
| lit_gpt10_boost_converter | 4 | 4 | 3 | 4 | POLISH | Faithful to the source at eps 2.6 (tight 2.58); the inclusion argument ("{G w} covers the ball") holds only for the convex hull or for sub-window mixing, and the header does not say this |
| rover_terrain_2to4 | 3 | 4 | 4 | 3 | KEEP | Tight sigma checked analytically; the left guard conjunct w <= c_T is a reachability restriction presented as a guard, and the I cut that carries the no-skid row rests on it |
| gantry_speed_zones | 4 | 3 | 4 | 3 | KEEP | Clean S exhibit; the claim is exact (tolerance 0 certifies) because a uniform override is a time reparametrization, so the 10 mm comes from a requirement, not from tightness |
| ventilator_vc_cuffleak | 4 | 4 | 3 | 4 | POLISH | Network constants reproduce; D is well motivated; the header's I explanation (INSP guard s >= 0.01) does not name the kept atom matrix.md reports (L.EXP s <= 0.01 closure, M6+) |
| watertank_twospeed | 4 | 5 | 4 | 4 | KEEP | Both rows tight with a clear cause law; several declared successor edges are dead (only Fast -> PumpOff was removed) |
| h2_refuel_ambientbias | 3 | 3 | 4 | 3 | KEEP | Honest header; the top 2.9 is 2.4 of cause plus 0.5 of certificate slack, and the stage "requirement" (lead 0) holds by construction |
| platoon_linkloss | 4 | 4 | 5 | 4 | KEEP | Every constant tight with a physical reading; a baseline with no letters, disclosed |

## Per benchmark

**hydro_rejection_gatecal.** A hydro unit with a gate transducer reading 2 % low, compared with the commissioned unit across a load rejection. On the grid the claim keeps the speeds equal and the gates within 0.027. After the rejection it allows a speed gap of up to 0.07 and keeps the gates within 0.027. I checked the 1.227 / 1.2055 peaks (a/4 + w0/2 with a = g0 - 0.1), the 0.0101 deployed-peak excess and 0.02 + 20 x 0.008 = 0.18; all agree.
Strongest concern (LOW): the uniform-row decline comes only from on-grid pairs with w_L != w_R. Those pairs are not physical, and the ONGRID row excludes them. This is the shared-grid premise the header states, so it is a real D, but it is the same kind of start-pair exclusion that removed R from h2 in round 6. LOW: the REJECT gate row is a "stated strengthening" with no requirement behind it (after the breaker opens, the gate no longer drives power).

**lit_gpt10_boost_converter.** The GPT10 boost converter (right, 2 modes) against a left model in which the lattice snap is replaced by a constant drift taken from a 24-gon (48 modes). The claim is the source's M-norm relation at eps 2.6. That is the source's value, tight at 2.58 and not claimed tight. The cover maps P_p d_k to P_p through a zero-time hop, which is consistent with the header's X.
Strongest concern (LOW, wording): the lines "the set {G w} covers the ball of radius eta" and "every transition ... ends a left window" are literally false for 24 vertex drifts in one window, since they reach only 24 end points. The inclusion holds for the convex hull of {G w}, or for a run of sub-windows that mixes adjacent vertices (allowed by windows of length at most epsilon). Either way the witness then switches p only at the left's p-switches. The header gives this argument only indirectly ("holds for every drift signal in the 24-gon").
Fix: say "the convex hull of {G w_k} covers the eta-ball (support ratio 1.0019); an abstraction transition is a left run of sub-windows mixing adjacent vertices, or the drift-signal argument", and say that the witness keeps the left's p.

**rover_terrain_2to4.** A 4-DOF rover with slip and sinkage, refining a 2-DOF no-slip plan across MUD, GRAVEL and PAVED, at lambda 1. The rover is never faster than or ahead of the plan, the wheel never turns faster than the plan's speed, and the slip velocity stays in [0, 0.25]. I verified tight sigma = 1.47/7 = 0.21. The stated 0.25 is the requirement and is not claimed tight.
Strongest concern (LOW): the left guards carry w <= c_T ("entry wheel speed"). The zone controller does not branch on w, so this conjunct is a reachability restriction, not controller behavior. It is also what makes v_L <= w_L hold: from w > c_T the wheel decelerates and the rover genuinely skids. The I letter (NO_CUT declines) is the cut built from it. It is a true fact on every run from admitted starts, so it is not an artifact, but the header should say plainly that it excludes real skid starts.
LOW: the zs domain cap 0.12 exceeds the largest equilibrium sinkage Z_T = 0.10, with no source ("the sinkage range"), and the tight-sigma witness uses zs = 0.12 (zs = 0.10 gives 0.207, which still rounds to 0.21). LOW: the right's w and zs are frozen dummy coordinates.

**gantry_speed_zones.** A two-axis gantry with zone-scheduled uniform speed overrides (x3, x2, x1), compared with the commissioning run. Paths agree within 10 mm per axis, up to a stretch per left mode. I verified the reach numbers 0.39 and 0.466.
Strongest concern (LOW): R is thin. A uniform override is exactly a time reparametrization, so the path claim certifies at tolerance 0, and the witness is the left re-timed. The content is the stretch (S), not the relation. The 10 mm comes from the commissioning clearance requirement and the grid-independence evidence (FREE [2.94, 3.06] and so on), and the header discloses that 0.00 certifies at lambda_max 3. M is withheld correctly under the 1-right-mode rule.

**ventilator_vc_cuffleak.** One volume-controlled breath with an under-inflated cuff leak (g = 0.002 L/s/cmH2O), compared with a sealed cuff. During inspiration the volume gap is within 4 mL + 15 % of V_R; during expiration it is within 0.08 L. Both phases also carry the delivered-volume rows. I re-derived the network: 0.376238 - 0.049505 V, -1.9419 V - 0.01224, the 32.9 mL loss and the -6.3 mL settle all agree. The tight values 0.104 and 0.064 are given; the stated values come from ISO.
Strongest concern (LOW, C): the header attributes I to the INSP guard s >= 0.01 and names only matrix code M5. matrix.md reports M6 yes and M6+ yes, with the kept widened atom L.EXP: s <= 0.01 (closure, frozen).
Fix: name M6/M6+ and the EXP closure atom, or explain how the INSP guard fact reaches the kept atoms.
LOW (P/R): the ISO 80601-2-12 accuracy is a device tolerance on the set tidal volume. Here the device delivers the same 0.4 L/s on both sides and the loss is patient-side, and applying the tolerance to the running volume is the file's own extension (stated). LOW: the INSP relative row is unsatisfiable for V_R < -0.0267, which silently drops those starts.

**watertank_twospeed.** The running example's attacked tank (3 dm offset, forced full speed) against a nominal controller with a two-speed low fill. The tank satisfies x_L <= x_R + 3 and x_R <= x_L + 1.5. Both are tight, the cause law (s, 4.5 - s) is measured, and I verified 11.76. S, M and B are genuine: Low pairs with Fast at lambda 1 and Slow at 2, the right has more than 2 modes, and Fast -> {Slow, MidEco, MidBoost} are all reachable in one window.
Strongest concern (LOW): round 6 removed Fast -> PumpOff because the edge was dead, but other dead edges are still declared. Left Mid -> High and High -> Mid cannot be taken (flow x' = 20 - x never crosses 20). Right MidEco/MidBoost -> High and High -> MidEco/MidBoost cannot be taken either (never crosses 17). matrix M3 "Mid branch=2" counts the dead High successor. B is still credited from Low, so no letter depends on these edges.
Fix: drop the dead edges, or state why they stay.

**h2_refuel_ambientbias.** A staged 70 MPa hydrogen fill whose end pressure is 72.4 instead of 70 because of a +10 K ambient bias. The stage rows require p_L <= p_R. The top rows allow p_L <= p_R + 2.9 together with p_R >= 58. I verified 72.4 = 70 x (1 + 10/288).
Strongest concern (LOW): 2.9 is tight for the tool, but the physical gap is about 2.4 plus one window's overshoot (about 0.03). The 0.5 is certificate slack and the header says so.
LOW: the stage requirement "the deployed may not lead" holds by construction (identical stages), and the conjunct p_R >= 58 is a reachability restriction. D therefore depends on choosing a stage row that is free to prove, although the keyed claim is meaningfully stronger than the certifying uniform row, which makes the stage claim nearly vacuous.
LOW (C): the "Caveat" credits D at s = 0 entirely to the certificate. In fact uniform p_L <= p_R is also false at s = 0 because of sampled overshoot past 70.0 (a deployed at 69.99 in TOPOFF against a reference COMPLETE at 70.0), so D at s = 0 is real but tiny.

**platoon_linkloss.** A CACC follower that degrades to ACC under V2V loss (a 0.2 s decision), compared with the always-up CACC (0.1 s). The claim is 0 <= Delta g <= 15 plus derived contraction forms, all tight with a physical reading. I verified the poles and d/dt(g + 2r).
Strongest concern (LOW, P): on the lead link a_pred = 0, so losing the feed-forward has no effect, and the link loss reduces to a set-point switch, 20 m to 35 m. The jamming scenario never exercises the feed-forward. No letters (M withheld under the rule, AEB removed), disclosed.

## Findings by severity

HIGH: none.

LOW:
1. lit_gpt10_boost_converter: the "{G w} covers the ball" / "ends a left window" wording holds only for the convex hull or sub-window mixing; state the argument and that the witness keeps p.
2. ventilator_vc_cuffleak: the I explanation and matrix codes do not match matrix.md (M6, M6+, kept atom L.EXP s <= 0.01).
3. ventilator_vc_cuffleak: the ISO device-accuracy tolerance is applied to a patient-side leak and to the running volume; the INSP row drops V_R < -0.0267 starts without saying so.
4. watertank_twospeed: dead successor edges remain (left Mid <-> High; right Mid* <-> High), inconsistent with the round-6 removal of Fast -> PumpOff; M3's "Mid branch=2" counts one.
5. rover_terrain_2to4: guard conjunct w <= c_T is a reachability restriction that carries the no-skid row (via the I cut); say so. The zs cap 0.12 has no source. The right's w and zs are frozen dummy coordinates.
6. h2_refuel_ambientbias: the top 2.9 contains 0.5 of certificate slack; the stage "requirement" holds by construction; the s = 0 caveat misattributes D entirely to the certificate (sampled overshoot also breaks the uniform row).
7. hydro_rejection_gatecal: D rests on excluding non-physical on-grid start pairs (the stated shared-grid premise); the REJECT gate row has no requirement behind it.
8. gantry_speed_zones: the relation is exact modulo re-timing (tolerance 0 certifies); R content is the stretch.
9. platoon_linkloss: with a_pred = 0 the link loss is only a set-point switch.

### g2

# Review r7, group g2 (8 benchmarks)

Inputs: rubric, ACCEPTED-LIST.md, the eight input.txt files, matrix.md and letters.md rows. No runs.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_tune_limp | 4 | 4 | 2 | 2 | POLISH | M is credited on a joint step whose path never leaves NORMAL (DISENGAGE dead in every cover); otherwise clean |
| acc_spoof_limp | 3 | 4 | 3 | 3 | POLISH | row 2 well sourced; "one cause" contradicts the header's own account (period and right-only profiles also differ) |
| acc_tune_lag | 3 | 3 | 3 | 3 | POLISH | lag tau = 0.32 chosen so the exact claim holds; the left "hull" guard is a loose modal box reaching a = 28.75 |
| quad_light_profiles | 4 | 4 | 2 | 3 | POLISH | good property; the header's system equation has a -K w term the file does not have |
| molding_pack_checkring | 3 | 3 | 4 | 3 | POLISH | D is real, but x_R <= 500 leaves out the switchover above hold pressure that the header itself calls common; 25 bar is self-chosen |
| turbine_startup_gearratio | 4 | 2 | 3 | 2 | RETHINK | the overspeed requirement is met by the unary ceiling alone, and the relational row needs that ceiling pinned at the deployed's asymptote |
| rover_terrain_6to12 | 3 | 3 | 3 | 3 | POLISH | relational rows are a monotone comparison; the numeric rows are left-only, and heave is output-only, the same reason the pitch rows were removed |
| flaps_slow_approach | 4 | 4 | 4 | 4 | KEEP | sound per-mode stretch, tight constants derived from placards; the claim (25) is wider than the requirement (20), as the header says |

## acc_tune_limp
- Model: a 1-D speed loop. The tuned CRUISE (gain 0.75) latches into LIMP (toward 25 m/s). The stock NORMAL has gain 0.5, with a DISENGAGE coast below 20 m/s.
- Property: in CRUISE, v_L = v_R exactly at stretch 3/2. In LIMP, v_L <= v_R. The numbers check by hand: 37.5 = 7.5/0.2, and the 7.00 lead = 15 - 0.4 x 20.
- **HIGH (letter from dead structure): M.** matrix.md shows `path modes ['NORMAL']` in both covers and DISENGAGE flags `'---'`. The CRUISE joint step is `NORMAL:joint(B=2)->[NORMAL@1, NORMAL@1]`. So the multi-step cover is one continuous NORMAL run cut at epsilon_R, which is exactly the case where the letter rule (suite_v2_letters.py, l.23-26) withholds M. The rule fires only because DISENGAGE is declared, and DISENGAGE is pruned and inadmissible everywhere ("the verdict never depends on it", header). acc_tune_lag gets the opposite treatment for the same cover shape.
  - Check: run suite_v2_letters.py on a copy with Rsys DISENGAGE deleted (NORMAL.next = [NORMAL]). If it is CERTIFIED with the same CRUISE cover (budget 2, NORMAL only), M depends only on the dead mode. Equivalently, confirm under RELCERT_NO_PRUNE=1 that no joint-step boundary retains DISENGAGE.
- Fix: count the right modes the cover's path actually visits (not the declared ones) in the M rule, or drop M (letters S D I).
- LOW: the LIMP row's constant 0 is forced by the handoff, not by a requirement. It is fine and stated.

## acc_spoof_limp
- Model: the spoofed speed reads 1.25 v (settles at 24 m/s) and debounce-latches into LIMP (22 m/s). The reference is unspoofed, with driver ECO/NORMAL/SPORT and DISENGAGE.
- Property: v_L <= v_R, and an AASHTO-derived closing bound 0.7 v_R <= v_L + 4. The numbers check: 10.05/16.32, 28.58, 34.5.
- LOW: the header says "One cause: the spoof", yet the pair also differs in period (2 s vs 1 s) and in having driver profiles only on the right. The header itself says M and B come from the period, and B branches into ECO/SPORT, which the deployed lacks.
- LOW: row 1 certifies down to v_L <= v_R - 5.00. "Constant 0 is forced" only means that positive slack declines (a non-monotone effect of the DISENGAGE start). The requirement justifies 0, so this is not a tightness claim.
- LOW: epsilon_L = 2 s read as "decisions at most every 2 s" does not encode the debounce (a latch could fire after 0.1 s). The debounce is encoded only through the 28.6 LIMP guard. Say so.
- Fix: reword "One cause", and list the period and the right-only profiles as the two further differences.

## acc_tune_lag
- Model: a two-state lagged speed loop, retune 0.75 vs stock 0.5, with tau = 0.32 on both sides.
- Property: the dominant-mode speeds are equal at stretch 2 (exact), plus |v_L - v_R| <= 3.34 (tight). The roots and envelope corners check out.
- LOW: tau = 0.32 is chosen as "the unique lag" at which the claim is exact. That is a plant constant tuned to the claim (disclosed; 0.30 declines). It is acceptable only as a specification instance.
- LOW: the left guard is called "the forward-invariant hull" of the engagement box. It is the modal-coordinate box, a parallelogram whose far corners (8.6, 28.75) no run reaches, and that is why the 1 g box is load-bearing (the domain itself is accepted, item 3). Call it a modal box.
- LOW: the header time is 0.10 s; matrix.md has 167 ms and letters.md 0.0 s. Run time itself is not a concern.
- Letters S with no M is consistent with the rule.

## quad_light_profiles
- Model: a vertical quad, with the P-loop feedforward for m_R flown on m_L = 0.8 m_R. There are three pilot profiles on both sides, with a per-profile stretch of 1.25/1.2/1.16.
- Property: |h_L - h_R| <= 0.8 (NAV_MC_ALT_RAD), with a conserved Phi (tight at 0.76) and rate orderings. S M B X are genuine (hops to the matching profile; branching at joint steps).
- **HIGH (header contradicts file):** the System line has "w' = T/m - g - K w" with T = m_R (g + K (w_sp - w)). With m = m_R this gives w' = K w_sp - 2K w = 4.905 w_sp - 9.81 w. The file's right NORMAL is 9.81 - 4.905 w (slope -K), and the header's own left formula omits the -K w term.
  - Check: substitute m = m_R into the header formula and compare with `[Rsys.mode.NORMAL] ode`.
- LOW: SPORT 2.5 m/s is picked so that 1.16 lies on the grid (disclosed). The "0.09" in the 0.76 derivation is unexplained. The domain w >= 0 (no descent) is not a physical limit, and no domain scan is reported for it.
- Fix: delete "- K w", explain 0.09, and report whether w >= 0 is load-bearing.

## molding_pack_checkring
- Model: injection-molding HOLD/COOL on a phase clock. The worn check ring adds a leak l = 0.4 to the nozzle loop.
- Property: in HOLD, nozzle and cavity are within 25 bar; in COOL, the cavity only, plus x_R <= 500. The tight value is 19.24, the hold droop. D is genuine: the cause test at l = 0 removes it, and the uniform rows decline because of the coupling physics.
- LOW (main concern): the x_R <= 500 conjunct is the hold set point, moved from the domain into the claim. Without it the claim fails above about 650 bar, and the header itself says switchover above hold pressure is "common on hydraulic machines". So the certified scope leaves out the typical cycle. It is disclosed, so not HIGH.
- LOW: 25 bar has "no external source" while the tight value is 19.24. "From x0 = 2000 it reaches about 33 bar" does not match the stated formula 0.4 x0/10.4 = 77 bar at x0 = 2000 (that formula gives 25 at 650 bar, which matches the cap test).
- Fix: either cite a switchover-at-or-below-hold profile as the scope, or drop the conjunct and state the tolerance measured at the 2000 bar rating. Reconcile the 33-bar sentence.

## turbine_startup_gearratio
- Model: the NREL 5-MW start-up phases (SPINUP/RAMP/GEN/STOP). A stale gearbox ratio makes the deployed read 5 % low.
- Property: w_L <= 1.05 w_R and w_L <= 12.705 in every phase.
- LOW (main concern, R): the stated requirement (overspeed 13.31) is discharged by the unary conjunct w_L <= 12.705 alone, which is a left-only forward-invariant fact (the GEN asymptote). The relational row certifies only with that ceiling, and the ceiling is pinned exactly at the asymptote (12.70 and 12.71 both decline). This is the round-B set-point domain moved into the claim.
  - R, P and I are present at g = 1.00 (disclosed), so no letter reflects the cause.
  - P proves STOP edges dead only because the model fixes rated wind (SPINUP always flows toward 9 rpm).
- LOW: the cause-dependence and window evidence ("g = 1.00 ... 1.20", "g < 1.2") was measured in round 2 or on the round-B domains, not on the current trip-domain-plus-ceiling model.
- Fix (RETHINK): state a requirement that only the relational row meets, for example a bound on the lag behind the re-scaled reference, or the 1.05 factor against a phase-aligned reference. Otherwise present the file as an R/P/I exhibit of one-sided claims rather than a gear-error claim. Re-measure the g-sweep on the current model.

## rover_terrain_6to12
- Model: a 12-DOF sloped, compliant rover refining a 6-DOF flat model over MUD/GRAVEL/PAVED.
- Property: v_L <= v_R and s_L <= s_R, plus left-only slip (sigma 0.25, tight 0.24) and heave (0.15, tight 0.13). The derivations of 0.127, 0.238 and 0.249 check out.
- LOW (R): u, w and zs have identical decoupled dynamics on both sides, so the orderings are trivially kept, and v_L <= v_R follows by comparison (the extra -9.81 theta_p <= 0). The quantitative rows are unary on the left.
  - The header removed the pitch rows as "unary bounds on an output-only chain". zh and vz are equally output-only (they do not feed v, s, w, zs or u), yet the heave rows stay.
- LOW: H is in "wheel radii" while zh's field rho_T v - zh is in SI. The theta_p <= 0.02 domain is load-bearing; it is the route's geometric grade bound (accepted as physical), but theta_p is a lag state, and an entry guard theta_p <= gamma would state it directly.
- Fix: make the rationale consistent (keep heave as a stated requirement or drop it), and fix the units of H.

## flaps_slow_approach
- Model: flap extension from CONF 1+F to CONF 2 at half drive rate (one hydraulic system lost), with autothrust deceleration toward F = 150.
- Property: f_L = f_R at stretch 1/2 (1 once the flaps are set), with V gaps of 25/10 kt. Both are tight and derived as (VFE - F)/2 and (F - VLS)/2. The placard domain is load-bearing and stated (accepted).
- LOW: the certified 25 kt exceeds the stated 20 kt operational window (disclosed; 20 holds only for selections at or below 190 kt). The grid dependence is disclosed.
- Concern: none blocking.

## Findings by severity
HIGH
1. acc_tune_limp: letter M comes from dead structure. The cover's right path is NORMAL only; DISENGAGE is pruned and never admissible. Check: letters on a copy with DISENGAGE deleted (NORMAL.next = [NORMAL]) gives CERTIFIED with the same budget-2 NORMAL-only cover; or confirm in matrix.md that `path modes ['NORMAL']` and DISENGAGE flags `'---'` hold in both covers.
2. quad_light_profiles: the header's system equation "- K w" contradicts the file's ODEs. Check: m = m_R gives w' = 4.905 w_sp - 9.81 w, but the file has 9.81 - 4.905 w.

LOW
- acc_tune_limp: the LIMP constant 0 is a handoff consequence, not a requirement.
- acc_spoof_limp: "One cause" contradicts the header (period and right-only profiles); row 1 is not tight (-5.00 certifies; disclosed); the debounce is encoded only via the 28.6 guard.
- acc_tune_lag: tau tuned to the claim; "hull" is a modal box; the header time differs from matrix.md.
- quad_light_profiles: SPORT set point picked for the grid; the 0.09 is unexplained; w >= 0 is not physical and has no scan.
- molding_pack_checkring: x_R <= 500 leaves out the common switchover regime; 25 bar is self-chosen; the 33-bar sentence contradicts the 0.4 x0/10.4 formula.
- turbine_startup_gearratio: the requirement is met by the unary ceiling at the deployed asymptote; letters are independent of the cause; the g-sweep is stale.
- rover_terrain_6to12: the relational rows are a trivial comparison; the heave rows contradict the removal rationale for the pitch rows; H units; theta_p is bounded through the domain.
- flaps_slow_approach: the claim (25 kt) is wider than the requirement (20 kt), disclosed.

### g3

# Review r7, group g3 (fresh skeptical reviewer)

Inputs: rubric, ACCEPTED-LIST, the seven input.txt files, matrix.md and letters.md rows. Letter rule M (right needs at least two modes) applied.
Header numbers checked against matrix.md and letters.md: verdicts, letters, handoff counts, prune lists, admissible sets and cut cells all agree for the seven files. Run-time differences (header vs matrix ms) are ignored (accepted item 6).

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| quad_light_lag | 3 | 4 | 4 | 3 | POLISH | Psi conservation claim is sound and sourced (0.8 m NAV_MC_ALT_RAD); the state `a` is mislabeled "net specific thrust", and its bound 14.715 equals the left set point and 3 K_R, both fixed by the contrived K = g/2 |
| acc_spoof_lag | 3 | 3 | 2 | 2 | POLISH | rows are true, but the header's "Reading" and "Row 2 holds with equality" are false as stated (only the dominant mode matches); row 1's constant 0 is 3.33 m/s slack |
| elevator_start_discbrake | 4 | 3 | 4 | 3 | KEEP | genuine R (reference lifts alone) and D; claim is true by construction (z, v dynamics identical, b never feeds motion), so its content is the re-timing mechanism |
| platoon_profiles | 4 | 3 | 4 | 3 | POLISH | clean derivation; the "Requirement" 3.34 m is the tool's route value (header: semantic tightest 2.78), and the TTC row's 5 is not tight (19.44 certifies) |
| rampmeter_poll_2to1 | 4 | 4 | 5 | 4 | KEEP | real CTM + table metering; 8 from HCM LOS bands, tight set {5} and [7, ...) measured and explained; cause dependence swept |
| fuelcell_chp_dos | 3 | 2 | 4 | 2 | RETHINK | attack is physically inert (exact claim true); 7 K is neither tight (5.00) nor sourced (45 degC floor is "a design value of this file"); certifying set non-monotone |
| engine_start_highidle | 4 | 3 | 4 | 3 | KEEP | realistic start sequence, genuine R D I and a reachable abort; with free right-only run-ahead the SELF/IDLE row is close to the unary bound N2_L <= 66 |

## quad_light_lag
- Model: 20 % lighter quadrotor vs reference, climb segment with first-order motor lag (tau 0.1 s) and a lag-free P velocity loop; one mode per side, stretch 6/5 pinned.
- Property: |h_L - h_R| <= 0.8 at t vs 1.2 t, plus a band |Psi| <= 0.45 on the conserved steady-climb gap Psi (checked: d/dt of h + ((w - w_term) + 0.1 (a - a_cmd))/k is exactly a_cmd/k; the smt2 constant 0.14525 and the hover Psi = -0.0237 recompute correctly).
- Concern 1 (LOW): `a` is the lagged set-point part of the thrust command, not net specific thrust (the actual net acceleration is a - k w, zero in steady climb). The domain bound a <= 14.715 "= 1.5 g thrust limit" is exactly the left's asymptote a_cmd_L and exactly 3 K_R (needed for the reference box to be forward invariant at the w <= 3 limiter; at PX4's K = 4.0 the header itself reports BLOCKING). All three coincide only because K = g/2. Not load-bearing for the verdict (20 % widening certifies), so not HIGH, but it is the "set point / asymptote" pattern of accepted item 3.
- Concern 2 (LOW): row 2's tightness at 0.80 is by construction (the Psi band 0.45 was chosen as the widest band for which 0.8 holds); from hover the real gap is 2.4 cm and |Delta h| <= 0.36 certifies with a narrow Psi band (disclosed).
- Fix: rename `a` as the lagged thrust-command component and state the a bound's physical source independently of a_cmd_L (or say plainly that the bound is the commanded level and why it is a physical limit).

## acc_spoof_lag
- Model: speed loop with powertrain lag, left spoofed 25 % high (settles at 24 m/s), right unspoofed (30 m/s); one mode per side, lambda 3/2 pinned (ratio of dominant rates 1 and 2/3, checked).
- Property: v_L <= v_R (re-timed) and u_L <= u_R - 6 with u the dominant-mode speed (checked: u_L - 24 decays at 1, u_R - 30 at 2/3; modal envelope guards recompute correctly).
- Concern 1 (HIGH, header claim false): "every speed profile of the attacked car is a sped-up, lowered profile of the reference" and "Row 2 holds with equality (u_L - 24 and u_R - 30 are the same exponential after re-timing)". The fast modes do not match (left 5/3, re-timed right 3), so v_L(t) = v_R(1.5 t) - 6 holds only for left starts on the slow eigenline; and row 2 is an inequality whose difference decays toward 0, equal only if equal at the start. The certified rows are fine; the prose overstates them, and "Exact: no tolerance constant" sits next to a row 1 that is 3.33 m/s slack.
- Concern 2 (LOW): row 1 (re-timed "never faster") certifies down to v_L <= v_R - 3.33; constant 0 is a requirement only in a re-timed sense whose relevance is not argued; the real-time overspeed claim exists at lambda 1 but is not this file's claim. The claim reads as chosen for S.
- Concern 3 (LOW): both guards are forward-invariant reachable hulls (engaged envelopes), not controller logic. Not load-bearing for the stated rows by a face argument (row 1 at 0 needs only row 2 and a_R >= -15, the domain gives -10), but no measurement with guard = domain is stated.
- Fix: replace the "Reading" with "the dominant-mode speed of the attacked car is at most the reference's re-timed by 3/2 and lowered by 6; the gap decays"; drop "holds with equality" and "Exact"; state why the re-timed comparison is a requirement or present row 1 as a consequence with its 3.33 slack.

## elevator_start_discbrake
- Model: 4-phase elevator trip (LIFT/UP/APP/STOP), left disc brake k = 50 vs right drum brake k = 5; everything else identical.
- Property: z, v equal in every left mode; in LIFT also b_R <= b_L; holds up to the reference finishing its lift alone (R).
- Concern (LOW): the claim is true by construction: the z, v ODEs are identical on both sides and b never enters them, so after the reference's lone lift the witness copies the left. The benchmark's value is the R mechanism, not the property. LIFT_L is entered only as a start and (k = 50) lasts one window, but every trip starts there, so the D letter is not start-only structure in the artifact sense.
- Minor (LOW): v <= 1.7 m/s has no stated physical source (about 106 % of rated; governor trips are usually about 115 %); rest 7 cm past the landing is a large levelling error for a real elevator; the brake drop rate b' = -5 b is the same on both sides though the brakes differ (irrelevant to rows).

## platoon_profiles
- Model: one CACC link, SPORT (kp 0.18, kd 0.85) vs NORMAL (kp 0.125, kd 0.75); poles, damping, modal forms and the disturbance w = 0.06 r_R all recompute correctly; lambda = 6/5 = sqrt(0.18/0.125).
- Property: |Delta g| <= 3.34 at t vs 1.2 t, with modal rows |P_0.4| <= 1.14, |P_0.45| <= 1.50 and left-only floors g_L >= 5, g_L + 2 r_L >= 5.
- Concern 1 (LOW): 3.34 is called a "Requirement" but is the tool's cut-chain value; the header itself shows the claim is inductive from 2.78 (face check verified: 1 + 0.04 c <= b <= 0.4 c). Not HIGH: the header says "not tight" openly and the tool declines the tighter pair. The label "Requirement" is circular.
- Concern 2 (LOW): g_L + 2 r_L >= 5 is literally the left guard face (left-only, implied by the forward-invariant guard), and its 5 is not tight (19.44 certifies, disclosed). These two unary rows add no relational content.
- Concern 3 (LOW): |r| <= 10 is load-bearing (W = 0.06 x 10); it is a radar rated range-rate / engagement limit, stated as such (accepted item 3 applies).
- Fix: call 3.34 "the certified bound" (not a requirement), or give a sourced spacing requirement it meets; drop or tighten the TTC row.

## rampmeter_poll_2to1
- Model: two-cell free-flow CTM with a 6-level density-banded ramp-meter table; left polled every 40 s, right updated every 20 s with rate-limited successors (proved by --wellformed). Units check: k' = (k1 + r/120 - k)/100 recomputes from 1.67 mi, 2 lanes, 60 mi/h.
- Property: equal demand and upstream density, |k_L - k_R| <= 8 (HCM LOS bands: at most one level of service apart).
- Concern (LOW): the free-flow branch at 60 mi/h up to k = 42.5 gives about 2550 veh/h/ln, above HCM basic-segment capacity at that free-flow speed; only start states reach it (steady maxima 34.3), so it is not load-bearing. Simulated gap 1.00 vs certified 8 (disclosed: inductive envelope).
- None otherwise; start-only levels disclosed and shown not to carry M or B.

## fuelcell_chp_dos
- Model: PEM CHP stack temperature with three current levels; right = nondeterministic protocol on overlapping bands every 10 s, left = deterministic thresholds held 20 s by DoS. Simulated excursions (4.30 K, 5.83 K) recompute.
- Property: |T_L - T_R| <= 7, equal return temperature.
- Strongest concern (R): the header shows the exact claim (0) is true and the attack has no physical consequence; the certified tolerances form a non-monotone set [5.00, 8.00] and {10}; 7 is neither tight (5.00) nor sourced: it is 85 - 78 = 52 - 45 where 45 degC is "a design value of this file" and the 56 degC return limit (78 = 56 + 22) is file-chosen (the cited 70/55 design gives 55). The letters P, X are genuine for the stated claim (LOW_L is the cold-start phase and, at Tin = 40, never left), but the tolerance and the letters measure the certificate's segment-end overhead, not the attack.
- Concern (LOW): the Tin design range lives in the guards and decides the prunings ([40, 58] declines); disclosed, and stated as the claim's premise.
- Fix: either (a) state the claim at the certificate's bound 5 and present it honestly as "the tool's bound for a hold that physically never leaves its band", dropping the invented 45 degC window, or (b) change the scenario so the hold is consequential and the tolerance has physical content.

## engine_start_highidle
- Model: turbofan ground start (starter, low-supply starter, light-off, self-sustain, idle, abort), left high idle 66 % vs right ground idle 62 %. Lock-step 5.51 % at t = 51 s recomputes (exact sampled flows).
- Property: starter rows exact (N2, timer, supply), light-off/abort N2_L <= N2_R, self/idle N2_L <= N2_R + 4 (tight: the idle increment).
- Concern (LOW): with unbounded right-only run-ahead, the reference can always be advanced toward 62 %, so the SELF/IDLE row is in effect N2_L <= 66 (the deployed's own idle); ABORT_L's admissible set includes a reference in IDLE (a hung deployed start related to a successful reference start). The claim is true and tight but its relational content above cut-out is thin.
- Minor (LOW): ABORT has N2' = 0 (a real aborted spool decelerates); disclosed coverage gap at N2 < 5 in ABORT_L.

## Findings by severity

HIGH
1. acc_spoof_lag: header claim false. "every speed profile of the attacked car is a sped-up, lowered profile of the reference" and "Row 2 holds with equality". Check: integrate the left from (v, a) = (24, 2) (inside the left guard: a + (v - 24) = 2, a + (5/3)(v - 24) = 2). Its fast-mode coefficient a + (v - 24) = 2 is nonzero (decays at 5/3), while every re-timed right run's fast mode decays at 3, so no right start gives v_L(t) = v_R(1.5 t) - 6 for all t. For row 2, take a related start with u_L = u_R - 7: the difference (u_L - 24) - (u_R - 30) = -1 decays to 0 but stays strictly negative, so equality never holds.

LOW
- quad_light_lag: `a` mislabeled as net specific thrust; bound 14.715 = a_cmd_L = 3 K_R (set-point coincidence via K = g/2; not load-bearing per 20 % widening); row-2 tightness is by construction of the 0.45 band.
- acc_spoof_lag: row 1 slack 3.33 with "Exact: no tolerance constant"; re-timed "never faster" requirement not argued; guards are reachable hulls (not load-bearing by face argument, not measured).
- elevator_start_discbrake: claim true by construction (b never enters z, v); v <= 1.7 unsourced; 7 cm overshoot of the landing; same brake drop rate both sides.
- platoon_profiles: "Requirement" 3.34 = tool route value (semantic 2.78, disclosed); TTC row is the guard face, not tight (19.44); |r| <= 10 load-bearing but stated physical.
- rampmeter_poll_2to1: free-flow flow above HCM capacity at the domain top (start-only states).
- fuelcell_chp_dos: inert attack, 7 K unsourced and not tight, non-monotone certifying set, guard Tin range decides P (all disclosed; scored as R = 2, RETHINK, but not HIGH by the definition: the header does not claim 7 is tight).
- engine_start_highidle: run-ahead makes SELF/IDLE nearly unary; ABORT_L admits a successful reference; ABORT N2' = 0.

## Verified HIGH findings and actions (2026-10-30)

| benchmark | finding | verification | action | letters |
|---|---|---|---|---|
| `acc_tune_limp` | M credited on a multi-step cover whose replayed path never leaves NORMAL (DISENGAGE never used) | matrix.json: the CRUISE cover's `modes_on_path` is `[NORMAL]`, budget 2, one joint step NORMAL -> NORMAL | letter rule M refined: M needs a right mode change on the replayed path of a multi-step cover (at least two right modes on the path); subsumes the single-mode rule of round 6; only this file changes; header | S M D I -> S D I |
| `quad_light_profiles` | header system equation `w' = T/m - g - K w` contradicts the file (right NORMAL is `9.81 - 4.905 w`) | with T = m_R (g + K (w_sp - w)) the file's flows are `w' = T/m - g`; the `- K w` term was spurious | header | S M B X |
| `acc_spoof_lag` | "every speed profile of the attacked car is a sped-up, lowered profile" and "row 2 holds with equality" are false as written | left roots -1, -5/3; right roots -2/3, -2, re-timed by 3/2: -1, -3; only the dominant modes match; the difference of the dominant-mode coordinates u_L - 24 and u_R - 30 decays (D' = -D) | header: the reading restricted to the dominant mode; row 2 described as a decaying, sign-keeping difference | S |

Not acted on (no HIGH): `fuelcell_chp_dos` (RETHINK at 2: the reviewer reads the exact claim as true, so the 5.00 / 7 K tolerance measures the certificate's segment-end overhead rather than the attack; a scenario redesign is an owner decision, listed as open), `turbine_startup_gearratio` (RETHINK at 2: after the round-6 fix the overspeed requirement is met by the unary ceiling; the relational factor 1.05 row stays tight), and the LOW items in the group notes.
