# Benchmark review, round 8 (2026-10-30; suite_v2 at bd7c608+, 3 benchmarks)

One fresh reviewer agent, 3 benchmarks, rubric `docs/review-rubric.md` plus the accepted list of decided structural choices (below); the reviewers did not see earlier reviews, scores or fix lists. Every finding carries a severity (HIGH: claim false, letter from an artifact, domain doing the claim's work, stronger claim certifies, header number wrong; LOW otherwise). Findings are reviewer claims; every claim acted on was verified by a tool run first (the fix log is in `docs/OVERNIGHT2-2026-10-30.md`).

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
| `acc_spoof_lag` | 4 | 3 | 3 | 3 | POLISH | Correct exact dominant-mode row (tight at 6). Row 1 is 3.33 m/s loose by the header's own measurement, the re-timed claim is weaker than the real-time one the file sets aside, and the header has a wrong "decaying toward 0" plus a long paragraph about rows that are not in the file. | 2 |
| `acc_tune_limp` | 3 | 4 | 4 | 3 | POLISH | Sound and tight (CRUISE exact at 3/2, LIMP 0 forced by the handoff), letters S D I are real. But the speed loops are unsaturated (7.5 m/s^2 commanded at the 20 m/s floor), DISENGAGE is dead structure, and the "7.00 m/s lead" reads as a reachable bound when it is not. | 2 |
| `quad_light_profiles` | 3 | 4 | 3 | 3 | POLISH | Nice conserved-Phi construction with a requirement-backed 0.8 m (NAV_MC_ALT_RAD), and S M B X are on the replayed path. But the Phi >= -0.8 evidence line contradicts itself, epsilon = 1.0 s is not explained, and w >= 0 is a climb-phase start restriction that the header calls the limiter. | 3 |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 0 | 3 | 0 | 0 |

Verdicts: KEEP 0, POLISH 3, RETHINK 0, DROP 0. Overall >= 4: 0/3 (0 %). Overall < 3: 0.

## Delta vs previous round

Previous histogram (1..5): 0, 4, 12, 7, 0 over 23; this round: 0, 0, 3, 0, 0 over 3.

Up: `acc_spoof_lag` 2->3, `acc_tune_limp` 2->3.

Down: none.

Not in this round: `acc_spoof_limp`, `acc_tune_lag`, `elevator_start_discbrake`, `engine_start_highidle`, `flaps_slow_approach`, `fuelcell_chp_dos`, `gantry_speed_zones`, `h2_refuel_ambientbias`, `hydro_rejection_gatecal`, `lit_gpt10_boost_converter`, `molding_pack_checkring`, `platoon_linkloss`, `platoon_profiles`, `quad_light_lag`, `rampmeter_poll_2to1`, `rover_terrain_2to4`, `rover_terrain_6to12`, `turbine_startup_gearratio`, `ventilator_vc_cuffleak`, `watertank_twospeed`.

Round 8 reviewed only the 3 files edited after round 7 (one fresh reviewer, the same rubric, accepted list and M rule).

## Reviewer notes by group

### g1

# Review r8, group g1 (acc_tune_limp, quad_light_profiles, acc_spoof_lag)

Inputs used: rubric, ACCEPTED-LIST, the three input.txt files, matrix.md and letters.md rows. No tool runs, so every
"check" below is a check to run, not one I ran.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| acc_tune_limp | 3 | 4 | 4 | 3 | POLISH | Sound and tight (CRUISE exact at 3/2, LIMP 0 forced by the handoff), letters S D I are real. But the speed loops are unsaturated (7.5 m/s^2 commanded at the 20 m/s floor), DISENGAGE is dead structure, and the "7.00 m/s lead" reads as a reachable bound when it is not. |
| quad_light_profiles | 3 | 4 | 3 | 3 | POLISH | Nice conserved-Phi construction with a requirement-backed 0.8 m (NAV_MC_ALT_RAD), and S M B X are on the replayed path. But the Phi >= -0.8 evidence line contradicts itself, epsilon = 1.0 s is not explained, and w >= 0 is a climb-phase start restriction that the header calls the limiter. |
| acc_spoof_lag | 4 | 3 | 3 | 3 | POLISH | Correct exact dominant-mode row (tight at 6). Row 1 is 3.33 m/s loose by the header's own measurement, the re-timed claim is weaker than the real-time one the file sets aside, and the header has a wrong "decaying toward 0" plus a long paragraph about rows that are not in the file. |

## acc_tune_limp

- **Model.** 1-D speed loops. The left is a tuned CRUISE (0.75 (30 - v)) with a latched LIMP map (0.3 (25 - v)). The right is the stock NORMAL (0.5 (30 - v)) with a DISENGAGE coast below 20 m/s. Both sides decide every 0.1 s.
- **Property.** In CRUISE, the tuned speed at t equals the stock speed at 3/2 t. In LIMP, the limp car is never faster than the stock car (lambda 1). I checked by hand that the LIMP face needs v <= 37.5, which is supplied by the checked L.LIMP band cut (v <= 36). So I is real, and NO_CUT declining is consistent. D, S, I and the matrix codes M1 M2 M5 M6 all agree with the header.
- **Strongest concern.** The "Measured, not part of the claim: in LIMP the reference leads by at most 7.00 m/s (6.99 declines)" line (l.62-63). The 7.00 comes from the v_L >= 20 face of the row v_R <= v_L + c (c >= 15 - 0.4 v_L). It is not a reachable lead. The closed form from v0 = 20 is 5 + 5e^{-0.3t} - 10e^{-0.5t}, with a maximum of about 5.33 at t of about 6.0 s.
- **Other concerns.**
  - CRUISE/NORMAL are unsaturated first-order loops: 7.5 and 5 m/s^2 at the floor, far above ACC acceleration limits (about 2 m/s^2). The header does not say this.
  - DISENGAGE can be entered only as a start (NORMAL from >= 20 never drops below 20). It exists for Assumption 1 coverage of [0, 20). This is disclosed in l.60 but not named as such.
  - CRUISE exactness holds by construction (0.75 := 1.5 x 0.5), so its content is a restatement of the tune's definition.
- **Fix.**
  - Reword l.62-63 as "the row v_R <= v_L + c is inductive down to c = 7.00 (the v_L = 20 face); the reachable lead is at most about 5.33 m/s".
  - Add one sentence that the speed loops are linear without acceleration saturation.

## quad_light_profiles

- **Model.** A climb-rate P loop with mass feedforward m_R, flown on a 20 % lighter airframe. Three pilot-selectable climb profiles exist on both sides. The witness follows the pilot (committed choice X).
- **Property.** At the per-profile stretch (w_sp + 0.4)/w_sp, altitudes agree within 0.8 m, the PX4 NAV_MC_ALT_RAD radius. They are held by the conserved Phi plus rate rows.
- **What I verified by hand.**
  - The ODE coefficients and terminals (2.0/2.4/2.9).
  - Phi' = 0 in matched pairings.
  - Phi <= 0.7633 is what makes h_L - h_R <= 0.8 inductive, which matches "0.77 declines".
  - The 1.16 w_R <= w_L face, inductive iff w_R <= 2.5 (ECO, SPORT) and w_R <= 3.72 (NORMAL), which matches the header.
  - M/B/X agree with matrix and letters.
- **Strongest concern (HIGH).** l.23-24 reads "Phi >= -0.8 (needed: dropping it declines; any constant >= 0.32 certifies...)". Taken literally this contradicts itself. The other rows already imply Phi >= -0.8 - 2.5/4.905 = -1.31: use h_R - h_L <= 0.8, w_L >= 0, and w_R <= 2.5 from 1.16 w_R <= w_L <= 2.9. So any constant >= 1.31 is the same as dropping the row, which the same line says declines. By hand, the h_R - h_L = 0.8 face needs w_L >= lambda w_R. With Phi >= -c that is guaranteed for c <= 0.8, and the face is empty for c < 0.327. So the certifying set is probably [0 or 0.32, 0.8], not ">= 0.32".
- **Other concerns.**
  - epsilon = 1.0 s on both sides (the pilot's profile-switch period) is not justified anywhere.
  - SPORT w_sp = 2.5 is chosen "so its stretch is a decimal grid point" (ad hoc, disclosed).
  - The domain lower bound w >= 0 forbids descent. The header justifies only the upper bound ("the 3 m/s climb-rate limiter"). w >= 0 is forward invariant on every mode, so it only restricts starts, but the h_R - h_L face argument uses w_R >= 0 (lambda w_R - w_L <= (lambda - 1.25) w_R <= 0).
  - "Pilot switches do not move it" (l.20-21) holds only if hops take zero right time. The header should say so.
  - The 0.8 radius is a requirement, not tight (|dh| <= 0.79 likely certifies). That is acceptable, but say so.
- **Fix.**
  - Restate the Phi lower-bound evidence as the measured interval.
  - Justify epsilon = 1.0 or change it.
  - State w >= 0 as the climb-phase start set, and give the result with a descent limit, e.g. w >= -1.

## acc_spoof_lag

- **Model.** A 2-D cruise loop with a 0.375 s powertrain lag. The left's speed sensor is spoofed +25 % (settles at 24 m/s). The right is unspoofed. Guards are the forward-invariant hulls of the engagement box (checked: corners match, and the right spans v in [16.5, 36.5]).
- **Property.** At lambda = 3/2:
  - Row 1 (v_L <= v_R): the spoofed car is never faster than the reference re-timed.
  - Row 2 (u_L <= u_R - 6): the dominant-mode speeds are related exactly.
- **What I verified by hand.**
  - The roots (s+1)(s+5/3) and (s+2/3)(s+2).
  - u_L' = -(u_L - 24), and (3/2) u_R' = -(u_R - 30), so D = u_L - u_R + 6 has D' = -D. Row 2 is invariant, and -6.01 fails, so it is tight.
  - Row 1's face needs a_R >= -15, while the guard gives a_R >= -11. So the domains are not load-bearing, which agrees with NO_CUT certifying.
  - Letter S only, and M2 without M is correct under the M rule.
- **Strongest concern.** Row 1 holds with 3.33 m/s to spare (l.35 says so) yet is stated with constant 0. For a sensor attack, the real-time bound (v_L <= v_R at equal times) is the meaningful claim. The file sets it aside (it certifies at lambda 1 with letter I) in favour of the re-timed one that earns S. The spoof direction (reading high, so the car is slower) also makes "never faster" the expected outcome.
- **Other concerns.**
  - l.79 says "each decaying toward 0", but 3a + 2v and a + 2v decay toward 60.
  - The header is long: l.61-69 describe rows not in the file, plus batch history. Trim them.
- **Fix.**
  - Fix l.79.
  - Either state row 1 as v_L <= v_R - 3.33 (or justify 0 as the requirement in one line and drop "Exact: no tolerance constant" for row 1), or move the real-time claim into the file.
  - Cut the consequence paragraph to one sentence.

## Findings with severity

| # | benchmark | severity | finding | check that verifies it |
|---|---|---|---|---|
| 1 | quad_light_profiles | HIGH | Header evidence line (l.23-24) "Phi >= -0.8 ... dropping it declines; any constant >= 0.32 certifies" contradicts itself. Phi >= -1.31 is implied by h_R - h_L <= 0.8, w_L >= 0 and w_R <= 2.5, so any constant >= 1.31 is dropping. | Run the file with the last conjunct's 0.8 replaced by 1.5, 1.0, 0.81, 0.8, 0.32, 0.31 and 0.0 (all three rows). Expected: 1.5 declines (same as dropping), 0.81/1.0 decline, and 0.31/0.0 most likely certify. Restate the measured interval. |
| 2 | quad_light_profiles | LOW | Domain lower bound w >= 0 (no descent) is a climb-phase start restriction, not a physical limit. The header justifies only the 3 m/s upper bound. w_R >= 0 is used in the h_R - h_L face. If the check declines, this becomes HIGH (the domain does the claim's work). | Change the evolve/guard to w >= -1.0 on both sides and run. |
| 3 | quad_light_profiles | LOW | epsilon = 1.0 s (the pilot's profile-switch period) is unjustified. | none needed (header) |
| 4 | quad_light_profiles | LOW | "Pilot switches do not move it" holds only for zero-time hops. Say that hops take zero right time (windows <= epsilon). | none needed (header) |
| 5 | quad_light_profiles | LOW | SPORT w_sp = 2.5 is picked for the grid (ad hoc, disclosed). The 0.8 radius is not tight (requirement-justified). | none needed |
| 6 | acc_tune_limp | LOW | "Reference leads by at most 7.00 m/s (6.99 declines)" is an inductiveness limit of the linear row at the v_L = 20 face. The reachable maximum lead is about 5.33 m/s (closed form from v0 = 20). | Closed form: max over t of 5 + 5e^{-0.3t} - 10e^{-0.5t} is about 5.33 at t of about 6.0. |
| 7 | acc_tune_limp | LOW | Unsaturated loops: 7.5 m/s^2 (CRUISE) and 5 m/s^2 (NORMAL) commanded at the 20 m/s floor, above ACC limits. Not stated. | none needed (header) |
| 8 | acc_tune_limp | LOW | DISENGAGE is start-only (NORMAL never drops below 20). It is kept for Assumption 1 coverage, and that reason should be said. 2 m/s^2 is high for engine braking. | none needed |
| 9 | acc_tune_limp | LOW | The CRUISE exact row holds by construction (0.75 = 1.5 x 0.5): it restates the tune's definition. | none needed |
| 10 | acc_spoof_lag | LOW | Row 1 constant 0 is loose by 3.33 (disclosed, l.35), yet l.52-53 say "Exact: no tolerance constant". Not claimed tight, so not HIGH. | none needed |
| 11 | acc_spoof_lag | LOW | The re-timed claim was chosen over the more meaningful real-time overspeed claim (which certifies at lambda 1). The spoof direction makes "never faster" the expected outcome. | none needed |
| 12 | acc_spoof_lag | LOW | l.79 says "each decaying toward 0": 3a + 2v and a + 2v decay toward 60 (v = 30, a = 0). | Substitute the equilibrium (30, 0). |
| 13 | acc_spoof_lag | LOW | The header is bloated: a consequence paragraph about non-file rows (l.61-69) plus batch history. | none needed |

Header numbers I checked against matrix.md/letters.md and found consistent: letters (S D I; S M B X; S), budgets
(2; 2/2/2; 2), the handoff counts (3/3 non-vacuous; 9/9 and 1/1 vacuous), pruned edges, the admissible starts, and the
NO_CUT/NO_PRUNE/SYNC verdicts.

## Verified HIGH findings and actions (2026-10-30)

| benchmark | finding | verification (`tmp/verify-r8/`) | action |
|---|---|---|---|
| `quad_light_profiles` | the evidence for the row Phi >= -0.8 ("any constant >= 0.32 certifies") contradicts itself | lower edge -c: c = 0, 0.31, 0.32, 0.8 CERTIFIED; c = 0.81, 1.0, 1.31, 1.5 and the row dropped DECLINED. Phi is conserved, so the band is a start relation and -0.8 is the widest edge for which the 0.8 m requirement holds | header (the measured interval stated) |

Checked on the way (LOW, would have been HIGH): the domain's `w >= 0` is not load-bearing (`w >= -1` on both sides CERTIFIES). Also fixed (LOW): `acc_spoof_lag`'s modal coordinates relax toward 60, not 0.
