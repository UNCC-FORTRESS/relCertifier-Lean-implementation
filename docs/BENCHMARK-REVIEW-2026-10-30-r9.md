# Benchmark review, round 9 (2026-10-30; suite_v2 at bd7c608+, 1 benchmarks)

One fresh reviewer agent, 1 benchmark, rubric `docs/review-rubric.md` plus the accepted list of decided structural choices (below); the reviewers did not see earlier reviews, scores or fix lists. Every finding carries a severity (HIGH: claim false, letter from an artifact, domain doing the claim's work, stronger claim certifies, header number wrong; LOW otherwise). Findings are reviewer claims; every claim acted on was verified by a tool run first (the fix log is in `docs/OVERNIGHT2-2026-10-30.md`).

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
| `quad_light_profiles` | 3 | 3 | 4 | 3 | POLISH | All numbers I could check by hand are correct and the tight values hold, but the stretch rests on a P-only climb loop with fixed m_R feed-forward that the header never calls a simplification. Within one profile the deployed is exactly the reference time-scaled, so beyond the start band the only content is a switch transient of at most 0.037 m. | 3 |

## Score histogram (overall)

| overall | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| count | 0 | 0 | 1 | 0 | 0 |

Verdicts: KEEP 0, POLISH 1, RETHINK 0, DROP 0. Overall >= 4: 0/1 (0 %). Overall < 3: 0.

## Delta vs previous round

Previous histogram (1..5): 0, 0, 3, 0, 0 over 3; this round: 0, 0, 1, 0, 0 over 1.

Up: none.

Down: none.

Not in this round: `acc_spoof_lag`, `acc_tune_limp`.

Round 9 reviewed only `quad_light_profiles`, the one file edited after round 8 (one fresh reviewer). No HIGH finding: the fixpoint of the review loop (2026-10-30, 02:23).

## Reviewer notes by group

### g1

# Review r9 / g1: quad_light_profiles

Inputs: rubric, ACCEPTED-LIST, `benchmarks/suite_v2/quad_light_profiles/input.txt`, matrix.md (rows 34, 60-62, 141, block 1202ff), letters.md (row 32). Nothing run.

| benchmark | P | R | C | overall | verdict | one-line reason |
|---|---|---|---|---|---|---|
| quad_light_profiles | 3 | 3 | 4 | 3 | POLISH | All numbers I could check by hand are correct and the tight values hold, but the stretch rests on a P-only climb loop with fixed m_R feed-forward that the header never calls a simplification. Within one profile the deployed is exactly the reference time-scaled, so beyond the start band the only content is a switch transient of at most 0.037 m. |

## quad_light_profiles

- **Model.** Vertical climb `h' = w`, `w' = T/m - g` under a P velocity loop `T = m_R (g + K (w_sp - w))`. The reference has mass m_R. The deployed has m_L = 0.8 m_R and runs the same thrust law, so it climbs at a steady w_sp + 0.4. Three pilot profiles (ECO, NORMAL, SPORT) can be switched in any order on both sides. I re-derived every ODE constant and they are all correct: 7.848, 9.81, 12.2625 on the right; 12.2625, 14.715, 17.780625 on the left; 0.4 = 0.25 g / 6.13125.
- **Property.** For each profile p, the reference is run λ_p = (w_sp+0.4)/w_sp times faster (5/4, 6/5, 29/25). Under that scaling |h_L - h_R| <= 0.8 m holds; 0.8 m is the PX4 parameter NAV_MC_ALT_RAD, which justifies the value. The rows Phi ∈ [-0.8, 0.76], 1.16 w_R <= w_L and w_L <= 2.9 make the claim inductive. I checked by hand:
  - Phi' = 0 in each matched pairing.
  - The upper edge is exactly 0.8 - 0.09·2.5/6.13125 = 0.7633, so "0.77 declines" is right.
  - Without Phi >= -0.8 the requirement row only forces Phi >= -0.837, and for u < 0 the ECO pairing (u' = -6.13 u) breaks the row. So "dropping it declines" and "-0.81 declines" are right.
  - The boundary derivative of the 1.16 row in SPORT is 1.280 - 0.512 w_R >= 0 iff w_R <= 2.5. With 1.17 it needs w_R <= 2.2 while w_R can reach 2.48, so "1.17 declines" is right.
  - w_L <= 2.9 is the SPORT terminal value, so "2.89 declines" is right.
- **Strongest concern (P).** The stretch comes entirely from a steady-state velocity error (the w_sp + 0.4 terminal value), which exists only because the loop is pure P with a fixed m_R·g feed-forward. A real multicopter velocity loop has an integrator and/or a hover-thrust estimator (PX4 MPC_Z_VEL_I_ACC, the hover-thrust estimator). Either one drives the deployed's terminal climb rate back to w_sp, which makes λ → 1 and the time-scaled claim no longer fits. Smaller points: K = 4.905 = g/2 and SPORT = 2.5 m/s were picked for a clean grid. The header says so for 2.5, but neither is a source parameter.
- **Second concern (R).** Per profile the deployed is *exactly* the reference time-scaled: with v = λ_p w_R, v' = 6.13125 (w_sp + 0.4 - v), the same ODE as the left. So Phi is a start relation (the header says so). The only behaviour not fixed at the start is the transient u = w_L - 1.25 w_R after a profile switch, which moves the altitude gap by at most 0.0367 m. Any requirement r certifies with the band [-r, r - 0.037]. The claim is genuine and the tightness evidence is good, but it is close to "the start offset is within the band".
- **Fix (POLISH).**
  1. Add a deviation line: the climb loop is P-only with fixed m_R hover feed-forward (no integrator, no hover-thrust estimation); this is what creates the steady over-speed and hence λ_p.
  2. Add one sentence: per profile the deployed equals the reference time-scaled by λ_p, so the content is the switch transient (<= 0.037 m) plus the start band.
  3. Change "about 11 s" to "about 10 s".
  4. Make the B line name all three covers.

## Findings with severity

HIGH: none found.

LOW:
1. (P) The P-only loop with fixed m_R feed-forward and no integral action or hover-thrust estimation is undisclosed, and the whole stretch depends on it (see above).
2. (R) Per-profile exact time-scaling conjugacy means the property's non-start content is a <= 0.037 m switch transient. The header discloses that Phi is conserved but not that the conjugacy is exact.
3. (C) The header says "CERTIFIED (about 11 s)", but matrix.md gives 10041 ms and 10.31 s and letters.md gives 9.9 s. The header should say "about 10 s". I graded this LOW rather than HIGH because it is a hedged timing rather than a claim number, and run time is not a quality measure (accepted item 6).
4. (C) The header's B note ("the reference's NORMAL segment retains ECO and SPORT") names only the NORMAL cover, but matrix M3 has branch=2 in all three covers (ECO, NORMAL, SPORT). Possible check to confirm B is on the replayed path: in the ECO_L cover the postJ hops `NORMAL:hop(B=1,postJ)->[ECO@1]` and `SPORT:hop(B=1,postJ)->[ECO@1]` send the right to another profile and back while the left stays in ECO. Replay a paired run with one pilot switch (for example ECO→SPORT at a window boundary) and log the cover segments it uses. B is real if the non-self successors of a joint step are among them. If only these postJ there-and-back branches supply branch=2, B is dead structure, and this item becomes HIGH. From the switching semantics I expect B to be real, because the right follows the left's switch at the joint's end.
5. (P) The domain `w >= 0` limits the benchmark to climbing (descent excluded); it is not a physical limit. The header says it is not load-bearing (w >= -1 certifies), so it is harmless, but the `# Domain` line calls the whole domain physical and only names the 3 m/s limiter.
6. (C) The run log entry "Review round 6 (2026-10-30): the deployed gained the three profiles..." records process history in the header. It should state the current design instead.
7. (C) `max_depth = 8` and `bound_T = 4.0` are not explained. They are probably tool defaults; this is minor.

Action on a LOW: the header's run time corrected to about 10 s (matrix 10.0 / 10.3 s). Open (LOW): confirm that B rests on hops on the replayed path after a pilot switch, not only on the ECO_L cover's there-and-back hops.
