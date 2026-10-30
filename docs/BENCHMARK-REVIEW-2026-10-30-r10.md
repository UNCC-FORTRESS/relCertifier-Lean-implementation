# Benchmark review, round 10 (2026-10-30, batch 10)

Scope: the files changed or added in batch 10 (`docs/BATCH10-2026-10-30.md`). Four fresh reviewers
(round 10: three groups; round 10b: the files edited after round 10), each given only
`docs/review-rubric.md`, the accepted list `tmp/review-r10/ACCEPTED-LIST.md` (the round-6 list with
two changes: stretch 0 is credited under S, the former W; M is the cover shape, matrix M2), the input
files, and this batch's `matrix.md` / `letters.md` (`tmp/review-r10/out/`, `out2/`). Every finding
carries HIGH or LOW; every HIGH was checked by a tool run or by arithmetic before any action.

## Round 10 (7 files)

| benchmark | P | R | C | overall | verdict | HIGH findings |
|---|---|---|---|---|---|---|
| `h2_refuel_ambientbias` | 4 | 3 | 4 | 3 | POLISH | none |
| `acc_spoof_limp` | 3 | 3 | 3 | 3 | POLISH | 1 (M B from the 2 s / 1 s periods) |
| `rover_terrain_2to4` | 4 | 3 | 4 | 3 | POLISH | none |
| `turbine_startup_gearratio` | 3 | 3 | 3 | 3 | POLISH | 2 (gust amplitude; R from start pairs) |
| `boiler_purge_vfd` | 4 | 3 | 3 | 3 | POLISH | 1 (a stronger claim certifies) |
| `autoclave_liquid_steambank` | 4 | 4 | 5 | 4 | KEEP | none |
| `pack_coldcharge_broadcast` | 3 | 3 | 2 | 2 | POLISH / RETHINK | 4 (header verdict; kinetics numbers; currents; cabin range) |

### HIGH findings and their verification

| file | finding | check | result | action |
|---|---|---|---|---|
| turbine | IEC 61400-1 eq. (17) used Lambda_1 / D instead of D / Lambda_1: V_gust = 3.3 sigma_1 / (1 + 0.1 x 126 / 42) = 5.03 m/s, not 6.33 | arithmetic: sigma_1 = 0.14 (0.75 x 11.4 + 5.6) = 1.981, 6.537 / 1.3 = 5.029 | VERIFIED | domain `G <= 5.03` on every mode, header numbers redone (plateaus 13.0198 / 13.6708 rpm, run-level 0.0173), Lean proof constants adapted; tight 0.0605 unchanged (0.0604 declines), letters unchanged R D I X |
| turbine | R only from start pairs on the 1.05 face; with `w_L <= w_R + 0.2` in the SPINUP row NO_REPO should certify | variant, `RELCERT_NO_REPO=1` | NOT VERIFIED (CERTIFIED, NO_REPO DECLINED) | test added to the header as further evidence |
| boiler | the per-run form `p_R <= p_L + e_L` is stronger than the band 0.1962 and should certify | variant | VERIFIED (CERTIFIED; NO_REPO DECLINED; `0.999 e_L` and `e_L - 0.001` DECLINE) | FIRE row now the per-run form; the fleet band 0.1962 stated as implied |
| acc_spoof_limp | M B come only from the 2 s left period (equal 1 s periods give I X), which the immediate latch contradicts | variant (measured in the design phase) | the fact VERIFIED (I X at equal periods); the artifact reading NOT accepted: the period is the supervisor's decision interval, disclosed since review round 6 (LOW there), a design difference like the M carriers' poll periods, not start-only or dead structure | header states that the 2 s is a design value of the file and that the spoof shows in I and X |
| pack | header lists RELCERT_SINGLE_STEP as certifying | run | VERIFIED (DECLINED) | file withdrawn (below) |
| pack | Ea 50 to 70 kJ/mol gives up to 2.16 per 7 K near 0 degC, not "below 2" | arithmetic | VERIFIED | file withdrawn |
| pack | P comes from chosen STL / RT currents | variant with the TRM defaults for STL and RT | NOT VERIFIED (certifies at 8, NO_PRUNE DECLINES) | - |
| pack | the cabin range [-5, 14] does the claim's work and sits inside the letter window | variant `p >= -10` | VERIFIED (DECLINED at 7) | file withdrawn: `fuelcell_chp_dos` stays (`benchmarks/skipped/pack_coldcharge_broadcast/SKIPPED.md`) |

### LOW findings acted on (header only)

`h2_refuel_ambientbias`: the relational content at completion is the 2.4 MPa shift (the binding pair is
the deployed at its top-off set point against the completed reference); the bank arm of the cause test
changes two things, so the bank evidence is the start-only test; TOPOFF_L's right-only step is a start
pair only (the letter rests on TOPOFFEARLY_L); the abort sentence now says the aborts are out of scope
(no gas temperature, the ramp is a design value). `acc_spoof_limp`: the X run shows the pairing is
reached (the driver's selection is the reference's existential choice); row 2 holds against some
legitimate driver profile, not every follower speed. `rover_terrain_2to4`: the box range of `w - v` is
[-0.75, 0.8]; 0.21 is the certificate's slip value, 0.161 the simulated one. `autoclave_liquid_steambank`:
the plateau load row is dropped because the right-only certificate cannot keep it, so D is partly a tool
need. Not acted on: header length and history (h2, rover).

## Round 10b (3 files edited after round 10)

| benchmark | P | R | C | overall | verdict | HIGH findings |
|---|---|---|---|---|---|---|
| `turbine_startup_gearratio` | 4 | 4 | 4 | 4 | KEEP | none |
| `boiler_purge_vfd` | 4 | 4 | 4 | 4 | KEEP | none |
| `acc_spoof_limp` | 3 | 3 | 4 | 3 | POLISH | none |

LOWs acted on: the turbine's stale first-draft value 0.058 removed; the boiler's tightness test is
`p_R <= p_L + 0.999 e_L` (DECLINED; the `- 0.001` form failed for small offsets at the handoff, the wrong
reason); `acc_spoof_limp`'s row-1 slack -1.33 is set by the 40 m/s domain top, and with `v <= 45` on every
mode the file still CERTIFIES. Not acted on: the turbine's GUST -> REG hops in start-up covers (start
pairs; X does not depend on them), the "same driver" parentheticals and the row-2 corner remark of
`acc_spoof_limp`.

**Fixpoint:** round 10b found no new HIGH finding.
