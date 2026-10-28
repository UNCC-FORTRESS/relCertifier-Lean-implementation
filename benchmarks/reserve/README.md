# Reserve benchmarks (`benchmarks/reserve/`)

Near-duplicates and weak benchmarks, kept as inputs with their headers and verdicts. They are
**not in `suite_v2`**, not in the paper, and have no Lean integration (no IR literal, cover,
bridge instance, Assumption 1 proof, refutation instance or declared count). Each file starts
with a `# RESERVE` banner; the header below it is the design's. The four that were suite
benchmarks keep their Lean integration in git history (last on branch `benchmark-fixes` at
commit 7939cd0). The four rover files (2026-10-27, batch I3) are design files; the suite files
`rover_lateral_8to12` and `rover_patrol_zones` of the same names left the suite then, with
their Lean integration in git history (last at commit 14e0405). The seven files of batch I4
(2026-10-27: the two chargers, `sat_detumble_nominal`, `sat3w_detumble_nominal`,
`sat3w_detumble_weak`, `arm_plateau_crit`, `arm_plateau_slow`) were suite benchmarks; each is
stored as its equal-period design of the round-A pass (RA2a), and their Lean integration (for
the round-2 files of the same names) is in git history (last at commit 0a40e7d). The four files of
batch I5 (2026-10-27: `datacenter_crah_poll`, `reactor_feed_wireless`, `rover_lateral_tirewear`,
`lng_cooldown_overspray`) are design files of rounds A and B that were never in the suite. Batch I7
(2026-10-27) swapped the two tier-2 suite members for reserve designs (a meaningful relational
property suffices; the claim need not depend on the cause): `charger_fast_tapers` returned to the
suite at the minute time scale and `quad_light_airframe_20` came here, as the suite file, with its
Lean integration in git history (last at commit a6585c2); `grid_ffr_dos` went to the suite and
`rampmeter_poll_2to1` came here, as the suite file (Lean integration last at commit 856c79a).
Batch I8 (2026-10-27) replaced own designs with case studies from published work (owner request:
credibility; the literature group of four was too thin): `hvac_fan_staging` and `platoon_profiles`,
the two tier-2 members of the final audit, came here as the suite files (Lean integration last at
commit 95033f6), for `lit_csf21_vehicle_thermo` and `lit_csf21_vehicle_bus`; then `rover_rollover_payload`,
`flaps_slow_approach` and `canal_gate_notches` came here as the suite files (Lean integration last at
commit f3400f1), for `lit_lz21_vehicle_position`, `lit_girard08_robot` and `lit_nahs25_salt_tank`.

Verdicts measured 2026-10-27 with the branch's `relcert` (`RELCERT_IMPLIED_CUT=1`; letters as in
`benchmarks/README.md`, "Header pass"). Every file CERTIFIES by default and under
`RELCERT_WELLFORMED_STRICT=1`.

| benchmark | from | declines under | letters | reason it is in reserve |
|---|---|---|---|---|
| `airheader_dos_3to1` | suite_v2 (2026-10-26) | `NO_PRUNE`, `NO_PRUNE`+`NO_CHOICE` | M P | the claim does not depend on the attack (the supervisor DoS never changes the pressure claim; P holds only for peak demand in [0.05, 0.08)) |
| `arm_plateau_profiles` | suite_v2 | `NO_CUT`, without the implied cut, `NO_IMPLIED_CUT`, `NO_LINEAR_CUT` | M B I | the planner's profile choice is never load-bearing (a near-duplicate of `arm_plateau_crit` / `arm_plateau_slow`) |
| `platoon3_profiles` | suite_v2, stored as its round-2 design | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE` | S M | three identical time-scaled links: the three-follower copy of `platoon_profiles` adds no mechanism |
| `platoon3_linkloss` | suite_v2, stored as its round-2 design | none | D | links 2 and 3 are exact copies of link 1; replaced in the suite by `platoon_latency` |
| `rover_rollover_6to8` | round-A design (never in the suite; the round-2 name of `rover_rollover_6to7`) | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_CUT` | S M I | the same model pair (L8 / L6) and cause as `rover_ladder_6to8`; its heading, roll and LTR rows are folded into that file |
| `rover_rollover_8to12` | round-A design (never in the suite; the round-2 name of `rover_rollover_7to12`) | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_CUT` | S M I | the same model pair (L12 / L8) and cause as `rover_ladder_8to12`; its heading, roll and LTR rows are folded into that file |
| `rover_lateral_8to12` | round-A design (the suite file of that name left the suite on 2026-10-27) | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_CUT` | S M I | the same model pair (L12 / L8) and cause as `rover_ladder_8to12`; its heading, roll and lane rows are folded into that file |
| `rover_patrol_zones` | round-2 design (the suite file of that name left the suite on 2026-10-27) | `SYNC`+`NO_CHOICE` | M B | its letters come only from a stretch the claim does not need: it certifies at real time (`RELCERT_SYNC=1`) with no letter |
| `charger_fast_setpoints` | suite_v2, stored as its round-A (equal-period) design | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE`, `NO_CUT`, without the implied cut, `NO_IMPLIED_CUT` | R D I | a twin of `charger_fast_tapers` (back in the suite since batch I7): the same charger and claim form with one taper and no P, on the old hour time scale; stale name (both sides target 90 %) |
| `sat_detumble_nominal` | suite_v2, stored as its round-A (equal-period) design | none | none | no letter; it equals `sat_detumble_phases` restricted to `DETUMBLE` |
| `sat3w_detumble_nominal` | suite_v2, stored as its round-A (equal-period) design | none | none | no letter (the 6-D lift of `sat_detumble_nominal`; `sat3w_detumble_phases` is the 6-D scaling point) |
| `sat3w_detumble_weak` | suite_v2, stored as its round-A (equal-period) design | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE`, `NO_CUT` | I X | the same numbers as `sat_detumble_weak` (the binding case puts all the energy on the weak axis) |
| `arm_plateau_crit` | suite_v2, stored as its round-A relational redesign | none | none | no genuinely relational claim against the ramp planner; the relational redesign (against the massless design model) earns no letter; planner fallback: the ramp-planner file with equal periods (R I, unary binding case) |
| `arm_plateau_slow` | suite_v2, stored as its round-A relational redesign | none | none | as `arm_plateau_crit`; planner fallback: the ramp-planner file with equal periods (I, unary binding case) |
| `datacenter_crah_poll` | round-A design (never in the suite) | none | M | near-duplicate of `tank_dos_3to1` (1-D storage driven by a monotone exogenous ramp, four stages on equal bands, one-sided rows, M from chain depth under a period-ratio cause; `tank_dos_3to1` keeps M I) |
| `rover_lateral_tirewear` | round-A fill design (never in the suite) | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE`, `NO_CUT` | X I | twin of `rover_rollover_payload` (in the reserve too since batch I8; the same right model, band guards and claim-form X I; the wear is one more gain in the same roll-slip loop), and it sits at three decline edges at once |
| `lng_cooldown_overspray` | round-A fill design (never in the suite) | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE` | X | the `hvac_fan_staging` pattern (an identity hop through a permissive band reference, X from the claim form); its parameter sits at a decline edge (rho 1.05 against about 1.054) |
| `quad_light_airframe_20` | suite_v2 (2026-10-27, batch I7) | `SYNC`, `SYNC`+`NO_CHOICE` | S M | the lag-free special case of `quad_light_lag` (the same airframe pair, cause, 0.8 m requirement and lambda 6/5); its tier-2 place in the suite went to `charger_fast_tapers` |
| `rampmeter_poll_2to1` | suite_v2 (2026-10-27, batch I7) | none | M B | the chain-depth template of `tank_dos_3to1` and `insulin_basal_cgmloss` repeated (shared with insulin: a constant exogenous input, a first-order upstream state, a regulated state read through a level table, a 2:1 update ratio, a symmetric band), and its 10 veh/mi/ln requirement is only 1.0 below the 11 at which any deployed schedule certifies; its tier-2 place in the suite went to `grid_ffr_dos` |
| `hvac_fan_staging` | suite_v2 (2026-10-27, batch I8) | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE` | X | tier 2 in the final audit: its X is the identity hop of template B (a deterministic left against a permissive reference), the pattern that sent `lng_cooldown_overspray` here; the literature case studies of batch I8 show X with a non-identity commitment |
| `rover_rollover_payload` | suite_v2 (2026-10-27, batch I8) | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE`, `NO_CUT` | X I | both letters come from the claim form (they persist at `h_L = h_R`), and the two sides differ in a second structural way besides the payload (the reference's 2 m transition bands with back edges, load-bearing) |
| `canal_gate_notches` | suite_v2 (2026-10-27, batch I8) | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE` | X | one of several X-only own designs (template B, with `bms_chiller_undercharge` and `compressor_station_recycle`); the literature case studies of batch I8 now show X |
| `insulin_basal_cgmloss` | suite_v2 (2026-10-28, batch I9) | none | M B | the chain-depth multi-cycle template under a 2:1 period ratio is carried by `tank_dos_3to1` (M I, with load-bearing mode facts), `fuelcell_chp_dos` (M B P X) and the three satellite files; the third slowest suite file (15 s); the medical domain stays represented by `ventilator_vc_cuffleak` and `syringe_relay_prearm`; its place in the suite went to `flaps_slow_approach` (S) |
| `bms_chiller_undercharge` | suite_v2 (2026-10-28, batch I10) | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE` | X | a single-letter file that certifies under `SYNC`; its non-identity commitment (the reference's half-speed chiller level against the deployed's degraded full-speed one) stays represented by `compressor_station_recycle` and `fuelcell_chp_dos`; its place in the suite went to `zone_lightmass_schedule` (S M B X, a time-scaled claim that declines under `SYNC`) |
| `antenna_track_kvretune` | suite_v2 (2026-10-28, batch I11) | none | D | the weakest D of the suite: its D comes only from the rule that a uniform row drops a stated requirement (the slew-lag envelope row), a single-letter own design; its place in the suite went back to `platoon_latency` (D, the degraded-network scenario) |
| `compressor_station_recycle` | suite_v2 (2026-10-28, batch I11) | `NO_CHOICE`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE` | X | a single-letter own design whose X is an identity hop into the deployed's own level (the hop persists with a healthy valve; the fault only moves its target), no external source; its place in the suite went to `reactor_feed_wireless` (M B P) |
| `molding_pack_checkring` | suite_v2 (2026-10-28, batch I11) | none | D | a single-letter own design with no external source for the 25 bar envelope or the hold time; its place in the suite went to `h2_refuel_ambientbias` (R D I, SAE J2601) |

Batch I9 (2026-10-27/28) took `flaps_slow_approach` and `platoon_profiles` back into the suite (the latter
as the round-A time-scaled design, SPORT = the CACC at 1.2 x bandwidth, S M D) and brought
`platoon_latency` (Lean integration last at commit 9dcda0c) and `insulin_basal_cgmloss` (last at c57ca5f)
here as the suite files; `tank_dos_3to1` was here between commits 5f3bb55 and c57ca5f and is back in
the suite (its I keeps the letter total at the frozen 17). Batch I10 (2026-10-28) brought
`bms_chiller_undercharge` here (Lean integration last at commit 3480f5b) and took `zone_lightmass_schedule` in.
Batch I11 (2026-10-28, the reserve scan) brought `antenna_track_kvretune`, `compressor_station_recycle` and
`molding_pack_checkring` here as the suite files (Lean integration last at commit fb55b6e) and took `platoon_latency`,
`reactor_feed_wireless` and `h2_refuel_ambientbias` (the latter two with their headers completed: the SAE J2601 source,
what the reactor file does not model, letter windows) into the suite.

Run one: `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/reserve/<name>/input.txt`.
