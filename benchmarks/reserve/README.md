# Reserve benchmarks (`benchmarks/reserve/`)

Near-duplicates and weak benchmarks, kept as inputs with their headers and verdicts. They are
**not in `suite_v2`**, not in the paper, and have no Lean integration (no IR literal, cover,
bridge instance, Assumption 1 proof, refutation instance or declared count). Each file starts
with a `# RESERVE` banner; the header below it is the design's. The four that were suite
benchmarks keep their Lean integration in git history (last on branch `benchmark-fixes` at
commit 7939cd0). The four rover files (2026-10-27, batch I3) are design files; the suite files
`rover_lateral_8to12` and `rover_patrol_zones` of the same names left the suite then, with
their Lean integration in git history (last at commit 14e0405).

Verdicts measured 2026-10-27 with the branch's `relcert` (`RELCERT_IMPLIED_CUT=1`; letters as in
`benchmarks/README.md`, "Header pass"). Every file CERTIFIES by default and under
`RELCERT_WELLFORMED_STRICT=1`.

| benchmark | from | declines under | letters | reason it is in reserve |
|---|---|---|---|---|
| `airheader_dos_3to1` | suite_v2 (2026-10-26) | `NO_PRUNE`, `NO_PRUNE`+`NO_CHOICE` | M P | the claim does not depend on the attack (the supervisor DoS never changes the pressure claim; P holds only for peak demand in [0.05, 0.08)) |
| `arm_plateau_profiles` | suite_v2 | `NO_CUT`, without the implied cut, `NO_IMPLIED_CUT`, `NO_LINEAR_CUT` | M B I | the planner's profile choice is never load-bearing (a near-duplicate of `arm_plateau_crit` / `arm_plateau_slow`) |
| `platoon3_profiles` | suite_v2, stored as its round-2 design | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_PRUNE`+`NO_CHOICE` | S M | three identical time-scaled links: the three-follower copy of `platoon_profiles` adds no mechanism |
| `platoon3_linkloss` | suite_v2, stored as its round-2 design | none | D | links 2 and 3 are exact copies of link 1; replaced in the suite by `platoon_latency` |
| `h2_refuel_ambientbias` | round-2 design (never in the suite) | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_CUT`, without the implied cut, `NO_IMPLIED_CUT` | R D I | twin of `engine_start_highidle` (the same staged single-coordinate pattern and letters) |
| `grid_ffr_dos` | round-A design (never in the suite) | `NO_PRUNE`, `NO_PRUNE`+`NO_CHOICE` | M P | the bound is the no-FFR worst case; it does not depend on the hold (`RELCERT_OPREGION=1` reports admitted starts outside every right guard) |
| `rover_rollover_6to8` | round-A design (never in the suite; the round-2 name of `rover_rollover_6to7`) | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_CUT` | S M I | the same model pair (L8 / L6) and cause as `rover_ladder_6to8`; its heading, roll and LTR rows are folded into that file |
| `rover_rollover_8to12` | round-A design (never in the suite; the round-2 name of `rover_rollover_7to12`) | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_CUT` | S M I | the same model pair (L12 / L8) and cause as `rover_ladder_8to12`; its heading, roll and LTR rows are folded into that file |
| `rover_lateral_8to12` | round-A design (the suite file of that name left the suite on 2026-10-27) | `SYNC`, `SYNC`+`NO_CHOICE`, `NO_CUT` | S M I | the same model pair (L12 / L8) and cause as `rover_ladder_8to12`; its heading, roll and lane rows are folded into that file |
| `rover_patrol_zones` | round-2 design (the suite file of that name left the suite on 2026-10-27) | `SYNC`+`NO_CHOICE` | M B | its letters come only from a stretch the claim does not need: it certifies at real time (`RELCERT_SYNC=1`) with no letter |

Run one: `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/reserve/<name>/input.txt`.
