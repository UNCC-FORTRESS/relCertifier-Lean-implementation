# Reserve benchmarks (`benchmarks/reserve/`)

Near-duplicates and weak benchmarks, kept as inputs with their headers and verdicts. They are
**not in `suite_v2`**, not in the paper, and have no Lean integration (no IR literal, cover,
bridge instance, Assumption 1 proof, refutation instance or declared count). Each file starts
with a `# RESERVE` banner; the header below it is the design's. The four that were suite
benchmarks keep their Lean integration in git history (last on branch `benchmark-fixes` at
commit 7939cd0).

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

Run one: `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/reserve/<name>/input.txt`.
