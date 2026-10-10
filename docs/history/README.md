# docs/history: superseded records

These files describe earlier states of the project. None of them describes the current
artifact; for that, read the top-level `README.md`, `docs/CERTIFICATION-CHECK.md`,
`docs/PAPER-MAPPING.md`, `docs/VERDICTS.md`, `docs/HANDOFF.md` and `docs/SUITE-REDESIGN.md`.
Most of them describe the retired legacy suite (`benchmarks/suite_uniform`, removed from the
tree on 2026-10-10; git history keeps it) and its batteries, whose modules were deleted in
the same cleanup unless one of the 19 carried-over theorems needs them.

| file | what it recorded | superseded |
|---|---|---|
| `ARCHITECTURE.md` | the early finding that forced the certified-checker re-architecture (search untrusted, cover re-decided by a verified checker) | 2026-07, by the architecture the repository has |
| `ASSET-MAP.md` | the load-bearing theorems of the legacy modal battery (`Instances/ModalBattery.lean`) | 2026-10-10, by the suite_v2 battery (README, "Theorem families") |
| `BENCHMARK_INSTANTIABILITY.md` | per-benchmark instantiability against the early `tooling_sound` chain | 2026-07, by the settling and modal batteries (both since retired or replaced) |
| `CONTAINMENT-AUDIT-2026-07-31.md` | the morning-of-2026-07-31 argument for the verdict hypotheses | the same day, by the pinned verdict runner |
| `COVER-AUDIT.md` | the tool's cover search vs. the mechanization: stratified differential cuts (R4), the `⊤`-guard note, the 2026-10-09 removal of the static (zero-duration) reposition, the parser-key finding | 2026-10-10: the current account of the `⊤` guards is `docs/PAPER-MAPPING.md`; the code is the record of the rest |
| `CUT-COMPOSITION.md` | the cut-composed `…_declared` theorems of the legacy arm benchmarks | 2026-10-10, retired with the legacy suite (`Proofs/Encoding/CutComposition.lean` stays as a generic leaf) |
| `CUT-LIFT-SCOPE.md` | scope of the checked-cut lift | completed 2026-07 (`Proofs/Soundness/CutLift.lean`, `CutCover.lean`) |
| `DEVELOPMENT-ARC.md` | narrative of the development arcs through 2026-07 | history only |
| `FIXPOINT-DESIGN.md` | proposal: the winning-region fixpoint (its prototype script was removed 2026-10-10) | premise superseded 2026-07-30; not implemented |
| `INTRA-PIECE-SWITCH-SCOPE.md` | scope of intra-window mode switching | completed 2026-07-30 (`Proofs/Encoding/SplitCoupling.lean`) |
| `KGT1-ASSEMBLY-SCOPE.md` | scope of the k > 1 window assembly | completed 2026-07-30 (`Proofs/Encoding/RepoPrefixR.lean`, `WindowRF.lean`) |
| `LEMMA-SCOPE.md` | scope of the response-structure lemma groups L1 to L7 | completed 2026-07-30 |
| `MULTIFLOW-REALIGN.md` | task H: realigning the legacy suite onto the multi-flow chain | completed 2026-07 |
| `PAPER-MAPPING-INVENTORY.md` | the 2026-07-19 paper ↔ mechanization inventory: every generic `rvalid (theorem3Form …)` theorem, the findings of a full read of `Proofs/`, the per-benchmark tables of the legacy suite, the R-series gates in detail | 2026-10-10, by the current `docs/PAPER-MAPPING.md` |
| `PRUNING.md` | the non-connection pruning exhibit of the legacy suite (`match_multi_rate`'s `STALL` fallback, thirteen dropped candidates) | 2026-10-10: the pruning record of the paper's suite is `docs/SUITE-REDESIGN.md` (matrix column M4) |
| `READING-GUIDE.md` | reading guide to the legacy-era repository: live vs historical routes, vacuity traps | 2026-10-10, by `README.md` and `docs/PAPER-MAPPING.md` |
| `RESET-MAPS-SCOPE.md` | proposal: reset maps in the models | deferred 2026-07-19; not implemented |
| `ROADMAP.md` | the R1 to R7 roadmap to the end-to-end guarantee | completed 2026-07 |
| `ROTATION-SCOPE.md` | proposal: equivalence of the flow-then-jump and jump-then-flow automaton shapes | scoping only (2026-07-19); not implemented |
| `SUITE-DEDUPE.md` | deduplication of the legacy suite, 46 to 40 certified benchmarks | 2026-10-10, by suite_v2 |
| `THEOREM3-ALL-BENCHMARKS-PLAN.md` | plan for modal Theorem 3 on every legacy benchmark | completed 2026-07-30 |
| `VERDICT-EVIDENCE-AUDIT.md` | the 2026-07-31 audit of the verdict hypotheses, which introduced the pin discipline still used by `Verdicts/` and `VerdictsV2/` | numbers superseded 2026-10-10 (`docs/VERDICTS.md`) |
| `VIABILITY-FACE-CENSUS.md` | face census of the legacy suite (47 benchmarks) behind the stratified-face lemmas | 2026-10-10, retired with the legacy suite |
