# `Archive/` — superseded developments, kept for the record

Files here are **compiled but not built upon**. Each one is either a retired route, a
hand-built template whose generated successor shipped, or a mechanized counterexample
that documents why a route was retired. Every file states at its head what superseded it.

They stay in the build (imported from `RelCertifier.lean`) for two reasons: a compiled
archive cannot silently rot, and several of them are cited by the docs as *evidence* —
`ProbeMvHd.lean`, for instance, is a mechanized vacuity counterexample referenced by
`docs/READING-GUIDE.md` §4.

**Do not cite an archived theorem as a result.** Some conclude impressive-looking
statements from hypotheses this repository proves unsatisfiable for its benchmarks
(`GBoxAll`, `hbudgetAll` — see `docs/READING-GUIDE.md` §4). The live results are the
per-benchmark instances in `Instances/`, audited by `Instances/ModalBattery.lean`; the
recipe for checking them is `docs/CERTIFICATION-CHECK.md`.

Archived on 2026-07-30, when the modal form reached suite parity (46/46): `EndToEnd.lean`,
`Mega.lean`, `ThroughoutPilot.lean`, `WatertankThroughout.lean`.
