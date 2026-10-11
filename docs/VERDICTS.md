# Verdicts: how every Z3 hypothesis of the battery is discharged

Every Theorem 3 of `RelCertifier/InstancesV2/BatteryV2.lean` carries hypotheses of the form
`z3solve q = unsat`, grouped into named packs: joint packs `Verd l m` (left window `l`, right
mode `m`: the cover's joint segment) and reposition packs `VerdD l m` (the cover's right-only
reposition of `m` with the left held at window `l`'s start). Since branch `replay` every one of
the 45 proofs replays the emitted cover, so none is Z3-free (`docs/REPLAY.md`). A theorem with a false hypothesis would be vacuously true, and
`#print axioms` cannot see that. This document says what discharges them.

**One command discharges all of them:**

```bash
./.lake/build/bin/relcert --run-verdicts-v2
# or, after certifying the 45 files first:
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt
```

The runner rebuilds every query from the committed, kernel-checked data (the IR literals,
the extended cut certificates, the emitted covers), prints it with the tool's own
`toScript`, sends it to Z3 and reports the verdict. Two disciplines make a green run
evidence about the theorems and not about lookalikes:

* **Pins.** For every pack a kernel theorem states that the instance's `Verd` IS the
  hypothesis the runner's table row denotes, and a generic theorem states that the
  rebuilt IR queries denote exactly that hypothesis. A wrong table row does not compile.
* **Declared counts.** Each phase's query count is declared (`VerdictsV2/RunV2.lean`) and
  proved equal, in the kernel, to what its table generates
  (`VerdictsV2/CoveragePinsV2.lean`); the runner fails if it discharged fewer or more
  (`Verdicts/Coverage.checkPhase`). A runner that silently skipped work cannot print green.
  Anything the runner cannot rebuild is a `SKIP` or `FAIL`, never a pass.

## The phases

| phase | declared | what it covers | what pins it |
|---|---|---|---|
| suite_v2 modal | 621 component queries in 234 packs | the joint packs of all 45 headline theorems (each row of `RunV2.packsV2` is consumed by exactly one headline: every joint segment of every replay) | one `pin_<bench>_<i>` / `pin_<tag>_j<k>` theorem per row in `VerdictsV2/PinsV2.lean` (each instance's `Verd l q` IS `packVerd` of its row of `RunV2.packsV2`; `irV2_`/`cutV2_` pairs resolve the IR literal and the extended certificate by name); `ModalX.modalVerdX_of_queries` (the rebuilt queries denote the hypothesis); `derivedModalV2_eq`; `packsV2_rowOfWindow` (the quoted row is the window's own row, by name) |
| suite_v2 handoff | 186 transitions | one domain-conditioned handoff query per declared left transition of all 45 files, self-loops included (`Trusted/Handoff.lean`); no declared failure | `derivedHandoffV2_eq`; the mode-keyed instances discharge their handoffs in the kernel, so this phase is the tool-level check of the same implication |
| suite_v2 non-connection | 44 pruned edges, 88 queries | both pruning queries (source, barrier) of every pruned edge of the emitted covers, the source cut rebuilt from the extended certificate (`Trusted/NonConnQuery.lean`) | `derivedPrunedV2_eq`, `derivedNonConnV2_eq`; `VerdictsV2/NonConnPinV2.lean` pins the `match_multi_rate DRIVE -> STALL` pair to `MatchMultiRatePruned.VerdNC`, the hypothesis of `match_multi_rate_nonconn` |
| copied benchmarks (legacy packs) | 385 queries in the 22 rows of `Verdicts/RunModal.modalTable` | the packs of the carried-over choice-form and relaxation theorems that remain in the tree (`Instances/*Modal.lean`); since branch `replay` no headline theorem takes a legacy pack | `InstancesV2/SameIR.lean` (`rfl`: the suite_v2 literal IS the legacy literal); `Instances/ModalSpecs` (each row's argument set ties to the theorem, `modal_from_spec`), `Verdicts/ModalPinTable` + `ModalTablePins` (the row's fields), `Verdicts/ModalCodePins` (the code that turns fields into terms), `Verdicts/ModalPins` (the rebuild denotes the host query); `derivedSameModalV2_eq` |
| suite_v2 reposition (dyn) | 81 component queries in 41 packs | the reposition packs of the 17 headline theorems whose replays reposition (`RunV2.dynPacksV2`; `OracleAPI.checkDynRepo` route A: `domain ∧ ġ > 0` UNSAT, the left field 0 at stretch 1, the domain the strata of both evolve domains, both sides' kept cut atoms and the left guard) | one `pin_<tag>_d<k>` theorem per row in `VerdictsV2/PinsV2.lean` (`VerdD l q` IS `dynPackVerd` of its row); `ModalDynX.modalVerdDynX_of_queries`; `derivedDynV2_eq`; `dynPacksV2_rowOfWindow` |

Total: 621 + 186 + 88 + 385 + 81 = **1361 queries**. "pruned edges 44/44" in the output is
a count check of the work list, not a sixth set of queries.

**Which packs the headline statements use.** The 45 headline theorems take 234 joint packs
(every row of `RunV2.packsV2`) and 41 reposition packs (every row of `RunV2.dynPacksV2`): 275
pack hypotheses (132 before branch `replay`, 194 before branch `guarded-right`). The legacy
phase still re-sends the packs of the carried-over choice-form and `⊤`-relaxation theorems that
the headline files import for shared definitions; no headline statement takes a legacy pack.
Six rows of `packsV2` were dropped on branch `replay` (their pairs are starts the cover drops
as inadmissible, now contradictory: `charger_fast_{setpoints,tapers}` `(FULL, BULK)`,
`watertank` `(Low, High)`, `(High, Low/MidEco/MidBoost)`).

Each pack component is tried with up to three route queries (A: non-strict DI on the whole
domain, B: strict DI on the boundary, C: superlevel); the output line records which route
came back `unsat` (`UNSAT (A=sat B=unsat)` means route B discharged it). The hypothesis is
the disjunction over the three routes, so one `unsat` suffices.

## Last run

2026-10-10, branch `replay`, Apple M2 Max (12 cores, 64 GB), Z3 4.15.1. `lake build`: `Build completed successfully (9014 jobs)`, no `sorry`; `lake build relcert relcert-test`: 17737 jobs. Axiom audit: BatteryV2 71 lines, 47 with `z3_unsat_sound` (the 45 Theorem 3s, `match_multi_rate_nonconn`, `couple_cutX`), 24 at the three standard axioms; WellFormedBattery 76 lines, all at the three standard axioms; nothing else. `--check-quick-v2`: 45 certified / 0 declined / 0 errors (strict well-formedness mode), modal 621/621, handoff 186/186, non-connection 88/88, pruned edges 44/44, copied benchmarks 385/385, reposition (dyn) 81/81, `[wellformed] STRICT: 146/146 right modes ok (83 invariant, 63 exit), 0 UNKNOWN — matches the declared suite`, `SUITE_V2 QUICK CHECKS PASSED`. `--run-verdicts-v2`: the same counts, `ALL suite_v2 HYPOTHESES DISCHARGED`. `relcert-test` with the suite_v2 manifest: 45 IR literals match, bare `ALL PASS`.

## Earlier runners

Until 2026-10-10 the binary also had `--run-verdicts` / `--check-quick` over the legacy
suite (phases: cut probes, modal, handoff, non-connection over `suite_uniform`). They were
removed with the legacy suite; their records are in the git history of this file and in
`docs/history/VERDICT-EVIDENCE-AUDIT.md`, which introduced the pin discipline used here.
