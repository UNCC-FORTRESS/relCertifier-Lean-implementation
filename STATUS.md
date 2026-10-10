# Status (2026-10-10, branch `cleanup`)

**The artifact.** `benchmarks/suite_v2` (45 benchmarks), the tool `relcert`, the generic
soundness development (`RelCertifier/Core`, `Checker`, `Proofs`, `Trusted`) and the suite_v2
battery (`RelCertifier/InstancesV2/BatteryV2.lean`). The legacy suite `suite_uniform` and its
batteries were retired on 2026-10-10; the 19 theorems the battery carries over from it are
kept with exactly what they need (`README.md`, "The 19 carried-over theorems").

**Proved.** Every one of the 45 suite_v2 benchmarks carries a kernel-checked Theorem 3
(`rvalid (theorem3Form …)`): 26 new instances and 19 carried-over theorems; 12 mode-keyed;
12 need the widened cut channel; 5 Z3-free; 6 stated on the conserved-momentum nonblocking
region. Plus the Theorem 2 instance of `match_multi_rate`'s pruned edge. Axioms of every
battery theorem ⊆ `{propext, Classical.choice, Quot.sound, z3_unsat_sound}`; no `sorry`.

**Discharged.** Every Z3 hypothesis is re-sent by `relcert --run-verdicts-v2` against
declared counts (modal 262, handoff 186, non-connection 88 over 44 pruned edges, legacy
packs 385), each query pinned in the kernel to the hypothesis it discharges.

**Assumed.** The trust base: parser, lowering, SMT printer, Z3's `unsat`, the Lean kernel,
and the transition semantics of the models (successor-completeness with guard-gated
switching; the paper's Assumption 1, nonblocking). `README.md`, "Trust base".

**Last verified run.** 2026-10-10, branch `cleanup`, Apple M2 Max (12 cores, 64 GB), Z3 4.15.1. `lake build`: `Build completed successfully (8922 jobs)`, no `sorry` (after a full rebuild of every `RelCertifier` module; `docs/CERTIFICATION-CHECK.md`, "Cost"); `lake build relcert relcert-test`: 17723 jobs. Axiom audit: 51 lines, 42 with `z3_unsat_sound`, 9 at the three standard axioms, nothing else. `--check-quick-v2`: 45 certified / 0 declined / 0 errors, modal 262/262, handoff 186/186, non-connection 88/88, pruned edges 44/44, copied benchmarks 385/385, `SUITE_V2 QUICK CHECKS PASSED` (about 2 minutes). `relcert-test` with the suite_v2 manifest: 45 IR literals match, bare `ALL PASS`.

**Open.**

* The instance witnesses of 19 legacy and 10 new instances use zero-duration right hops
  over the `⊤`-guarded right automaton; whether each such switch lands where the successor's
  guard holds is not checked by the kernel (`docs/PAPER-MAPPING.md` §2e).
* Per-mode evolve domains (the paper's Eq. 2) are outside the Lean lift; no suite_v2
  benchmark has them.
* The generic X-channel theorem is the throughout form (`check_sound_multi_cutX`); the
  Theorem 3 instances are per benchmark (response strategy and existence).

How to re-check: `docs/CERTIFICATION-CHECK.md`.
