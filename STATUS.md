# Status (2026-10-10, branch `guarded-right`)

**The artifact.** `benchmarks/suite_v2` (45 benchmarks), the tool `relcert`, the generic
soundness development (`RelCertifier/Core`, `Checker`, `Proofs`, `Trusted`) and the suite_v2
battery (`RelCertifier/InstancesV2/BatteryV2.lean`). The legacy suite `suite_uniform` and its
batteries were retired on 2026-10-10; the 19 theorems the battery carries over from it are
kept with exactly what they need (`README.md`, "The 19 carried-over theorems").

**Proved, over the guarded right automaton.** 22 of the 45 benchmarks carry a kernel-checked
Theorem 3 (`rvalid (theorem3Form …)`) in which every right edge tests the lowered guard of the
mode it enters and every switch of the response is kernel-checked legal
(`Proofs/Encoding/GuardedSwitch.lean`, `docs/GUARDED-SWITCHING.md`): 20 suite_v2 instances and
`rover3tier_rung12`, `match_multi_rate` (restated by an explicit catch-up). 6 mode-keyed; 4
Z3-free; 6 stated on the conserved-momentum nonblocking region. No theorem carries a
nonblocking (Assumption 1) hypothesis. Plus the Theorem 2 instance of `match_multi_rate`'s
pruned edge. Axioms of every battery theorem ⊆ `{propext, Classical.choice, Quot.sound,
z3_unsat_sound}`; no `sorry`.

**Refuted.** For 21 benchmarks the guarded Theorem 3 is false as stated: the invariant admits
a right state from which the guarded automaton has no move while a left window breaks the row
(`docs/GUARDED-SWITCHING.md` §4.3). Two refutations are kernel-checked at the three standard
axioms: `rover_patrol_zones_guarded_false` (suite_v2) and `rover_ladder_rung1_guarded_false`
(carried over). Their Theorem 3 over the `⊤`-guarded relaxation stays in the battery, labeled.

**Open.** `platoon3_profiles`, `platoon3_linkloss`: the right never gets stuck, but the
certified response can end outside every successor's guard, and no legal witness could be
built from it; their theorems stay over the `⊤` relaxation (§4.4).

**Discharged.** Every Z3 hypothesis is re-sent by `relcert --run-verdicts-v2` against
declared counts (modal 262, handoff 186, non-connection 88 over 44 pruned edges, legacy
packs 385), each query pinned in the kernel to the hypothesis it discharges. (The guarded
theorems of `rover3tier_rung12` and `match_multi_rate` no longer use their 4 + 4 packs; the
packs are still re-sent.)

**Assumed.** The trust base: parser, lowering (including the right guards placed on the
edges), SMT printer, Z3's `unsat`, the Lean kernel. Guard-gated switching is no longer
assumed for the guarded theorems (`README.md`, "Trust base").

**Last verified run.** 2026-10-10, branch `guarded-right`, Apple M2 Max (12 cores, 64 GB), Z3
4.15.1. `lake build`: `Build completed successfully (8927 jobs)`, no `sorry`. `lake build
relcert relcert-test`: 17723 jobs. Axiom audit (`BatteryV2`): 56 lines, 40 with
`z3_unsat_sound`, 16 at the three standard axioms, nothing else. `--check-quick-v2`: 45
certified / 0 declined / 0 errors, modal 262/262, handoff 186/186, non-connection 88/88, pruned
edges 44/44, copied benchmarks 385/385, `SUITE_V2 QUICK CHECKS PASSED`. `--run-verdicts-v2`:
the same counts, `ALL suite_v2 HYPOTHESES DISCHARGED`. `relcert-test` with the suite_v2
manifest: bare `ALL PASS`.

**Open (other).**

* A guarded Theorem 3 for the 21 refuted benchmarks needs a different statement (a right
  region carrying the entered mode's guard, window-internal switching for the ladders), not a
  migration (`docs/GUARDED-SWITCHING.md` §4.3).
* Per-mode evolve domains (the paper's Eq. 2) are outside the Lean lift; no suite_v2
  benchmark has them.
* The generic X-channel theorem is the throughout form (`check_sound_multi_cutX`); the
  Theorem 3 instances are per benchmark (response strategy and existence).

How to re-check: `docs/CERTIFICATION-CHECK.md`.
