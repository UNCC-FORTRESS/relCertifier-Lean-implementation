# Status (2026-10-10, branch `guarded-right`)

**The artifact.** `benchmarks/suite_v2` (45 benchmarks), the tool `relcert`, the generic
soundness development (`RelCertifier/Core`, `Checker`, `Proofs`, `Trusted`) and the suite_v2
battery (`RelCertifier/InstancesV2/BatteryV2.lean`). The legacy suite `suite_uniform` and its
batteries were retired on 2026-10-10; the 19 theorems the battery carries over from it are
kept with exactly what they need (`README.md`, "The 19 carried-over theorems").

**Proved, over the guarded right automaton at the mode-consistent region.** One statement
shape for all 45: `rvalid (theorem3Form …)` over the right automaton in which every edge tests
the lowered guard of the mode it enters, with the loop invariant carrying
`regionG guard cuts q = guard q ∧ cuts q` of the right's current mode (`docs/GUARDED-SWITCHING.md`
§3.1). 39 benchmarks carry it for every window length (24 suite_v2 instances, 15 carried
over), `refinement_ladder_rover_rung2c_6dof` for windows `dt < 1`; every switch of every
response kernel-checked legal. 11 mode-keyed; 16 Z3-free; 6 stated on the conserved-momentum
nonblocking region. No theorem carries a nonblocking (Assumption 1) hypothesis; no new
axiom; the declared rows unchanged. Plus the Theorem 2 instance of `match_multi_rate`'s
pruned edge. Axioms of every battery theorem ⊆ `{propext, Classical.choice, Quot.sound,
z3_unsat_sound}`; no `sorry`.

**Refuted.** Kernel-checked at the three standard axioms: `platoon3_linkloss_guarded_false`
(every `dt > 0`) and `platoon3_profiles_guarded_false` (every `dt ≥ 1`; by argument every
`dt > 0.575`, `dt ≤ 0.575` open). By a stated argument (not kernel-checked):
`refinement_ladder_rover_rung2_3to6`, `story2_lateral_rung_a_8dof`,
`story2_lateral_rung_b_12dof` (every `dt > 0`), `rung2c` for `dt > 2.12`
(`docs/GUARDED-SWITCHING.md` §4.5, exact states). These six keep their Theorem 3 over the
`⊤`-guarded relaxation in the battery, labeled. History: at the old invariants (no guard in the
region) 23 statements were false; the two kernel refutations of that cut-only statement
(`rover_ladder_rung1`, `rover_patrol_zones`) were retired with it (§4.3).

**Discharged.** Every Z3 hypothesis is re-sent by `relcert --run-verdicts-v2` against
declared counts (modal 262, handoff 186, non-connection 88 over 44 pruned edges, legacy
packs 385), each query pinned in the kernel to the hypothesis it discharges. The runner's
tables are unchanged; the guarded theorems take 109 packs where the theorems they replace
took 171 (`rung1`, `rung3_6to8`, `rung4_8to12`, the four `rover_dof_terrain` rungs,
`rover_patrol_zones`, `rover_patrol_refine` became Z3-free); those packs are still re-sent
because the relaxation theorems that stay in the tree take them.

**Assumed.** The trust base: parser, lowering (including the right guards placed on the
edges), SMT printer, Z3's `unsat`, the Lean kernel. Guard-gated switching is no longer
assumed for the guarded theorems (`README.md`, "Trust base").

**Last verified run.** 2026-10-10, branch `guarded-right`, Apple M2 Max (12 cores, 64 GB), Z3
4.15.1. `lake build`: `Build completed successfully (8949 jobs)`, no `sorry`. `lake build
relcert relcert-test`: 17723 jobs. Axiom audit (`BatteryV2`): 68 lines, 32 with
`z3_unsat_sound`, 36 at the three standard axioms, nothing else.
`RELCERT_IMPLIED_CUT=1 … --check-quick-v2`: 45 certified / 0 declined / 0 errors, modal
262/262, handoff 186/186, non-connection 88/88, pruned edges 44/44, copied benchmarks 385/385,
`SUITE_V2 QUICK CHECKS PASSED`. `--run-verdicts-v2`: the same counts, `ALL suite_v2
HYPOTHESES DISCHARGED`. `relcert-test` with the suite_v2 manifest: bare `ALL PASS`.

**Open (other).**

* `platoon3_profiles` for windows `dt ≤ 0.575` and `rung2c` for `1 ≤ dt ≤ 2.12`: the guarded
  statement is neither proved nor refuted.
* The three argued refutations (`rung2_3to6`, the story2 pair, `rung2c` for long windows) are
  not kernel-checked.
* Per-mode evolve domains (the paper's Eq. 2) are outside the Lean lift; no suite_v2
  benchmark has them.
* The generic X-channel theorem is the throughout form (`check_sound_multi_cutX`); the
  Theorem 3 instances are per benchmark (response strategy and existence).

How to re-check: `docs/CERTIFICATION-CHECK.md`.
