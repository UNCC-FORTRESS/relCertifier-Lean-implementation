# Status (2026-10-10, branch `assumption1`)

**The artifact.** `benchmarks/suite_v2` (45 benchmarks), the tool `relcert`, the generic
soundness development (`RelCertifier/Core`, `Checker`, `Proofs`, `Trusted`) and the suite_v2
battery (`RelCertifier/InstancesV2/BatteryV2.lean`). The legacy suite `suite_uniform` and its
batteries were retired on 2026-10-10; the 19 theorems the battery carries over from it are
kept with exactly what they need (`README.md`, "The 19 carried-over theorems").

**Proved, all 45, one statement.** Theorem 3 with the paper's LEFT program (the guard-gated
left automaton `leftAutomatonBody A u_L`: each left window entered inside its lowered guard,
the declared successors and `u_L` read from the file) against the GUARDED right automaton
(every edge tests the lowered guard of the mode it enters), with the loop invariant carrying
the rows keyed by `u_L`, both envelopes, `u_L ∈ modes` and `regionG guard cuts q = guard q ∧
cuts q` of the right's current mode (`docs/GUARDED-SWITCHING.md` §3.1, §3.3). 44 benchmarks
for every window length, `refinement_ladder_rover_rung2c_6dof` for every window up to its
control interval (`dt ≤ ε_L = 1`); every switch on both sides kernel-checked legal. 12
mode-keyed, 33 mode-independent (carried to the left automaton by the generic bridge
`theorem3_leftAut_of_choice`, proved once); 16 Z3-free; 6 stated on the conserved-momentum
nonblocking region. No theorem carries a nonblocking (Assumption 1) hypothesis; no new
axiom; the declared rows unchanged. Plus the Theorem 2 instance of `match_multi_rate`'s
pruned edge. Axioms of every battery theorem ⊆ `{propext, Classical.choice, Quot.sound,
z3_unsat_sound}`; no `sorry`.

**Repaired.** `platoon3_linkloss`, `platoon3_profiles`: the guarded Theorem 3 was refuted in the
kernel on the old model (commit `1a3507f`) because its nominal controller BLOCKED after a full
cycle (engagement-band stay guards, no catch-all mode: a violation of Assumption 1 the
certificate cannot detect). The guards are now the operating range (floor 20, radar range,
rated closing rate, projected gap `21 ≤ g + 2r ≤ 59`; `docs/SUITE-REDESIGN.md` §20); both are
CERTIFIED and proved. The earlier "refuted by argument" entries (`rung2_3to6`, the story2
pair) refuted only a left program without guard tests; they are proved
(`docs/GUARDED-SWITCHING.md` §4.5).

**Assumption 1, verified per benchmark** (`docs/WELLFORMED.md`). The paper's Assumption 1
(the right model is nonblocking and complete for its declared successors over one control
interval `ε_r`) is stated once as `WellFormedR` (`Proofs/Encoding/WellFormedR.lean`) and
settled for all 45 right models, Z3-free (`InstancesV2/WellFormedBattery.lean`, 80 axiom
lines, the three standard axioms only): **proved for 30**; **false for 9**, each refuted in
the kernel with an exhibited blocking state, every other mode proved: `arm_plateau_{crit,
profiles,slow}` (ApproachA / ApproachB overshoot the next band within one interval),
`platoon_delay_{linkloss,profiles}` (sink BRAKE leaves its guard), `platoon3_{linkloss,
profiles}` (sink BRAKE1), `quad_light_{airframe_20,profiles}` (sink LIMIT); **proved on the
conserved momentum band for the 6 satellites** (the band is invariant; off it `DETUMBLE` has
no full-interval run, also refuted). These are model defects to report, not used by any
Theorem 3 (no theorem assumes Assumption 1). The tool's sufficient check
(`relcert --wellformed`, informational; `RELCERT_WELLFORMED_STRICT=1` declines on `UNKNOWN`)
reports 77 ok (invariant), 53 ok (exit), 16 UNKNOWN right modes, exactly the blocking modes
(the kernel refutes one per defect benchmark and both arm approach bands; `platoon3`'s
`BRAKE2`/`BRAKE3` block by the same argument as `BRAKE1`);
it flags every mode of the old `platoon3` model (`1a3507f`).

**Discharged.** Every Z3 hypothesis is re-sent by `relcert --run-verdicts-v2` against
declared counts (modal 262, handoff 186, non-connection 88 over 44 pruned edges, legacy
packs 385), each query pinned in the kernel to the hypothesis it discharges. The runner's
tables are unchanged in shape (the platoon3 packs re-run on the repaired model); the 45
statements take 132 packs where the theorems before this branch took 194 (`rung1`,
`rung3_6to8`, `rung4_8to12`, the four `rover_dof_terrain` rungs, `rover_patrol_zones`,
`rover_patrol_refine` became Z3-free); those packs are still re-sent because the choice-form
and relaxation theorems that stay in the tree take them.

**Assumed.** The trust base: parser, lowering (including the right guards placed on the
edges), SMT printer, Z3's `unsat`, the Lean kernel. Guard-gated switching is no longer
assumed (both sides) (`README.md`, "Trust base").

**Last verified run.** 2026-10-10, branch `assumption1`, Apple M2 Max (12 cores, 64 GB), Z3 4.15.1. `lake build`: `Build completed successfully (9005 jobs)`, no `sorry`; `lake build relcert relcert-test`: 17725 jobs. Axiom audit: BatteryV2 71 lines, 31 with `z3_unsat_sound`, 40 at the three standard axioms; WellFormedBattery 80 lines, all at the three standard axioms; nothing else. `--check-quick-v2`: 45 certified / 0 declined / 0 errors, modal 262/262, handoff 186/186, non-connection 88/88, pruned edges 44/44, copied benchmarks 385/385, informational `wellformed`: 77 ok (invariant), 53 ok (exit), 16 UNKNOWN of 146 right modes, `SUITE_V2 QUICK CHECKS PASSED`. `--run-verdicts-v2`: the same counts, `ALL suite_v2 HYPOTHESES DISCHARGED`. `relcert-test` with the suite_v2 manifest: 45 IR literals match, bare `ALL PASS`. Switch-off regression: `--emit-ir/--emit-cover/--emit-cuts` byte-identical for all 45 (135 outputs) against the binary before the Assumption 1 check.

**Open (other).**

* `rung2c` beyond its control interval: `1 < dt ≤ 2.12` neither proved nor refuted, `dt > 2.12`
  false by a stated argument (not kernel-checked); outside the model (`ε_L = 1`).
* Per-mode evolve domains (the paper's Eq. 2) are outside the Lean lift; no suite_v2
  benchmark has them.
* The generic X-channel theorem is the throughout form (`check_sound_multi_cutX`); the
  Theorem 3 instances are per benchmark (response strategy and existence).

How to re-check: `docs/CERTIFICATION-CHECK.md`.
