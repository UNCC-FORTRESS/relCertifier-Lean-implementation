# relCertifier-lean

A **fully mechanized relational certifier** for hybrid-system refinement, in Lean 4.
Given two hybrid automata — an ideal system `L` and an implementation `R`, written in a
small textual DSL — it certifies relational invariants of their co-execution
(`|L_x − R_x| ≤ ε`-style bounds) and delivers, per benchmark, a **kernel-checked
end-to-end theorem** whose only assumptions are a five-item trust base and a finite
list of Z3 `unsat` verdicts, each re-runnable on demand.

Everything is Lean: the parser, the lowering, the query printer, the search, the
certificate checker, the proofs, and the per-benchmark theorem instances. Z3 is the
single external oracle, consulted only through printed SMT scripts, and only its
`unsat` answers are trusted.

## Quickstart

```bash
lake build                                   # whole development (proofs + instances)
lake build relcert                           # the certifier executable
./.lake/build/bin/relcert benchmarks/suite_uniform/watertank/input.txt   # certify one
./.lake/build/bin/relcert --run-verdicts     # empirically re-check theorem hypotheses
```

Reports land in `docs/VERDICTS.md`. Axiom audits: see [Trust audit](#trust-audit).

---

## The end-to-end guarantee, intuitively

**What is being proven.** The paper's Theorem 3 shape: *whatever the ideal system `L`
does, the implementation `R` can respond so that the relational invariant holds — and
keeps holding through every round.* "Whatever `L` does" is a `∀` over `L`'s runs
(windows of its modes, clock-capped); "`R` can respond" is an `∃` over `R`'s runs
(certified flow pieces, possibly opened by *repositioning* `R` through its declared
mode graph when its current mode carries no certificate for the window). The loop
invariant that survives the rounds is the relational invariant strengthened with the
mode-validity and envelope bookkeeping the response construction needs.

**How a benchmark theorem is assembled.** Three ingredient kinds, three trust levels:

1. **Proved once, for all benchmarks** (pure Lean, three axioms): the ∀∃ proof
   calculus — how per-piece flow certificates compose into window responses, how
   reposition hops re-anchor, how the loop closes (`Proofs/`). Also the analytic
   facts: differential-invariant rules, Picard existence, bounded-time viability,
   the explicit exponential witnesses for contract fields (`Proofs/Flow/`).

2. **Checked per benchmark by the kernel** (still three axioms): that the instance
   data *is* the benchmark — the emitted IR is what the parser produced
   (drift-checked literals), the cover decision replays (`decide`), the lowered
   queries in the theorem are identical to what the runner prints (the *pins*,
   `Verdicts/`), well-formedness of the cut certificates, side-splits, encodings.

3. **Observed** (the fourth axiom, `z3_unsat_sound`): a finite list of named facts
   `z3solve (query) = unsat`. `z3solve` is an *opaque* constant — operationally, the
   printer plus a Z3 process. Running `relcert --run-verdicts` (or the certification
   run itself) is what discharges these: each query is printed and Z3 answers
   `unsat`. The kernel pins (ingredient 2) guarantee the printed query is exactly
   the one the theorem names — nothing can drift in between.

**The trust boundary, exactly.** A benchmark's theorem holds if you accept:

| assumption | why it is irreducible |
|---|---|
| the **parser** reads the benchmark file correctly | the file is the spec |
| the **printer** (`toScript`) renders formulas to SMT faithfully | Z3 reads text |
| **Z3's `unsat`** answers are correct | the one oracle (axiom `z3_unsat_sound`) |
| the **Lean kernel** | checks everything else |
| **successor-completeness with guard-gated switching**: every mode change of `R` enters a *declared* successor, and at that instant the entering mode's guard holds | the automaton's transition semantics — a fact about the modeled system, not about formulas |

Nothing else. In particular: the search (cover exploration, cut fixpoints, route
selection) is completely untrusted — it only *proposes*; every accepted output is
re-validated by kernel-checked replay or becomes a named Z3 fact.

**The key hypothesis families**, per benchmark theorem:
* *invariant-preservation verdicts* — per (window, right-mode) pair, one of three
  differential-invariant route queries is unsat (route A: whole-domain `ġ ≤ 0`;
  B: strict boundary inflow; C: superlevel);
* *cut probes* (13 benchmarks) — each guard-derived cut atom is flow-invariant along
  its own side's field (same three routes; O2);
* *existence* — the response flow actually runs for the clock-capped duration without
  escaping its domain. For contract-shaped fields (e.g. watertank) this is **proven
  outright** via the explicit exponential witness — no hypothesis remains. In
  general it reduces to face-viability verdicts with growth budgets (the S3 chain);
  the suite-wide census certifies 1121/1121 evolve-box faces.

**Flagship instantiation** — `watertank_modal_certified`
(`Instances/WatertankViability.lean`): the multi-mode reposition-window Theorem 3 for
watertank, with existence proven in-kernel; its complete hypothesis list is six route
verdicts, all observed `unsat` (route B) by the runner. That theorem holds under the
trust table above, full stop.

---

## Theorem families and status

| family | statement shape | benchmarks | hypotheses beyond the trust base |
|---|---|---|---|
| **settling** (`*_real`) | cadenced rounds settle into the invariant band | 46/46 | flow/cut verdicts (certification run) |
| **throughout** | every component of the invariant holds throughout every right coexecution | 33 cut-free | cover verdicts (certification run) |
| **cut throughout** | same, via the guard-threaded cut lift (`RightReachG`) | 13 cut-reliant | cut-narrowed cover verdicts + per-atom O2 probes (runner: all unsat) |
| **modal (Theorem 3)** | `rvalid (theorem3Form …)` — the paper's ∀∃ with reposition-opened windows | watertank (pattern generalizes) | 6 route verdicts (runner: all unsat); existence **proven** |

All instances: axioms exactly `[propext, Classical.choice, Quot.sound]` plus
`z3_unsat_sound` at the verdict leaves.

---

## Repository map — the two columns

```
RelCertifier/
  Core/       shared syntax-level machinery (flow queries, Lie derivatives, ℚ parsing)
  Trusted/    the tool: parser, lowering, printer, Z3 session, search, emission doors
  Checker/    the certified checker: cover graphs, decideCovered, cut certificates
  Proofs/     the proof calculus (benchmark-independent, 3 axioms)
    Encoding/   the ∀∃ chain: bridges, windows, repositions, envelopes, cut baton
    Flow/       analysis: DI routes, Picard, viability, contract witnesses
    Soundness/  cut lift, guard threading, uniform evolution
    Transfer/   rescaling / chart-change transfer lemmas
  Instances/  KERNEL COLUMN: per-benchmark theorem instantiations + emitted data
    Throughout/     33 cut-free throughout instances (generated)
    CutThroughout/  13 cut-lifted throughout instances (generated)
    WatertankModal / WatertankViability   the modal flagship
    Bench*.lean     drift-checked emitted data (IR, covers, cuts, viability census)
  Verdicts/   EMPIRICAL COLUMN: query mirrors, kernel pins, the runner
  Archive/    superseded developments (kept for the record, not imported)
benchmarks/   the input suite (one dir per benchmark, textual DSL)
scripts/      instance generators + build orchestration
docs/         design records, audits, the verdict report
```

The separation that matters: **`Instances/` states theorems; `Verdicts/` makes their
hypotheses empirically checkable without any possibility of drift** (kernel identity
theorems tie the runner's printed queries to the theorems' named queries).

---

## File guide — what each file does for the guarantee

### Trusted/ — the tool (inside the trust base only via parser + printer)
* `Parse.lean` — the strict benchmark-DSL parser (rejects, never repairs).
* `Smt.lean` — the SMT IR (`ITerm`/`IForm`), the **printer** (`toScript`), the
  route-A query mirror and its `toHost` bridge.
* `Oracle.lean` — `z3solve` (opaque) and **the one axiom** `z3_unsat_sound`;
  `flow_certified`, the top-level verdict-to-invariance composition.
* `Z3.lean` — the Z3 process session (warm, budgeted).
* `Run.lean` — lowering: DSL → IR → host terms (`lowerE/lowerF/dynOf/invToG`).
* `OracleAPI.lean` — the untrusted search: stratified `checkSeg`, checked cuts
  (O1/O2), dynamic repositions, cover exploration, emission doors (`--emit-*`).
* `ViabilityEmit.lean` — the S3 emission door: per-face strict/growth tags.
* `EmitIR.lean` — IR emission for the drift-checked `BenchIR` literals.

### Checker/ — certified checking (what replaces trusting the search)
* `Cover.lean` — cover graphs, `RightReach` (right coexecutions), `SegPreservesOn`,
  `decideCovered` — the decision the kernel replays per benchmark.
* `Checker.lean` — `decideCovered_sound`: a `true` replay yields the `Covered` fact.
* `EvolStrengthening.lean` — cut-certificate data (`cutAtoms`, `cutAtomG`, routes)
  and its kernel well-formedness check.
* `NonConn.lean`, `Cover/…` — auxiliary certified checks.

### Proofs/Encoding/ — the ∀∃ chain (the paper's proof, mechanized)
* `Reification.lean`, `JointBridge.lean`, `BridgeUnit*.lean`, `BridgeDischarge.lean`,
  `BridgeFinish.lean` — the transition-faithful ∀∃ core: joint flow certificates
  become per-segment bounded couplings; the right automaton is reified.
* `BridgeReposition.lean` — the clocked segment (`clockedSeg`), the bounded coupling
  (`faModalB`), multi-segment lockstep composition.
* `MultiSeg.lean`, `UniformMultiflow.lean`, `UniformFvDischarge.lean` — the clocked
  ε-window chain (`windowSeg`), its `Hmulti` assembly, footprint dischargers.
* `RepositionDischarge.lean`, `RepositionFinish.lean`, `RepositionEndToEnd.lean` —
  cert-sourced reposition couplings and their end-to-end composition.
* `RepoPrefix.lean` — **reposition-opened windows**: frozen-left hops replay at the
  left endpoint; hop paths fold into the first piece's coupling.
* `EnvelopeChain.lean` — the envelope-carrying loop invariant (`phiInvE`), the
  LR-split relational envelope (`envLR`), `theorem3_faithful_multiE_LR` — the
  multi-mode modal top theorem the flagship instantiates.
* `CanonicalInv.lean` — the canonical relational invariant and its encoding identity.
* `CoverExtract.lean`, `CoverMulti.lean`, `CoverInstance.lean` — from the checker's
  `Covered` facts to theorem-grade responses; multi-component certificates
  (`CoverCertM`, `check_sound_multi`); the `realGraphOf` instance layer.
* `ClockedTop.lean`, `FvDischarge.lean`, `ClockReduce.lean`, `CSFBridge.lean`,
  `EncodingBridge.lean`, `LoweringSide.lean`, `ToolLevel.lean` — the settling
  (cadenced) chain and shared dischargers. The cadenced chain is deprecated for new
  work; the settling battery still rests on it.

### Proofs/Flow/ — analysis (existence and invariance facts)
* `StratifiedBarrier.lean` — the R4 fix: sequential (acyclic) differential cuts;
  multi-component route verdicts to simultaneous preservation.
* `PicardBridge.lean` — Picard–Lindelöf into `Program.sem` runs (`RunFor`), gluing,
  polynomial fields' ball-Lipschitz data.
* `BoxViability.lean` — R6: strict-face box viability (first-exit argument).
* `BoxViabilityBounded.lean` — S3: growth faces with entry budgets; the budget-
  telescoping chained viability (`box_viability_bounded_chain`).
* `ViabilityWiring.lean` — the bounded existence residual (`HExistSegB`) discharged
  from viability; the bounded coupling (`segment_faModalB_from_certB`); anchor
  conditioning verdicts.
* `FaceBridge.lean` — faces ⟺ evolve domain; uniform Picard data; the contract-
  witness transfer (`WellFormedFlowB_transfer`).
* `WellFormedFlow.lean`, `DISuperlevel.lean`, … — bounded flow well-formedness and
  DI route backings.

### Proofs/Soundness/ — the cut lift and guard threading
* `CutChannel.lean`, `CutLift.lean` — task-D cut lift: per-atom staying from O2
  verdicts (all four routes), the narrowed-query lift, `cut_hcert`.
* `CutCover.lean` — **S2**: `RightReachG` (guard-gated switching recorded),
  `CoverCertMC`, `pres_multi_cut` (the cut baton), `check_sound_multi_cut`.
* `CutCoverDischarge.lean` — instance dischargers: O1 at the `getD` level, per-atom
  route adapters incl. frozen and contract-shape (superlevel) staying.
* `UniformEvol.lean` — contract fields' explicit exponential witnesses
  (`contractΦ`, `WellFormedFlowB_contract`).
* `GuardThreaded.lean`, `CutLift.lean` — the settling-side guard threading.

### Instances/ — the kernel column
* `BenchIR/<name>.lean` — drift-checked emitted IR literal, one leaf module per
  benchmark (X0 modularization: editing one benchmark re-elaborates only its own
  column, not the battery); `BenchIR.lean` aggregates the leaves and carries the
  whole-suite `benchIRTable` (the single
  source of truth the instances quote).
* `BenchCovers/`, `BenchCoversNC/` — emitted cover data (with/without cuts), one
  leaf per benchmark; thin aggregators re-export.
* `BenchCoverReplay.lean` — kernel replays of every cover decision (`by decide`).
* `EvolStrengthenings/` — emitted cut certificates + kernel well-formedness, one
  leaf per benchmark; thin aggregator re-exports.
* `BenchViability2.lean` — the S3 face census (1121/1121, suite-wide).
* `Throughout/*.lean`, `ThroughoutBattery.lean` — the 33 cut-free instances.
* `CutThroughout/*.lean`, `CutThroughoutBattery.lean` — the 13 cut-lifted instances.
* `WatertankModal.lean` — the modal flagship's statement-level instance.
* `WatertankViability.lean` — its existence discharge + `watertank_modal_certified`.
* `SettlingInstances.lean`, `EndToEnd.lean`, `Mega.lean`, `FaithfulCerts.lean`,
  `ThroughoutPilot.lean`, `UniformPilot.lean`, `WatertankThroughout.lean`, … —
  the settling battery and the pilots that validated each chain.

### Verdicts/ — the empirical column
* `Mirrors.lean`, `Combinators.lean` — route-C mirror; fold mirrors (`istrataDomHost`,
  `icutF`) with `toHost` bridges.
* `GenericPins.lean` — the `getD`-collapse pins: runtime-rebuilt queries denote
  exactly the hypothesized ones, one lemma per query shape, all benchmarks at once.
* `Watertank.lean` — the flagship's per-query identity theorems.
* `Run.lean`, `RunCut.lean` — the runner behind `relcert --run-verdicts`.

---

## Lean mechanization ↔ the paper's formal results

| paper result | mechanization | notes |
|---|---|---|
| Theorem 3 (relational ∀∃ over co-executions, reposition-opened windows) | `theorem3Form` + `theorem3_faithful_multiE_LR` (`EnvelopeChain.lean`); instantiated as `watertank_modal_certified` | the loop invariant is the paper's invariant ∧ mode-validity ∧ the joint envelope; responses = certified pieces, opened by static hops along declared edges |
| per-segment flow certificates (differential invariants, three routes) | `flow_certified` (route A), `flow_cert_sound_strict` (B), `…_superlevel` (C); stratified multi-component form in `StratifiedBarrier.lean` | the mutual-narrowing variant was found unsound (R4) and replaced by sequential cuts — a tool fix surfaced by the mechanization |
| checked guard cuts (O1 entry / O2 invariance) | `CutLift.lean` per-atom staying + `CutCover.lean` baton | O2's one-sidedness covers both joint and frozen-left flows; the shape route is subsumed by route C |
| response existence (non-blocking flows) | R6 strict faces + S3 growth budgets (`BoxViability*.lean`), contract witnesses (`UniformEvol.lean`) | the `∀s` form of the paper's side condition is unsatisfiable in general; the honest clock-capped `HExistSegB` is what the coupling consumes |
| cover soundness (the certificate checker) | `decideCovered_sound`, `check_sound_multi{,_cut}` | search untrusted; decisions kernel-replayed per benchmark |
| settling rounds (the cadenced presentation) | `theorem3_faithful_settling` + the 46-benchmark `_real` battery | retained; superseded for new work by the modal chain |

---

## Re-checking the guarantees

```bash
./.lake/build/bin/relcert --run-verdicts        # modal + cut-probe hypotheses → docs/VERDICTS.md
./.lake/build/bin/relcert benchmarks/suite_uniform/*/input.txt   # full certification re-run
./.lake/build/bin/relcert --emit-viability2 <bench>/input.txt <name>  # face census
```

<a name="trust-audit"></a>
### Trust audit

```lean
#print axioms RelCertifier.WatertankModal.watertank_ESW
-- [propext, Classical.choice, Quot.sound]           (existence: proven)
#print axioms RelCertifier.WatertankModal.watertank_modal_certified
-- + RelCertifier.z3_unsat_sound                     (six named verdicts)
#print axioms RelCertifier.pres_multi_cut            -- 3 axioms (pure chain)
#print axioms RelCertifier.WatertankVerdicts.wt_id   -- 3 axioms (the pins)
```

Every `Instances/` theorem audits to the standard three axioms plus `z3_unsat_sound`
exactly at the verdict leaves.

---

## Soundness findings (the mechanization improving the tool)

Mechanizing surfaced real issues; each is recorded in `docs/COVER-AUDIT.md`:

* **R4 — circular multi-barrier narrowing** (real tool bug): mutual narrowing of
  sibling components is unsound (the `t²` pathology); fixed by sequential acyclic
  differential cuts. 14 benchmarks transiently declined, all recovered.
* **Unconditioned existence** (`∀ν HExistSeg`) is false in general; replaced by the
  envelope-conditioned, clock-capped `HExistSegB`.
* **`Hmulti_window_prefixed`** is unusable for real reposition hops (its
  vars-disjointness hypothesis is unsatisfiable); the k = 1 route replaced it.
* **Kernel-reduction limits**: `String.startsWith` and the numeral parser
  (ByteArray/`Rat` ops) are not kernel-reducible; the working recipe for
  lowered-literal facts is elaborator-side `simp` with per-numeral `String.data`
  facts + `norm_num`.
* **Route C subsumes the bespoke contract-shape check** — a tool simplification.

---

## Benchmarks

`benchmarks/suite_uniform/<name>/input.txt` — one file per benchmark: state variables,
`L`/`R` mode lists (`odes`, `guard`, `evolve`, `next`), per-mode relational invariants,
and the `λ` stretch range. The parser is strict; the emitted IR (`BenchIR/<name>.lean`) is the
drift-checked single source every instance quotes. 47 benchmarks: watertank, arm/plant
families, rover refinement ladders, terrain and rollover stories up to 12 dof.

## History

`docs/ROADMAP.md` (arc records: R1–R7 realignment, S1–S4, all closed), `docs/COVER-AUDIT.md`
(soundness findings), `docs/CUT-LIFT-SCOPE.md`, `docs/DEVELOPMENT-ARC.md`,
`docs/VERDICTS.md` (the current empirical report). Superseded design documents live in
`docs/archive/` (`ARCHITECTURE.md` — the certified-checker re-architecture and the
finding that forced it; `BENCHMARK_INSTANTIABILITY.md` — the pre-battery instantiability
census).
