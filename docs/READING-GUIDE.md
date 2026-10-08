# Reading guide — the whole repository, in dependency order

Start here. This connects every layer, names the theorems that carry each guarantee, and
says plainly which routes are **live** and which are **historical layers with documented
vacuity traps**. It was written from a full read of `Proofs/` (50 files, ~19,200 lines)
and `Instances/`, not from grepping — the distinction matters, because greps cannot tell
a live theorem from a superseded one and several earlier summaries in this repo's history
got that wrong.

**The single most important thing to know before reading any theorem:** this development
contains *both* the current chain and several retired ones. Retired routes are still
compiled and still conclude impressive-looking statements, but rest on hypotheses the
repo itself proves or documents to be **unsatisfiable**. Always check a theorem's
hypotheses against §4 before citing it.

---

## 1. What the tool claims, in one paragraph

Given two hybrid automata `L` (ideal) and `R` (implementation) in a small textual DSL,
plus a candidate relational invariant, `relcert` searches for a **cover** — a finite
strategy saying how `R` answers every `L` window — and discharges the analytic side
conditions with Z3. The Lean development then re-checks, in the kernel, that the emitted
data *is* the benchmark, that the cover decision replays, and that the certificates
compose into the semantic guarantee. Z3's `unsat` answers are the only assumed facts.

## 2. Layers, bottom-up

| layer | files / lines | what it is | read for |
|---|---|---|---|
| `Core/` | 3 / 543 | flow queries, Lie derivatives, ℚ parsing | `FlowCert.lean` — the three DI routes and the note on why the boundary-only form is unsound |
| `Trusted/` | 10 / 2,273 | parser, lowering, printer, Z3 session, search, emission doors | `Oracle.lean` — the axiom and its four wrappers; `Parse.lean` — the reject-never-weaken contract |
| `Checker/` | 11 / 9,767 | cover graphs, `decideCovered`, cut certificates, fidelity | `Cover.lean` — `CoverCert`, `SegPreserves`, `Covered`; `Checker.lean` — the decision procedure |
| `Proofs/Encoding` | 35 / 9,782 | the ∀∃ chain: bridges, windows, repositions, envelopes | `CoverExtract.lean`, `BridgeDischarge.lean` — the live Theorem 3 routes |
| `Proofs/Flow` | 15 / 6,113 | DI routes, Picard existence, viability, contract witnesses | `PicardBridge.lean` (1,607 L, the analytic core); `ViabilityWiring.lean` |
| `Proofs/Soundness` | 6 / 2,397 | cut lift, guard threading, uniform evolution | `CutLift.lean`, `CutCover.lean`; **`GuardThreaded.lean:374` — the `GBoxAll` quarantine** |
| `Proofs/Transfer` | 5 / 3,918 | rescaling, the `Faithful` denotation bridge | `Rescale.lean` — the scaling-transfer lemma |
| `Instances/` | 280 / 85,680 (mostly generated) | per-benchmark theorems + emitted data | `ModalBattery.lean` — every benchmark's Theorem 3 and its axiom audit; `WatertankModal`/`WatertankViability` — the flagship, existence proven |
| `Verdicts/` | 14 / 2808 | query mirrors, kernel pins, the runner | `ModalPinTable.lean` — each theorem's hypothesis *is* the runner's query |
| `Archive/` | 17 / 2,683 | superseded developments, not built upon | `ProbeMvHd.lean` — a mechanized vacuity counterexample |

## 3. The live chain, end to end

Follow this path to see one guarantee all the way through:

1. **Z3 verdict → invariance.** `flow_certified` / `segPres_from_flowCert`
   (`Trusted/Oracle.lean`, `Proofs/Encoding/BridgeDischarge.lean`) turn
   `z3solve q = unsat` into `SegPreservesOn g sys dom`. This is where the axiom enters.
2. **Per-mode certificates → a bundle.** `CoverCert` / `CoverCertM`
   (`Checker/Cover.lean`) collect per-mode `SegPreserves`, reposition region invariants,
   and prune soundness. Crucially `SegPreservesOn` is **conditional** (`InvHolds g ν →`)
   and over the **joint** system — this is what keeps it satisfiable (contrast §4).
3. **The cover decision.** `decideCovered` (`Checker/Checker.lean`) walks
   `⟨mode, budget, source-setting⟩`; `decideCovered_sound` replays it in the kernel.
   Its `step` case is `(retainedSucc q).all …` — the paper's all-successors condition.
4. **Preservation over reaches.** `check_sound_multi` / `check_sound_multi_cut`
   (`CoverMulti.lean`, `CutCover.lean`) give
   `Covered ∧ CoexecInvAllThroughout{,G}` — *the invariant holds throughout every right
   co-execution*. **This is what all 40 benchmarks instantiate** (46 before the 2026-10-08 deduplication, `SUITE-DEDUPE.md`).
5. **The ∀∃ modality.** `theorem3_uniform_from_covered` /
   `decideCovered_implies_theorem3_faithful` (`CoverExtract.lean`,
   `BridgeDischarge.lean`), or the `hstep`-parametric family
   `theorem3_faithful_multiE_LR` / `theorem3_faithful_multiF_LR` /
   `theorem3_faithful_multiR_LR` (`EnvelopeChain*.lean`), conclude
   `rvalid (theorem3Form …)`. **All 40 certified benchmarks instantiate this** —
   see `Instances/ModalBattery.lean` and `docs/CERTIFICATION-CHECK.md`.
6. **Existence.** The ∀∃ route needs the response flow to exist: `WellFormedFlowB_contract`
   (`UniformEvol.lean`) for contract fields — no Z3, no budget — the stratified-face
   consumers `HExistSegB_of_viability_strat{ified,A,A2}` (`Proofs/Flow/StratifiedFaces.lean`,
   `AffineFaces{,2}.lean`) for general polynomial fields, or an explicit closed-form
   witness where the response flow is elementary (`rover_tier_r1`; and, for the
   catch-up instances, an explicit linear or exponential run). **Every modal instance
   discharges existence in-kernel — no instance carries an existence hypothesis, and
   no existence obligation is a Z3 verdict.**
7. **Encoding.** `theorem3_encoded` (`Checker/Cover/Encoding.lean`) rests on dL-rel's
   **Theorem 2** (`RFormula.encoding_correct`, soundness *and* completeness, never
   vacuous by `exists_bridge`).

## 3a. The equation: how "throughout" and Theorem 3 relate

Both routes consume the **same** certificate — `cert.segPres`, the per-mode-pair joint
flow certificates built from the Z3 verdicts. Nothing about *preservation* differs
between them. So:

> **Theorem 3  =  throughout-preservation  +  existence  +  assembly**,
> after which the loop rule and the encoding close it for free.

| term | what it is | status |
|---|---|---|
| **throughout-preservation** | the invariant survives every certified joint piece and every reposition | ✅ **40/40** — this is what `Throughout/` and `CutThroughout/` prove |
| **existence** | for a given L run, R's matching flow actually exists. Because `jointSys` puts L and R on **disjoint coordinate blocks**, L's flow plus R's flow in `domR` compose into the joint flow in `domL ∧ domR` (`hExistSegB_of_wellFormedFlowB`) | ✅ **46/46 proven in-kernel** — contract witnesses, stratified/affine face consumers, or explicit closed-form runs. Zero existence hypotheses, zero existence verdicts |
| **assembly** | knowing *all* joint runs are safe is not the same as *exhibiting one* spanning the whole L window; the ∃ must build a chain of pieces (plus repositions) covering the full duration | ✅ **40/40** via the window layer (`Hmulti_window{1,R,RF}_prefixed`, `hstep_assembled_multi{E,F}`), the split layer for mode-switching responses (`SplitCoupling.lean`), and the catch-up layer for right-only responses (`WindowGrowth.lean`) |
| **loop + encoding** | chaining windows (`relational_loop_multi`) and wrapping into the dL modality (`theorem3_encoded`, on dL-rel's Theorem 2) | ✅ **generic and proven** — no per-benchmark cost |

This is why the two statements feel like they should be nearly the same thing: they are.
The certificate is shared. The difference is that "throughout" *quantifies over* runs while
Theorem 3 must *construct* one — and constructing needs existence and assembly.

**All 46 of the then-suite are written** (2026-07-30; 40 after the deduplication). watertank and rover_drag were the pilots — each
built to validate one chain end to end (`UniformPilot.lean`'s header: *"First benchmark
instance of `theorem3_uniform_multiflow`"*; watertank was the S1 gate) — and the rest
followed as the response layers landed: right-only hops, k > 1 windows, λ-reparametrized
pieces, list-valued invariants, mode-switching splits, per-left-mode statements, and
finally the catch-up form (`WindowGrowth.lean`), where the response is a pure right-side
flow and the invariant is re-established by endpoint arithmetic. The last five benchmarks
closed that way carry **no Z3 verdicts at all**. Per-benchmark theorem names, hypotheses
and audited axioms: `docs/CERTIFICATION-CHECK.md`.

## 4. Live vs historical — check this before citing anything

| route | hypotheses | status |
|---|---|---|
| cover / uniform — `decideCovered_implies_theorem3_faithful`, `theorem3_uniform_from_covered` (R1 gate), `theorem3_uniform_guarded` (R2 gate) | `CoverCert`, `decideCovered`, `RightProjAlign` | ✅ **live** |
| `hstep`-parametric — `theorem3_faithful{,_multi,_multiE,_multiE_LR}` | `hstep` + disjointness | ✅ **live** |
| preservation — `check_sound_multi{,_cut}` | `CoverCertM{C}` + conditional `InvAllHolds` | ✅ **live** |
| settling — `theorem3_faithful_settling` and its clocked/cadenced variants, `settling_end_to_end` | **`GBoxAll`** — quarantined, *unsatisfiable* for an `L`-mentioning `g`; the unclocked form also carries `hbudgetAll` | ❌ **vacuous** |
| landing — `theorem3_faithful_landing_clocked{,_wf,_uniform}` | **`hbudgetAll`** — "unsatisfiable for autonomous benchmarks unless the caller smuggles a clock into `domL`" | ❌ vacuous for these benchmarks |
| Emit-carrying — `*_of_emit`, `theorem3_uniform_multiflow`, `uniform_multiflow_end_to_end`, reposition multi | `EmitSegs`/`EmitWindows` — *assumes* the witness | ⚠️ sound, but assumes what R1 proves — unless discharged at the instance (as `rover_drag` does) |

**Why the two traps exist and why they are safe.** `GBoxAll` uses an *unconditional*
`BoxLe` over a *right-only* system with a *right-only* guard region, so a zero-duration
run forces `g ν ≤ 0` at every `ν` in that region — impossible when `g` mentions left
coordinates. `hbudgetAll` asserts every left-ODE solution is duration-bounded, which
fails for autonomous fields. Both are **named at their definitions**, both were
superseded, and the live routes fix exactly these defects (conditional premises, joint
systems, clocked left segments).

## 5. What every benchmark has

| guarantee | benchmarks | status |
|---|---|---|
| relational invariant holds **throughout** every right co-execution | **40/40** | ✅ live |
| right-system well-formedness at the real scale (the paper's nonblocking + successor-complete assumption, **discharged**) | **40/40** (`*_real`) | ✅ live, but **stands alone** — see note |
| the instance **is** the parsed file (`faithful… := rfl`) | 40/40 | ✅ live |
| the tool's cover decision replayed (`coverReplays := by decide`) | 40/40 | ✅ live |
| full ∀∃ `rvalid (theorem3Form …)` | **40/40** (`Instances/ModalBattery.lean`) | ✅ live; existence proven in every instance; 5 instances carry no Z3 verdict at all |
| (`EndToEnd` ×3; `Mega` deleted 2026-10-08 with its benchmark) | watertank (arm_refinement) | ❌ vacuous route |

**Note on the `*_real` battery.** `GuardSettlingB` takes no invariant term — its
parameters are `(G) (Gd) (fR) (lam) (domR) (dt) (q)` — so it is a **unary** property of
the right system: from any state in a mode's guard region a solution exists, runs the
control interval inside the evolution domain, and lands in a retained successor's guard.
It says nothing about `L` or the relational invariant. Its value is that this is
*precisely* the paper's nonblocking/successor-complete **assumption**, so the
mechanization proves what the paper assumes. But its only downstream consumers —
`GuardSettlingH` → `theorem3_faithful_settling`, and the landing family — are the routes
carrying `GBoxAll`/`hbudgetAll` (§4). Nothing live consumes it. Claim it as a standalone
strengthening, not as a step toward the ∀∃ guarantee; the relational content for all 40
comes from the Throughout/CutThroughout batteries.

**How the ∀∃ form reached all 46 of the then-suite (and what the old obstacle was).** The historical
constraint was never the cover budget — `emitWindows_self` answers a k-piece window with
k self-loop residences. It was `RightProjAlignV`'s requirement that **every** mode be
joint-certified (one non-joint mode forces a reposition prefix), combined with
`Hmulti_window_prefixed`'s unsatisfiable disjointness side condition. Both were resolved
by later layers rather than by that lemma: right-only hop prefixes (`RepoPrefixR.lean`,
whose disjointness is *derived*), k > 1 windows (`WindowRF.lean`), λ-reparametrized
pieces (`Reparam.lean`), list-valued invariants (`EnvelopeChainM.lean`),
mode-region-threaded statements (`EnvelopeChainR.lean`), intra-window mode switching
(`SplitCoupling.lean`), per-left-mode statements (`rover3tier_rung12`), and finally the
catch-up form (`WindowGrowth.lean`), where the response is a *right-only* flow and the
invariant is re-established by endpoint arithmetic — no joint certificate, hence no Z3.
The uniform route was retired for this purpose in R7; every instance goes through the
modal chain. Per-benchmark inventory: `docs/CERTIFICATION-CHECK.md`.

The 41st benchmark, `shield_unreachable`, is honestly reported as non-certifying.

## 6. The trust base, enumerated

`z3solve` is `opaque`; `z3_unsat_sound` (`Trusted/Oracle.lean:37`) is the only axiom
beyond Lean's three. It is **applied at 12 sites in 5 files**: `Trusted/Oracle.lean` (4),
`Proofs/Soundness/CutLift.lean` (4), `Proofs/Flow/BoxViability.lean` (1),
`BoxViabilityBounded.lean` (1), `ViabilityWiring.lean` (2). Note `Instances/AxiomCheck.lean`
prints only two of these — extending it would make the claim self-evident.

Beyond the axiom: the parser, the printer, the Lean kernel, and successor-completeness
with guard-gated switching (a fact about the modeled system). See README's trust table.

## 7. Where the documents fit

**Active:**
- `READING-GUIDE.md` (this file) — the entry point
- `CERTIFICATION-CHECK.md` — **how to check the suite end to end**: the five checks, the
  exact commands, and the per-benchmark theorem/hypothesis/axiom table
- `PAPER-MAPPING.md` — paper ↔ mechanization inventory, the full-read findings, and the
  R-series gate glossary
- `COVER-AUDIT.md` — tool↔proof findings, incl. the ⊤-guard note and the open parser hole
- `VERDICTS.md` — the current empirical report
- `ASSET-MAP.md` — load-bearing theorems, with the vacuous routes flagged

**Design proposals (nothing scheduled):** `FIXPOINT-DESIGN.md` (winning-region
alternative — its premise is superseded, see its banner), `RESET-MAPS-SCOPE.md` (per-mode
state resets), `ROTATION-SCOPE.md` (jump-then-flow vs flow-then-jump equivalence).

**Measurements:** `VIABILITY-FACE-CENSUS.md` (the 1133-face census, measured on the 46-benchmark suite; the counts stand, the
route columns are historical — every class has a Lean route now).

**`history/`** — true, completed records: `ROADMAP.md` (the R/S arcs and their acceptance
gates), `DEVELOPMENT-ARC.md` (the narrative, including findings that turned out false),
`CUT-LIFT-SCOPE.md` (task D, delivered as S2), `MULTIFLOW-REALIGN.md` (task H), and the
four T3-arc scope documents archived on 2026-07-30 when the arc closed:
`THEOREM3-ALL-BENCHMARKS-PLAN.md`, `LEMMA-SCOPE.md`, `KGT1-ASSEMBLY-SCOPE.md`,
`INTRA-PIECE-SWITCH-SCOPE.md`. Each carries a banner saying what landed and — where the
prediction was wrong — how it actually resolved.

**`archive/`** — superseded by later architecture: `ARCHITECTURE.md`,
`BENCHMARK_INSTANTIABILITY.md`.

## 8. Standing discipline

Before building: check `ASSET-MAP.md`. Any tool↔proof mismatch: record in
`COVER-AUDIT.md`, resolve **by the code**, never invent parallel structures. Before
citing a theorem: check §4. Proof-layer edits rebuild the world — batch them
(`rebuild-hygiene`); per-benchmark edits are cheap since the X0 leaf modularization.
