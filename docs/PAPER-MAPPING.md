# Paper ↔ mechanization: an inventory

Status: INVENTORY (2026-07-19, main = f85e61f). Produced by a full read of
`RelCertifier/Proofs/**` — every theorem concluding `rvalid (theorem3Form …)` — and every
file in `RelCertifier/Instances/`. It replaces three earlier partial assessments in this
file's history, each of which **understated** what the development proves; §6 records
what went wrong so the mistake is not repeated.

---

## 1. What the paper asks for

The paper states its obligation in the ∀∃ modality over the `cpsProg` programs:

- **Definition 1**: `φInv → [|(L, R)⟩⟩ φInv`
- **Eq. (relational-invariant)**: one-iteration preservation, `φInv → [|(Lsysi, Rsys)⟩⟩ φInv`
- **Eq. (mode-inv)**: the same, decomposed per left mode
- **Theorem 3** (Soundness of Synthesis): an all-successors cover induces a certified
  witness strategy, hence `φInv → [|(L,R)⟩⟩ φInv`

Target Lean shape: `rvalid (theorem3Form L R φ)` — and `theorem3Form`
(`Checker/Cover/Encoding.lean:51`) *is* that formula, stars both loop bodies, and says so
in its own docstring.

---

## 2. Theorem 3 is mechanized generically, Emit-free, from the checker's own decision

**Three generic theorems take `decideCovered` — the function the tool runs — plus a
Z3-backed `CoverCert`, and conclude `rvalid (theorem3Form …)`. None assumes an emission
device.**

| theorem | where | left shape | note |
|---|---|---|---|
| `decideCovered_implies_theorem3_faithful` | `Proofs/Encoding/BridgeDischarge.lean:176` | one ODE program | also yields the throughout conjunct; **listed in the axiom audit** |
| `theorem3_uniform_from_covered` | `Proofs/Encoding/CoverExtract.lean:122` | list of `windowSeg`s | **R1 gate** — section header *"The top theorem, Emit-free — the checker in the conjunction"*; docstring: *"the ASSUMED `EmitWindows` is GONE"* |
| `theorem3_uniform_guarded` | `Proofs/Encoding/CoverExtract.lean:218` | guard-gated windows, one per left mode | **R2 gate** — each mode's lowered guard carried, so the obligation arises only at guard-satisfying entries |

`decideCovered_implies_theorem3_faithful` also documents exactly what is load-bearing:

> `cert` is required for the `rvalid` conjunct … `hchk` (`decideCovered`) is load-bearing
> for the **throughput** conjunct, NOT for `rvalid`: the `faModal_LOCK` loop preserves the
> invariant over any number of iterations, so the ∀∃ modality needs every mode CERTIFIED
> (`cert.segPres`), not the coverage/budget DECISION.

Axioms: `[propext, Classical.choice, Quot.sound]` — parametric in `cert`, so
`z3_unsat_sound` enters only where the certificate is constructed per mode
(`segPres_from_flowCert` / `flow_certified`). Re-emitted on every build by
`Instances/AxiomCheck.lean`.

---

---

## 2a. Theorem 3, clause by clause

The paper's statement:

> **Theorem 3 (Soundness of Synthesis).** For a left mode `m_L`, if every admissible
> initial right mode `q₀` admits an all-successors cover from `(q₀, ε_L, pre-joint)`,
> then the cover induces a certified witness strategy for `m_L`. If such a cover exists
> for every `m_L ∈ modes_L`, then `φInv` is a ∀∃ invariant:
> `φInv → [|(L,R)⟩⟩ φInv`.

Against `theorem3_uniform_from_covered` (`Proofs/Encoding/CoverExtract.lean:122`):

| paper clause | Lean |
|---|---|
| *"every admissible initial right mode `q₀` admits an all-successors cover from `(q₀, ε_L, pre-joint)`"* | `hchk : ∀ q, q < Gj.modes.length → decideCovered Gj fuel ⟨q, B, SrcSetting.preJ⟩ = true` — `q₀ ↔ q`, `ε_L ↔ B` (ℕ-discretized), *pre-joint* `↔ SrcSetting.preJ`, and *all-successors* is `decideCovered`'s own successor case `(G.retainedSucc q).all (…)`, i.e. Definition 4 verbatim |
| *"the cover induces a certified witness strategy for `m_L`"* | **not a hypothesis — the proof.** `emitWindows_self` builds the window response from the declared self-edges and feeds `theorem3_uniform_multiflow`. This is exactly what the **R1 gate** required: the witness *derived* from `Covered`, never assumed (Definition 5 in the paper) |
| *"if such a cover exists for every `m_L ∈ modes_L`"* | `leftData : List (…)`, one entry per left mode, with `hleft : ∀ d ∈ leftData, …`; the left program is `bigChoice (leftData.map (windowSeg …))` |
| *"`φInv → [|(L,R)⟩⟩ φInv`"* | `rvalid (theorem3Form (bigChoice (leftData.map …)) (rightAutomatonBody Gr mv) (ϕinv ∧ mvValidR mv Gr.modes.length))` |

**What the Lean makes explicit that the paper folds in.** The Lean takes
`cert : CoverCert Gj g` — the flow certificates — as a *separate* argument. The paper
folds this into the graph construction (§4.2: *"If no flow certificate is available at
`m_R`, none of its candidate edges is retained"*), so "a cover exists" already
presupposes certificates. Both are the same content; the Lean simply names it.

**What the Lean adds.** A second conjunct, `∀ q, ∀ ν, InvHolds g ν →
CoexecInvThroughout Gj g ⟨q, B, preJ⟩ ν` — the invariant holds *throughout* the
co-execution, not merely at the round's end. The paper's Theorem 3 states only the
endpoint form.

**A decomposition of your own proof, worth knowing.** The Lean proof draws the two
conjuncts from *different* hypotheses, and `decideCovered_implies_theorem3_faithful`
records it:

> `cert` is required for the `rvalid` conjunct … `hchk` (`decideCovered`) is load-bearing
> for the **throughput** conjunct, NOT for `rvalid`: the `faModal_LOCK` loop preserves the
> invariant over any number of iterations, so the ∀∃ modality needs every mode CERTIFIED
> (`cert.segPres`), not the coverage/budget DECISION.

So Theorem 3 bundles two guarantees with two different sources: **invariant preservation**
comes from the flow certificates at every mode, while **duration coverage** — that the
response spans the whole `m_L` residence — comes from the budget walk. The paper's §4.4
("Finiteness and Duration Coverage") is the second; §3's flow certificates are the first.
Stating that split explicitly would sharpen the theorem's proof sketch.

## 3. Full inventory of generic `rvalid (theorem3Form …)` theorems

Twenty-odd, in five families by what they assume. This variety is the "additional
machinery" — routes built at different times for different witness shapes.

**(a) Cover-based, Emit-free** — §2. The paper's Theorem 3 proper.

**(b) Certificate-based, no cover decision.**
- `settling_end_to_end` (`Proofs/Encoding/FvDischarge.lean:632`) — parametric in
  `SettlingModel n`; needs `decideWellFormed M = true` (kernel `rfl`) plus per-mode Z3
  `BoxLe` certificates. Cadenced left and right.
- `theorem3_faithful_settling` (`Proofs/Soundness/GuardThreaded.lean:417`) and the
  clocked / cadenced variants (`Proofs/Encoding/ClockedTop.lean:41,368,462`) — from
  `GuardSettlingH`, which `wellformed_sound` + `FvDischarge` discharge **generically**.
  The family headers say so: *"per-run Z3 certificates yields `GuardSettlingH` — hence
  `theorem3_faithful_settling` — with no per-benchmark proof"*
  (`Instances/SettlingInstances.lean:7`, `Instances/TerrainInstances.lean:8`).

**(c) `hstep`-parametric** (Emit-free by construction; `hstep` supplied per instance).
`theorem3_faithful` (`BridgeFinish.lean:77`), `theorem3_faithful_multi`
(`RepositionFinish.lean:27`), `theorem3_faithful_multiE` / `_multiE_LR`
(`EnvelopeChain.lean:170,387`), and the landing family
(`Proofs/Flow/MultisegLandingBridge.lean`). Here `hstep` is *literally* the paper's
eq. (relational-invariant): since `faModal ρ α β φ = [α]⟨ρβ⟩φ`, it reads "for every run
of one left body iteration there exists a run of the starred right automaton preserving
the invariant", and `relational_loop_multi` inside the proof is the paper's *"repeated
application … for every finite number of control cycles"*.

**(d) Emit-carrying** — superseded by (a), retained.
`decideCovered_implies_theorem3_faithful_multi` (`RepositionEndToEnd.lean:28`),
`theorem3_faithful_multi_reposition` (`:71`), `theorem3_uniform_multiflow`
(`UniformMultiflow.lean:300`), `uniform_multiflow_end_to_end`
(`UniformFvDischarge.lean:287`), and the two `*_of_emit` forms.

**(e) Encoding layer.** `theorem3_encoded` / `rvalid_of_encoded_unsat`
(`Checker/Cover/Encoding.lean:36,57`) — Z3 unsat on the encoded negation ⟹ `rvalid`, via
dL-rel's **Theorem 2** (`RFormula.encoding_correct`: soundness *and* completeness of the
bi-state↔host encoding, with `exists_bridge` proving it never vacuous).

---

## 4. What each benchmark has

**Ingredients, all 46 — kernel-checked:**

| artefact | file | check |
|---|---|---|
| the instance **is** the parsed benchmark file | `Instances/FaithfulCerts.lean` | 46 × `faithful… = true := rfl` |
| the tool's cover decision, replayed | `Instances/BenchCoverReplay.lean` | 46 × `coverReplays IR cover = true := by decide`, for **every** emitted left-mode cover and **every** admissible start |
| model well-formedness | `SettlingInstances` (25), `TerrainInstances` (19), `AffineInstances` (2) | `decideWellFormed … = true` by `rfl` |
| real-chart transport | `Instances/RealInstances.lean` | 46 `*_real` theorems — the generic family theorem instantiated at the parser-emitted IR, concluding `GuardSettlingB` |
| emitted data | `BenchIR/`, `BenchCovers/`, `BenchCoversNC/`, `EvolStrengthenings/`, `BenchViability2` | drift-checked literals |

**Per-benchmark theorem instantiations:**

| family | benchmarks | conclusion |
|---|---|---|
| `Instances/Throughout/*.lean` | 33 | `Covered … ∧ CoexecInvAllThroughout …`, per left mode, from named Z3 verdicts |
| `Instances/CutThroughout/*.lean` | 13 | same, guard-threaded via `RightReachG` |
| `Instances/EndToEnd.lean` | watertank | **`rvalid (theorem3Form …)`** ×3 — physical, clocked, ε-cadenced |
| `Instances/Mega.lean` | arm_refinement | fidelity ∧ settling in one term; *"yields `rvalid (theorem3Form …)` exactly as in `EndToEnd.lean`"* |
| `Instances/UniformPilot.lean` | rover_drag | **`rvalid (theorem3Form …)`** from **one** Z3 verdict + `hES`; includes `rover_drag_covered : decideCovered … = true := by decide` |
| `Instances/WatertankModal` + `WatertankViability` | watertank | **`rvalid (theorem3Form …)`**, multi-mode with repositions, existence proven in-kernel |

So `rvalid (theorem3Form …)` is **written out for three benchmarks** (watertank in four
forms, arm_refinement, rover_drag).

**For the other 43 it is NOT a one-line application** — an earlier version of this
section said it was; that was checked and is false. The two chains are disconnected:

| | throughout battery (33 + 13) | the `rvalid` chain |
|---|---|---|
| certificate | `CoverCertM` (multi-component, R4) | `CoverCert` (single `g`) |
| alignment | — | `RightProjAlign` / `RightProjAlignV` required |
| conclusion | `Covered ∧ CoexecInvAllThroughout` (∀∀ preservation) | `rvalid (theorem3Form …)` |

Verified against HEAD: the 33 `Throughout/*.lean` instances build **only** `CoverCertM`
(83 occurrences, zero `CoverCert`); **no instance** outside `UniformPilot.lean` mentions
`RightProjAlign`; **no `CoverCertM`-based `rvalid` theorem exists** anywhere in
`Proofs/`; and **no `CoverCertM → CoverCert` bridge exists**.

Closing it therefore needs two things, only the second of which is mechanical:

1. **A multi-component sibling of `theorem3_uniform_from_covered`** taking `CoverCertM`
   (or a bridge from `CoverCertM` to `CoverCert` per component, which would only yield a
   per-component conclusion rather than the conjunction). This is real proof work.
2. **Per-benchmark `RightProjAlignV`** — for each right mode, exhibit `fR`, `lam`,
   `domR`, `mj` with the block/domain shapes and the joint-graph correspondence. Since
   `realModeOf` builds exactly those shapes this is plausibly mechanical, but it is
   written for one benchmark today.

---

## 5. Where the real distinctions lie

Not coverage — **witness shape**:

| | cadenced / settling | uniform window chain | multiflow + repositions |
|---|---|---|---|
| generic theorem | (b) | (a) | (c) + (d) |
| written out at | watertank, arm_refinement | rover_drag | watertank |
| witness | one right cycle per round, full width | window chain over declared self-edges | several right cycles, mode changes, right-only reposition segments |
| paper content | Definition 1 / eq. (mode-inv) | + window chaining | + **§4** (all-successors cover, budget, repositions) |
| status | R7: cadenced chain DEPRECATED, retained until the modal form and cut lift reach parity | — | current |

**Modelling choices to state in the paper** (all documented in-repo; none are defects):

| paper `cpsProg` | mechanized | direction |
|---|---|---|
| left has guards, `mv`, clock | left flattened to `star (bigChoice leftProgs)`, guard-free — or guard-gated in `theorem3_uniform_guarded` | **stronger**: the left is ∀-quantified, so over-approximating strengthens |
| `?guard_m(x)` on transitions | `e.guard = ⊤` | permissive — the documented "⊤-model"; harmless because the cover is demonic over successors (`docs/COVER-AUDIT.md`) |
| `t := 0; {…, t' = 1 & t ≤ ε_R}` | clocked in the cadenced/landing routes; unclocked in `rightAutomatonBody` | permissive where unclocked |
| invariant `φInv` | `φInv ∧ mvValidR` (and `∧ envLR` in the E-forms) | bookkeeping conjuncts, both sides of the implication |
| jump-then-flow | flow-then-jump | rotation (`docs/ROTATION-SCOPE.md`) |
| budgets `B = ε_L`, `w = ε_R/λ` (real-valued) | `weight : ℕ`, budget `⌈ε_L/δ_L⌉` | faithful ℕ-discretization |

**Two paper assumptions land well.** § Well-formedness (nonblocking + successor
completeness) is exactly what `GuardSettlingB`'s final conjunct **proves** for all 46; and
Limitations already says resets are identities, matching the mechanization
(`docs/RESET-MAPS-SCOPE.md`). **Definition 4** (All-Successors Cover) maps onto
`Covered`/`decideCovered` — base case `B ≤ w`, successor case ∃kind ∀retained-edges,
σ ↔ `SrcSetting`.

---

## 6. The R-series gates, and what each supports in the paper

The development was built as an ordered arc (`docs/ROADMAP.md`), R1–R7, each item
carrying an **acceptance gate** — the concrete artifact that counts as done: *"an item is
done when its gate is kernel-green, committed, and pushed."* The gates are the natural
evidence list for a referee, because each removes a specific way the mechanization could
have been weaker than the paper.

| item | what it removed / established | gate | Lean artifact | paper element it supports |
|---|---|---|---|---|
| **R1** witness extraction | the assumed `EmitSegs`/`EmitWindows` devices — hypotheses asserting *a chain of response segments exists*. Replaced by induction on the `Covered` derivation (joint cases → pieces; the four reposition cases → frozen-left segments; staying backed by declared self-edges) | *"`theorem3_faithful_multi{,_reposition}` restated without any `Emit*` hypothesis; rover_drag pilot re-based on it; axioms unchanged"* | `theorem3_uniform_from_covered` (`CoverExtract.lean:122`) | **Theorem 3** and **Definition 5 (Witness Strategy)** — makes "the cover *induces* a certified witness strategy" an inference rather than an assumption. Without R1 the mechanization would assume exactly what §4 constructs |
| **R2** statement conditioning | quantification over more initial configurations than the tool certifies (instances demanded "phantom pairs"). Entry conditioned on `admissible` (SAT `guardL ∧ guardR ∧ inv`), `mv = q₀`, `σ = preJ`; left family = all modes' windows, each `test(guardL)`-gated | *"top theorem's start set provably matches `coverMode`'s admissible-start ∀; a watertank-shaped 3-mode toy goes through where it previously demanded phantom pairs"* | `theorem3_uniform_guarded` (`CoverExtract.lean:218`) | **§4.3 admissibility** (*"an initial right mode is admissible for `m_L` if some initial state pair satisfies `φInv`"*) and **eq. (mode-inv)**'s per-mode, guard-entered decomposition |
| **R3** canonical `ϕinv` + encoding identity | the per-instance `hψ`/`hinvL`/`hinvR` residuals — a builder from the lowered invariant components plus a generic `encode … = invLe g` proof | *"pilot instance carries NO encoding hypotheses"* | `canonInv`, `encode_canonInv` | **eq. (polynomial-invariant)** — the invariant language `⋀ᵢ p_i ≤ 0` — and the encoding step into dL-rel's Theorem 2 |
| **R4** multi-component invariants | certification of only the primary component. Per-component certificates via three routes (A domain / B strict / C superlevel), each component's domain narrowed by the others `≤ 0` (multi-barrier coupling) and by the checked cuts | *"a multi-component benchmark's full conjunction invariant certified, not just the primary component"* | route adapters + the multi-barrier lemma; `CoverCertM` | **Definition 2 (Flow Certificate)** and **Theorem 1** — the paper's *"when this condition holds for every component, no boundary of the conjunction can be crossed outward"* |
| **R5** emission door + battery | hand-built instance data. `--emit-cover` emits λ, budget, node flags, edges + pruned bits, admissible starts and the verdict list as drift-checked literals; the generator writes instances re-running `decideCovered` in the kernel | *"all 46 tool-certified benchmarks build with axioms exactly `[propext, Classical.choice, Quot.sound, z3_unsat_sound]`; suite + drift + trust audits green"* | `Instances/BenchCovers/`, `BenchCoverReplay.lean` (46 × `by decide`) | the **evaluation claim** (§5) — that what the tool reports CERTIFIED is what the kernel checks, per benchmark |
| **R6** viability certificates | the last analytic hypothesis: that certified evolutions exist for the needed durations. Per mode, per evolve-box face, `UNSAT(on-face ∧ field-outward)`, plus one generic Picard lemma | *"viability hypotheses removed on every mode whose face-queries pass; legitimate failures fall back to a named per-mode hypothesis or a model-margin fix"* | `Proofs/Flow/BoxViability*`, the face census (1121/1121) | the **existence side of Definition 5** — a witness strategy must map to an actual execution, not merely a formal segment chain. Also the counterpart to the paper's "bounded-time reachability" paragraph |
| **R7** closure | drift between the docs' stated assumptions and the proofs'. Cadenced chain deprecated, contract frozen | *"`#print axioms` battery = the four axioms everywhere; hypothesis list in docs matches the frozen contract verbatim"* | `Instances/AxiomCheck.lean` | the **trust-base claim** — what a paper section on the mechanization would assert about its assumptions |

**The follow-on S-arc**, for completeness: **S1** built the reposition-window modal form
(multi-mode `rvalid`) — the paper's §4 multi-step matching; **S2** the guard-threaded cut
lift for the 13 cut-reliant benchmarks — the paper's use of guards to strengthen the
evolution constraint (§3); **S3** bounded-time viability wired per mode — existence;
**S4** housekeeping.

**How to use this list in the paper.** R1 and R2 are the two a referee should care about
most: R1 is why the mechanized Theorem 3 does not assume its own conclusion, and R2 is
why its ∀ ranges over exactly the admissible entries the tool certifies rather than a
larger phantom set. R5 is why "certifies all 46" is a kernel-checked claim rather than a
tool report. R4 and R6 are why the certificate covers the *full* conjunction invariant
and a *real* execution respectively.

---

## 7. Record: how the earlier assessments went wrong

Three prior versions of this file understated the development. The causes, so they are
not repeated:

1. **Searching for a name instead of reading.** R1's deliverable was looked up as
   `emit_from_covered` (the task-list name); not finding it, the assessment concluded the
   work was missing. It had shipped as **`theorem3_uniform_from_covered`**.
2. **Reading one sibling and generalizing.** Seeing `theorem3_faithful_multi_of_emit` led
   to "the chain is Emit-bound", without checking for the Emit-free sibling defined
   earlier in the same file.
3. **Anchoring on one route.** The modal/multiflow route was treated as the only path to
   `theorem3Form`, so the settling, uniform, and cover-based routes were never surveyed.
4. **Correcting by spot-check.** Each revision fixed one symptom from another partial
   read rather than enumerating the top theorems once.

The enumeration in §3 exists so that any future claim about "what is missing" is checked
against a list rather than re-derived.

---

## 8. Note on `tooling_sound`

`Archive/GapThreeTask3.lean:63` is the Arc-1 automaton-parametric statement — programs
derived from two `HybridAut`s via `graphOf_Gr` — instantiated non-vacuously at rover data
(`GapThreeRoverTooling.lean:531`). It routes through `EmitSegs`, so it is superseded by
§2's cover-based, Emit-free theorems. Its one surviving contribution is packaging:
deriving the programs from an automaton rather than taking `leftProgs`/`G` as given,
which is worth borrowing only if an automaton-parametric statement is ever wanted.
