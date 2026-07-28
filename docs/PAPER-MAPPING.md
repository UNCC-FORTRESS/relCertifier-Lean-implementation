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
forms, arm_refinement, rover_drag). For the rest, the generic theorems of §2–§3 plus the
46/46 ingredients above make the top line an application, not new mathematics — a
packaging gap, not a mathematical one.

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

## 6. Record: how the earlier assessments went wrong

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

## 7. Note on `tooling_sound`

`Archive/GapThreeTask3.lean:63` is the Arc-1 automaton-parametric statement — programs
derived from two `HybridAut`s via `graphOf_Gr` — instantiated non-vacuously at rover data
(`GapThreeRoverTooling.lean:531`). It routes through `EmitSegs`, so it is superseded by
§2's cover-based, Emit-free theorems. Its one surviving contribution is packaging:
deriving the programs from an automaton rather than taking `leftProgs`/`G` as given,
which is worth borrowing only if an automaton-parametric statement is ever wanted.
