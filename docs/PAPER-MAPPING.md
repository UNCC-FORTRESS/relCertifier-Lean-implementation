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

**(b) Settling / cadenced — ⚠️ VACUOUS for relational invariants. Do not cite.**
`theorem3_faithful_settling` (`Proofs/Soundness/GuardThreaded.lean:417`), its clocked and
cadenced variants (`Proofs/Encoding/ClockedTop.lean:41,368,462`), and
`settling_end_to_end` (`Proofs/Encoding/FvDischarge.lean:632`) all require a hypothesis of
the `GBoxAll` shape (`GuardThreaded.lean:380`), whose own docstring reads:

> **QUARANTINED (defective shape — task H).** Relational `g`-preservation along right
> residences, stated LEFT-CONTEXT-FREE: for an `L`-mentioning `g` and a drain-type mode
> this is **unsatisfiable** (the left coordinates are unconstrained), so no certificate
> battery can discharge it. … **Do not build on this.**

Why it is unsatisfiable, concretely: `BoxLe α g ν := ∀ ω, sem α ν ω → g ω ≤ 0`
(`dL-lean/DLLean/DI.lean:46`) is *unconditional* — the zero-duration run forces
`g ν ≤ 0` for **every** `ν` satisfying `Gd q`. But `Gd q` (`realGdOf`) constrains only
right-side coordinates, while a relational `g` mentions left ones. For watertank,
`g = x_L − x_R − 3`: take `x_R = 5` (inside Low's guard) and `x_L = 100`; then
`g ν = 92 > 0` and `BoxLe` fails. So the hypothesis is false and every theorem above is
**vacuously true** for the suite's actual relational invariants.

This is why R7 deprecated the cadenced chain and quarantined `GBoxAll`, and why the
S-arc built the replacement: *"the paper-faithful replacement couples each within-window
piece by its own JOINT certificate and each seam by a REPOSITION certificate
(left-contextualized)"*.

**What the settling battery does prove, non-vacuously:** the 46 `*_real` theorems
conclude `GuardSettlingB`, which mentions no invariant term at all — it says the right
system's flow exists for the control interval, stays in its evolution domain, and lands
in a state satisfying some retained successor's guard. That is the paper's
**well-formedness assumption** (nonblocking + successor-complete), discharged for 46/46.
Valuable, and worth claiming — but it is *not* relational invariant preservation.

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


### 3f. Findings from the full read of `Proofs/Encoding` (27 files, 7,746 lines)

**The Z3 leaf is exactly one theorem.** `segPres_from_flowCert`
(`BridgeDischarge.lean`) is the only theorem in the layer whose hypothesis is a
`z3solve … = unsat`; it produces `SegPreservesOn`. Every route above is parametric in
`CoverCert`, so `z3_unsat_sound` enters only there. This matches the axiom audit exactly.

**Route classification by hypothesis** (read off every signature in the directory):

| route | distinguishing hypotheses | verdict |
|---|---|---|
| cover / uniform — `decideCovered_implies_theorem3_faithful`, `theorem3_uniform_from_covered`, `theorem3_uniform_guarded` | `cert : CoverCert`, `hchk : decideCovered`, `hproj : RightProjAlign(V)`, side-split disjointness | **live, non-vacuous** |
| settling / cadenced — `theorem3_faithful_settling`, `_clocked`, `_cadenced`, `_cadenced'`, `settling_end_to_end` | **`hgbox : GBoxAll`** (all four ClockedTop/GuardThreaded variants) or the same shape as `hcert` | **vacuous** (§3b) |
| Emit-carrying — `theorem3_faithful_multi_reposition`, `decideCovered_implies_theorem3_faithful_multi`, `theorem3_uniform_multiflow`, `uniform_multiflow_end_to_end` | `hemit : EmitSegs` / `EmitWindows` | assumes the witness; superseded by R1 |
| `hstep`-parametric — `theorem3_faithful`, `_multi`, `_multiE`, `_multiE_LR` | `hstep` plus disjointness only | sound; `hstep` supplied per instance |

**Three further defects, each already self-documented, each with a live replacement:**

1. `Hmulti_window_prefixed` (`EnvelopeChain.lean`) carries `hdisH`, which the file marks
   **UNSATISFIABLE for genuine hops** — "the frozen hop binds every left coordinate".
   The replacement `Hmulti_window1_prefixed` (k = 1) carries **no `hdisH`**, only
   `hcouple`; watertank's modal instance uses that one.
2. `ClockedTop`'s `hbudgetAll` is "unsatisfiable for autonomous benchmarks unless `domL`
   itself bounds time" — repaired in the uniform route, where "the clock caps every
   piece" (`UniformMultiflow.lean:10`).
3. `rightReach_is_R_real_run` (`JointBridge.lean`) requires **`NoRepoModes`** — it
   applies only to graphs with no reposition modes. A real scope limit on that
   particular reach→program bridge, not previously noted here.

**The disjointness side conditions are genuinely discharged, not hidden.**
`hdis_multi`, `hddF_multi`, `hddF_multiE` (`UniformFvDischarge`, `EnvelopeChain`) and
`hdis_aux`, `hddF_aux` (`FvDischarge`) prove them generically by side-splitting the
variable space into `Lv` / `Rv` / `Aux`. This is what makes the `Aux` placement of `mv`
and `tg` load-bearing — and it is the repair for the archived `MvFrozen` vacuity
(`BridgeUnit1.lean:119` records the same failure mode).


### 3g. Findings from the full read of `Proofs/Flow` (12 files, 5,165 lines)

**The trust leaf, counted exactly.** `z3_unsat_sound` is *applied* at **12 sites across 5
files**: `Trusted/Oracle.lean` (4 — flow certificate, segPreserves, and two pruning
wrappers), `Proofs/Soundness/CutLift.lean` (4 — the cut-channel routes),
`Proofs/Flow/BoxViability.lean` (1), `BoxViabilityBounded.lean` (1) and
`ViabilityWiring.lean` (2 — the face/anchor viability verdicts). Everywhere else the
`hz3 : z3solve … = unsat` occurrences are *hypotheses*, discharged by supplying named
facts. So the trust boundary is narrow and enumerable, but it is **not** confined to
`Trusted/` — the viability and cut routes apply the axiom directly. Worth stating
precisely rather than as "one leaf".

**`Instances/AxiomCheck.lean` prints only `flow_certified` and `segPres_from_flowCert`.**
The other leaf sites (cut lift, the four viability verdict theorems) are not in the
printed battery. Not unsound — they are the same axiom, used the same way — but the audit
under-reports the leaf set, and extending it would make the claim self-evident.

**Proven vacuity and proven satisfiability are used as a discipline, in both directions:**
- `SuccReachUnion_vacuous` (`MultisegLanding.lean`) takes **no hypotheses** and proves a
  tempting formulation unconditionally true — hence useless. The development uses the
  non-vacuous `SuccReach` instead. The vacuity is a *theorem*, not a comment.
- `WFBoundary_narrowing_satisfiable` and `narrowing_coherence_true` (`WFBoundary.lean`)
  go the other way: they exhibit witnesses proving the boundary hypothesis is
  satisfiable, so the instances built on it are not vacuous.

This is the pattern that makes the `GBoxAll` finding (§3b) legible rather than alarming:
where the project suspects vacuity it either proves it and retires the route, or proves
satisfiability and keeps it.

**The analytic core is real.** `PicardBridge.lean` (1,607 lines) carries genuine
Mathlib-level ODE work — `odeField_contDiff`, `odeField_lipschitzOnWith`,
`IsPicardLindelof` construction, `uniform_local_existence_on_compact`, compactness
subcovers, slab chaining. `StratifiedBarrier.lean` records that "mutual narrowing was
circular and unsound for the non-strict routes" and now routes through the repaired
indexed `stratified_barrier_sound`.

**Route-(b) existence cost, confirmed concretely.** `HExistSegB_of_viability`
(`ViabilityWiring.lean`) needs, per benchmark: `hM`, well-formedness, the face lists,
strict/growth bounds, domain satisfaction, `ha : 0 < a`, `hLipOn` and `hfbnd` (the
per-anchor Lipschitz and field-bound data). That is the S3 route-(b) price for
non-contract fields, and it is why watertank's contract route
(`hExistSegB_of_wellFormedFlowB`, 124-line file) was the cheap path.


### 3h. Findings from the full read of `Proofs/Transfer` (5 files, 3,918 lines)

This layer is the bridge from the **scaled integer model** — where the kernel
certificates live (values ×σᵢ, time in `dt`-units) — to the **real parsed benchmark**.
It is what makes the 46 `*_real` theorems mean something about the benchmark files.

- `Rescale.lean` (389 L) — `GuardSettlingB_rescale`, the scaling-transfer lemma, proved
  once: the scaled model's per-mode settling obligation implies the real one, provided
  the two sides correspond by the pushforward law `f(σ·x) = σᵢ·u·f'(x)` (exactly the
  coefficient laws `Faithful` checks) and guards/envelopes correspond under state
  scaling. The witness flow transports by `Φ'(t) = σ⁻¹·Φ(t/u)` (chain rule).
- `FaithfulBridge.lean` (2,307 L) — gives the kernel's raw `ℤ × ℤ` `QF` arithmetic a
  real denotation, so `Faithful`'s Boolean coefficient laws become real-valued
  pushforward identities. This is the bulk of the layer and it is genuine work.
- `FaithfulBridgeGuards.lean` (401 L) — terrain/affine guard-map variants.
- `FaithfulBridgePad.lean` (687 L) — the eight padded benchmarks (`vs.length < n`),
  where a padded coordinate needs an invertible scale the transcription does not supply
  (`sigmaPad`).
- `RealEndToEnd.lean` (134 L) — the generic per-family theorems; its header states the
  design intent plainly: *"Per-benchmark instantiation (Instances/) is then a dozen lines
  of `decide`/`rfl`/`norm_num` discharges — the watertank pattern, mechanized for all 46."*

**Non-vacuity of the 46 `*_real` theorems — checked, and it holds by construction.**
`GuardSettlingB` is `∀ base, sat (Gd q) base → …`, so it would be vacuous if
`realGdOf q` were unsatisfiable. `realGdOf` is a conjunction of per-coordinate closed
bands (`envFormulaR` ∧ the guard band). And `decideWellFormed` — kernel-checked `rfl`
for all 46 — includes `(List.finRange n).all fun i => bandOrdered (M.env i)`, where
`bandOrdered b` is `l ≤ h` when both endpoints are present, plus per-mode clauses
including `0 ≤ m.glo` and band-containment (`bandInside`). So band non-emptiness is part
of what every benchmark's well-formedness certificate establishes; the `*_real`
obligations are non-vacuous **because a kernel check says so**, not by inspection.
(Verified `bandOrdered` and the `decideWellFormed` clause list directly; did not trace
every `checkMode` sub-clause.)

**Net for §4:** the 46 `*_real` theorems are substantive — they establish, at the real
benchmark's own scale, that every declared right mode's flow exists for the control
interval, stays in its evolution domain, and lands in a state satisfying some retained
successor's guard. That is the paper's well-formedness assumption, discharged 46/46 and
non-vacuously.


### 3i. `Proofs/Soundness` (6 files, 2,397 lines) — and the consolidated route verdict

**`CutLift.lean` (505 L)** — the checked-cut channel. Four atom routes
(`atom_boxle_{R,L}_{nonstrict,strict}`) plus `AtomFact.ofLie`, each **conditional** on
the atom holding initially (`hinit`), so none repeats the `GBoxAll` trap. `cut_lift_boxle`
does the narrowing lift; `cut_hcert` assembles it from O1 (guard entry) and the Z3
verdict. Four of the twelve `z3_unsat_sound` sites live here.

**`CutChannel.lean` (70 L)** — the core lift, cleanly stated: if the invariant holds on
the narrowed domain `D ∧ S` and the flow provably stays in `S`, it holds on `D`.

**`UniformEvol.lean` (291 L)** — `contract_stays` and `WellFormedFlowB_contract` need
only arithmetic side conditions (`0 ≤ k`, band containment): **no Z3, no budget**. This
is why watertank's existence discharge (S3 route (a)) was cheap.

**A second documented vacuity trap: `hbudgetAll`.** It states that *every* solution of
the left ODE within `domL` has duration `≤ k·dt`. `ClockedTop.lean`'s header names it
outright: *"unsatisfiable for autonomous benchmarks unless the caller smuggles a clock
into `domL` — a vacuity trap"*. It is carried by `theorem3_faithful_settling` (which
therefore has **both** traps) and by the whole landing family —
`theorem3_faithful_landing_clocked`, `_wf`, and `_uniform`. Clocking the left retires it,
which is exactly what `ClockedTop` and the uniform route do.

**Consolidated verdict over every route to `rvalid (theorem3Form …)`:**

| route | distinguishing hypotheses | verdict |
|---|---|---|
| cover / uniform — `decideCovered_implies_theorem3_faithful`, `theorem3_uniform_from_covered`, `theorem3_uniform_guarded` | `CoverCert`, `decideCovered`, `RightProjAlign(V)` | **live** |
| `hstep`-parametric — `theorem3_faithful`, `_multi`, `_multiE`, `_multiE_LR` | `hstep` + disjointness | **live** |
| settling, unclocked — `theorem3_faithful_settling` | **`GBoxAll` and `hbudgetAll`** | doubly vacuous |
| settling, clocked/cadenced (×3) and `settling_end_to_end` | **`GBoxAll`** (budget retired by clocking) | vacuous |
| landing, clocked (×3 incl. `_uniform`) | **`hbudgetAll`** | vacuous for autonomous benchmarks |
| Emit-carrying — `*_of_emit`, `theorem3_uniform_multiflow`, `uniform_multiflow_end_to_end`, the reposition multi forms | `EmitSegs` / `EmitWindows` | sound, but assumes the witness — *unless discharged at the instance* |

**Both live instantiations survive this.** `rover_drag_multiflow` goes through
`uniform_multiflow_end_to_end`, whose `hcov` bundles `EmitWindows` — but the instance
**discharges it inside the proof**, leaving only `hz3` (one Z3 verdict) and `hES`
(existence). `watertank_modal` goes through `theorem3_faithful_multiE_LR` with `hstep`
assembled from six joint verdicts and six existence facts, the latter proven in-kernel by
`WatertankViability`. Neither touches `GBoxAll` or `hbudgetAll`.


### 3j. `Instances/` — the per-benchmark verdict, settled

Routing is uniform and was checked exhaustively, not sampled:

- **all 33** `Throughout/*.lean` apply `check_sound_multi`;
- **all 13** `CutThroughout/*.lean` apply `check_sound_multi_cut`;
- **none of the 46** mentions `rvalid` — they stop at
  `Covered ∧ CoexecInvAllThroughout{,G}`.

Both are **live**: `check_sound_multi`'s certificate is `CoverCertM` over the *joint*
graph (`realModeOf` builds `jointSys` with domain `evolveL ∧ evolveR`) and its invariant
premise is conditional (`hinit : InvAllHolds gs ν`) — neither the `GBoxAll` nor the
`hbudgetAll` trap.

**The definitive per-benchmark table:**

| what is proven | benchmarks | route | status |
|---|---|---|---|
| relational invariant holds **throughout** every right co-execution | **46/46** (33 cut-free + 13 cut-lifted) | `check_sound_multi{,_cut}` from named Z3 verdicts | ✅ **live** |
| right-system well-formedness at the real scale — flow exists for the control interval, stays in its domain, lands in a retained successor's guard | **46/46** (`*_real`) | Transfer/rescale + `decideWellFormed` `rfl` | ✅ **live** (this is the paper's well-formedness *assumption*, discharged) |
| the instance **is** the parsed benchmark file | 46/46 | `faithfulSettling… = true := rfl` | ✅ live |
| the tool's cover decision, kernel-replayed | 46/46 | `coverReplays … := by decide` | ✅ live |
| full ∀∃ `rvalid (theorem3Form …)` | **2** — `watertank` (`WatertankModal`/`Viability`), `rover_drag` (`UniformPilot`) | `theorem3_faithful_multiE_LR` / `uniform_multiflow_end_to_end` | ✅ **live** |
| `rvalid (theorem3Form …)` | `watertank` ×3 (`EndToEnd`), `arm_refinement` (`Mega`) | settling route | ❌ **vacuous** (§3b) |

**Answer to "are all benchmarks end-to-end verified?"** — depends on which statement:

- **Invariant preservation throughout co-executions: yes, all 46, non-vacuously**, from
  named Z3 verdicts with the instance pinned to the benchmark file by kernel `rfl` and
  the cover decision replayed by `decide`. This is the substantive relational result.
- **The ∀∃ modality (`theorem3Form`, the paper's Definition 1 / Theorem 3 conclusion):
  two benchmarks.** The other 44 have no non-vacuous ∀∃ statement, and the four written
  ones outside those two go through the quarantined settling route.


### 3k. What "Theorem 3 for all 46" would actually take — measured

Measured from the emitted covers, not estimated. The cover budget `B` is the
ℕ-discretization of `ε_L` against per-mode weight 1, so `B` is **the number of joint
pieces a window needs** (base fires at `B ≤ weight`).

| | benchmarks | route |
|---|---|---|
| **budget = 1** (one piece per window) | **21** — 13 of them also use repositions | watertank's exact shape: `Hmulti_window1_prefixed` |
| **budget > 1** (multi-piece windows) | **25** — **all 25 also use repositions** | needs k > 1 **with hops** |
| budget > 1, no repositions | **0** | — |

**The 25 are blocked on a documented negative finding.** The only k > 1 route with hops is
`Hmulti_window_prefixed` (`EnvelopeChain.lean`), and its own note reads:

> its `hdisH` hypothesis (vars-disjointness of the frozen-left hop program against the
> clocked left segment) is **UNSATISFIABLE for genuine hops** — the frozen hop binds every
> left coordinate (derivative 0), so its `Program.vars` always meets the left window's.
> **NEGATIVE FINDING**, kept per the never-delete rule; the `k = 1` route below needs no
> such disjointness (single window piece ⟹ nothing to commute past).

This is not a missing proof — it is a formulation whose side condition **cannot** be
satisfied. Multi-piece windows need the hop program commuted past a window piece, and
vars-disjointness is the wrong tool for that because a frozen hop still *binds* the left
coordinates. A k > 1 route needs a **different argument** (e.g. an explicit clock-tracking
interleave, or absorbing the hop into the piece boundary) — research-level work, not
mechanical generation.

**Revised sizing of "Theorem 3 for all 46":**

1. **21 benchmarks** — plausibly reachable with existing lemmas, per-benchmark cost:
   `HExistSegB` existence (route (a) cheap for contract fields, route (b) Picard data
   otherwise), the `hstep` assembly (S1's pattern, currently hand-built), the
   `CoverCertM` → `CoverCert` gap, and `Aux` room. Mechanical-to-moderate.
2. **25 benchmarks** — **blocked** until a k > 1-with-hops window lemma exists. Over half
   the suite.

So the roadmap's "modal instances beyond watertank" line understates this considerably:
it is not one generator away. The k = 1 restriction that let watertank through is exactly
the restriction 25 benchmarks violate, and the general case has a recorded impossibility
for its current formulation.

**Where this interacts with the shelved fixpoint design.** `docs/FIXPOINT-DESIGN.md`
§4 claims the winning-region reformulation dissolves precisely this blocker ("hops are
just edges inside `F`; chains handled by the fixpoint, not by a per-length lemma"). That
claim now has a concrete price tag attached: it would be addressing a wall that blocks
25/46 benchmarks, not a convenience.

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
| `Instances/EndToEnd.lean` | watertank | `rvalid (theorem3Form …)` ×3 — **but via the settling route, hence vacuous (§3b)**; the first form additionally carries a documented `hbudget` caveat |
| `Instances/Mega.lean` | arm_refinement | fidelity ∧ settling in one term — **same settling route, same vacuity (§3b)** |
| `Instances/UniformPilot.lean` | rover_drag | **`rvalid (theorem3Form …)`** from **one** Z3 verdict + `hES`; includes `rover_drag_covered : decideCovered … = true := by decide` |
| `Instances/WatertankModal` + `WatertankViability` | watertank | **`rvalid (theorem3Form …)`**, multi-mode with repositions, existence proven in-kernel |

So `rvalid (theorem3Form …)` is written out for three benchmarks — but **only two of
those are non-vacuous**: `rover_drag` (`UniformPilot`, joint certificate) and `watertank`
(`WatertankModal`/`WatertankViability`, joint certificates + proven existence). The
`EndToEnd` and `Mega` forms go through the settling route and are vacuous for relational
invariants (§3b).

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

The development was built as an ordered arc (`docs/history/ROADMAP.md`), R1–R7, each item
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
