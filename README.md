# relCertifier-lean

A **formally verified** relational-invariant certifier for pairs of hybrid programs,
mechanized in Lean 4 on top of [dL-lean](https://github.com/UNCC-FORTRESS/dL-formalization-Lean)
(`v0.1.0-DI`) and [dL-rel](https://github.com/UNCC-FORTRESS/NFM25-relDL-Lean) (`v0.1.0-NFM25`, NFM'25 encoding).

It certifies a supplied relational invariant between a left (deployed) and right (reasoning)
hybrid system via UNSAT-of-negation with Z3-NRA, with **every soundness-critical function proven
correct**, each proof citing a mechanized theorem of the imported theory. The single
trusted assumption of the whole tool is that Z3's `unsat` verdict is sound
(`z3_unsat_sound`); everything else is kernel-checked.

The headline guarantee is **`tooling_sound`** (`GapThreeTask3.lean`): given hybrid automata `L` and `R`
and an invariant candidate, if the tooling's cover succeeds, the paper's ∀∃ refinement modality holds
over the programs **derived from the actual `L` and `R`** — the right ∃-response jumps only along
*declared* transitions (`R_real = star(rightAutomatonBody)`), not the weaker flat choice-star. It covers
**genuine multi-flow** (the right switches modes mid-residence), **repositions** (static and dynamic),
and the **whole left automaton** (all left modes). Separately, on the 47-benchmark suite the tool runs
and reports **46 CERTIFIED / 47** (1 inconclusive-Z3 ERROR, never a false verdict) — that is *tool
behavior*, a distinct and weaker claim than the Lean theorem. The two are kept distinct throughout.

## What "end-to-end verified" means — and its exact scope

**(a) What the tool does.** relCertifier checks a ∀∃ *relational* property between two hybrid systems —
a deployed system (left) and a reference / reasoning model (right): *for every deployed behavior, the
reference has a matching behavior that keeps the two within a stated tolerance.* It is a **certifier** —
it validates a supplied relational invariant via Z3 (UNSAT-of-negation is the only trusted verdict) and
reports `CERTIFIED` / `DECLINED` / `ERROR`.

**(b) What "end-to-end verified" means — intuitively.** The tool has two layers: a **checker** that
outputs `CERTIFIED`, and the **mathematical property** from the paper (the ∀∃ refinement modality of
differential dynamic logic — Theorem 3). It is easy for these to drift apart: the checker could say YES
while nobody has proven that YES actually *means* the property holds — and worse, it could prove
something about *a* graph unrelated to the input programs. We closed both gaps with a machine-checked
proof in Lean. **When the tooling's cover succeeds — bottoming out at Z3 UNSAT obligations on `L,R`'s
actual dynamics — the paper's ∀∃ property provably holds, for the reference automaton's *actual declared
transitions*, over the programs the graph is *built from*.** The chain runs unbroken from the tooling's
certificate → the paper's Theorem 3 → the dL semantics of the actual `L, R`, with a single trusted axiom:
Z3's `unsat` is sound (`z3_unsat_sound`). The verdict is not *asserted* to mean the property — it is
*proven* to, and about *your* `L` and `R`.

**(c) The exact scope — stated plainly.** The end-to-end theorem `tooling_sound` (`GapThreeTask3.lean`)
covers:

- **genuine multi-flow** — one left residence during which the right switches modes several times, each
  segment coupled by a duration-bounded ∀∃ certificate (GAP 1);
- **repositions** — both *static* (state-preserving mode switch) and *dynamic* (frozen-left right flow),
  modeled as atomic modes the loop interleaves (GAP 1);
- **the whole left automaton** — every left mode contributes its own per-mode cover; the family is
  composed by `faModal_bigChoiceL` with the right's mode carried in the state (GAP 2);
- **cover of the actual programs** — the graphs are `graphOf(L, R)`, built from `L,R`'s real
  dynamics/transitions; the graph↔program alignment is *derived*, not assumed (GAP 3).

**Honest boundaries** (stated up front, not buried — see the walkthrough for detail): the model is
**automaton-shaped** programs (mode lists, the fragment the tool handles); edges are **⊤-guarded** (the
⊤-edge model, guard-reaching folded into the model, as in the runtime graph); the left is
**over-approximated** on the ∀-side (free mode-choice ⊇ the guarded automaton, so `[[L>>R]]inv` follows
soundly); and the **emit boundary** — the Z3 UNSAT witnesses and the cover's mode sequences enter as
emitted per-obligation facts, `z3_unsat_sound` at the leaf, exactly the boundary certificate-based
verification standardly uses.

> **Two claims, kept distinct.** "The tool certifies 46/47 benchmarks" is *tool behavior*. "The tooling's
> cover is proven to entail the paper's ∀∃ property over the actual `L, R`" is the *Lean guarantee*.
> Neither implies the other, and this README does not conflate them.

**Trusted:** Z3's `unsat` verdicts — one axiom, `z3_unsat_sound`. Everything else (the cover, the ∀∃
bridge, the multi-flow/reposition machinery, the family composition, the `graphOf` tie) is proven in Lean
on the three standard axioms. Reproduce: `lake env lean RelCertifier/AxiomCheck.lean`.

### Verification status

| Link | Status |
|---|---|
| Checker → co-execution invariant (`check_sound`) | **proven** |
| Cover → ∀∃ modality, transition-faithful (`decideCovered_implies_theorem3_faithful`) | **proven** |
| Genuine multi-flow + reposition (GAP 1, `theorem3_faithful_multi_reposition`) | **proven** |
| Whole left-mode family (GAP 2, `theorem3_faithful_family`) | **proven** |
| Cover of the actual programs `L,R` (GAP 3, `tooling_sound`) | **proven** |
| Modality → paper Theorem 3 / dL-rel (`faModal_to_faShape`, `encoding_correct`) | **proven** |
| Trust boundary | Z3 UNSAT (`z3_unsat_sound`, 1 axiom) |

## Imported theories — the four repos it builds on

relCertifier-lean proves nothing about differential dynamic logic from scratch; it **composes
already-mechanized theories**. Every soundness-critical lemma cites a theorem from one of these:

| Repo | Pin | What it provides | Key theorems used here |
|---|---|---|---|
| **[dL-lean](https://github.com/UNCC-FORTRESS)** | `v0.1.0-DI` | Core dL: syntax `Term`/`Formula`/`Program`, semantics `Term.eval`/`Formula.sat`/`Program.sem`, and the **differential-invariant** calculus | `DI_strict`, `DI_nonstrict_domain`, `Lie`, `Lie_eq_fderiv`, `hasDeriv_g_along_flow`, `sem_ode_iff_integralCurve`, `nonstrict_boundary_insufficient` (the `t²` soundness countermodel) |
| **[dL-rel](https://github.com/UNCC-FORTRESS/NFM25-relDL-Lean)** (NFM'25) | `v0.1.0-NFM25` | The **relational (bi-state) extension** of dL and its host **encoding** | `RFormula`, `encode`, `faShape` (the ∀∃ relational modality `[|(α,β)⟩⟩ψ`), `encoding_correct` / `encoding_correct_exists` (**Theorem 2**), `Bridges` / `exists_bridge` |
| **dL-caltiming** (CSF'25) | `v0.1.0-CSF25` | The **∀∃ endpoint modality** `faModal` and its ODE / composition rules (the timed relational calculus) | `faModal`, `faModal_ODE_G`, `faModal_LOCK`, `faModal_MULTI`, `faModal_seq`, `plantT` |
| **Mathlib** | (bundled) | Real analysis + ODE existence | `IsPicardLindelof` (Picard–Lindelöf), `ContDiff`, `isCompact_univ_pi`, `IsCompact.elim_finite_subcover`, `Convex.lipschitzOnWith_of_nnnorm_fderiv_le` |

The dependency flow: **Mathlib** (analysis) → **dL-lean** (dL + `DI`) → **dL-rel** (bi-state
encoding) and **dL-caltiming** (∀∃ modality) → **relCertifier-lean** (this repo: certifier + witness).
dL-rel is required from GitHub (`NFM25-relDL-Lean`, pinned to tag `v0.1.0-NFM25`); dL-caltiming and
dL-lean are pinned transitively through dL-rel (no sibling checkout needed).

## The end-to-end theorem, in depth

This is the centerpiece: what `tooling_sound` proves and how the proof composes. A reader who knows
differential dynamic logic and hybrid systems, but not this codebase, should be able to follow it. Read
it as a chain — each step says *why* it is needed and *what* it establishes.

### 0. The trust boundary — where the foundation sits

One thing is trusted: **Z3's `unsat` verdict is sound** (`z3_unsat_sound`, `Oracle.lean`). `z3solve` is
an *opaque* Lean constant; the axiom says that when it returns `unsat` for a query, that query really is
unsatisfiable. Everything else — the cover, the ∀∃ bridge, the multi-flow and reposition machinery, the
family composition, the graph↔program tie — is proven in the Lean kernel on the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The Z3 leaf enters only where a per-obligation
`z3solve … = unsat` is turned into a flow certificate. So the top theorem is **parametric in the
certificate** (3 axioms in its own `#print axioms`), and the 4th axiom (`z3_unsat_sound`) appears when
the certificate is *constructed*, per obligation. This is the standard certificate-based-verification
boundary: the checker is verified, the SMT `unsat` is trusted.

### 1. The checker side — the cover keeps the invariant (`Cover.lean`, `Checker.lean`)

`decideCovered` is a *verified, computable* transcription of the paper's **Definition 4**: from a
configuration (right mode `q`, budget `B`), either one residence closes the budget (`base`), or every
retained successor covers the decremented budget (`step`), plus σ-matched reposition steps. `cover_sound`
proves that a `Covered` graph, with each mode's flow certificate, preserves the invariant along **every**
right response (`RightReach`): if it holds at the start, it holds at every reachable endpoint. Budget
strictly decreases each residence (`cover_budget_decreases`), the finiteness argument that rejects
budget-neutral cycles. **Intuition:** the cover search finds a way for the *reasoning* right program to
respond to every *deployed* left behavior while keeping the two within the stated tolerance, forever.

### 2. The ∃-right faithfulness — the heart (`JointBridge.lean`, `BridgeFinish.lean`)

The ∀∃ modality is `∀ left run, ∃ right run, invariant preserved`. The *right* run must be something the
**actual reference automaton can do** — a run that follows *declared* transitions — not a permissive
over-approximation. The naive encoding uses the **flat** choice-star `(⨆ right modes)*`: any sequence of
modes, in any order. Because the ∃ quantifies over runs of that flat program, it is *easier* to satisfy
than "there exists a run that follows the automaton's declared edges" — so the flat statement is *valid
but weaker than intended*. `theorem3_faithful` replaces it with `R_real G mv = star(rightAutomatonBody G
mv)`, where a mode variable `mv` names the current mode and a jump fires **only** along a declared edge
`e ∈ edgesFrom q`. **Intuition:** the existential witness has to be something the real automaton can
actually do, or the guarantee is hollow. (A companion soundness finding: the invariant must carry
`mvValid` — that `mv` holds a *declared* mode index — or `rvalid` is false at bi-states whose fresh mode
variable is undeclared. See "Soundness findings".)

### 3. Genuine multi-flow — bounded coupling, clock, collapse (`BridgeReposition.lean`)

Within one left residence, the right may switch modes several times (the right runs "faster" than the
left). Each such segment is coupled by a **duration-bounded** ∀∃ certificate: the left flows for at most
a budget unit `dt`, the right responds staying in its domain. The subtle question — *where do the segment
boundaries come from?* — is answered by the **cover code, not by analysis**: the switch is
**budget-triggered** (`decideCovered`'s `B`-recursion, one clock unit `dt = ε_r/λ` per segment), a
**fixed** cut, not a run-dependent first-passage (solving where a trajectory exits a domain). A transient
**clock** `tg` states the fixed-duration segment (`plantT_split`) and is then eliminated (`clockReduce`);
`plantT_split_iter` tiles the residence into `k` fixed-`dt` pieces (verified arithmetic, `Σ = k·dt`, not
assumed). The duration bound is carried as a **predicate on the run** (`plantT`: this run has duration
≤ `dt`), *not* as a narrowing of the domain — the mode's real evolution domain stays intact
(`faModalB`, `faModal_ODE_G'_bounded`). The `k` segments compose (`multiseg_clocked`), and a **clock-lift
collapse** (`clockLift_collapse`) reduces the `k`-fold clocked left back to the single physical left
flow, the transfer riding on `tg`-invisibility (the right never reads the clock). **Intuition:** the
segment boundaries are the certificate's *budget* units — fixed, not discovered — and the right's
mode-switch response is a real declared-edge star run (`faithful_rights_bridge`, threading each switch
through a declared `G`-edge and carrying mode-validity across the whole fold).

### 4. Repositions — pause and re-aim (`BridgeReposition.lean`, `RepositionDischarge.lean`)

Between flow segments the right can **reposition**: switch modes while the left is paused. Two kinds:
*static* (state-preserving — the right jumps to a new mode, nothing evolves, preserved by
`reposition_step_pres` via zero-motion + mode-variable-invisibility) and *dynamic* (the right *flows*
under a **frozen-left** field, `dynSys = jointSys 0 fR λ`, its certificate `cert.repoDynPres`). The key
structural move: a reposition is modeled as a **separate atomic (frozen) left mode**, and the loop
`star (bigChoice [flow, frozen])` **interleaves** flow and frozen modes. This is sound (the star covers
the cover's mixed run as one interleaving) and dissolves a piecewise-left problem. The dynamic reposition
then *reuses* the multi-flow coupling at `fL := 0`, sourced from `cert.repoDynPres` — no new machinery.
**Intuition:** the right can "pause and re-aim" between flow segments; each pause-and-aim is just an extra
loop iteration with a frozen left.

### 5. The family — all left modes (`GapTwo.lean`)

The whole deployed automaton is a *family* of covers: each left mode has its **own** cover graph `Gj` and
certificate (the tool's `certifyCore` runs a separate cover `for mL in L.modes`). `theorem3_faithful_family`
composes them via `faModal_bigChoiceL` over the left choice, with each left mode's hstep from GAP 1.
A left-mode switch `mL → mL'` is **per-iteration loop re-entry**: the loop invariant `invLe g ∧ mvValid`
is preserved across iterations, the right's current mode is carried in `mv`, and each iteration reads
`mv` and dispatches. **`mv` is the sync**, carried in the state — no cross-mode argument. (Each mode
carries its own `Gj`/certificate; a shared `Gj` would be vacuous, since `RightProjAlign Gj … fL` forces
`Gj`'s joint modes to `jointSys fL fR`, injective in `fL`.) **Intuition:** each left mode has its own
cover; the loop composes them, tracking the right's current mode in the state across the switch.

### 6. The tooling-soundness tie — cover of the *actual* programs (`GapThreeFoundation.lean`, `GapThreeTask2.lean`, `GapThreeTask3.lean`)

Steps 1–5 prove `cover ⟹ ∀∃` for a graph `G`. But nothing yet forces `G` to be the graph *of the input
programs* `L, R` — the theorem could be about a graph unrelated to your input. GAP 3 closes that. A
`HybridAut` is the mode-list representation of `L, R`; `⟦·⟧` (`leftEncode`/`rightEncode`) encodes it to
the dL programs the modality is about (`⟦R⟧ = R_real (graphOf_Gr R)`, exactly the theorem's right);
`graphOf(L, R)` builds the semantic search graphs from `L,R`'s *real* dynamics (`jointSys mL.dyn mR.dyn`,
`mL.dom ∧ mR.dom`) and transitions. The graph↔program alignment (`RightProjAlign`) — previously an
*assumption* — is now **derived** from the `graphOf` construction (`RightProjAlign_from_graphOf`): both
the right graph `Gr` and the joint graph `Gj(mL)` are built per-`mR` from the same `R.modes`, so the
per-mode alignment holds by `rfl`/unfolding. **Intuition:** the theorem would be hollow if it proved
something about *a* graph; this step makes it about *your* `L` and `R`, and the fact that the graph is a
faithful picture of the programs is *proven from how the graph is built*, not assumed.

### 7. The composition — and the honest boundaries

`tooling_sound` assembles steps 1–6 into: *given hybrid automata `L, R`, per left mode its emitted
certificate + cover sequences + the framework side-conditions, if the cover succeeds then*
`inv → [[⟦L⟧ >> ⟦R⟧]]inv` — the ∀∃ refinement modality over the programs derived from `L, R`. The honest
boundaries, stated plainly:

- **⊤-edge model** — declared edges are ⊤-guarded; the guard-reaching condition is folded into the model
  (as the runtime graph does). Shared throughout.
- **∀-left over-approximation** — the left is modeled as free mode-choice (guards dropped on the ∀-side).
  This *over*-approximates the guarded `L` (more left runs), so `[[⟦L⟧ >> ⟦R⟧]]inv` follows *soundly* (∀
  over more ⟹ ∀ over fewer); it is stronger, not a gap. The reposition-pause frozen mode likewise
  over-approximates the left (a stay option).
- **the emit boundary** — the Z3 `unsat` witnesses (the flow/reposition certificates) and the cover's
  mode-switch **sequences** (`EmitSegs`) enter as *emitted* per-obligation facts. The Z3 witness is a
  fact about the *opaque* `z3solve`, provided at certificate construction with `z3_unsat_sound` at the
  leaf — the *same* boundary `certified_relational` and every certificate-based verification use. The
  cover sequences are the search's output (which modes the right visits, in what order), a dynamic fact,
  not derivable from the static graph.
- **automaton-shaped scope** — the programs are mode-list hybrid automata (`isLeftAut`/`isRightAut`), the
  fragment the tool handles. The theorem's conclusion is about general dL programs; the scope predicate
  names where it applies.

A reader should come away understanding both *what is proven* (the tooling's cover ⟹ the paper's ∀∃ over
the actual programs, transition-faithful, multi-flow, reposition, all left modes) and *where the trust
sits* (Z3 `unsat` at the leaf; the ⊤-edge model; the ∀-left over-approximation; automaton-shaped
programs) — without overclaiming.

## What is verified

The tool is built bottom-up as three verified local certificates, their composition into the
cover (Theorem 3), the transition-faithful ∀∃ bridge over the real automaton, the multi-flow /
reposition / family lift, the tie to the actual programs, then a runnable front-end.

| Stage | File | Function(s) | Correctness theorem | Cites |
|---|---|---|---|---|
| **1. Flow certificate** | `FlowCert.lean` | `tderiv`, `lieDeriv`, `flowQuery` | `flow_cert_sound` / `_strict` / `_superlevel` | `DI_nonstrict_domain` / `DI_strict` / `DI_nonstrict_superlevel` |
| **2. Non-connection** | `NonConn.lean` | `lieAlong`, `sourceCheck`, `barrierCheck` | `nonconn_sound` | dL-lean `DI_strict` (Nagumo barrier) |
| **3. Cover / Theorem 3** | `Cover.lean`, `Cover/Encoding.lean` | `Covered`, `RightReach`, `cover_sound` | `cover_sound`, `theorem3_encoded` | flow + nonconn + dL-rel `encoding_correct` |
| **4. Transition-faithful ∀∃** | `JointBridge.lean` … `BridgeFinish.lean` | `R_real`, the 5-unit bridge | **`theorem3_faithful`** | `faModal_LOCK` + `faModal_to_faShape` + `encoding_correct` |
| **5. End-to-end seam** | `BridgeDischarge.lean` | discharge `hstep` from `cert.segPres` | **`decideCovered_implies_theorem3_faithful`** | `check_sound` + `cert.segPres` + Stage-4 |
| **6. Runner** | `Parse.lean`, `Run.lean`, `Main.lean` | parser + Z3-driven cover | — (trusted IO) | uses the verified queries |

The load-bearing new proof is **`tderiv_correct`**: the syntactic partial derivative of a
term denotes its analytic partial derivative (`HasDerivAt`, by induction on `Term`,
product rule ↦ `HasDerivAt.mul`). It is what connects the computed Lie derivative to
dL-lean's semantic `Lie`, and thereby to the differential-invariant theorems `DI`.

**`cover_sound`** is the paper's Theorem 3 (`ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`): by induction
on the assembled right response, each segment preserves the invariant (`flow_cert_sound`,
a time-unbounded `BoxLe`), a jump cannot follow a pruned edge (`nonconn_sound`), and the
budget strictly decreases each step (`cover_budget_decreases` — the mechanized rejection
of budget-neutral cycles, the load-bearing finiteness argument).

## Lean files → paper results

Every source file, its job, the paper result it mechanizes, and the imported theorem it rests on.

| File | Purpose | Paper result | Rests on |
|---|---|---|---|
| `FlowCert.lean` | `tderiv`/`lieDeriv`/`flowQuery` + `flow_cert_sound`/`_strict` | per-segment sync (Lie) obligation | dL-lean `DI_nonstrict_domain`, `DI_strict` |
| `DISuperlevel.lean` | `flow_cert_sound_superlevel` | marginal `ġ=0`-on-boundary energy/contraction class | dL-lean `DI_nonstrict_superlevel` (no subtangency) |
| `NonConn.lean` | `sourceCheck`/`barrierCheck` + `nonconn_sound` | Guard-Boundary-Crossing / edge pruning | dL-lean `DI_strict` (Nagumo barrier) |
| `Cover.lean` | `Covered` (Def. 4), `RightReach`, **`cover_sound`** | **Theorem 3** `ϕ_inv → [|(L*,R*)⟩⟩ϕ_inv` | flow + nonconn certs |
| `Cover/Encoding.lean` | `theorem3_encoded`, `rvalid_of_encoded_unsat` | global ∀∃ validity from Z3 UNSAT | dL-rel `encoding_correct` (**Theorem 2**) |
| `Cover/Coexec.lean` | `CoexecInvThroughout`, `cover_sound_throughout` | cover ⟹ co-execution invariant throughout | `cover_sound` |
| `Checker.lean` | `decideCovered`, **`check_sound`** | `CERTIFIED` ⟹ the ∀∃-throughout invariant | `cover_sound_throughout` |
| `CSFBridge.lean` | `faModal_ODE_G'` | domain-restricted ∀∃-ODE base rule | dL-caltiming `faModal_ODE_G` |
| `Reify.lean` | `segment_faModal`, `segment_relational` | one cover segment ⟹ a CSF ∀∃-ODE guarantee | `faModal_ODE_G'` |
| `Reification.lean` | mode-list ⟹ choice/star programs | assemble `(L*, R*)` from the parsed automata | `faModal` choice/seq rules |
| `MultiSeg.lean` | `multiseg_het`, `hstep_multiseg_het` | B>1 multi-segment mode-switching witness | dL-caltiming `faModal_MULTI`, `plantT` |
| `ClockReduce.lean` | `clockReduce` | the timing clock is an eliminable proof device | dL-lean `sem`, `Term.coincidence` |
| `EncodingBridge.lean` | `faModal_to_faShape`, `relational_loop` | CSF `faModal` ⟹ NFM'25 `faShape` = `[|(L,R)⟩⟩ψ` | dL-rel `sat_encode_faShape`, `encoding_correct` |
| `PicardBridge.lean` | the `hExist` witness (existence + invariance + chaining) | discharges the ∀∃ duration-existence side-condition | Mathlib `IsPicardLindelof`; dL-lean `sem_ode_iff_integralCurve` |
| `HExistDischarge.lean` | `hExist_from_rover`/`_cubic` | thread the witness into `segment_faModal` (masking seam) | `PicardBridge`, `Reify` |
| `ToolLevel.lean` | `certified_relational`, `pair_faModal` | tool-level (**flat** `R*`): a Z3 verdict ⟹ a valid ∀∃ modality over the flat choice-star | Encoding + Reify + `z3_unsat_sound` |
| `JointBridge.lean` | `rightAutomatonBody`, `R_real`, the transition witness (`rightReach_is_R_real_run`), `psi_ignores_mv` | the **transition-faithful** right automaton: `R_real = star(rightAutomatonBody)` jumps only along *declared* edges | dL-lean `Program.sem`/`coincidence` |
| `OdeProject.lean` | `ode_project_right` | decouple the joint ODE onto the right block (freeze `Lv`) — `RightAutonomous` | dL-lean `Term.coincidence` |
| `RightReachProject.lean` | `rightReach_project` | run-level projection of a joint co-execution onto the right automaton | `ode_project_right`, `Formula.coincidence` |
| `BridgeUnit1.lean` | `diamond_right_wrap`, `hstep_single`, `mvValid`/`EdgeTargetsValid` | wrap a bare right-flow segment into one `rightAutomatonBody` transition; carry mode-validity | `bigChoiceP`, `Formula.coincidence` |
| `BridgeUnit2.lean` | `hstep_assembled` | assemble per-left-mode wraps into the loop step (`faModal_bigChoiceL`, mode dispatched from `mvValid`) | dL-caltiming `faModal_bigChoiceL` |
| `BridgeUnit3.lean` | `relational_loop_faithful` | close the `faModal_LOCK` loop over `R_real` and lift to bi-state `faShape` | `faModal_LOCK`, `faModal_to_faShape` |
| `BridgeFinish.lean` | **`theorem3_faithful`**, `mvValidR` | **Theorem 3 over the *real* automaton**, `rvalid` form (mode-validity in `ϕ_inv`) | units 1-4 + `exists_bridge` + `encoding_correct` |
| `BridgeDischarge.lean` | **`decideCovered_implies_theorem3_faithful`**, `hpair_from_cover`, `rvalid_from_cert` | **single-flow end-to-end**: `decideCovered = true ⟹` the ∀∃ over `R_real` (`hstep` discharged from `cert.segPres`, no assumed Z3) | `check_sound` + `cert.segPres` + `theorem3_faithful` |
| `BridgeReposition.lean` | GAP 1 core: `faModalB`/`faModal_ODE_G'_bounded` (bounded coupling), `plantT_split_iter` (fixed-cut tiling), `faModalB_clockedSeg_iff` (clock bridge), `clockLift_collapse`, `hstep_single_multi`/`hstep_assembled_multi` (mv-lift + star hstep), reposition step-lemmas (A)/(B), `faithful_rights_bridge` | **mechanization infrastructure** (budget-fixed multi-flow coupling; ⊤-model/clock, no direct paper analog) — one left residence, right switching modes mid-residence, coupled per fixed-`dt` segment | dL-caltiming `plantT`/`plantT_split`; `segment_faModal`; `ClockReduce` |
| `RepositionFinish.lean` | `theorem3_faithful_multi` (star-right loop via `relational_loop_multi`), `theorem3_faithful_multi_of_emit` | the reposition-inclusive multi Theorem 3 (`rvalid`), modulo the cover emit | dL-caltiming `faModal_MULTI` (`relational_loop_multi`) |
| `RepositionDischarge.lean` | GAP 1 discharge: `boxLe_clock_lift`/`sem_ode_perm` (clock-lift the cert box), `hExist_clocked_of_HExistSeg`, `segment_faModalB_from_cert`, `multi_faModal_from_couplings`, `Hmulti_from_cover`/`_dyn`, `dynreposition_faModalB_from_cert` | **mechanization infrastructure** — assemble the emitted Z3 certs + cover topology into the per-residence multi-flow `faModal`, flow from `cert.segPres`, dynamic reposition from `cert.repoDynPres` | `segment_faModal`; `clockReduce`; `cert.segPres`/`repoDynPres` |
| `RepositionEndToEnd.lean` | `decideCovered_implies_theorem3_faithful_multi` | GAP 1 end-to-end (genuine multi-flow, per left mode): `decideCovered`/`cert ⟹ Theorem 3` | `RepositionFinish` + `RepositionDischarge` + `check_sound` |
| `GapTwo.lean` | **`theorem3_faithful_family`**, `FlowModeData` (per-mode `Gj`/`cert`) | **GAP 2**: the whole left automaton — `faModal_bigChoiceL` over per-left-mode covers, `mv` carrying the sync | dL-caltiming `faModal_bigChoiceL`; GAP 1 |
| `GapThreeFoundation.lean` | GAP 3 Task 1: `HybridMode`/`HybridAut`, `leftEncode`/`rightEncode` (`⟦·⟧`), `isLeftAut`/`isRightAut`, `graphOf_Gr`/`graphOf_Gj` | **mechanization infrastructure** — the hybrid-program representation and the `graphOf` construction (ties the graph to `L,R`'s dL semantics; no direct paper analog) | `rightBlock`/`jointSys`/`R_real` |
| `GapThreeTask2.lean` | **`RightProjAlign_from_graphOf`** | **GAP 3**: the graph↔program alignment **derived** from `graphOf` (assumed → derived), leaving only the CSF framework side-conditions | `graphOf` (Task 1) |
| `GapThreeTask3.lean` | **`tooling_sound`**, `graphOfFlowMode` | **GAP 3 — the tooling-soundness theorem**: cover of the *actual* `L, R`, modality over `⟦L⟧ >> ⟦R⟧` | `theorem3_faithful_family` + `RightProjAlign_from_graphOf` |
| `Oracle.lean` | `z3_unsat_sound` (the one axiom) + `flow_certified` | the trusted SMT leaf | — (axiom) |
| `Smt.lean` / `Z3.lean` / `Parse.lean` / `Run.lean` / `Main.lean` | computable IR + SMT printer, Z3 session, parser, runner, `relcert` exe | trusted IO shell | uses the verified queries |

## The main soundness result — the cover (Theorem 3)

The whole tool exists to discharge one theorem. Here it is, verbatim (`Cover.lean`):

```lean
theorem cover_sound (G : SearchGraph V) (g : Term V) (cert : CoverCert G g) :
    ∀ cfg ν ω, Covered G cfg → RightReach G cfg ν ω → InvHolds g ν → InvHolds g ω
```

**In words.** Fix a relational invariant component `g ≤ 0` (`InvHolds g`). `Covered G cfg` is the
paper's **Definition 4** — a purely combinatorial fact about the mode graph `G`: from configuration
`cfg = (right mode q, budget B)`, either the budget is closed in this residence (`base`), or **every
retained successor** covers the decremented budget (`step`). `RightReach G cfg ν ω` is the actual
∀∃ **right response**: starting at `ν`, the right system stays put, flows within a mode (time-unbounded —
the flow certificate is a *forward* invariant, not a bounded check), or jumps along a declared successor
whose guard the evolved state enables. `cover_sound` says: **if the graph is covered and the invariant
holds at the start `ν`, it holds at every reachable right-response endpoint `ω`.** That is exactly the
paper's Theorem 3 conclusion — *for every left execution there exists an admissible right response that
keeps the relational invariant within tolerance, throughout*.

The proof is an induction on `RightReach`: the `evolve` case is discharged by `cert.segPres` (the
per-segment flow certificate `flow_cert_sound`, itself citing dL-lean's `DI`); the `jump` case uses that
the jump's budget gate `m.weight < B` matches `Covered`'s `step`, so the target config is still covered,
and that a pruned edge (via `nonconn_sound`) is never taken. **Budget strictly decreases each residence**
(`cover_budget_decreases`) — the finiteness argument that rejects budget-neutral cycles, the reason the
star `(L*, R*)` terminates.

**From the local theorem to the global ∀∃ claim — the encoding.** `cover_sound` is a statement about
one host-dL invariant `g` along right responses. The paper's actual guarantee is a **relational
(bi-state)** formula `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`, a sentence of dL-rel about *pairs* of states. Two
mechanized bridges connect them:

1. `faModal_to_faShape` (`EncodingBridge.lean`) lifts the CSF endpoint modality `faModal` (what a
   covered segment yields) to dL-rel's **`faShape α β ψ = [|(α,β)⟩⟩ψ`** — the NFM'25 ∀∃ relational
   modality — via the proven `sat_encode_faShape` (with the identity renaming `ρ = id`, since the joint
   system already binds disjoint `Side.L`/`Side.R` coordinates).
2. `theorem3_encoded` (`Cover/Encoding.lean`) closes the loop to Z3: a **single `unsat`** of the encoded
   negation `encode ρ (¬ theorem3Form L R ϕ_inv)` implies `RFormula.rvalid (theorem3Form …)` — the
   bi-state validity of the global claim — by dL-rel's **`encoding_correct` (Theorem 2)**, which states
   that bi-state truth of a relational formula equals host-dL truth of its encoding at a bridged join
   state. `theorem3_encoded` proves `rvalid` for the **flat** `theorem3Form` from a single Z3 UNSAT — a
   valid but weaker over-approximation. The **transition-faithful** `CERTIFIED ⟹ rvalid` (real automaton,
   `hstep` discharged from the cover certificate) is `decideCovered_implies_theorem3_faithful`, and it
   and its lifts — `theorem3_faithful_multi_reposition` (genuine multi-flow + reposition),
   `theorem3_faithful_family` (all left modes), and `tooling_sound` (a cover of the actual `L, R`). See
   *The end-to-end theorem, in depth* above.

**Where dL-rel does the load-bearing work.** dL-rel is not a convenience import; it is what makes the
∀∃ fragment expressible and the encoding sound. `faShape`/`encode` were built for exactly this modality,
and `encoding_correct` is the one theorem that turns "Z3 said `unsat`" into "the relational sentence is
valid." The single trusted assumption remains `z3_unsat_sound`; the bridge itself is a proven dL-rel
theorem.

## The transition-faithful ∀∃ — `theorem3_faithful` (`BridgeFinish.lean`)

The assembly above (`certified_relational`, `ToolLevel.lean`) proves a ∀∃ modality whose **right**
program is the **flat** choice-star `(⨆ right modes)*` — *any* sequence of right modes, in any order.
Because the ∃-right quantifies over runs of that flat program, it is an **over-approximation of the real
reasoning automaton**: it is *easier* to satisfy than "there exists a run **that follows the automaton's
declared transitions**." So the flat statement is *valid but weaker than intended* — the paper's Theorem 3
is about the ∃ right response of the **actual** automaton, jumping only along declared edges.

`BridgeFinish.theorem3_faithful` closes that gap. It proves the ∀∃ modality over the **transition-faithful**
right automaton

```
R_real G mv = star (rightAutomatonBody G mv)
```

where `rightAutomatonBody` is `⨆_q (test(mode = q) ; ode(mode q) ; ⨆_{e ∈ edgesFrom q} (test e.guard ; mv := e.tgt))`
— a mode variable `mv` names the current mode, and a jump is possible **only** along a declared edge
`e ∈ edgesFrom q`. The right-response witness (`JointBridge.rightReach_is_R_real_run`) shows every
`RightReach` co-execution IS such a run, so `R_real` neither adds nor drops transitions.

The proof is a five-unit assembly (each banked sorry-free, axioms `[propext, Classical.choice, Quot.sound]`):

| Unit | File | Lemma | Job |
|---|---|---|---|
| projection | `OdeProject`, `RightReachProject` | `ode_project_right`, `rightReach_project` | project the joint co-execution onto the right block (`RightAutonomous`, freeze `Lv`) |
| 1 | `BridgeUnit1` | `diamond_right_wrap`, `hstep_single` | one bare right-flow segment ⟹ one `rightAutomatonBody` transition |
| 2 | `BridgeUnit2` | `hstep_assembled` | ∀ left mode (`faModal_bigChoiceL`), right mode **dispatched from the state's `mv`** |
| 3+4 | `BridgeUnit3` | `relational_loop_faithful` | `faModal_LOCK` loop over `R_real` + `faModal_to_faShape` lift |
| 5 | `BridgeFinish` | **`theorem3_faithful`** | `rvalid` lift over every bi-state (`exists_bridge` canonical join) |
| discharge | `BridgeDischarge` | **`decideCovered_implies_theorem3_faithful`** | discharge `hstep` from `cert.segPres` (no assumed Z3); the two islands in one signature |

**The end-to-end theorem — the two islands in one signature (`BridgeDischarge.lean`).** Units 1–5 leave
`theorem3_faithful` taking the per-iteration step `hstep` as a *hypothesis*; on its own that is a proven
Island B (`hstep ⟹ rvalid`), not yet connected to the checker's Island A (`decideCovered ⟹`
`CoexecInvThroughout`, `check_sound`). `decideCovered_implies_theorem3_faithful` closes that seam —
`hstep` is **discharged from `cert`** (`hpair_from_cover`: each per-pair `faModal` comes from
`cert.segPres` — the cover certificate the checker validates on `Gj` — carried to the R-projected mode by
the *structural* `RightProjAlign`, then decoupled by `segment_faModal`). **There is no `z3solve = unsat`
hypothesis**; the flow certificate is `cert`, and `cert` is load-bearing (delete it → no `faModal`):

```
decideCovered Gj fuel cfg = true  ∧  cert : CoverCert Gj g
   (+ RightProjAlign Gj Gr — structural, no Z3 — hExist, disjointness, Bridges)
⟹  rvalid (theorem3Form L_flat R_real (ϕ_inv ∧ ⌊mvValid⌋_R))          -- from cert
    ∧ (∀ ν, InvHolds g ν → CoexecInvThroughout Gj g cfg ν)            -- from decideCovered + cert

#print axioms decideCovered_implies_theorem3_faithful
  = [propext, Classical.choice, Quot.sound]      -- parametric in cert; the Z3 leaf enters at
                                                 -- cert construction (segPres_from_flowCert, +z3_unsat_sound)
```

`decideCovered = true` in the hypotheses, `rvalid(theorem3Form … faithful)` in the conclusion. Three
findings surfaced closing this (reported, not papered over): **(1)** the cover graph `Gj` (modes
`m.sys = jointSys`) and the R_real graph `Gr` (modes `m'.sys = rightBlock`) are **distinct**, linked by
the structural `RightProjAlign` (= `rightReach_project.hmode`) and bridged by `segment_faModal`'s
joint→right decoupling; **(2)** `decideCovered` is **not** load-bearing for `rvalid` — proven by
`rvalid_from_cert`, which discharges the ∀∃ with no `hchk`/`fuel`/`cfg`: the `faModal_LOCK` loop preserves
the invariant over any iteration count, so the modality needs every mode *certified* (`cert.segPres`), not
the cover to *close*. `decideCovered` is load-bearing for the throughput conjunct only. **(3)** you cannot
have both no-`z3solve`-hypothesis and `z3_unsat_sound`-in-axioms — a `Prop` `CoverCert` cannot apply the
axiom (3 axioms); the leaf enters at `cert` construction. The per-pair certificate is also
invariant-**conditional** (`∀ s, invLe g s → faModal …`) — a segment preserves `g ≤ 0`, cannot restore a
violated one. **Scope of this single-flow theorem:** one fixed left mode, all-`jointOK` (flow) modes. The
genuine multi-flow (right switching modes mid-residence), the repositions, and the whole left-mode family
are the GAP 1–3 lifts (`theorem3_faithful_multi_reposition`, `theorem3_faithful_family`, `tooling_sound`)
— see *The end-to-end theorem, in depth*. This section documents the single-flow base case that those
build on.

**The mode-validity precondition — a real soundness finding.** `rvalid` quantifies over **all**
bi-states, including ones whose fresh mode variable `mv` holds an **undeclared** index. A bare relational
invariant `ϕ_inv` never constrains `mv`, so at such a state the automaton's first `test(mode = q)` matches
nothing, the ∃-right can only take the empty run, and a `ϕ_inv`-breaking left move goes unmatched —
`faShape` false while `ϕ_inv` true. **So `rvalid(theorem3Form L_flat R_real ϕ_inv)` with a bare `ϕ_inv` is
false.** The sound statement carries mode-validity in the invariant:

```
rvalid (theorem3Form L_flat R_real (ϕ_inv ∧ ⌊mvValid⌋_R))
```

read: *for initial states where the reasoning automaton is in a declared mode, the finer (left) system
refines the coarser (right) within tolerance.* `mvValid := ⋁_{q < #modes} (mv = q)` is a genuine loop
invariant — entry-valid, preserved by each `mv := e.tgt` (declared target, `EdgeTargetsValid`), and it
`encode`s to itself on the right (`⌊·⌋_R`), so the encoded precondition is exactly the loop invariant
`invLe g ∧ mvValid`. This is a well-formedness assumption on the reference system's initial control state,
not a soundness dodge; it was caught **in the assembly** (the loop step `hstep` is underivable without it)
and resolved by strengthening the invariant, leaving `faModal_LOCK` untouched.

**Two routes, one trust boundary.** The *encoding* route (`theorem3_encoded`, a single Z3 `unsat` of the
negation) and the *transition-faithful assembly* route (`theorem3_faithful`, per-segment certs composed
through `R_real`) are independent soundness arguments; both rest on the same `z3_unsat_sound` leaf and the
same three Lean axioms. `theorem3_faithful` is the one that pins the ∃-right to the **declared** automaton.

### Trust boundary

```
#print axioms cover_sound          -- propext, Classical.choice, Quot.sound
#print axioms nonconn_certified    -- + z3_unsat_sound
#print axioms flow_certified       -- + z3_unsat_sound
```

The pure core depends only on the three standard Lean axioms. The IO-boundary theorems add
exactly one leaf, `z3_unsat_sound` (an `unsat` verdict from the opaque `z3solve` is sound),
isolated in `Oracle.lean`. **No subtangency axiom** — where a boundary-only
non-strict flow check is unsound (dL-lean's `nonstrict_boundary_insufficient`, the `t²`
counterexample), the verified version takes the sound strict route (`DI_strict`).

## Soundness findings

Carried through every stage: a **boundary-only non-strict** check (`ẋ ≤ 0` on `{g=0}`
alone) is unsound without a regular-boundary hypothesis. The tool therefore certifies via
either the domain-wide non-strict route (`DI_nonstrict_domain`) or the strict-boundary
route (`DI_strict`), never the unsound one — declining where only the unsound route would
succeed. Pruning is one-sided: an edge is dropped only on a trusted UNSAT; failing to
prune is safe by default.

Two further findings surfaced building the transition-faithful bridge (both resolved, see the
section above): (1) the **flat `R*` over-approximation** is a *weaker* ∀∃ than the paper's
automaton claim — the ∃-right must follow **declared** transitions, which `theorem3_faithful`
(`R_real`) enforces; (2) `rvalid` over a **bare** relational invariant is **false** at bi-states
whose fresh mode variable is undeclared — the sound statement carries `⌊mvValid⌋_R` in `ϕ_inv`
(the reasoning automaton starts in a declared mode).

## The oracle (for invariant-synthesis search)

Built to be called thousands of times in a synthesis loop. Three **distinct, never-
conflated** outcomes — the honesty boundary a search depends on:

| outcome | meaning | synthesis reads it as |
|---|---|---|
| `CERTIFIED` | the **verified** `decideCovered` accepted the cover (⟹ `check_sound` ⟹ the ∀∃-throughout invariant), every segment discharged by a sound-route UNSAT | a real, sound YES |
| `DECLINED` | all queries definitive `sat`/`unsat`, no cover closes | a real, sound NO |
| `ERROR msg` | any harness/solver/env failure (missing Z3, crash, malformed, `unknown`/timeout, unlowerable) | retry / abort — never learn from it |

An `ERROR` can never masquerade as a verdict: `CERTIFIED` is only ever produced by actual
`unsat`; an inconclusive/failed query surfaces as `ERROR` when a covering route needed it.

**In-process API** (link the pipeline directly — no per-call process spawn):

```lean
open RelCertifier RelCertifier.Oracle
-- one warm, persistent Z3 session serves thousands of calls:
def loop (s : Z3Session) (cands : List PProblem) : IO (List Outcome) :=
  cands.mapM (certify s)          -- certify : Z3Session → PProblem → IO Outcome
```

Hermetic + deterministic: Z3 is a **pinned** absolute path (`RELCERT_Z3`, never
PATH-resolved), a **persistent** `z3 -in` process (warm), with `(reset)` + a per-query
`:timeout` + a machine-independent `:rlimit` + an `(echo)` **sentinel** that keeps the pipe
in sync so the same query always gives the same verdict. The cover DFS is memoized so a
large time-stretch can't blow up the pure search. **Warm per-call: mean 49 ms, median
26 ms, p90 101 ms, max 199 ms** (all 47 in ~2–3 s) — dominated by the Z3 solve. Every call
terminates (query / SMT-size / wall / rlimit bounds, all deterministic).

## Running it

```sh
lake build                      # verified library + `relcert` + `relcert-test`
lake exe relcert <input.txt> …  # oracle over each file on one warm session (3-way verdict + ms)
lake exe relcert                # no args: the Stage-1 flow-certificate demo
BENCH_PATHS=<name-tab-path-file> lake exe relcert-test   # trusted-layer test suite
```

## The ∀∃ witness — `hExist` discharged (`PicardBridge.lean`)

The paper's ∀∃ relational modality `[|(L*,R*)⟩⟩ψ` carries a **duration-existence
side-condition** (`hExist`, from dL-caltiming): for every left run there must **exist** a
right run of the matching duration, staying in the right evolution domain. This is the
existential witness of the ∀∃ — carrying it makes the result a ∀-conditional, not a ∀∃.
`PicardBridge.lean` **discharges it by explicit witness construction**, standard three
axioms throughout, **no new axiom, no subtangency, no clock, no `sem`-gating**.

- **Existence** (Mathlib Picard → dL-lean `sem`): `term_contDiff`/`odeField_contDiff`
  (fields are `ContDiff`), `odeField_lipschitzOnWith` (Lipschitz-on-compact),
  `sem_of_integralCurveOn` (the reification seam: a Mathlib integral curve **is** a dL-lean
  `sem` run, via the proven `sem_ode_iff_integralCurve`). Three routes, K/L **proven**:
  `picard_isPL_of` (global-Lipschitz, affine fields), `uniform_local_existence_on_compact`
  + `box_compact` (compactness-subcover), `picard_isPL_of_local` + the s-independence
  establishment (`odeField_sindep` → compact cross-section → uniform K/L) for the nonlinear
  (cubic, degree-3 `v·ψ²`) fields.
- **Invariance** — un-gated raw-curve positive invariance (the piece dL-lean leaves
  `sem`-gated): `strict_invariance_raw` (first-exit, strict), `nonstrict_antitone_raw`,
  `growth_bound_raw`/`_lower`, `asymptotic_invariance_raw` (general-box asymptotic, covers
  attitude `ψ'=−ψ`), and the coupled faces `lie_two_coord` + `coupled_eigen_invariance`
  (eigencoord decoupling — **every coupled subsystem has real eigenvalues, no Lyapunov**) +
  `driven_bound_raw` (defective/critically-damped companions, via `(v−C)e^{λt}` antitone).
- **Chaining** to the full parser duration: `sem_ode_glue`, `RunFor` + algebra, `chainN`
  (uniform step ⟹ finite steps cover `[0,Tᵢ]`).
- **Packaging + relational wiring**: `RunFor_unpack` → the witness shape;
  `hExist_from_rover`/`hExist_from_cubic` thread it into `segment_faModal` through the
  **field-independent cross-side masking seam** (`Rv_not_mem_leftBlock_bound`, `Side.R≠Side.L`:
  the left run freezes the right's coords ⟹ right starts in-slab).

`hsmax_of_left_duration` closes the timing coupling (left domain bounds duration →
`ν si + v_max·s ≤ S_max`) as `left_duration_bound` (analytic, proven) + a Z3-checkable
arithmetic inequality.

## Benchmark suite — results

The full **47**-benchmark suite (under `benchmarks/suite/`, each a directory with `input.txt`) run on
the trusted method (Z3 UNSAT-of-negation), reproduced by
`lake exe relcert benchmarks/suite/*/input.txt`:

| | count | meaning |
|---|---|---|
| **CERTIFIED** | **46/47** | verified `decideCovered` accepted the cover; every segment a sound-route Z3 `unsat` |
| **ERROR** | **1** (`shield_unreachable`) | inconclusive Z3 verdict on a candidate route — surfaced as ERROR, never a false verdict |

The one non-CERTIFIED entry is an **honest** boundary, not an invariant bug and never a
false-certify (`CERTIFIED` is only ever produced by an actual `unsat`):

- **`shield_unreachable` — ERROR (inconclusive).** A candidate route returned a non-definitive Z3
  verdict (`unknown`/timeout class); the tool refuses to guess and reports ERROR rather than certify.

Getting to 46/47 was **spec/cover work, never a soundness loosening**: fuel/λ-grid bumps (reported, not
silently raised), Hold-mode reachable-set tightening (`arm`/`plant`), coupled conserved-lead invariants
(`endurance`/`rover_terrain`/`orderlift`, including the strengthened `endurance_orderlift_2to3` folded in
from the former `benchmarks/restated/`), position-only invariants (`rover3_M1`), single-mode attitude
keys (`story`), and the watertank fill-drift redesign — each reverted-and-retested, each a sound spec fix.

Requires Lean 4 (`leanprover/lean4:v4.31.0`, pinned) and a pinned Z3 (`RELCERT_Z3` or a
standard absolute path). `dL-rel` is fetched from GitHub at tag `v0.1.0-NFM25` (transitively
provides dL-lean `v0.1.0-DI` and the encoding bridge) — `lake build` resolves it, no sibling
checkout. Env: `RELCERT_Z3_TIMEOUT` (ms, default 10000).

## Soundness of `CERTIFIED` — the certified-checker architecture

`CERTIFIED` is **backed by proof**, not by the search. The untrusted cover DFS does not decide
the verdict: the runner builds the abstract `SearchGraph` from the parsed model and gates
`CERTIFIED` on the **verified computable `decideCovered`** — a transcription of the paper's
Definition 4 (`base`: `B ≤ w(mR)` → budget closed; `step`: every retained successor covers at
`B−w`). `decideCovered = true ⟹ Covered ⟹`, with the evolution-domain flow certs as `CoverCert`,
the ∀∃-throughout invariant (`check_sound`, citing `cover_sound`). A search/runner bug can only
make it **reject** — never a false `CERTIFIED`. Residual TCB: the parser and the single Z3
`unsat` leaf.

**Soundness fixes caught while validating (real bugs, `Lean-object ≠ paper-object` class):**
- **Guard-narrowing**: an earlier version conjoined the mode **guard** into the flow-certificate
  domain, narrowing the certificate to a sliver the real flow leaves — a Return mode entered at
  `θ≥0.7` flows to `θ<0.7`, so the query was *vacuously* UNSAT (falsely certified) while
  `ġ=0.7>0` on the real flow. Fixed to the **evolution domain only** (holds throughout the
  segment); the affected benchmarks correctly moved to DECLINED. Only `Run.lean` changed.
- **`Covered` base case** (Definition 4): single-segment covers could not terminate, spuriously
  forcing closed-leaf certification — corrected by the `base`/`step` split.
- **Two parser bugs**: `dynOf` silently defaulted an unlowerable term to `0` (a wrong field
  could falsely certify) — now propagates to ERROR; the tokenizer split `-` inside negative
  literals — now `mergeSigns` re-glues signed literals. Neither had produced a wrong CERTIFIED.

The sound routes: strict / domain / **superlevel** flow certificates (`DI_nonstrict_superlevel`,
proven from vendored Mathlib — **no subtangency**, closes the marginal `ġ=0`-on-boundary
contraction/energy class, rejects the `t²` pathology). The trusted layer is tested
(`relcert-test`): determinism, outcome-integrity (missing Z3 / unparsed / crash → ERROR),
parser, lowering, Z3-layer verdicts. See the **Benchmark suite** section above for the current
46/47 trusted-method tally and the honest ERROR breakdown.

## Layout

```
RelCertifier/
  FlowCert.lean       Stage 1 — tderiv/lieDeriv + flow certificate soundness
  NonConn.lean        Stage 2 — Nagumo non-connection barrier
  Cover.lean          Stage 3 — cover relation, finiteness, cover_sound (Theorem 3)
  Cover/Encoding.lean Stage 3 — global ∀∃ encoding bridge (encoding_correct)
  JointBridge.lean    Stage 4 — R_real (transition-faithful automaton) + right-response witness
  OdeProject.lean     Stage 4 — joint-ODE projection onto the right block
  RightReachProject.lean Stage 4 — run-level projection of the co-execution
  BridgeUnit1/2/3.lean Stage 4 — segment-wrap, loop-step assembly, faModal_LOCK close
  BridgeFinish.lean   Stage 4 — theorem3_faithful (∀∃ over R_real, rvalid form)
  BridgeDischarge.lean Stage 5 — decideCovered_implies_theorem3_faithful (discharge hstep, end-to-end)
  Smt.lean            computable IR + SMT-LIB printer (pinned to lieDeriv by bridge lemmas)
  Oracle.lean         the single trusted leaf (z3_unsat_sound) + IO-boundary theorems
  Parse.lean          input.txt parser (trusted IO)
  Run.lean            end-to-end cover runner
  PicardBridge.lean   the ∀∃ witness — hExist discharged (existence + invariance + chaining)
  HExistDischarge.lean cross-side masking seam — hExist into segment_faModal
Main.lean             `relcert` executable
ARCHITECTURE.md       certified-checker architecture + the finding that reshaped it
```
