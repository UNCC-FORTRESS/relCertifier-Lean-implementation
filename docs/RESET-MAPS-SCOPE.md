# Scope: supporting reset maps in the models

Status: SCOPING ONLY (2026-07-19, against main = d7a6d17). Nothing here is implemented
and nothing is scheduled. This document says what a reset map would touch, what is
free, what is genuinely hard, which soundness gates are mandatory, and what it would
cost. Companion reading: README ("The end-to-end guarantee, intuitively"),
`docs/FIXPOINT-DESIGN.md` (interacts with §7 below).

---

## 1. What a reset map is here, and what it buys

Today a mode switch changes **only the mode**: the state is continuous across the
jump. In `Proofs/Encoding/JointBridge.lean:34`,

```lean
def modeStep (G : SearchGraph V) (mv : V) (q : ℕ) (m : RMode V) : Program V :=
  Program.seq (Program.test (modeIs mv q))
    (Program.seq (Program.ode m.sys m.dom)
      (bigChoiceP ((G.edgesFrom q).map (fun e =>
        Program.seq (Program.test e.guard) (Program.assign mv (Term.const (e.tgt : ℝ)))))))
```

the edge does `?guard; mv := tgt` — the only assignment is to the mode variable.

**The model of interest** (user-supplied, 2026-07-19) places a **per-target-mode**
reset immediately before the flow:

```
( ⋃_{m ∈ modes}  ?(m ∈ next(mv)) ; ?guard_m(x) ; mv := m ; x := ρ_m(x) ;
                 {x' = f_m(x) & evolC_m} )*
```

Two features of this shape drive everything below. The guard is the **target mode's**,
tested at the **pre-reset** state — so a reset can never enable a transition that was
not already enabled. And the reset sits **immediately before the flow** — so every mode
residence begins at a reset image.

**What it buys the modeling story.** Resets are how one writes: controller
re-initialization at a switch, clock/timer resets, impacts and bouncing, quantized or
snapped actuator settings, and — the one that matters most for this project's attack
narrative — a sensor **spoof at switch time** rather than a continuous drift. The
current watertank attack is a continuous offset plus a fill-rate drift; with resets the
suite could carry attacks that *set* a value discretely at a mode boundary, which is a
strictly different (and commonly modeled) threat shape. No benchmark in the suite uses
resets today, so the feature is purely additive.

---

## 2. What is already free (four genuine head starts)

1. **The object language already has assignments.** `Program.assign : V → Term V →
   Program V` (`dL-lean/DLLean/Syntax.lean:101`), with its semantics and substitution
   theory already in the imported dL development. No new program constructor, no new
   semantic clause, no new dynamic-logic axiom.

2. **The top-level theorem statement needs *zero* change.** `theorem3Form` takes
   arbitrary programs:
   ```lean
   def theorem3Form (L R : Program V) (ϕinv : RFormula V) : RFormula V
   ```
   (`Checker/Cover/Encoding.lean:51`). A reset-carrying automaton is just a different
   `R`. Every benchmark theorem keeps its exact shape, and the encoding soundness
   (`theorem3_encoded`, `encoding_correct`) is untouched.

3. **The decision procedure is state-free, so it does not change.** `decideCovered`
   (`Checker/Checker.lean:48`) walks `Config = ⟨q, B, σ⟩` — mode index, budget, source
   setting — consulting only per-mode Boolean flags. It never mentions a state. So the
   combinatorial cover search, its soundness theorem `decideCovered_sound`, and every
   `by decide` replay in the instances keep working verbatim.

4. **The printer — trust base — should not need to change.** A reset obligation is
   "invariant survives the substitution": `inv(x) ∧ guard(x) → inv(ρ(x))`. That is a
   substitution performed at the IR level, printed with the existing term grammar. No
   new SMT construct. (Verify early in any build: this is an assumption, and keeping
   `toScript` untouched is worth real money since it is one of the five trusted items.)

---

## 3. What changes, layer by layer

### 3.1 Surface syntax, IR, and the tool (mechanical, but touches the strict parser)

- Because `ρ_m` is indexed by the **target mode**, not the edge, `PMode`
  (`Trusted/Parse.lean:54`) simply gains a `reset : List (String × PExpr)` field. No
  `PEdge` restructuring, and the obligation count is |Q|, not |E| — materially smaller
  than an edge-indexed design. This changes `PProblem`'s derived `DecidableEq`, which is
  exactly what the drift check uses, so drift checking extends for free.
- The guard convention already matches: the mechanization indexes guards by target mode
  (`hostGuard` reads `m.guard`, `CoverInstance.lean:39`; built edges carry `Formula.tt`
  and the guard is threaded as `Gd : ℕ → Formula`, consumed as `sat (Gd e.tgt) μ`). No
  change needed.
- Parser: a concrete syntax (e.g. `next = [Mid { x := x - 3 }, Low]`), held to the
  standing **reject-never-weaken** discipline — an unparseable or ill-formed reset must
  error, never silently degrade to the identity.
- Lowering: a `resetOf : vars → n → Side → PMode → Option (List (Fin n × ITerm n))`,
  mirroring the existing `dynOf` (`Trusted/Run.lean:109`). Same shape, same failure
  mode.
- Emission doors: `--emit-ir` must round-trip resets; `--emit-cover` must record which
  edges a cover actually uses (it effectively does already).
- Search (`coverMode`, `Trusted/OracleAPI.lean:428`): two new probe kinds per mode —
  reset-preserves-invariant, and reset-lands-in-target-domain (§3.4).

### 3.2 Checker data (small, but upstream)

- The reset rides the **target mode** (`RMode`), not `REdge` — matching `ρ_m`.
- `RMode` unchanged; `decideCovered` unchanged (§2.3).
- The reset's proof obligation should live in the **certificate** (`CoverCertMC`), not
  in the decision procedure — a new `jumpPresC` field discharged per target mode. This
  keeps the decidable combinatorial and avoids adding a flag that every `decide` replay
  would have to re-establish.
- Cost note: `Checker/Cover.lean` is upstream of the whole proof layer, so this is a
  full-world rebuild — one, batched (see §8).

### 3.3 The proof layer — where the actual work is

**Loop shape.** The model of interest is *jump-then-flow*; the mechanization's
`modeStep` is *flow-then-jump*. Over a whole run these produce the same alternation of
segments and discrete events, so this is a boundary/initialization question rather than
a restructure — but it lands on the admissible-starts conditioning (R2), which was
already delicate, and it is what makes the repeated-self-reset obligation (§4.4)
visible.

**The load-bearing assumption to break.** `RightReachG.jump`
(`Proofs/Soundness/CutCover.lean:136`):

```lean
| jump {q B σ ν μ ω} (m : RMode (Var n)) … (e : REdge (Var n)) … :
    Program.sem (Program.ode m.sys m.dom) ν μ →
    Formula.sat e.guard μ →
    Formula.sat (Gd e.tgt) μ →
    RightReachG G Gd ⟨e.tgt, B - m.weight, SrcSetting.postJ⟩ μ ω → …
```

The same `μ` flows into the continuation — *that is* "state is continuous at a switch",
stated once and consumed everywhere. With resets it becomes `… → μ' = applyReset e μ →
RightReachG … μ' ω`. Note this hits **five constructors, not one**: `jump`,
`repositionPre`, `repositionPost`, `repositionDynPre`, `repositionDynPost` — every
reposition also traverses a declared edge, so every reposition also fires its reset.

**The preservation induction.** `pres_multi_cut` (`Proofs/Soundness/CutCover.lean:274`)
currently closes each jump case by applying the induction hypothesis at the *same*
state, with cut atoms re-entered from the guard (`cert.entryR _ _ hGd`). Three new
obligations appear:

- *invariant across the reset*: `InvAllHolds gs μ → sat e.guard μ → InvAllHolds gs μ'`
  — a new certificate field backed by a new Z3 query;
- *right cut atoms re-established post-reset*: today's baton re-enters right atoms at
  the switch using the guard at `μ`; now they must hold at `μ'`. If a reset moves the
  state out of the cut region, the cut channel breaks — and the cut channel is exactly
  what the 13 cut-reliant benchmarks depend on;
- *left cut atoms survive a right reset*: true by variable disjointness, but it needs
  an explicit coincidence lemma (cheap, new).

**Witness extraction.** `emit_from_covered` (R1) builds the ∃-witness run from the
`Covered` derivation; each jump's witness must now include the assignment steps in the
right order (`?guard; x := ρ(x); mv := tgt`). Moderate, mechanical, but it is the
bridge between the combinatorial certificate and the program semantics, so it must be
got exactly right.

**Freshness side conditions.** `MVFresh` (`Proofs/Encoding/JointBridge.lean:52`) and
the clock-variable freshness conditions must extend: reset targets are state variables
and must be disjoint from `mv` and the clock `tg`. This is the family of side
conditions that produced the archived `MvFrozen` vacuity finding
(`Archive/ProbeMvHd.lean`) — a disjointness hypothesis that was provably *false*, making
instances vacuous. Any reset work must re-run that check deliberately.

### 3.4 Existence and viability (a real, not clerical, obligation)

`HExistSegB` (`Proofs/Flow/WellFormedFlow.lean:89`) starts the right flow at the left
segment's endpoint: `∃ ΦR, ΦR 0 = ΦL s ∧ …`. After a reset the right flow restarts at
the **reset image**, not the pre-jump point. Two consequences:

- *landing*: `sat domR (ρ μ)` — the reset must land inside the target mode's evolution
  domain. New query, easy.
- *re-anchoring, and it is universal*: because the reset sits immediately before the
  flow, **every** mode residence begins at a reset image — not occasionally, always. The
  bounded-viability chain must therefore be re-entered at `ρ_m(x)` on every entry, with
  the anchor budget recomputed at a point the model author chose rather than one the
  dynamics produced. This lands squarely on S3's known weak spot: the tangential case,
  an anchor sitting *on* a face with zero budget. Contract-shaped fields (route a) are
  unaffected; general polynomial fields (route b) pay here, on every entry. This is the
  largest single sharpening relative to an edge-indexed reading of the feature.
- *the landing obligation is a precondition, not a nicety*: the flow runs with domain
  `evolC_m` immediately after the reset, so if `ρ_m(x)` violates that domain the loop
  body is stuck and the ∃-witness dies outright.

### 3.5 Instances, verdicts, generators

- New query shapes ⟹ new pins in `Verdicts/GenericPins.lean` (one lemma per shape, the
  established pattern) plus mirrors, so `--run-verdicts` can re-check reset obligations.
- Generators emit the per-mode reset verdict names; the leaf modularization from X0 means
  per-benchmark regeneration is now cheap.
- `Faithful` (`Checker/Faithful.lean:357`) already compares per-**mode** data
  (`modeCore` per `q`), and `ρ_m` is per-mode — so the fidelity predicate extends along
  its existing grain, one new clause. It is still mandatory: without it the kernel
  identity "the instance IS the benchmark" would not cover the reset data.

---

## 4. The four genuinely hard problems

Everything in §3 except these is plumbing.

1. **The cut baton across resets.** The 13 cut-reliant benchmarks certify *only*
   because guard-derived cut atoms persist and re-enter at switches. A reset can
   invalidate an atom instantly. Either the reset must be shown to preserve each atom
   (a per-edge, per-atom query — combinatorially the largest new query family), or the
   cut lift degrades on reset-carrying edges. Unknown until tried whether the natural
   modeling resets preserve the atoms.

2. **Existence re-anchoring at the reset image** (§3.4). The reset image is an
   adversarially-chosen anchor: nothing stops it from sitting on a growth face. This is
   the S3 tangential case arriving by construction rather than by accident.

3. **Repositions get strictly harder — there is no compensating gain.** An earlier
   draft of this document claimed resets would *help* repositioning by making
   unreachable guards reachable. **That is false**, and the model shape is why: the
   guard is tested *before* the reset (`sat (Gd e.tgt) μ` at the pre-jump state), so a
   reset can never enable a transition that was not already enabled. What actually
   happens is the reverse. Every hop through mode `m` drags the right state through
   `ρ_m`, so a multi-hop reposition chain composes resets —
   `ρ_{m₃}(ρ_{m₂}(ρ_{m₁}(x)))` — and the relational invariant must survive each one.
   Today a reposition is right-state-preserving (a frozen-left flow, or nothing);
   under resets every hop displaces the right state discretely, and long chains can
   drift out of the invariant band. In the shelved fixpoint design this makes `Serve`'s
   hop moves costly rather than free (`docs/FIXPOINT-DESIGN.md` §3.1).

4. **Repeated self-resets on the left.** Every mode in this suite declares itself a
   successor (watertank's `Low` has `next = [Mid, Low]`). Under the jump-then-flow loop
   shape, staying in a mode may be realized as many iterations, each re-applying `ρ_m`.
   For the right system this is harmless — we choose the witness, so we take one long
   flow. For the **left** system, which is ∀-quantified, the proof must tolerate
   arbitrarily many repeated self-resets inside a single window. If `ρ` is not
   idempotent this is a genuine obligation, and an easy one to miss.

---

## 5. Mandatory soundness gates

These are not optional hardening; without them the extension is unsound or vacuous.

- **Cross-side resets must be rejected.** A reset such as `R_x := L_x` reads the other
  system's state and breaks the `Disjoint varsL varsR` premise the entire relational
  encoding rests on. The parser must reject it, mirroring the existing side discipline
  (`namesFree "L_"`, `lowerE_fv_side`). This is the single highest-risk item: it is
  easy to write, looks natural to a modeler, and silently invalidates the encoding.
- **Reset targets must be state variables of their own side** — never `mv`, never the
  clock `tg` (§3.3 freshness, and the archived vacuity lesson).
- **Fidelity must cover resets** (§3.5), else the instance↔file identity no longer
  pins the model actually certified.
- **Identity default stays identity.** Absent resets, every definition must reduce
  *definitionally* to today's, so the 46 existing benchmarks are unaffected and their
  proofs do not merely "still work" but are literally the same proofs.

---

## 6. Scope tiers

| tier | what it admits | difficulty |
|---|---|---|
| **T1 — deterministic, same-side, right-only** | `R_x := ρ_m(R_x)`, polynomial ρ, on R's modes only | the tractable core; all of §3, hard problems 1–4 in their mildest form |
| **T2 — both sides** | L's windows also reset | adds left-window jump handling to the ∀ side; the `windowSeg`/`leftProgs` chain and the frozen-left invariants need review |
| **T3 — nondeterministic / guarded resets** | `x := *` with a post-condition, or reset choice per edge | `Program.assignAny` exists, but the ∃-witness must now *choose*, and the cover certificate becomes a choice structure — a different (larger) design |

Recommendation if pursued: T1 only, with T2 as a follow-on, and T3 explicitly out of
scope until a benchmark demands it. Note T2 is *not* symmetric with T1: left-side
resets are ∀-quantified, so they inherit the repeated-self-reset obligation (§4.4),
which the right side escapes by witness choice.

---

## 7. Interaction with the shelved fixpoint design

The winning-region design (`docs/FIXPOINT-DESIGN.md`, SHELVED) would absorb resets
*more* cleanly than the current derivation route: a reset is one more edge-labelled
move inside the inner `Serve` fixpoint, its obligation is one more per-entry hypothesis
of `winning_region_sound`, and resets *enlarge* reachability (hard problem 3's silver
lining). If both are ever wanted, doing the fixpoint arc first makes the reset arc
smaller; doing resets first means paying the five-constructor `RightReachG` surgery
that the fixpoint route would have replaced anyway. Worth knowing, not worth
reordering on its own.

---

## 8. Cost

**Comparable in size and shape to S2** (the guard-threaded cut lift), which is the
right anchor because it touched the same layers: `RightReachG` constructors, the
preservation induction, certificate fields, per-benchmark verdicts, and a generator.
S2 ran as one focused arc plus a serial heavy-build campaign.

- Active work, T1: the proof layer dominates — the five-constructor surgery and the
  `pres_multi_cut` re-derivation with three new obligations. Parser/lowering/emission
  and the pins are a day's mechanical work by comparison.
- **Rebuilds: one full-world rebuild** (~12 h serial), because `Checker/Cover.lean` and
  `Proofs/Soundness/CutCover.lean` sit upstream of everything. The X0 leaf
  modularization does *not* help here — it decouples *benchmark data*, not the proof
  layer. Batch every reset-related change into that single rebuild ([[rebuild-hygiene]]:
  proof-layer edits are the remaining world-rebuild class, and always were).
- Unknowns that could expand it: hard problem 1 (whether real resets preserve cut
  atoms) and hard problem 2 (anchor-on-face at the reset image). Both are discoverable
  cheaply — see below.

**Cheapest decision-complete probe** (≈ a day, no rebuild): write one reset-carrying
benchmark by hand, run the *existing* tool on the pre-reset and post-reset models as
two separate problems, and check by hand whether (a) the invariant survives the
substitution, (b) the reset image lands strictly inside the target domain, and (c) the
cut atoms survive. That answers hard problems 1 and 2 empirically before any Lean work
starts — the same "run the example first" discipline that corrected the fixpoint
document.

---

## 9. Bottom line

Structurally favorable: the object language, the top-level statement, the decision
procedure, and the printer all survive untouched — which is more than one would expect,
and it means the trust base does not grow. The work concentrates in one place: the
transition relation carries "state is continuous at a switch" as a hard-wired equality
across five constructors, and unpicking that ripples through the preservation
induction, the witness extraction, and the existence anchoring.

Not hard in the sense of "we do not know how"; sized in the sense of "an S2-shaped arc
plus one world rebuild", with two empirical unknowns that a one-day paper probe would
settle before committing.
