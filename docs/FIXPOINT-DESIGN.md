# Design: the winning-region fixpoint — "the automaton refines L" for every benchmark

Status: DESIGN PROPOSAL (2026-07-17). Nothing here is implemented; the current
derivation-style pipeline (cover search → `decideCovered` replay → per-benchmark
assembly) stays the production route until this design lands end-to-end on a pilot.
Companion reading: README ("The end-to-end guarantee, intuitively"), `docs/ROADMAP.md`
(final closure — options 1 and 2 are the problem this design attacks).

---

## 1. The problem this solves

Today every benchmark carries a kernel-checked end-to-end theorem, but the *statement*
comes in two strengths:

- **Throughout/settling form (all 46).** The R-side program inside the theorem is
  already strategy-specialized: the statement itself names which right mode answers
  which left window, with which λ stretch. True, useful — but the object certified is
  a *choreographed slice* of the implementation.

- **Modal form (watertank only).** The R-side program in the statement is the automaton
  itself — `rightAutomatonBody`, all modes, all declared edges, guard-gated switching.
  The statement reads "whatever L does, the automaton can respond"; the strategy exists
  only inside the proof, as the witness. This is the faithful reading of Theorem 3:
  *the deployed automaton, switching logic and all, refines the ideal system.*

Scaling the modal form from 1 benchmark to 46 on the current architecture is expensive
for a structural reason: the cover is a **derivation** — a tree of joint cases and
reposition cases — and the modal proof proceeds by **induction over that derivation**.
So every per-benchmark instantiation re-assembles window chains, hop lemmas, and
envelope bookkeeping by hand (or by a generator that must emit assembly *proofs*, not
just data). Three recorded blockers price this out:

1. **Mode correspondence** (the H5 finding): the cover plan's mode indices must be
   matched to the automaton graph's indices — this alone blocked the rover_drag
   multi-mode pilot.
2. **The hop-lemma limit** (S1 negative finding): the general prefixed-window lemma
   `Hmulti_window_prefixed` has an unsatisfiable side condition for real hop sequences
   (a frozen hop binds every left coordinate); watertank went through on the special
   k = 1 route. Longer reposition chains need new lemmas — open-ended proof work.
3. **Assembly cost**: 36 window theorems for the 13 cut benchmarks took a bespoke
   generator and ~7.5 h of serial heavy builds — and that was for the *weaker* form.

The fixpoint design removes the derivation, and with it all three blockers.

---

## 2. The intuition: refinement is a game, and the certificate is the winning region

Think of refinement as a two-player game played in rounds:

- **L moves**: it presents a window — "I am in mode `l`, evolving under my dynamics
  for up to one clock period."
- **R answers**: from its current mode `q`, it must produce behavior that tracks the
  window within ε — either *flow* (co-evolve its own mode, time-rescaled by λ) or
  first *reposition* (hop through its declared mode graph, guards permitting, with L's
  clock not advancing) and then flow.
- The relational invariant must survive the round, and then L moves again. Forever.

"**The automaton refines L**" means: R has a way to win every round, from every
admissible start, against every L line. That is a ∀∃ over infinite plays.

The classical way to certify such a claim is *not* to exhibit the play, and *not* to
exhibit the search that found the strategy. It is to exhibit the **winning region**:

> **W** = the set of configurations `(l, q)` — L in mode `l`, R in mode `q`, states in
> the invariant — from which R can win the next round *and end up back in W*.

That "…and end up back in W" is the whole trick. W is self-supporting: every position
in it has an answer that leads back into it. Once you are in W, you are in W forever —
by induction on rounds. The game-theoretic name for this is a **simulation relation**,
and simulations are **greatest fixpoints**: W is the largest set that survives the
pruning "delete every position with no good answer."

Three consequences, and they are exactly the three simplifications we want:

- **The certificate is a set, not a tree.** To check W you do not replay any search.
  You check one *local* property per member: "this position has an answer into W."
  Finitely many positions, finitely many checks, each decidable given the Z3 verdicts.

- **The loop invariant of Theorem 3 IS membership in W.** The top-level modal proof
  becomes a single generic coinduction lemma, proven once for all benchmarks:
  *post-fixpoint + admissible start in W ⟹ the ∀∃ holds*. Per-benchmark work reduces
  to a `decide` (the post-fixpoint check) plus named Z3 facts. No assembly.

- **Indices cannot drift.** W lives on `L-modes × R-modes` — the automaton's own
  graph. There is no separate "plan" whose numbering must be corresponded back to the
  automaton (the H5 blocker dissolves structurally: there is nothing to correspond).

---

## 3. The design, precisely

### 3.1 The universe and the step operator

Fix a benchmark: left modes `l ∈ L`, right modes `q ∈ Q`, declared edge relation
`E ⊆ Q × Q` (with guards), relational invariant `ϕ`, stretch range for λ.

- **Positions**: pairs `(l, q)` — finitely many (|L| × |Q|).
- **Answers** available to R at `(l, q)`, for the window `l` presents:
  - **flow(λ)**: the joint piece — `l`'s dynamics vs `q`'s dynamics ×λ, invariant
    preserved throughout the piece. Backed by the *same* per-piece Z3 queries the
    tool prints today (routes A / B / C, cut-narrowed domains, evolve-box faces).
  - **hop(q → q′)**: an edge in `E` whose guard holds at the switch instant
    (guard-at-entry — the folded successor-completeness contract), left clock frozen,
    invariant preserved across the hop (the frozen-left verdicts). Hops chain.
- **Step operator** `F : Set (L × Q) → Set (L × Q)`:

  ```
  (l, q) ∈ F(W)  ⟺  for every L-successor mode l′ of l (including l itself):
                      ∃ hop chain q → … → q* along E, guards entered legally,
                      invariant carried, such that q* has a certified flow answer
                      to l′'s window and (l′, q*) ∈ W.
  ```

  `F` is monotone (bigger W ⟹ easier membership), the lattice is finite, so the
  greatest fixpoint `gfp F` exists and pruning iteration reaches it.

### 3.2 Where ε_R lives: inside R's move, as a tiling

**The short answer: ε_R does not change the fixpoint machinery at all. It changes
what counts as "an answer" inside the membership test.** It is an input parameter of
the game, like the mode graph. The design has three layers, and ε_R touches exactly
one of them:

- **Layer 1 — the pruning loop.** "Delete positions with no answer, repeat." Knows
  nothing about widths. Unchanged by ε_R.

- **Layer 2 — the membership test, per position `(l, q)`.** Asks: can `q` fully
  cover the window `l` presents? Here ε_R enters. The window has left-duration ε_L.
  R answers with pieces; a piece run at stretch λ consumes `ε_R/λ` of left time.
  λ is *R's choice, per piece*, from the range the benchmark file declares — the
  benchmark fixes the range, R picks within it. To cover the window, the piece
  durations must add up to ε_L — a *tiling* `Σᵢ ε_R/λᵢ = ε_L`, hop chains permitted
  at the seams (the multiflow round shape, task H). Whether a tiling exists depends
  on ε_R and the declared λ range — *before any Z3 query is even asked*:
  - **Success:** ε_L = 1, ε_R = 0.4, declared λ ∈ [1, 2] → each piece covers between
    0.2 and 0.4 of left time; the tiling 0.4 + 0.4 + 0.2 = 1 works (λ = 1, 1, 2).
  - **Failure:** ε_L = 1, ε_R = 0.7, declared λ ∈ [1, 1.05] → each piece covers
    `0.7/λ` ∈ [0.667, 0.7]; k pieces total in [k·0.667, k·0.7], so k = 1 reaches at
    most 0.7 < 1 and k = 2 already needs ≥ 1.333 > 1. The reachable sums have a gap
    at 1 — no tiling, whatever λs R picks, *no matter how good the dynamics are*.
  - **The general criterion:** a tiling exists iff
    `ε_L ∈ ⋃ₖ [k·ε_R/λmax, k·ε_R/λmin]`; gaps occur only while consecutive
    intervals fail to overlap, i.e. while `λmax/λmin < (k+1)/k`. Generous λ ranges
    never fail; narrow ranges with ε_R large relative to ε_L can.

  This is precisely the observation that motivates the section: for a fixed L, some
  ε_R designs can match and some cannot — and it surfaces here, in layer 2, as
  "does a tiling exist."

  (Caveat, recorded: all of this assumes pieces are *full-width* — each consumes its
  whole ε_R budget — which is what the current certificates provide. If the
  machinery ever admits a certified *truncated last piece*, the arithmetic gap
  failure mode disappears and ε_R sensitivity reduces to guard/domain constraints at
  the seams. That partial-width certificate is the alternative fix, at the cost of a
  new certificate shape.)

- **Layer 3 — the consequence.** Positions failing the test are pruned → W shrinks →
  if the admissible starts fall out of W, there is no modal theorem *for that ε_R
  design*. Different ε_R = a different game = a different winning region.

One could imagine instead making ε_R part of the state the fixpoint iterates over —
that would bloat W for nothing: for a given benchmark, ε_R is *fixed by the benchmark
file*. So the design places ε_R under the ∃ — in the answer, never in the position:

- **Positions stay mode pairs.** W does not grow with the width parameters.
- **A σ flow entry is a tiling**, not a single piece: a finite list
  `[(λ₁, w₁), …, (λₖ, wₖ)]` with its seam hops. Its obligations split cleanly:
  - *arithmetic* — `Σ wᵢ = ε_L`, `wᵢ = ε_R/λᵢ`, each λᵢ in the declared range:
    decidable rational facts, kernel `decide`, no Z3;
  - *analytic* — per-piece invariant preservation (Z3 verdicts) and existence (§5),
    one set per piece, exactly as for single pieces.
- **F stays monotone** — a richer answer type does not disturb the lattice; the
  pruning iteration is unchanged.

Consequence worth naming: the fixpoint yields a **per-design verdict**. Under a given
ε_R, if a position admits no tiling it is pruned; if the admissible starts then fall
out of W, the tool reports "this ε_R design cannot match this L" *with the exact
windows that failed* — a diagnosis, not a silent failure. Sweeping candidate ε_R
values (doubling sweep, as with the growth budgets M) turns this into cheap
design-space exploration, since only σ's arithmetic layer varies per candidate.

Status note: the current watertank modal instance is single-piece full-width
(`λ = ε_R/ε_L` per pair); the multiflow tiling machinery exists in the uniform chain.
σ must carry tilings from day one — retrofitting the answer type later would rebuild
the lemma.

### 3.3 The tool side: search = pruning

Replace (rather: complement) the cover exploration with the textbook iteration:

```
W₀ := all (l, q) whose invariant/guard conjunction is satisfiable   (admissible pairs)
Wₖ₊₁ := Wₖ ∩ F(Wₖ)      -- delete positions with no certified answer into Wₖ
stop when Wₖ₊₁ = Wₖ
```

Each `F` evaluation asks Z3 the *same query shapes as today* (flow-piece routes,
frozen-hop preservation, guard entry SAT) — the oracle interface does not change.
The iteration terminates in ≤ |L|·|Q| rounds. This is *simpler* than the current
cover exploration: no windows-within-derivations, no case tree; just a shrinking set.

**Emission** (`--emit-winning-region`): the final `W`, the **choice table**
`σ : W × L-successor → answer` (which flow/hop chain each surviving position uses —
recorded during the last iteration), and the named verdict list backing every table
entry. All as drift-checked Lean literals, EmitIR pattern.

### 3.4 The kernel side: one lemma, then `decide`

Proven **once**, generically (the entire per-benchmark proof burden of the old route
concentrates here):

> **Coinduction soundness.** If
> (i) `postFix : ∀ p ∈ W, p ∈ F_σ(W)` — kernel-checked by `decide` over the emitted
>     table, where `F_σ` is `F` restricted to the choices σ actually records;
> (ii) every flow entry of σ carries its Z3 verdicts (named `z3solve … = unsat` facts)
>     and its existence discharge (§5);
> (iii) every hop entry of σ moves along declared edges with guard-at-entry
>     (successor-completeness — already the frozen contract) and carries its
>     frozen-hop verdicts;
> (iv) admissible starts lie in `W`;
> then `rvalid (theorem3Form L (rightAutomatonBody …) ϕ⁺)` — the modal statement,
> the automaton in the statement, strategy nowhere visible.

The proof is the coinductive reading of §2: membership in W is the loop invariant;
each round, σ's entry supplies the ∃-witness; (i) says the witness lands back in W.
Structurally it reuses what already exists — per-piece modality
(`segment_faModalB_from_certB`), hop re-anchoring, envelope transfer — but *linearly,
once*, instead of per benchmark per derivation shape.

Per-benchmark instantiation then collapses to:

```lean
theorem bench_modal_certified ... :=
  winning_region_sound benchW benchσ
    (by decide)          -- postFix: the one kernel check
    ⟨v₁, v₂, …⟩          -- the named Z3 verdict facts (as today)
    ⟨e₁, e₂, …⟩          -- the existence discharges (route a or b, §5)
```

No window chains. No hop lemmas per instance. No envelope bookkeeping per instance.
The generator emits *data*, not proofs.

---

## 4. What dissolves, what remains

**Dissolved by construction:**

| old blocker | why it disappears |
|---|---|
| mode correspondence (H5) | W is indexed by the automaton's own modes; no plan-to-graph matching exists |
| k = 1 hop-lemma limit | hops are just edges inside `F`; chains handled by the fixpoint, not by a per-length lemma |
| per-benchmark assembly proofs | replaced by one coinduction lemma + `decide` |
| derivation replay (`decideCovered` for the modal route) | replaced by the post-fixpoint check — a strictly simpler decidable |

**Unchanged — the trust base is identical:**

- the per-piece **Z3 verdicts** (same routes, same printer, same `z3_unsat_sound`);
- the **existence residuals** (§5) — a fixpoint says nothing about solutions existing;
- parser, printer, kernel, successor-completeness with guard-at-entry.

Nothing about this design weakens or strengthens what is trusted; it relocates the
*proof assembly* from per-benchmark work into one generic lemma.

**Also retained:** the existing 46 settling/throughout instances and the watertank
modal theorem stay green and untouched. This is a new front door, not a rewrite.

---

## 5. Existence stays a real obligation (the old "option 1")

Every flow entry of σ asserts "this piece evolves for the window's duration" — that is
an analytic fact about ODE solutions, and no combinatorial fixpoint can supply it.
Two discharge routes exist today and slot in per table entry:

- **Route (a), contract fields** (`WellFormedFlowB_contract`): exact exponential
  witness, complete, budget-free. Covers the watertank family.
- **Route (b), general polynomial fields** (`box_viability_bounded_chain`): chained
  Picard steps + per-face strict/growth verdicts with entry budgets. The suite-wide
  census already tags all 1121 faces (576 strict, 545 growth M ≤ 8, zero fails);
  the remaining per-benchmark cost is anchor-budget conditioning (the tangential
  case — anchors sitting on a growth face).

The fixpoint design makes existence *modular*: it is a per-entry hypothesis of the
coinduction lemma, discharged independently of all game/graph reasoning.

---

## 6. Pilot: watertank, worked through

Watertank is the one benchmark whose modal theorem exists on the old route
(`watertank_modal_certified`), so it is the calibration target: the fixpoint route
must reproduce it with visibly less machinery.

**The system.** One tank level `x`. Three right modes (setpoint fields, all exact
contracts `x′ = (3/25)(c_q − x)` on the band `x ∈ [−1/20, 25]`):

| q | c_q | behavior |
|---|-----|----------|
| 0 | 12.5 | settle to mid level |
| 1 | 25   | fill toward full |
| 2 | 2.5  | drain toward low |

Three left modes `l ∈ {0, 1, 2}` with the ideal dynamics, declared edges `GrW` with
self-loops, invariant `gW` (the ε-band between `L_x` and `R_x`), mode-validity
bookkeeping `mvValidR`.

**Step 1 — the universe.** 3 × 3 = 9 positions `(l, q)`.

**Step 2 — the pruning iteration.** `W₀` = the admissible pairs. Evaluating `F` asks,
per pair, the same route-A/B/C queries the tool already printed for watertank. The
recorded verdict set (docs/VERDICTS.md: the six `VerdW`, all UNSAT via route B) tells
us exactly which pairs carry certified flow answers:

```
W₀ = { (0,0) (0,1) (0,2)
       (1,0) (1,1) (1,2)
       (2,0) (2,1) (2,2) }

flow-certified pairs (the six VerdW):
       (0,0) (0,1)
             (1,1)
       (2,0) (2,1) (2,2)
```

Iteration 1 deletes `(0,2)`, `(1,0)`, `(1,2)` — no certified flow answer, and no hop
rescues them *for their own window* (a hop changes `q`, then the target's flow answer
is what counts; the deleted pairs' windows are covered from other `q`s, which is
irrelevant to their own membership — pruning is per-position). Intuition for the
deletions: the drain mode cannot ε-track a filling window and vice versa; only the
pairings the tool certified survive.

```
W₁ = { (0,0) (0,1) (1,1) (2,0) (2,1) (2,2) }
```

Iteration 2 re-checks the survivors' *successor closure*: for `(l, q) ∈ W₁` and every
declared L-successor `l′`, is there a (possibly empty) hop chain to some `q*` with
`(l′, q*) ∈ W₁`? E.g. from `(1,1)`, if L switches to mode 0: stay at `q = 1` — since
`(0,1) ∈ W₁`, no hop even needed. If L switches to mode 2 from `(0,0)`: `(2,0) ∈ W₁`,
stay again. Where staying fails, the declared edges of `GrW` (with guard-at-entry
checked SAT at the switch instant) provide the hop; every such hop used by σ is
backed by a frozen-left verdict. For watertank the closure check passes without
deleting anything:

```
W₂ = W₁  →  fixpoint. W = the six certified pairs — exactly the six VerdW indices.
```

This is the reassuring identity: **the winning region IS the verdict index set** the
old route already named. The fixpoint route doesn't discover new facts about
watertank; it reorganizes the same facts so the proof assembles itself.

**Step 3 — the choice table σ** (illustrative shape):

```
σ(l, q)(l′) =  stay-and-flow(λ_{l′q})      if (l′, q) ∈ W
               hop(q → q′) ∘ flow(λ_{l′q′}) otherwise, q → q′ ∈ GrW, guard entered
```

**Step 4 — the per-benchmark theorem on the new route:**

```lean
theorem watertank_modal_fixpoint (dt : ℝ)
    (h00 h01 h11 h20 h21 h22 : …z3solve facts…) :   -- the SAME six verdicts
    rvalid (theorem3Form (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvM) ϕ⁺) :=
  winning_region_sound wtW wtσ
    (by decide)                                    -- postFix over 6 positions
    ⟨h00, h01, h11, h20, h21, h22⟩                 -- verdicts, unchanged
    (fun _ q hq => watertank_ESW_from_contract …)  -- existence: route (a), proven
```

Compare with what `watertank_modal` cost on the old route: the envelope split
(`envLR`), `hddF_multiE`, `faModalB_strengthen_plant`, the k = 1 prefixed-window
lemma, hand-wired hop re-anchoring — S1 was a full autonomous session. On the
fixpoint route all of that is *inside* `winning_region_sound`, paid once, and the
watertank instance is the six facts plus a `decide`.

**Pilot acceptance gate:** `watertank_modal_fixpoint` kernel-green with axioms exactly
`[propext, Classical.choice, Quot.sound]` + `z3_unsat_sound` at the leaves, and its
statement literally identical (or provably equivalent) to `watertank_modal_certified`'s
conclusion. That identity is the proof that the new route proves the *same thing*.

---

## 7. Honest risks

1. **The coinduction lemma is a real proof.** All the difficulty the old route paid
   per benchmark concentrates into `winning_region_sound` — envelope transfer, hop
   re-anchoring, clock bookkeeping, admissible-start conditioning, now in full
   generality (arbitrary hop chains, arbitrary mode counts). The S1 negative findings
   (the `hdisH` unsatisfiability for frozen hops) were *statement* problems of a
   particular lemma, not facts about the systems — the fixpoint statement avoids that
   lemma's shape — but the general proof may surface its own findings. That is what
   the pilot is for.
2. **Guard SAT at hops.** σ's hop entries need "guard satisfiable at the switch
   instant *given the invariant*" — per-edge SAT checks (new query kind for the tool,
   though trivially printable; SAT answers are used only to *select* σ during search,
   never trusted — only UNSAT facts enter theorems, as today; the *proof* obligation
   at a hop is invariant preservation, a frozen-left UNSAT verdict).
3. **W can be empty or miss the starts.** Then the benchmark genuinely lacks a modal
   certificate at this granularity — the design reports it honestly (as
   shield_unreachable is reported today) rather than failing silently.
4. **State-dependent strategies.** W as defined is mode-granular (positions are mode
   pairs). If some benchmark needs the response choice to depend on *where in the
   invariant region* the state is, positions must be refined (mode pair × region
   predicate) — the design extends (predicates from the cut/strata machinery slot in
   as position refinements), but the lattice grows. No current benchmark is known to
   need this; the pilot and the first tier-2 benchmark will tell.
5. **Existence is untouched** (§5) — route (b) wiring is still the price of admission
   for non-contract benchmarks, exactly as under the old option 1.

---

## 8. Plan (when/if scheduled — nothing is committed by this document)

- **W1 — the lemma.** Define positions, `F_σ`, `postFix` (decidable); prove
  `winning_region_sound` against `theorem3Form`. Reuses `segment_faModalB_from_certB`,
  the envelope machinery, the frozen-hop preservation lemmas. Gate: lemma kernel-green,
  3 axioms.
- **W2 — the pilot.** Hand-write `wtW`/`wtσ` for watertank (no tool changes yet);
  prove `watertank_modal_fixpoint`; compare statements. Gate: §6's acceptance gate.
- **W3 — the tool door.** The pruning search + `--emit-winning-region` (new files,
  rebuild hygiene — no `OracleAPI` edits); drift-check against the pilot's hand
  literals. Gate: emitted watertank data = pilot data, `rfl`.
- **W4 — the generator + tiers.** Instances tier by tier (tier 1 mechanical, tier 2
  needs route-(b) existence wiring, tier 3 the 12-dof heavies, serial). Gate per tier:
  batteries green, axiom audit exact.

W1+W2 together are one focused arc (S1-sized) and are decision-complete: if the pilot
reproduces watertank cheaply, the route is validated; if it surfaces findings, they
are findings about the *general* lemma we were going to need anyway.
