# Design: the winning-region fixpoint — "the automaton refines L" for every benchmark

Status: DESIGN PROPOSAL (2026-07-17). Nothing here is implemented in Lean; the current
derivation-style pipeline (cover search → `decideCovered` replay → per-benchmark
assembly) stays the production route until this design lands end-to-end on a pilot.
An executable prototype exists — `scripts/fixpoint_prototype.py`, six runs on
watertank's real data — and its findings are folded into §6.
Companion reading: README ("The end-to-end guarantee, intuitively"), `docs/history/ROADMAP.md`
(final closure — options 1 and 2 are the problem this design attacks).

**Scope, in three sentences (details in §9).** This design buys nothing for the
existing results: the 46 settling/throughout theorems and the watertank modal
theorem are done, green, and unaffected, and the project headline stands without
it. It matters only if the *modal* statement — "the automaton refines L," strategy
proof-internal — is wanted for every benchmark; for that goal it converts
open-ended per-benchmark proof work into one hard generic lemma plus emitted data
plus `decide`. If that suite-wide modal claim is not needed, this document is a
recorded design option, not scheduled work.

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
  - **hop(q → q′)**: an edge in `E`, taken as a *frozen-left right flow* — L's
    clock does not advance while R flows into `q′`'s guard and enters it legally
    (guard-at-entry — the folded successor-completeness contract), invariant
    preserved throughout (the frozen-left verdicts). Legality is a *reachability*
    fact, not a syntactic edge check (§6 Step 3, risk 2). Hops chain.

The design is **two nested fixpoints** — an inner one *per left mode* over R's
graph, and an outer one over pairs. They answer different questions and neither
subsumes the other.

- **Inner fixpoint (least, per left mode): reachability — "who can serve this
  window?"** Fix a target left mode `l′` and a candidate landing set
  `T ⊆ Q` (below: the modes `q*` with `(l′, q*)` still in the outer W). Define

  ```
  Serve(l′, T) = lfp of:  q ∈ S  if  q ∈ T and q has a certified flow answer
                                     (a tiling, §3.2) to l′'s window
                          q ∈ S  if  ∃ edge q → q′ ∈ E, guard-legal at entry,
                                     invariant carried (frozen-left verdict),
                                     with q′ ∈ S
  ```

  This is transitive closure on R's mode graph. **Multi-hop witnesses live
  entirely here**: a response needing several repositions to reach the answering
  mode is just several steps of this reachability, computed per left mode — the
  per-left-mode fixpoint. (It is essentially what the tool's cover search already
  computes per left mode today.)

- **Outer fixpoint (greatest, over pairs): persistence — "and then keep
  serving, forever."** `Serve` answers ONE window. Winning means answering every
  window of every L line. The step operator evaluates the inner fixpoint inside
  each membership test:

  ```
  (l, q) ∈ F(W)  ⟺  for every declared L-successor mode l′ of l
                      (including l itself):
                      q ∈ Serve(l′, { q* | (l′, q*) ∈ W })
  ```

  `F` is monotone (bigger W ⟹ bigger landing set ⟹ easier membership; `Serve` is
  monotone in `T`), the lattice is finite, so the greatest fixpoint `gfp F` exists
  and pruning iteration reaches it.

  Why the outer layer cannot be dropped: one fixpoint per left mode alone
  expresses "this window is answerable," not "and the landing mode is again
  well-positioned for the next window." W is exactly that across-time coupling —
  membership in W is the loop invariant of the rounds.

R hops in two places, both frozen-left, both moves of the *inner* fixpoint:
at L's mode switches, and at the seams *between tiling pieces within one window*
(the multiflow round shape permits mid-window repositions). Same chain machinery,
same frozen-hop verdicts.

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
  Two λ layers must not be conflated:
  - the **declared range** (benchmark file) is only the *search space* — a design
    input; nothing in it works by fiat;
  - the **certified set** of a pair `(l, q)` is the λs that actually work — the
    tool probes candidates inside the range and Z3 certifies (or rejects) each;
    finite, dynamics-dependent, discovered during the `F` evaluation.

  To cover the window, piece durations must add up to ε_L — a *tiling*
  `Σᵢ ε_R/λᵢ = ε_L` with every λᵢ drawn from the **certified set**, hop chains
  permitted at the seams (the multiflow round shape, task H). So the membership
  test interleaves: probe λ candidates (Z3) → collect certified widths `ε_R/λ` →
  tiling arithmetic over those widths. Concretely, with ε_L = 1:
  - **Success:** ε_R = 0.4, certified λs include {1, 2} → widths {0.4, 0.2};
    the tiling 0.4 + 0.4 + 0.2 = 1 works.
  - **Failure:** ε_R = 0.7, certified λs all in [1, 1.05] (whether because the
    declared range is that narrow or because Z3 rejects everything outside it) →
    widths in [0.667, 0.7]; k pieces total in [k·0.667, k·0.7], so k = 1 reaches
    at most 0.7 < 1 and k = 2 already needs ≥ 1.333 > 1. The reachable sums have
    a gap at 1 — no tiling from that certified set.
  - **The general criterion** (certified widths within `[wmin, wmax]`): a tiling
    exists iff `ε_L ∈ ⋃ₖ [k·wmin, k·wmax]`; gaps occur only while consecutive
    intervals fail to overlap, i.e. while `wmax/wmin < (k+1)/k`. A rich certified
    set never fails; a thin one — narrow declared range *or* picky dynamics —
    with ε_R large relative to ε_L can.

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
  `[(λ₁, w₁), …, (λₖ, wₖ)]` with its seam hops — and the pieces may be drawn
  from *different* R modes along the walk (mid-window repositions: piece in q₁,
  frozen-left hop, piece in q₂, …). Several modes can jointly cover one window
  none of them covers alone. The inner fixpoint then runs over
  `(mode, covered-time)` pairs instead of modes — flow moves advance time within
  a mode, hop moves change mode at fixed time — still finite, same frame
  (prototype RUN 6). Its obligations split cleanly:
  - *arithmetic* — `Σ wᵢ = ε_L`, `wᵢ = ε_R/λᵢ`, each λᵢ inside the declared
    range: decidable rational facts, kernel `decide`, no Z3;
  - *analytic* — per-piece invariant preservation at that λᵢ (the Z3 verdicts —
    these are what make λᵢ *certified*, not merely declared) and existence (§5),
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
frozen-hop preservation, hop-reach probes, guard entry SAT for selection) — the
oracle interface does not change. The iteration terminates in ≤ |L|·|Q| rounds.
This is *simpler* than the current cover exploration: no
windows-within-derivations, no case tree; just a shrinking set.

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
    ⟨r₁, r₂, …⟩          -- the reach certificates for σ's hops
    ⟨e₁, e₂, …⟩          -- the existence discharges (route a or b, §5)
```

No window chains. No hop lemmas per instance. No envelope bookkeeping per instance.
The generator emits *data*, not proofs.

Two properties of this shape are the entire point, stated precisely:

- **The statement is clean.** The per-benchmark theorem *statement* mentions only
  L's program, `rightAutomatonBody` (the automaton), the invariant, and the named
  hypotheses (verdicts, reach, existence). The strategy appears **nowhere in the
  statement** — σ and W are arguments to the generic lemma *inside the proof
  term*, which is the right place for witness data backing an ∃. The claim reads
  "the automaton refines L," full stop.

- **Instantiation is uniform.** Every benchmark's proof is the *same one-liner*,
  differing only in the emitted data literals (`benchW`, `benchσ` — drift-checked
  like `BenchIR` today). Contrast the old route: `watertank_modal`'s statement was
  also clean, but its *proof* was a hand-assembled, benchmark-shaped construction,
  and scaling means a generator emitting *proofs*, each able to fail in
  benchmark-specific ways (the §1 blockers). Here every benchmark-shaped
  difficulty lives in the one lemma; the only per-benchmark failure mode is honest
  and diagnostic — W does not contain the starts.

### 3.5 What the fixpoint formulation actually buys (it is not the search)

A fair challenge: computationally, the inner layer is essentially the bounded
cover search the tool already runs (the benchmark files even declare
`max_depth`). If the fixpoint were a search algorithm, it would buy nothing. It
is not; it is the shape of the **certificate and the lemma**. Three gains:

1. **Certificate locality — the kernel never sees the search.** The old route
   makes the kernel replay the derivation, and the per-benchmark proof does
   induction over it — where all the assembly cost and the H5/hop-lemma blockers
   lived. Here the search emits `W` + σ and the kernel checks a *local closure
   property*: each entry lands back in W. How W was found is irrelevant to
   soundness — bounded search, heuristics, buggy pruning are all fine, because
   the search is untrusted and the check is independent of it. The fixpoint
   equation is the specification the certificate must satisfy — which is exactly
   what makes it checkable by one `decide`.

2. **The outer gfp is load-bearing, not decorative.** "The automaton refines L"
   quantifies over *unbounded* rounds; no bounded search certifies "forever"
   directly. The greatest fixpoint is the device that reduces an infinite-horizon
   ∀∃ to a finite set closed under one step: in W now + closure ⟹ in W after
   every future round, by coinduction. The current per-left-mode search does not
   express this at all — today it is handled by baking the choreography into the
   statement. The outer fixpoint is what lets the statement mention the automaton
   and still be discharged by finite checks.

3. **Monotonicity makes search bounds harmless.** A depth-bounded inner search
   under-approximates the true `Serve`; under-approximating `Serve` shrinks the
   certifiable W — but a post-fixpoint of an under-approximated operator is still
   a post-fixpoint of the true one. Truncation costs *coverage*, never
   *soundness*. Without the framing, every bound in the search would need its own
   soundness argument.

One sentence: the search stays what it is today; the fixpoint is what turns its
output into a certificate a single generic theorem can consume.

### 3.6 In plain loop-invariant terms (deflating the gfp vocabulary)

The fixpoint language deflates entirely into the familiar story — "prove the
invariant inductive and you are done" — with exactly two additions:

- **"W is a post-fixpoint of F" = "membership in W is an inductive invariant of
  the game."** Nothing more. The proof obligation is the standard one: a set,
  one-step preservation under σ's moves, starts inside. Induction on rounds
  closes it; "coinduction" here is that induction, no deeper.

- **Which invariant: a strengthening.** The relational invariant ϕ alone is NOT
  inductive for the ∀∃ game — inductiveness must carry the strategic content
  "and R currently has an answer." (Watertank: ϕ can hold at `(Mid, High)` while
  R is about to be dragged out of the band — true now, not preservable from
  there without the hop.) W = ϕ ∧ "R well-positioned" — the classic
  loop-invariant strengthening, of the classic reason: raw postconditions are
  rarely inductive.

- **Where "greatest" enters: the tool side only, never the proof.** Any
  inductive W yields the theorem; smaller W = fewer certified starts, same
  soundness. The gfp is merely the *largest* inductive W, and pruning iteration
  is the classic way to compute it — the search finds the weakest sufficient
  strengthening automatically instead of a human guessing it. The kernel and the
  lemma only ever use "inductive."

The design in one line of this vocabulary: **the tool computes the strengthened
inductive invariant of the refinement game and emits it; the kernel checks
inductiveness; one generic lemma says inductive + start inside ⟹ refines.**

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

**Step 0 — the board.** Positions = the 9 cells of the 3 × 3 grid `(l, q)`. Think of
a checkerboard: rows = what L is doing, columns = what R is doing.

**Step 1 — admissibility.** `W₀` = cells where the invariant and both guards can
hold at all. For watertank all 9 pass — a filling L and a draining R *can*
momentarily be within ε of each other. The board starts full.

**Step 2 — the direct flow test, per cell.** For each cell, ask: *if L runs this
window, can R's current mode track it directly, no repositioning?* Per cell this
unfolds as §3.2's layer 2: probe λ candidates (Z3 — route B here, strict decrease of
the barrier along the joint dynamics); each `unsat` certifies one λ, i.e. one piece
width `ε_R/λ`; then tiling arithmetic over the certified widths. Watertank is the
easy case — one full-width piece per window, so tiling degenerates to "the single
certified λ exists." The recorded verdict set (docs/VERDICTS.md: the six `VerdW`,
all UNSAT via route B) gives the direct-certificate grid (rows = L's mode, columns
= R's mode; the invariant is the one-sided `x_L ≤ x_R + 3`):

```
           R:Low   R:Mid   R:High
  L:Low      ✓       ✓       ✗
  L:Mid      ✗       ✓       ✗
  L:High     ✓       ✓       ✓
```

Intuition per ✗ (the benchmark file documents these as its no-certificate pairs):
`(Mid, High)` — L fills toward 25 while R drains toward 2.5; `x_L − x_R` grows
monotonically, and no λ rescale fixes a wrong *direction*. `(Mid, Low)` — L
fast-fills toward setpoint 25 while R slow-fills toward 12.5; L outruns the bound.
`(Low, High)` — filling left against draining right, same growth. (Note `(High,
Mid)` ✓ even though right *fills* while left drains: the invariant is one-sided —
the right side running ahead only helps.)

**Step 3 — serve, with repositions.** A cell without a direct certificate is not
dead: a reposition is a **frozen-left right flow** — L's clock does not advance
while R flows in its own time toward the target mode's guard, enters it legally,
and only then does the window's joint flow start. So the inner fixpoint
`Serve(l, …)` of §3.1 can rescue a ✗ cell *for its own window*. Concretely,
`(Low, High)`: R sits in High (`x ≥ 17`) while L runs a Low window — R drains in
frozen left-time until `x < 17`, Mid's guard turns true, R enters Mid, and
`(Low, Mid)` is directly certified. The hop is legal *only because the drain flow
reaches the guard* — High's and Mid's guard regions are statically disjoint, so
hop legality is a **reachability certificate** (the existing frozen-left
reposition machinery), not a syntactic edge check.

**Step 4 — the outer fixpoint, executed.** `scripts/fixpoint_prototype.py` runs
the nested fixpoints on this exact data (real mode lists, real declared edges,
flow oracle = the six recorded verdicts; hop legality approximated by the declared
edges, with the reachability caveat above). Result:

```
RUN 1 (watertank as-is):   W = ALL NINE positions, stable in one iteration.
```

Every cell serves every successor window — the ✗ cells via a reposition into the
Mid column, everything else directly. **This falsified the first draft of this
section**, which claimed W would equal the six verdict indices with the ✗ cells
pruned: running the example showed that window-start repositions *widen* the
winning region beyond the directly-certified pairs. The identity that actually
holds (visible in the emitted σ): **every flow endpoint σ uses is one of the six
VerdW pairs** — six verdicts = the strategy's flow endpoints; W = the serviceable
*starts*, which hops legitimately enlarge. Against the old route this is a
strengthening: `watertank_modal` conditions its starts on the certified pairs,
while the fixpoint certifies the full board as admissible starts — at the honestly
named price of one reachability certificate per hop used.

The prototype's counterfactuals show the fixpoint biting in both inputs:

```
RUN 2 (delete R edge High→Mid): drain trap — R stuck in High can never rejoin
      a filling mode; the whole High column is pruned, W = 6.
RUN 3 (delete the (High,Mid) verdict instead): W stays 9, but σ reroutes —
      (Mid,Mid) now answers a High switch by hopping Mid→High and flowing
      at (High,High) rather than staying.
```

Graph weakness and dynamics weakness compose through the same operator; a bad
design shrinks W and the pruning trace *names the windows that failed*.

**Step 5 — the certificate.** Emit two literals: `W` (here: all nine cells) and the
choice table σ — per cell, per L-successor, the recorded answer (excerpts from the
prototype's actual output):

```
at (Low, Mid),  L switches to Mid:   stay, flow at the certified λ for (Mid,Mid)
at (Low, High), L switches to Low:   hop High→Mid, then flow for (Low,Mid)
at (High,High), L switches to Mid:   hop High→Mid, then flow for (Mid,Mid)
```

**Step 6 — the kernel's share.** Four checks, all mechanical:

1. `decide`: every cell of W, under σ's choices, lands back in W — the post-fixpoint
   property, a finite table lookup (nine cells × their successors; the prototype's
   `post_fixpoint_check` is this check in miniature);
2. the named Z3 facts: the six flow verdicts plus the frozen-hop preservation
   verdicts σ uses — the same `z3solve … = unsat` hypotheses as today;
3. reach certificates for σ's hops: each reposition is a frozen-left right *flow*
   into the target guard (Step 3), so each hop used carries a reachability
   discharge — the existing reposition machinery, now named per edge;
4. existence: each flow entry actually evolves for its window — watertank's fields
   are exact exponential contracts, so this is the already-proven `watertank_ESW`,
   no Z3.

**Step 7 — the theorem.** The generic lemma converts checks 1–4 into the modal
statement — the automaton in the statement:

```lean
theorem watertank_modal_fixpoint (dt : ℝ)
    (h00 h01 h11 h20 h21 h22 : …z3solve facts…) :   -- the SAME six verdicts
    rvalid (theorem3Form (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvM) ϕ⁺) :=
  winning_region_sound wtW wtσ
    (by decide)                                    -- postFix over 9 positions
    ⟨h00, h01, h11, h20, h21, h22⟩                 -- verdicts, unchanged
    ⟨hopReach_HighMid, …⟩                          -- reach certs for σ's hops
    (fun _ q hq => watertank_ESW_from_contract …)  -- existence: route (a), proven
```

Compare with what `watertank_modal` cost on the old route: the envelope split
(`envLR`), `hddF_multiE`, `faModalB_strengthen_plant`, the k = 1 prefixed-window
lemma, hand-wired hop re-anchoring — S1 was a full autonomous session. On the
fixpoint route all of that is *inside* `winning_region_sound`, paid once, and the
watertank instance is the six facts plus a `decide`.

**Where ε_R hid — and the runs that expose it.** Watertank as-shipped never
exercises the tiling arithmetic: all six verdicts are at λ = 1 with
ε_R = ε_L = 1, one full-width piece per window. The prototype's RUNs 4–5 turn the
dial with the dynamics, graph, and certified *pairs* all held fixed — only the
certified λ sets are varied (hypothetical there; real ones come from Z3 probes),
and the tiling requirement `Σ ε_R/λᵢ = ε_L` is checked exactly:

```
RUN 4 (ε_R sweep, certified λ set = {1}):
  ε_R = 1    → width 1        tiles → |W| = 9
  ε_R = 1/2  → width 1/2      tiles (1/2 + 1/2) → |W| = 9
  ε_R = 7/10 → width 7/10     NO TILING (reaches only 7/10, 14/10, …) → |W| = 0

RUN 5 (ε_R = 7/10 kept, richer certified λ set {1, 7/5}):
  widths {7/10, 1/2}          tiles (1/2 + 1/2 = 1) → |W| = 9
```

RUN 4's third line is the clean demonstration of the phenomenon: **the dynamics
never changed — the width dial alone collapsed the winning region to empty.** And
RUN 5 shows the recovery lever: certifying one more λ (7/5, width 1/2) restores the
tiling and the full region returns. ε_R sensitivity = thinness of the certified
width set against the window — exactly §3.2's criterion — and the fixpoint
surfaces it as a per-design verdict with the failing windows named, not as an
unexplained proof failure.

**RUN 6 — several modes jointly cover a window none covers alone** (mid-window
repositions, §3.2's `(mode, covered-time)` upgrade of the inner fixpoint):

```
pair (Low,Low): width 3/10  — cannot tile alone (reaches 3/10, 6/10, 9/10, …)
pair (Low,Mid): width 7/10  — cannot tile alone (reaches 7/10, 14/10)
mixed-mode Serve(Low) = {Low}:
  from Low:  flow 3/10 in Low;  hop Low→Mid;  flow 7/10 in Mid   (= 1) ✓
```

No single pair tiles the window, yet the alternation — piece, frozen-left hop,
piece — covers it exactly. And the graph's *direction* matters: from Mid or High
the Low-piece is unreachable (no edge back to Low), so only starts in Low serve.
The mixed tiling drops into the same fixpoint frame, and its failures are as
informative as its successes.

**Pilot acceptance gate:** `watertank_modal_fixpoint` kernel-green with axioms exactly
`[propext, Classical.choice, Quot.sound]` + `z3_unsat_sound` at the leaves, and its
conclusion at least as strong as `watertank_modal_certified`'s: restricted to the old
route's admissible starts it must provably imply the old conclusion (the prototype
indicates the fixpoint starts are strictly *wider* — the full board versus the six
certified pairs — so "identical statement" is the wrong gate; "provably subsumes" is
the right one).

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
2. **Hop legality is reachability, not a syntactic edge check.** The prototype run
   made this concrete: R's High and Mid guard regions are statically *disjoint*
   (`x ≥ 17` vs `x < 17`), yet the hop High→Mid is legitimate — a reposition is a
   frozen-left right *flow* that carries the state into the target guard (here:
   draining below 17). So each hop σ uses needs a **reach certificate** (the
   existing frozen-left reposition machinery, named per edge) plus the frozen-hop
   invariant-preservation UNSAT verdict. SAT probes may still guide the *selection*
   of σ during search — never trusted, as today; only UNSAT facts and reach
   discharges enter theorems. The prototype approximates legality by the declared
   edge relation and says so; the real design must not.
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

---

## 9. Scope: what this buys, and the decision rule

**Buys nothing for (all done, green, unaffected):**

- the 46 settling/throughout end-to-end theorems;
- the watertank modal theorem (`watertank_modal_certified`) — the fixpoint route
  would only widen its start set, marginal;
- the project headline — "end-to-end verified in Lean, modulo Z3-unsat and the
  modeling boundary" stands without this design.

**Buys something only under one condition:** the *modal statement* — the automaton
in the theorem, strategy proof-internal (§3.4's two properties) — is wanted for
**every** benchmark, not just watertank. Under that condition the win is real and
structural: the open-ended per-benchmark proof work of the old route (mode
correspondence, hop-lemma limits, generators emitting proofs — §1's blockers)
becomes one hard generic lemma + emitted data + `decide` per benchmark, and every
per-benchmark failure is the diagnostic kind (W misses the starts), never the
mysterious kind (a proof script that will not close). Even then, two costs are
route-independent: `winning_region_sound` is an S1-sized-or-larger proof, and the
existence wiring for non-contract fields (§5, route b) must be paid on any route.

**Banked already at zero further cost:** the design-space clarifications this
document and the prototype produced — where ε_R bites (tiling over certified
widths), hop legality as reachability, repositions widening the start set, the
per-design diagnostic capability. Recorded; useful independently of whether the
arc ever runs.

**Decision rule.** Does the paper, a reviewer, or a certification story require
"the automaton refines L" suite-wide? If yes: schedule W1+W2 (§8) — it is the
cheapest path to that claim, and decision-complete. If no: shelve — this document
costs nothing on the shelf, and the shipped results are complete and defensible as
they stand. Default recommendation: **shelved** until the suite-wide modal claim
is concretely demanded.
