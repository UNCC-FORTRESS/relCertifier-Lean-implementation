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
  `[(λ₁, w₁), …, (λₖ, wₖ)]` with its seam hops. Its obligations split cleanly:
  - *arithmetic* — `Σ wᵢ = ε_L`, `wᵢ = ε_R/λᵢ`, each λᵢ in the declared range:
    decidable rational facts, kernel `decide`, no Z3;
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

**Step 0 — the board.** Positions = the 9 cells of the 3 × 3 grid `(l, q)`. Think of
a checkerboard: rows = what L is doing, columns = what R is doing.

**Step 1 — admissibility.** `W₀` = cells where the invariant and both guards can
hold at all. For watertank all 9 pass — a filling L and a draining R *can*
momentarily be within ε of each other. The board starts full.

**Step 2 — the flow test, per cell.** For each cell, ask: *if L runs this window,
can R's current mode track it for the whole window?* Per cell this unfolds as §3.2's
layer 2: probe λ candidates (Z3 — route B here, strict decrease of the barrier along
the joint dynamics); each `unsat` certifies one λ, i.e. one piece width `ε_R/λ`;
then tiling arithmetic over the certified widths. Watertank is the easy case — one
full-width piece per window (`λ = ε_R/ε_L` per pair), so tiling degenerates to "the
single certified λ exists." The recorded verdict set (docs/VERDICTS.md: the six
`VerdW`, all UNSAT via route B) gives the grid:

```
          q0 settle   q1 fill   q2 drain
  l0         ✓           ✓          ✗
  l1         ✗           ✓          ✗
  l2         ✓           ✓          ✓
```

Intuition per ✗: cell `(l1, q2)` — L fills toward 25, R drains toward 2.5; the gap
`|L_x − R_x|` grows monotonically, and no λ rescale fixes a wrong *direction* —
every probe fails, the certified set is empty. Cell `(l1, q0)`: R plateaus at 12.5
while L climbs past `12.5 + ε`. Cell `(l0, q2)`: the same divergence in the other
direction. Only the pairings the tool certified survive.

**Step 3 — prune.** Delete the three ✗ cells. (A hop cannot rescue a deleted cell
*for its own window*: a hop changes `q`, and then the *target's* flow answer is what
counts — pruning is per-position.)

```
W₁ = { (l0,q0) (l0,q1)  (l1,q1)  (l2,q0) (l2,q1) (l2,q2) }
```

**Step 4 — the closure test (the "…and lands back in W" half).** Re-examine each
survivor: when L *switches* modes, can R stay in the region? In general this
evaluates the *inner* per-left-mode reachability fixpoint `Serve(l′, …)` of §3.1 —
multi-hop chains through R's graph. Watertank is degenerate here: every needed
chain has length ≤ 1 (q1's column is full and direct edges reach q1), so the test
collapses to "stay, or hop once." For each `(l, q) ∈ W₁` and each declared
L-successor `l′`:

- **Stay works?** Is `(l′, q) ∈ W₁`? From `(l1, q1)`, L switches to `l0`:
  `(l0, q1) ∈ W₁` → R does nothing, just flows. Column q1 is full, so from q1 R
  *never* needs to hop.
- **Stay fails → hop.** From `(l2, q2)`, L switches to `l1`: `(l1, q2) ∉ W₁` → R
  hops `q2 → q1` along a declared edge of `GrW`, guard holding at the entry instant
  (guard-at-entry — the folded contract), invariant carried across the frozen-left
  hop (a frozen-hop verdict). Lands at `(l1, q1) ∈ W₁`. ✓

Every survivor passes for every successor (q1's column covers every row and the mode
graph reaches q1), so nothing more is deleted:

```
W₂ = W₁  →  fixpoint. W = the six certified pairs — exactly the six VerdW indices.
```

The reassuring identity: **the winning region IS the verdict index set** the old
route already named. The fixpoint route discovers no new facts about watertank; it
reorganizes the same facts so the proof assembles itself.

**Step 5 — the certificate.** Emit two literals: `W` (six cells) and the choice
table σ — per cell, per L-successor, the recorded answer:

```
σ(l, q)(l′) =  stay-and-flow(λ_{l′q})       if (l′, q) ∈ W
               hop(q → q′) ∘ flow(λ_{l′q′})  otherwise, q → q′ ∈ GrW, guard entered

e.g.  σ(l2,q2)(l1) = hop q2→q1, then flow at λ₁₁
      σ(l1,q1)(l0) = stay, flow at λ₀₁
```

**Step 6 — the kernel's share.** Three checks, all mechanical:

1. `decide`: every cell of W, under σ's choices, lands back in W — the post-fixpoint
   property, a finite table lookup (six cells × their successors);
2. the named Z3 facts: the six flow verdicts plus the hop verdicts σ uses — the same
   `z3solve … = unsat` hypotheses as today;
3. existence: each flow entry actually evolves for its window — watertank's fields
   are exact exponential contracts, so this is the already-proven `watertank_ESW`,
   no Z3.

**Step 7 — the theorem.** The generic lemma converts checks 1–3 into the modal
statement — the automaton in the statement:

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

**Where ε_R hid in all this:** watertank never exercised the tiling arithmetic —
single full-width piece per window, certified set = one λ per cell. A benchmark
where Z3 certifies only a thin λ set would show its ε_R sensitivity in Step 2:
certified widths that cannot sum to the window → cell ✗ despite healthy dynamics →
W shrinks → the per-design diagnosis of §3.2.

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
