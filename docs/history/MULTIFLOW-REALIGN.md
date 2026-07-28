> **HISTORY.** Completed record, retained for provenance — not a description of the
> current state. For what is live today see `docs/READING-GUIDE.md`.

# Task H: realigning the uniform suite onto the paper-faithful multi-flow chain

## Design agreement (from the F2 discussion)

Within one left ε_L-window: a sequence of right modes matches it — alternation of
**joint sub-segments** (`(Lmode ‖ Rmodeᵢ)` co-evolve; right field ×λᵢ; the piece covers
ε_R/λᵢ of left time; invariant preserved by the **joint certificate**) and **repositions**
(frozen-left right flows at the seams, left clock not advancing; invariant preserved by the
**reposition certificate**, whose domain carries the left context — pre-j
`guardL ∧ evolveL ∧ evolveR`, post-j `evolveL ∧ evolveR`). The witness is constructed from
right modes covered by one of these two certificates. H is single-system well-formedness
only (DONE — unbundled, commit 6c977e6; the defective left-context-free `GBoxAll` is
quarantined with a do-not-build-on notice).

`EvolStrengthening` (formerly "checked cut") is the third, non-certificate device:
single-execution evolution-constraint strengthening that makes joint certificates findable.
Already separated and kernel-certified (task D).

## Status after the overnight run

* H1 DONE: rename (commit 8337d96).
* H2 DONE: the paper structure is FULLY mechanized in the GAP-1 arc, all live files:
  - fixed budget cuts `dt = ε_r/λ` per piece — `BridgeReposition.lean` header, `plantT_split_iter`;
  - per-piece bounded couplings `faModalB` + the clock bridge `faModalB_clockedSeg_iff`;
  - `multiseg_clocked`: k-fold clocked left ‖ `bigSeq rights` preserves φinv from per-piece couplings;
  - clock-lift collapse (`clockLift_*`): k-fold clocked left → the single physical left flow;
  - mv-lift (`hstep_single_multi`/`hstep_assembled_multi`): `bigSeq rights` → `star (rightAutomatonBody G mv)`
    along declared edges; `faModal_bigChoiceL` over left modes; `relational_loop_multi` closes to
    `[|(L*,R*)⟩⟩ψ`;
  - repositions: `reposition_step_pres` (static), `dynreposition_faModal` (dynamic — literally
    `segment_faModal` at `fL = 0`, hcert = `BoxLe (ode (jointSys 0 fR λ) (domL ∧ domR))` — matching
    `checkDynRepo`'s query with the left context INCLUDED);
  - the tie: `BridgeDischarge.decideCovered_implies_theorem3_faithful`.
* H3 DONE (commit 6c977e6): `GuardSettlingH` single-system; `wellformed_sound{,T,A}` need no
  relational hypothesis; the 46 `_real` theorems are now **Z3-hypothesis-free** (their conclusions
  are single-system; residuals = freshness data only). `GBoxAll` threaded explicitly only where the
  deprecated cadenced chain still consumes it.

## H5 grounding status (2026-07-15)

* LANDED: `theorem3_uniform_multiflow` (UniformMultiflow.lean) — per-left-window cover data
  (`∃ Gj, CoverCert ∧ RightProjAlignV` inside `hleft`; joint systems differ per window, a
  global `Gj` cannot align them). Axioms clean.
* LANDED: `UniformFvDischarge.lean` — hd/hddF dischargers + the bookkeeping-free wrapper
  `uniform_multiflow_end_to_end` (side-splits ⟹ every freshness/hygiene hypothesis).
* LANDED: `LoweringSide.lean` — lowered data lives on its declared side (`namesFree`
  prefix-freedom check, per benchmark by simp; `String.startsWith` does NOT kernel-reduce,
  so `decide`/`rfl` are unavailable — simp's ground-string evaluation is the route).
* LANDED: **pilot** `Instances/UniformPilot.lean` — `rover_drag_multiflow` end to end
  (1 left mode, 1 right mode, k = 1). Residuals: `hψ` + invariant splits, `hz3` (one joint
  query), `hES`. Axioms: the standard three + `z3_unsat_sound`.

### The honest multi-mode blocker (mode correspondence)

Watertank CANNOT be instantiated this way: the ∀∃ form quantifies over every
(left window, right start mode) pair, but off-diagonal pairs have no joint certificate —
left `Low` (fill 0.6) vs right `High` (fill 0.1) has `ċ` gap 0.5 > 0.12 on `g = 0`: the
flow query is SAT. The cadenced chain carried the pairing via `inModeGuardF` in `ψpostG`
(mv = q ⟹ the right sits in its mode region). The multiflow chain needs the same:
either (a) a region conjunct in the loop invariant + region restoration at piece ends, or
(b) window entry starts with a REPOSITION to the matching right mode (paper's witness) —
repositions interleaved inside the window. Design decision pending.

### hES per shape

`HExistSeg` residual is dischargeable via the revived `HExistDischarge` seam for the
rover-chase and cubic shapes; `rover_drag`'s quadratic drag (`0.05 − 0.3·vx²`, forward-
invariant `[0, 1.4]`, interior equilibrium `√(1/6)`) needs a new slab-Lipschitz Picard
instance — mechanical but not yet written.

## Remaining (H4/H5) — the execution list

1. **H4a — joint-piece adapter.** From `hz3 : z3solve (flowQuery ⟨g, fL, fR, λᵢ, domL∧domR⟩) = unsat`
   (+ hExist + footprint facts, i.e. `CertSeg` data) produce the per-piece
   `faModalB (refl) (ode (clk tg leftBlock) domL) (ode (rightBlock fR λᵢ) domR) (invLe g) tg dt`
   coupling `multiseg_clocked` consumes. Ingredients: `pair_faModal` (unbounded, unclocked) +
   a `faModalB`-weakening + the clock treatment — CHECK `faModal_ODE_G'_bounded` first: it is
   "the domain-restricted base rule, duration-bounded" and may already BE this adapter
   (GapThree's own usage is the template — read `Archive/GapThreeTask2/3.lean` call sites).
2. **H4b — reposition adapter.** From `checkDynRepo`-shaped Z3 verdicts (route-A UNSAT per
   invariant component over `(evolveL ∧ evolveR) ∧ strengthenings`, fL = 0, λ = 1) build
   `dynreposition_faModal`'s `hcert` via `flow_cert_sound`; `hExist` at fL = 0 is trivial-ish
   (left constant; right needs existence — the settling `GuardSettlingB` witnesses supply it —
   this is the slim H's role in the new chain).
3. **H5a — witness data emission.** `relcert --emit-cover`: per benchmark per left mode, the
   cover's `(rightMode, λᵢ | reposition)` sequence as a Lean literal (Faithful pattern), with the
   budget arithmetic (`Σ ε_R/λᵢ` fits ε_L) kernel-checked (`bBudget` mirror).
4. **H5b — assembly.** New top theorem: from slim-H (existence) + per-piece joint hyps + reposition
   hyps + emitted cover data → `rvalid (theorem3Form … )` for the uniform-suite graphs; then
   re-run the Faithful bridge on top (real-model form) and regenerate the instance battery with
   the new (Z3-verdict-shaped) residuals. The cadenced ClockedTop chain and `GBoxAll` retire to
   Archive once this lands.
5. **H5c** — suite regression, axiom audit, README/status table update.

## Watch-outs

* `HExistDischarge.lean` is ARCHIVED but is the hExist-discharge seam — likely needs revival.
* `pair_faModal` is at `leftBlock fL`; the clocked left is `clk tg (leftBlock fL)` (extra `(tg, 1)`
  pair) — the adapter must add the clock pair to the LEFT field (fresh `tg`, invisible to `g`/right).
* Static repositions (`reposition_step_pres`) need the `mv`-invisibility facts only.
* The 13 strengthening-reliant benchmarks: their joint-piece queries are narrowed — `cut_hcert`/
  `CutLift` machinery composes here (O1 at the piece's entry region, which the cover provides).
