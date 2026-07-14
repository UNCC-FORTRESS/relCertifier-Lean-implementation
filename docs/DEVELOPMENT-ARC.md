# The development arc — how the proofs, the tool, and the benchmarks converged

This documents the project's three development arcs: what was attempted, what was *found* (several
claims widely assumed in the early design turned out to be false, and are now mechanized
counterexamples), and what shipped. It is the narrative companion to the README's theorem
walkthroughs — read this to understand *why* the final design looks the way it does.

Conventions throughout: every stage landed sorry-free with `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (plus `z3_unsat_sound` exactly at the Z3 leaf);
later layers never modified shipped theorems (non-breaking); negative findings were mechanized
as theorems, not noted and forgotten.

## Arc 1 — the transition-faithful chain (`tooling_sound`)

**Goal.** Close the gap between "the checker said CERTIFIED" and "the paper's ∀∃ refinement
holds over the actual input programs."

**Path.** `theorem3_faithful` (the ∀∃ over the *real* right automaton `R_real =
star(rightAutomatonBody)`, jumps only along declared edges) → `decideCovered_implies_
theorem3_faithful` (the hstep discharged from the cover certificate, not assumed) → GAP 1
(genuine multi-flow: the right switches modes *within* one left residence, coupled per
fixed-budget `dt = ε_R/λ` segment via a fresh clock that is later collapsed —
`plantT_split_iter`, `faModalB`, `clockLift_collapse`; repositions as a frozen left mode the
loop interleaves) → GAP 2 (the whole left automaton, per-mode covers composed with the right's
mode carried in the state variable `mv`) → GAP 3 (`graphOf(L,R)`: the graph↔program alignment
*derived* from the graph's construction, making the theorem about *your* `L` and `R`) →
**`tooling_sound`**.

**Findings (all mechanized).**
- The **flat choice-star** right program is a strictly *weaker* ∀∃ than the declared automaton —
  valid but not the paper's claim. Fixed by `R_real`.
- `rvalid` over a bare invariant is **false**: at bi-states whose mode variable holds an
  undeclared index the automaton is stuck and the ∃-side is empty. The sound statement carries
  `mvValid` in the invariant.
- **Freshness needs a third variable side.** The mode variable and the clock cannot live in the
  left or right coordinate blocks: a "frozen left coordinate" satisfies the named freshness uses
  but makes the left/right variable-disjointness hypothesis **unsatisfiable**
  (`ProbeMvHd.probe_hd_false`). `Side.Aux` was added. Lesson: check a hypothesis's
  satisfiability against *all* antecedents, not just the ones that name it.
- `∀ν HExistSeg` (the duration-existence side-condition quantified over all states) is **false
  for bounded evolution domains** — an out-of-domain start is frozen by the left run into a
  domain-violating right start. It is dischargeable at `domR = ⊤` by global existence
  (demonstrated for the affine field), and this is field-shape-independent.
- The ⊤-edge model is an **encoding-layer** relaxation only: the coverage relation
  (`RightReach.jump`) carries the real guard, so a coverage witness is a legal guarded run
  (`witness_is_guarded_execution`).

## Arc 2 — the landing chain (the automaton-right star)

**Goal.** Certify the more demanding shape where the right is a mode-switching automaton run
under a star, discharging the ∃-witness existence per segment with *no* assumed guard-reaching
and *no* first-passage computation.

**Path.** Landing-*selected* dispatch: run the segment flow, then choose the automaton branch by
where the constructed endpoint actually **landed** (a membership check), with the endpoint's
domain fact carried through the body step (`starStep_wrap`) and a strengthened threaded star
invariant (`starInvF` = invariant ∧ mode-validity ∧ current-mode-domain-membership) dissolving
the ∀-state seam that had blocked every earlier composition. Folded onto the clocked substrate
(per-`dt` pieces, collapsed back to the physical model by `clockLift_collapse`) and reified to
the shipped `rvalid` layer: `theorem3_faithful_landing_clocked(_wf)`.

**Findings (all mechanized).**
- `WellFormedFlow` — the ∀-duration staying hypothesis ("the mode's flow stays in its domain for
  every duration") — is **false** for growing-bounded fields (`WellFormedFlow_rover_false`:
  a constant-acceleration coordinate exits any bounded domain). 33 of the 47 benchmarks have such
  a coordinate. The honest form is duration-bounded (`WellFormedFlowB`, one `≤ dt` segment) —
  and even that is false when quantified over **all** domain bases
  (`WellFormedFlowB_rover_boundary_false`: a base *on* the boundary exits immediately).
- The narrowing/reaching machinery (`SuccReach`: "the flow reaches the successor's tighter
  domain") is falsifiable at faithful domain boundaries, and its tempting disjunctive weakening
  is **vacuously true** (`SuccReachUnion_vacuous`) — a mechanized anti-collapse check that killed
  a wrong generalization early.
- The landing membership hypothesis (`LandingH`) turned out to be a **tautology** — the dispatch
  only ever needs the current-mode disjunct and the self-edge. The junction was never the deep
  problem; the staying obligation was.

## Arc 3 — uniform evolution domains, settling, and the checked-cut channel

**Goal.** Make the staying obligation *true and discharged* rather than carried, and align the
benchmarks, the certifier's queries, and the Lean theorems on one design.

**The diagnosis (empirical — the certifier as arbiter).** Naively unifying each benchmark's
per-mode evolution domains to their join broke 20 of 46 certifications. Per-variable bisection
showed why: per-mode evolution domains had been silently **carrying reachability facts** (a
mode's `v ≤ equilibrium` cap with nothing in the model enforcing entry below it). The flow
queries read the evolution domain as ground truth, so an unjustified tightening narrows the
proof obligation invisibly — the "reachability-in-evolve" defect class.

**The design.** *Uniform evolution domains* (one shared physical envelope per side, strictly
containing every guard) make the junction trivial and retire the narrowing machinery; *guard-
enforced settling* (growing modes switch away from the envelope with margin exceeding one-step
travel, `margin > max-rate·dt`; stabilizing modes contract to an interior equilibrium) makes the
staying obligation a consequence of geometry. `benchmarks/suite_uniform/` instantiates it —
after diagnosing and legitimately fixing all 13 initially-declining benchmarks (the fix
principle: a per-mode fact is admissible **iff guard-derivable** — entry guard + dynamics prove
it; terrain speed caps moved into the guards, exactly at the equilibrium), the suite certifies
**46/47**, the same ceiling as the pre-discipline form (history: `git log -- benchmarks/suite`).
The discipline costs nothing and removes every unchecked domain declaration.

**The proofs.**
- `UniformEvol.lean`: the uniform re-point (`theorem3_faithful_landing_clocked_uniform`, junction
  content deleted from the hypothesis), `staying_from_margin` (mean value: a rate-bounded flow
  from a guard-capped base cannot cross the margin in one segment), and
  `WellFormedFlowB_contract` (a contractive coordinate with interior equilibrium makes the
  envelope forward-invariant — the ∀-base staying is discharged outright, explicit exponential
  witness). A structural fact fell out: ∀-base staying is dischargeable **only** on
  forward-invariant envelopes, and growing fields have none — so guard-base restriction is
  fundamental, not a proof limitation.
- `GuardThreaded.lean` (Tier B): the star invariant strengthened to "the state is in its current
  mode's **guard** region" (a guard map parameter — the graph's mode records carry no guards),
  so the staying obligation quantifies only over guard bases, where the settling geometry
  discharges it by construction (`GuardSettlingB_of_margin_const`, `GuardSettlingB_of_contract`);
  `theorem3_faithful_settling` re-derives the same `rvalid` conclusion on that foundation. The
  clocked chain needed no change — it was invariant-generic all along.
- The **checked-cut channel** (`OracleAPI.checkedCut` + `CutChannel.lean`): mode-specific facts
  enter the certifier as *differential cuts that the certifier itself re-derives* before use.
  Candidates are the guard's non-strict atomic conjuncts (plus an optional per-mode
  `strengthen =` input field); a candidate narrows the query domains only after **O1** (entry:
  the guard implies it) and **O2** (invariance along the mode's own field — the same DI routes
  as the main certificates, plus a tangent-capable contract-shape check) both certify, under a
  greatest-fixpoint filter. Failures are silently dropped: completeness-only, never soundness.
  The evolution domains are **never modified**, so the model matches the uniform proof structure
  exactly; `boxLe_cut_lift` proves the narrowed certificate lifts back to the uniform-domain
  obligation the proof consumes. One unsoundness was caught during this build: a *strict*
  candidate atom sitting in its own invariance domain vacuously passes the boundary route (the
  boundary contradicts the strict atom) — excluded by the non-strict candidate discipline and
  self-exclusion.

**The principle the arc converged on** (and the reason the final design is what it is):

> **The evolution domain means physics, and it is shared. Mode-dependent behavior enters through
> the guards, where the model enforces it. Anything tighter than the shared envelope must be
> re-derived — by the certifier at run time, or by a Lean discharge lemma — never asserted.**

Every earlier failure mode of the project is an instance of violating this: the guard-narrowing
bug (unjustified query narrowing), reachability-in-evolve (unjustified domain tightening), the
∀-duration and ∀-base staying overclaims (asserting staying the dynamics don't provide). The
final stack makes each of these either impossible by construction or a checked obligation.

## Arc 4 — the verified well-formedness checker (the reduction, mechanized)

**Goal.** Turn per-benchmark soundness into a computation: prove ONCE that a decidable check on
the model data implies the settling hypothesis, so a benchmark verifies by running two programs
(the checker + the certifier) with no bespoke proof.

**Path.** `SettlingModel` (integer model data — `Rat` arithmetic does not kernel-reduce, an
early forced design fix), `decideWellFormed` (pure integer/structural checks: envelope ⊋ guard
bands, per-mode settling by shape, successor validity), and **`wellformed_sound`**: checker
passes + per-run Z3 certificates ⟹ `GuardSettlingH` ⟹ `rvalid`. Built in proven increments,
each an explicit-witness discharge lemma: single-active-coordinate (constant/affine/exponential
witnesses), driven-by-const integrators (quadratic — the rover class), driven-by-contract
integrators (exp-integral — the terrain-dynamics class), signed rates (the Return modes),
frozen-driver coordinates, and the **EXT 4 union landing covers** (a TRANSIT mode's one-step
image spans its own band plus one touching successor band — const rates both signs, and
contract modes with the equilibrium above/below their band via the hull `[band, c]`; landing
discharged by an endpoint case-split). 21 of 47 benchmark data terms are in-grammar; **16
carry closed kernel `rfl` certificates**.

**Findings (the honest ones).**
- The guard map must be envelope-intersected (`GdOf = envF ∧ band`) or the hypothesis is
  vacuously false for every multi-coordinate model — caught at statement time.
- An unverified claim died the right way: 18 instances were reported as certificate-pending on
  a "kernel-reduction quirk" — `#reduce` showed the checker genuinely REJECTS them, i.e. the
  kernel had been refusing a false proposition all along. Root cause was one completeness gap:
  the landing rule demanded a single band contain the one-step image, but TRANSIT modes cross
  from their own band into a successor's. The union-cover extension (EXT 4, now proven) plus
  per-instance segment-budget selection (`dt = ε_R/λ` is a free parameter of
  `theorem3_faithful_settling`, constrained only by the `k·dt` budget cover — so each instance
  picks the largest in-range dt the checker accepts) closes 13 of the 18. The episode is the
  architecture's argument in miniature: the untrusted layer asserted, the kernel refused, the
  record was corrected.
- Two smaller findings from the EXT 4 deployment: a frozen ACTIVE coordinate with driven
  others is `constRate 0` (the identical field) — the flex-others grammar comes for free, no
  new lemma; and `arm_chain_rung2`'s right `Return.next = [ApproachFast]` was a DEAD edge
  under partitioned guards (the drain cannot cross the intermediate band in one step) — the
  cover analysis exposed it, the edge was corrected to the actual landing successor, and the
  benchmark still certifies.
- **The H-falsification audit** (`scripts/h_audit.py`): the settling hypothesis's landing
  geometry is decidable arithmetic even where the PROOF grammar can't express its discharge —
  so its *falsity* is hunt-able by numeric simulation (RK4 per sampled guard base, every legal
  integer λ) without any Lean. Run over the out-of-grammar benchmarks it split "unknown" into
  two honest classes. (a) NO counterexample at some legal λ: attitude_rate,
  endurance_orderlift_2to3, rover_4d_box, rover_drag, and the four parked exp-bound terms —
  hypothesis believed true, only decidability/grammar missing. (b) Genuinely FALSE as modeled,
  one witness shape — **terminal-band overflow**: the last mode's band is capped with positive
  drift toward or through the cap and no successor beyond it (the terrain/story/refinement
  family's final `s`-segment `s < 899.95` under `evolve s ≤ 1000`; rover3tier_rung12,
  rover_tier_r1; match_multi_rate's `v ≤ 0.95` under an equilibrium at `1.0`). These need a
  modeling decision before any checker extension helps — unbounded terminal segment (the
  honest-envelope principle applied to `s`) or a band reaching the equilibrium.
  match_multi_rate was fixed on the spot (band cap 0.95 → the equilibrium 1.0, DRIVE becomes
  contract-inside): it re-certifies and its `rfl` certificate closes — 17 of 21. An audit
  lesson repeated the arc's theme: the first audit run flagged spurious witnesses because the
  sampler ignored `Gd = envelope ∧ band`; verify the counterexample before correcting the
  record.
- **The rational-gain extension (`contractQ`), closing the exp-bound class.** A new
  non-breaking shape `CoordShape.contractQ kn kd c` stores fractional gains exactly; the
  checker's transit cover uses the finite-dt landing cap `ghi + (c − ghi)·(kn/kd)·dt`,
  cross-multiplied by `kd > 0` so it kernel-reduces in ℤ, and
  `settling_contractQ_above/_below` discharge it from `1 − e^{−x} ≤ x`
  (`Real.add_one_le_exp`) — the flow can't cover more than an `x`-fraction of its remaining
  gap in `x` time-constants. The linear cap sufficed for all four parked benchmarks (checked
  numerically first, then by kernel `rfl`): watertank (gain 3/25, λ = 1), match_multi_eps and
  rover3tier_M1 (gain 1/25 in scaled time, λ = 5 — the ACCEL cap lands with 2‰ of band to
  spare: 0.648 ≤ 0.65), robot_braking (gain 1/2, λ = 2). **All 21 in-grammar data terms now
  carry closed kernel certificates.**
- **The terminal-band fix (the audit's H-false class, resolved).** All 21 flagged benchmarks
  carried an unenforced upper cap on the drifting coordinate — the final terrain segment's
  `s < 899.95` under `evolve s ≤ 1000`, or a velocity cap under constant positive
  acceleration — i.e. the reachability-in-evolve defect class again, this time in the guards.
  Fix per the honest-envelope principle: the terminal band is unbounded above and the
  unenforced evolve caps are gone (nothing in the dynamics ever enforced them). All 21
  re-certify, and the audit finds NO H-counterexample on any of them afterwards. Status after
  this pass: **every certified benchmark is either H-PROVEN (the 21 in-grammar kernel
  certificates) or audit-clean** (no counterexample at some legal λ, awaiting the EXT 3 /
  phase D grammars); shield_unreachable (no guard band, inconclusive-Z3) remains the one
  intentional outlier.
- **EXT 3 (the terrain checker), built.** A `TerrainModel` WRAPS a `SettlingModel` and adds
  per-mode s-bands, so the entire transcription stack (envelope, graph, graph lemmas) is
  reused verbatim and `GuardSettlingH`'s guard-map parameter absorbs the new box guard —
  `theorem3_faithful_settling` consumes `wellformed_sound_terrain` unchanged. The discharge
  (`settling_terrain`): the contract velocity stays in `[v₀, c]` (cap at the equilibrium —
  the guard discipline from this arc's own fix list), the integrated position's one-step
  image sits in `[s₀, s₀ + c·dt]` and lands by an endpoint case-split at the segment edge
  (`shi + c·dt ≤ shi'` per declared successor, terminal segment unbounded), and decaying
  others stay in the hull of base and equilibrium. 5 terrain benchmarks carry closed kernel
  certificates (refinement rung1, dof-terrain rungs); the nonlinear-`s'` variants
  (`s' = v(1 − 0.5ψ² − 0.3θ²)`, cubic rungs) remain phase D.
- Remaining roadmap: phase D (coupled/nonlinear fields — attitude_rate,
  endurance_orderlift_2to3, rover_drag, rover_4d_box, the nonlinear-`s'` terrain/story
  variants; existence via `PicardBridge`).

## Current state

- **Suite**: `benchmarks/suite_uniform/` (canonical, the paper's benchmark set) — 46/47
  CERTIFIED, 1 inconclusive-Z3 ERROR (`shield_unreachable`), literal shared evolution domains on
  all 47, mode physics in guards, cuts re-checked on every run.
- **Theorems**: `tooling_sound` (Arc 1), `theorem3_faithful_landing_clocked_uniform` +
  `theorem3_faithful_settling` + `boxLe_cut_lift` (Arcs 2–3), `wellformed_sound` (Arc 4);
  all axioms-clean, the Z3 leaf only at certificate construction.
- **Trust boundary**: unchanged throughout — `z3_unsat_sound`, the parser, and nothing else.
