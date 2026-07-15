# Audit: the tool's cover search vs. the mechanization (task H realign)

Method correction (2026-07-15): the mechanization follows the code. This audit maps
`OracleAPI.coverMode` — the tool's actual per-left-mode certification — onto what is
already kernel-verified, and isolates the one genuine gap. The `UniformMultiflow`
`EmitWindows` device and the hand-built pilot graphs are scheduled for replacement:
they were parallel inventions, and the "off-diagonal SAT" observation they produced
was an artifact of quantifying over configurations the tool never admits.

## What the code does (`coverMode`, per left mode `mL`)

1. **Admissible starts** (`admissible`, FIX 1): the right start modes are those `mR` with
   `guardL(mL) ∧ guardR(mR) ∧ ϕ_rel` SAT. Drop only on definitive Z3 UNSAT. CERTIFIED
   requires EVERY admissible start to cover — the ∀ over initial pairs. This is where
   `(Low_L, High_R)`-style phantom pairs die in the code: they are simply not admissible,
   or they are admissible and MUST be covered (watertank `(Mid_L, High_R)`: admissible,
   covered via the pre-j reposition `High_R → Mid_R`).
2. **Reposition certificates** (λ-independent, per right mode): static pre-j/post-j region
   invariants (`regionUnsat` on `¬inv ∧ region`, region = `guardL ∧ guardR ∧ evolveL ∧
   evolveR` resp. without `guardL`), and dynamic pre-j/post-j right-only flow certificates
   (`checkDynRepo`, frozen left `fL = 0`, λ = 1, whole-domain route A).
3. **Per λ candidate**: joint segment status per right mode (`checkSeg`, the flow query at
   stretch λ over `evolveL ∧ evolveR`, checked-cut narrowed); `δL = εR/λ`;
   `bBudget = ⌈εL/δL⌉` (cap 256); base case fires at `B ≤ 1 ⟺ εL ≤ εR/λ`.
4. **The real graph** (`cgReal`, FIX 2): nodes = modes joint-certified OR reposition-
   certified, carrying the five flags; edges = ALL declared `next` edges, an uncertified
   target mapped to an out-of-range sentinel (so the ∀-over-successors fails there, never
   silently stripped); `pruned` bits from the Def-3 non-connection certificate
   (`nonConnPrune`, both checks UNSAT, strict scalar guards only).
5. **The verified gate**: `decideCovered cgReal fuel ⟨q0, bBudget, preJ⟩` per admissible
   start — the tool runs the kernel-verified checker itself; `dfsCov3` is only untrusted
   search. Initial σ = `preJ`.

Note `cgReal` carries structural placeholders (`sys := []`, `dom := ⊤`): the tool's own
`decideCovered` run checks the STRUCTURE (flags, budget, edges); the semantic content
lives in the certificates (2)–(3).

## What is already kernel-verified (follows the code exactly)

* `Covered` (Checker/Cover.lean) — Definition 4 with base/step + the four σ-matched
  reposition cases; budget strictly decreases (`cover_budget_decreases`); mirrors
  `dfsCov3`/`coverVisit` including the base-`B ≤ 1` fidelity fix.
* `decideCovered` + `decideCovered_sound` — the computable checker the tool actually runs.
* `CoverCert` — one field per certificate kind in (2)–(3), each discharged by a proven
  theorem over the tool's exact query shape (`flow_certified`, region invariants,
  `nonconn_sound` for `pruneSound`).
* `check_sound` : `decideCovered = true` + `CoverCert` ⟹ `CoexecInvThroughout G g cfg ν`
  — the ∀∃-throughout invariant over `RightReach` (joint evolves, budget-gated jumps,
  state-preserving static repositions, genuinely-flowing dynamic repositions, σ-matched).

## The one genuine gap

`CoexecInvThroughout` (semantic co-execution relation) is not yet connected to the
dL-rel modal statement `rvalid (theorem3Form (L-windows)* (R_real)* inv)`. That bridge —
replaying the `Covered` derivation (obtained from `decideCovered_sound`) as the right
response against the clocked left windows — is the real content of H5. `BridgeDischarge.
decideCovered_implies_theorem3_faithful` is the single-flow prototype; the window form
must extend it, with:

* start conditioning = the code's admissibility (`guardL ∧ guardR ∧ inv` at entry,
  `mv = q0`, σ = preJ) — NOT all (window, mode) pairs;
* the graph = the emitted `cgReal` structure paired with the REAL lowered systems
  (RModes with `sys`/`dom`/`dynSys` from the IR at the emitted λ), flags drift-checked
  against the tool's emission;
* witness sequences = the `Covered` derivation's cases (joint piece / reposition), NOT an
  assumed `EmitWindows`;
* per-piece coupling = the existing `segment_faModalB_from_cert` / reposition bridges.

## Realign plan (replaces the `EmitWindows` design)

1. `--emit-cover` door (EmitIR pattern): per benchmark per left mode emit λ, `bBudget`,
   node list with flags, edges + pruned bits, admissible starts — as drift-checked Lean
   literals.
2. In-kernel: rebuild the graph with real lowered systems, re-run `decideCovered` by
   kernel computation, build `CoverCert` from named Z3-verdict hypotheses (the exact
   `checkSeg`/`regionUnsat`/`checkDynRepo`/`nonConnPrune` query shapes).
3. Prove the `CoexecInvThroughout → theorem3Form` bridge (the new proof work).
4. Instances: every tool-certified benchmark instantiates; a benchmark that will not go
   through marks a genuine code-or-proof finding to act on.

## FINDING (R4, 2026-07-15): multi-barrier cross-narrowing unsound for routes A/C

`checkSeg` narrowed EVERY route's query domain by the sibling components (`others ≤ 0`).
For route B (strict boundary) this survives the first-exit argument. For routes A
(domain-wide) and C (superlevel) it is UNSOUND — counterexample `comps = [x², x²]`,
`x' = 1`, domain ⊤: the narrowed domain is `{x = 0}`, route A's query `x = 0 ∧ 2x > 0`
is UNSAT, falsely certifying `x² ≤ 0` under `x' = 1` — the t²-pathology reintroduced
through the conjunction (circular differential cut).

**Fix (soundness-safe: queries only get harder):** `routeQueriesMB` — routes A/C take
the un-narrowed domain (checked cuts retained: independently justified), route B keeps
the narrowing. Soundness of the mixed form: A/C components are independently preserved
(existing single-component theorems); at a first joint exit the exiting component must
be B-certified, all components are ≤ 0 there, and the strict Lie sign contradicts the
exit slope.

**Operational impact (re-run of the 19 multi-component benchmarks):** 5 remain
CERTIFIED (endurance_orderlift_2to3, rover3tier_rung12, story1_attdist_rung_a_6to8,
story1_attdist_rung_b_12dof, story3_rollover_ladder_rung_b); **14 now DECLINE** — their
previous verdicts depended on the unsound narrowing: refinement_ladder rungs 1/2_3to6/
2c/3/4, rover_attitude_cone_12dof, rover_dof_terrain rung1/2/3/3_8d, story2_lateral
a/b, story3_rollover base/rung_a. Suite: 46 → 32 certified.

**Sound strength recovery (proposed, not yet implemented): stratified differential
cuts.** The narrowing is sound when ACYCLIC: prove a component standalone first, then
add it to the others' domains (iterate to a fixpoint — sequential DC, not circular).
Strictly stronger than the fix, may re-certify part of the 14. Requires: tool loop in
`checkSeg` + the domain-refinement lemma in Lean (runs staying in a proven invariant
are runs of the narrowed-domain ode — `ODESol_restrict` + pointwise BoxLe, the
CutLift pattern).
