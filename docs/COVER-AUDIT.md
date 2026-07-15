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
