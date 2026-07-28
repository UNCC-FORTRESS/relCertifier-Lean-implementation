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

### Stratified DC implemented (2026-07-15, follow-up): FULL RECOVERY, 46/46

`checkSeg` now runs the acyclic fixpoint: a component narrows its domain only by
components proven in earlier rounds (sequential differential cuts; ≤ |comps|+1 rounds).
Census: **all 14 previously-declining benchmarks re-certify**, and the full suite is
back to 46/46 — now under a SOUND coupling discipline. The invariant families are
genuinely stratified (velocity components certify standalone; position offsets then
assume them), confirming the structural prediction.

Lean debt (R4 mechanization, open): the domain-refinement lemma (runs pointwise inside
a proven invariant are runs of the narrowed ode) + the stratified `multi_barrier_sound`
assembly + the list-generalized invariant through the modal chain. Until it lands, the
multi-component verdicts rest on the paper argument in this section, kernel-checking
pending.

## R6 status (2026-07-16, overnight)

Strict-face viability landed: `BoxViability.lean` (`strict_faces_endpoint/raw` —
multi-face box-conditioned first-exit; `box_viability` — Picard + chainN, any duration;
`face_strict_from_verdict` — the Z3 leaf as frozen-left `flowQueryStrict`, no new query
surface). Tool: `checkViability` + `--emit-viability`; `BenchViability.lean` emitted.

Census: 9/126 right modes pass all-faces-strict (compact self-invariant boxes: drag,
level bands; watertank Low/High). The rest decline LEGITIMATELY — integrator
coordinates (`s' = v`) exit their boxes in finite time, so unbounded-horizon viability
is false; the correct general certificate is BOUNDED-TIME viability: strict faces +
growth faces (`Lie ≤ M` on the box) + the per-piece entry-budget query
(`s₀ + M·ε_R ≤ s_max`) — `growth_bound_raw`/`hExist_multi`'s pattern folded into the
same first-exit lemma (growth faces cannot exit before the horizon by the budget).
Follow-up: `box_viability_bounded` + the budget query family + per-mode instance
wiring; until then declining modes carry the named per-mode single-system hypothesis —
within the frozen contract.

---

## Note (2026-07-19): why the right automaton carries no guard test in the program

Raised by the question "is the mechanization consistent with the writeup's `cpsProg`?",
whose loop body is `?(m ∈ next(mv)) ; ?guard_m(x) ; mv := m ; {x' = f_m(x) & evolC_m}`.
The mechanized `modeStep` (`Proofs/Encoding/JointBridge.lean:34`) is the same up to
rotation — `?(mv = q) ; ODE_q ; ⋃_e (?e.guard ; mv := e.tgt)`, guard between the two
flows either way — but **every constructed graph sets `e.guard := Formula.tt`**
(`CoverInstance.lean:154`, `CoverEmit.lean:86`, and the modal flagship's `edgeW` in
`WatertankModal.lean:72`, where `httW` *proves* all `GrW` edge guards are `tt`).

**This is by design, and the guard is not discarded — it does its work in the
certificate rather than in the program.** There is no reliable general reachability
analysis available, so the cover cannot know which successor the implementation will
take. It therefore treats the mode choice **demonically**: `decideCovered`'s joint step
is `(retainedSucc q).all (…)`, requiring the continuation to work for *every* declared,
unpruned successor (`retainedSucc` always includes `q` itself,
`Checker/Cover.lean:107`). Against that backdrop the guard has two jobs, both
soundness-load-bearing, neither of which a program test would serve:

1. **Pruning — the partial reachability analysis.** `nonconn_sound`
   (`Checker/NonConn.lean:101`) concludes
   `∀ ω, Program.sem (ode sysR domain) ν ω → ¬ Formula.sat o.guard ω`: from an
   admissible entry, no state reachable by the mode's own flow satisfies the
   successor's guard, so that edge is dropped from `retainedSucc`. This shrinks the
   demonic ∀ exactly where unreachability can be *proven* (Nagumo barrier; strict
   scalar guards only — a closed guard has a boundary the strict barrier cannot
   exclude). Deliberately conservative: prune only when both checks are definitively
   `unsat`, otherwise keep the edge, so a query bug can over-decline but never
   false-certify.

2. **Domain strengthening — narrowing where the flow certificate must hold.** The
   entering guard's lower bound becomes a cut atom, maintained through the residence by
   differential induction, which narrows the region in which the Lie-derivative query
   must be discharged. Watertank makes the derivation visible: L `Mid` guard
   `x ≥ 13 ∧ x < 20` → cut `x ≥ 13`; R `Mid` guard `x ≥ 10 ∧ x < 17` → cut `x ≥ 10`;
   both `Low`s → `x ≥ 0` (`Instances/EvolStrengthenings/watertank.lean`). This is
   precisely why guard-at-entry is the load-bearing half of the folded
   successor-completeness contract: the atom holds at entry *because* the guard did, and
   DI carries it forward. Consumed by the 13 cut-reliant benchmarks via `RightReachG`'s
   `Gd`.

**Consequence for fidelity.** Because the treatment is demonic, the guarded
automaton's transitions are a *subset* of what is already certified, so everything
proven covers `cpsProg`. Making the automaton more permissive by omitting the test makes
the proof harder, not weaker. The only property not literally covered is
**non-blocking** — that the guarded automaton always has some enabled successor, without
which it has no run to exhibit at all. That is standard hybrid-automaton
well-formedness and belongs beside the existing successor-completeness item in the
paper's declared assumptions; it is not a certifier obligation.

**Actions.** None required for soundness. Optional: (a) one line in the paper's
assumptions covering non-blocking; (b) if the displayed program should read literally
like the instances, present it without the `?guard_m` test and explain the two roles
above; (c) note the rotation (flow-then-jump vs jump-then-flow) in one sentence, or
re-shape `modeStep` to match the writeup — cheap to write, but upstream, so batch it
with any other world-rebuild work.

*Record: this entry was initially filed as a soundness/fidelity finding and twice
narrowed before reaching the account above. The error was reasoning about the ∃
direction of `theorem3Form` before reading how `decideCovered` quantifies over
successors.*

**Minor, confirmed faithful:** `?(m ∈ next(mv))` is encoded structurally (the `edges`
list, built from `Run.succOf`), and R1 verified every benchmark mode declares itself in
`next`, so staying put is always available.

---

## Finding (2026-07-19): the parser silently drops unknown keys

`Trusted/Parse.lean` is in the trust base and its stated contract is **"the parser
REJECTS, never weakens"**. It honours that for malformed input and even rejects one
*retired* key by name (`strengthen`, `Parse.lean:394-395`). But it **silently ignores
unknown keys**: `parseModeE` (`Parse.lean:367-397`) `secNeed`s exactly `ode`, `guard`,
`evolve`, `next`; anything else in a `[*.mode.*]` section is dropped. `assembleE`
(`Parse.lean:435-457`) likewise `secNeed`s only `name`, `lambda_min`, `lambda_max` from
`[problem]`.

**Verified against HEAD (2026-07-19).** All **47/47** benchmarks carry a `max_depth`
key; `Parse.lean` mentions `max_depth` **zero** times. So every benchmark in the suite
already contains a key the parser never reads.

**Demonstrated.** Inserting `reset = x := 1.0` into two mode sections of watertank and
running the tool:

```
wtreset: CERTIFIED (665ms)
errors=0
```

The reset was discarded and the model certified green — a certified object different
from the file the user believes was certified, with no warning.

**Why it matters.** The parser decides *which model the kernel certifies*. This is the
same silent-weakening class the project already closed once (trailing tokens after
`smt2:` s-expressions, `Parse.lean:243-252`). It is also a hard prerequisite for reset
support (`docs/RESET-MAPS-SCOPE.md` §0): any reset syntax added on top of this door
inherits the trap.

**Fix** (no kernel changes, no regeneration of generated instance files; about an hour):

1. Whitelist known keys per section and `throw` on anything else, following the existing
   `strengthen` rejection style:
   - mode sections: `ode`, `guard`, `evolve`, `next`
   - `[problem]`: `name`, `lambda_min`, `lambda_max`, plus known-but-unused
     `max_depth`, `bound_T`
   - system sections: `state_vars`, `epsilon`
   - `[relational_invariant]`: mode names (already validated, `Parse.lean:464-486`)
2. Put `max_depth` / `bound_T` on a *known-but-unused* list rather than stripping them
   from 47 files — cheaper, and keeps the published files as they are.
3. Reject-tests in the parser battery (`Test.lean`, the existing `bad "…" (skel …)`
   style): unknown key in a mode section, unknown key in `[problem]`, typo'd key
   (`guardd`).
4. Re-parse the whole suite to confirm 47/47 still load.

Status: **not fixed** — recorded as actionable. Originally raised in the QRC-paper
thread (`relcertifier-handoff.md`, item A), now reconciled into this repository.
