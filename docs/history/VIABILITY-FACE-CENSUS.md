> **HISTORY (moved to `docs/history/` on 2026-10-10).** A superseded record, kept for
> provenance; `docs/history/README.md` says what replaced it. Paths, file names and counts
> below describe the repository at the time of writing, not the current artifact.

# Viability face census — measured, 47 benchmarks

> **Note (2026-10-08).** Census taken on the 46-benchmark suite. After the removal of six duplicate benchmarks (`SUITE-DEDUPE.md`) the committed `BenchViability2.lean` lists 1085 faces (36 fewer: 8 + 4 + 6 + 8 + 4 + 6 for `arm_fidelity_high`, `arm_refinement`, `match_multi_eps`, `plant_fan_high`, `plant_fan_low`, `plant_fan_mid`); the per-face findings below are unchanged.

> **UPDATE (2026-07-30).** The census measurements below stand. The *route* columns do
> not: every face class now has a Lean route and all of them are instantiated. Non-strict
> faces go through `Proofs/Flow/StratifiedFaces.lean` (strata, no Nagumo needed); the 45
> affine/equilibrium faces through `AffineFaces.lean` (with the auxiliary-strict-face
> trick that supplies the ball bound); monotone lower faces through `AffineFaces2.lean`
> (L1d). Where a face class was awkward, some benchmarks instead use an explicit
> closed-form witness (`rover_tier_r1`) or a right-only response that needs no viability
> certificate at all (the five catch-up instances). Existence is proven — not
> hypothesised, and not Z3-backed — in all 46 modal instances; see
> `docs/CERTIFICATION-CHECK.md`. Read "not available" / "unscoped" below as historical.


**Measurement only. Nothing built.** Answers: can the right system blockingly escape its
evolve envelope, which is the one open question whose answer could have been "no".

**Answer: no. Zero hopeless faces, zero ambiguous faces.**

## Method

For each benchmark, each right mode, each bounded coordinate of the right evolve
envelope, both faces (upper and lower):

- the face term is `gT = v − hi` (upper) or `gT = lo − v` (lower); inside is `gT ≤ 0`
- the flow is `rightBlock fR lam`; the piece duration is `dt = εR/λ`, so a growth budget
  `M·dt` scales as `λ·M·(εR/λ) = M·εR` — **λ cancels**, and εR is the only scale that matters
- the field is evaluated by interval arithmetic, **with the face coordinate pinned to its
  bound** (evaluating over the whole box instead is what makes a relaxation field like
  `3(0.65 − v)` look outward when it is strictly inward at `v = 0.8`)

Interval arithmetic over-approximates, so "strict" and "non-strict over the whole box"
are sound classifications; "outward" and "face-only" may be pessimistic.

## Result — 1133 faces

| class | faces | benchmarks | route | state |
|---|---|---|---|---|
| strict inward on the face | 582 | 47 | `face_strict_from_verdict` (R6) | **built** |
| non-strict inward, holds over the whole box | 474 | — | `nonstrict_antitone_raw` ([PicardBridge.lean:220](../RelCertifier/Proofs/Flow/PicardBridge.lean:220)) | **exists, already used** |
| non-strict inward **on the face only** | 45 | 8 | genuine sub-tangency (Nagumo) | **not available** |
| outward, box slack exists | 32 | 14 | growth budget + anchor Z3 | lemma exists, verdict unverified |
| ambiguous (both signs on the face) | **0** | — | — | — |
| hopeless (`M·εR` > box width) | **0** | — | — | — |

## Reading it

**The suite does not have a physics problem.** Every face is inward, non-strictly inward,
or outward with enough slack that a budget can exist. The R6 census figure of "9/126
strict-pass" was never evidence of escape — it was evidence that the strict-only test
covers about half the faces and says nothing about the rest.

**The dominant remaining item is non-strict invariance, not viability.** 474 of the 519
non-strict faces satisfy `Lie ≤ 0` over the whole box, which is exactly the along-curve
premise `nonstrict_antitone_raw` takes — the lemma is in the repo and already carries the
`s ≥ 0` faces. Those 474 are wiring.

**The residual hard set is 45 faces across 8 benchmarks** — `Lie ≤ 0` holds on the face
but not throughout the box, so `nonstrict_antitone_raw` does not apply directly and the
boundary-only check is unsound (`nonstrict_boundary_insufficient`, the t² trap). Nagumo
sub-tangency is not in the vendored Mathlib.

Affected: `endurance_orderlift_2to3`, `refinement_ladder_rover_rung4_8to12`,
`story1_attdist_rung_b_12dof`, `story2_lateral_rung_a_8dof`, `story2_lateral_rung_b_12dof`,
`story3_rollover_ladder_rung_b`, `robot_braking`, `watertank`.

A stratified argument is the likely escape, mirroring R4's sequential differential cuts:
prove a stronger invariant first that confines the state to the region where `Lie ≤ 0`,
then apply `nonstrict_antitone_raw` there. Not scoped.

**The 32 outward faces have box slack but unverified anchor budgets.** Slack in the box
means such states exist; the obligation needs *every* `inv ∧ env` anchor to clear the
threshold. That is a Z3 UNSAT query (`inv ∧ env ∧ gT + M·εR ≥ 0`), consumed by
`anchor_budget_from_verdict` ([ViabilityWiring.lean](../RelCertifier/Proofs/Flow/ViabilityWiring.lean)).
The relational invariants constrain L−R differences, so whether they confine a single
right coordinate below its own bound is benchmark-specific and **not predictable from
geometry**. Running those queries is the next measurement.

## Anchor budgets — RUN (Z3, 74 queries)

`UNSAT(inv ∧ envL ∧ envR ∧ gT + M·εR ≥ 0)` for every outward face of the 13 benchmarks
carrying one, under every declared left-mode invariant.

**74/74 SAT.** The growth-budget route closes for none of them. Cause is structural, not
looseness in `M`: the outward fields are constants (`theta' = 0.2`, `vx' = 0.4`), so `M` is
exact, and the relational invariants bound L−R differences (`px_l ≤ px_r + 0.5`) and say
nothing about how close a right coordinate sits to its own bound.

Encoding validated by controls on `rover_position`: `inv ∧ env` sat; `gT + 1000 ≥ 0` sat;
`gT − 1000 ≥ 0` unsat; `vx_r > 1.1` unsat.

## What the budgets actually cost — only landing modes matter

Existence is needed at the mode a window's pieces live in — the **landing mode** `q*`
(jointOK, self-loop, reachable from every mode). Hops are zero-duration, so intermediate
modes need nothing. Re-measuring against landing modes only:

| | benchmarks | |
|---|---|---|
| landing mode's faces all strict or whole-box non-strict | **34** | existence route clean |
| landing mode has an equilibrium/face-only face | **7** | existence **TRUE**, needs the non-strict/asymptotic lemma |
| landing mode has a genuinely outward face | **5** | existence **FALSE as stated** |

**Group B (7)** — `endurance_orderlift_2to3`, `refinement_ladder_rover_rung4_8to12`,
`story1_attdist_rung_b_12dof`, `story2_lateral_rung_a_8dof`, `story2_lateral_rung_b_12dof`,
`story3_rollover_ladder_rung_b`, `watertank`. All relaxation/decay shapes (`y' = −y` at
`y = 0`; `psi' = ω − psi` at `psi = 0.6`; watertank `x' = 3(1 − 0.04x)` at `x = 25`). The
flow does not cross the face. `asymptotic_invariance_raw` (PicardBridge) is the affine-chase
route already used for shapes of this kind.

**Group A (5)** — `arm_chain_rung1`, `arm_chain_rung2`, `arm_fidelity_low`, `arm_refinement`,
`plant_fan_low`. All `theta' = ±0.2/0.3` constant against `theta ∈ [0, 1]`.

Worked case, `arm_chain_rung1` window `ApproachFast` (λ = 5/2, k = 3, εL = εR = 1):
`dt = εR/λ = 0.4`, and over one piece `theta_r` moves `λ·0.2·dt = 0.2`. So a full-duration
piece in `Approach` needs `theta_r ≤ 0.8` at the anchor. The invariant is
`theta_l ≤ theta_r + 0.4` — it does not bound `theta_r`, and `theta_r = 0.9` is both an
admissible anchor and reachable in-mode (the right enters `Approach` at `theta_r ≤ 0.7` and
flows up). `Return` stays in the envelope from there, but the cover says `Return` is **not**
joint-certified for that window (`repoPre`/`repoPost` only — static, zero-duration).

So under the available composition — `multiseg_clocked` pairs **one right ODE per left
piece** — there is no witness. Both candidate modes fail, for different reasons.

**This is NOT "existence is false."** The statement's right program is
`star (rightAutomatonBody Gr mv)`, which permits a response that switches modes *inside* one
left piece: flow `Approach` for `s₁`, jump, flow `Return` for `s₂`. `faModalB`'s `Q` is an
arbitrary program, so the statement admits it. What is missing is the machinery: a coupling
that splits one left piece against a **sequence** of right modes, with the invariant carried
across the switch point. `segment_faModalB_from_certB` produces the coupling for a single
joint ODE only.

Group A therefore needs a *finer* decomposition than the current lemmas support — not a
different landing mode, and not a stronger viability certificate. Unscoped.

### Correction to `KGT1-ASSEMBLY-SCOPE.md` §4

That measurement — "hop prefix + k self-loops suffices, extraction off the critical path" —
tested **certificate** coverage, and holds for that. It does not settle **existence**: for
Group A the right must leave the landing mode to stay in its envelope, and the departure is
not aligned with left piece boundaries. The gap is intra-piece, so piece-sequence extraction
from the `Covered` derivation would not close it either.

## Validation

The census independently reproduces a previously recorded fact: watertank's `Mid` mode is
the single face-only case in that benchmark — `x' = 3(1 − 0.04x)` is exactly `0` at the
evolve bound `x = 25`, while `Low` (`−1.5`) and `High` (`−2.7`) are strictly inward there.
That equilibrium-on-face case was noted during R6 design and the measurement finds it
without being told.
