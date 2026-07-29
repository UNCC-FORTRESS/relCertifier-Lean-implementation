# Plan — Theorem 3 instantiated for all 46 benchmarks

**Scope document. Nothing built.** Consolidates the measurements of 2026-07-28.

Target: `rvalid (theorem3Form L R φ)` for every certified benchmark, i.e.
`φ → [α*]⟨ρβ*⟩φ` with the relational invariant as `φ`.

> **CORRECTED — read [`LEMMA-SCOPE.md §0`](LEMMA-SCOPE.md) first.** This document's W1 treats
> existence as emission work unlocking 19 benchmarks immediately, with the hard non-strict
> case isolated to 7. That split is wrong: `HExistSegB_of_viability` has no face class for
> non-strict inward faces, only 2 of 47 benchmarks have all-strict faces, and the non-strict
> class is on the critical path for essentially every benchmark. The **work items W2/W3/W5
> and all the counts below stand**; the W1 increment does not.

Evidence tags: **[V]** read in source · **[M]** computed from emitted data or Z3 ·
**[I]** reasoned from definitions, not built.

> **SECOND CORRECTION (2026-07-29 re-scope) — the uniform route is a type mismatch.**
> `theorem3_uniform_from_covered` consumes `RightProjAlignV`, which bundles
> `∀ ν, HExistSeg …` ([UniformMultiflow.lean:229](../RelCertifier/Proofs/Encoding/UniformMultiflow.lean:229))
> — the **unbounded, unconditioned** existence the S1 finding established false in general,
> and which L1a cannot produce (L1a yields the envelope-conditioned, dt-bounded
> `HExistSegB`). So "copy `rover_drag`" does not compose with the existence plan: the
> rover_drag pilot carries that `hES` as an assumed residual, and even for rover_drag it is
> unwritten. **Resolution: route all 46 through the modal chain.**
> `theorem3_faithful_multiE_LR` + `hstep_assembled_multiE`
> ([EnvelopeChain.lean:387](../RelCertifier/Proofs/Encoding/EnvelopeChain.lean:387), :124)
> are fully generic — arbitrary `leftProgs`, an `Hmulti` provider over `inv ∧ env`, couplings
> from `segment_faModalB_from_certB`, which takes exactly `HExistSegB`. The 9 all-joint
> benchmarks are the modal chain's trivial case: every start mode joint-certified, hop lists
> empty, k self-loop pieces. No new lemma; the uniform chain is retired for Theorem-3
> purposes (its `CoexecInvThroughout` conjunct is separately available via `check_sound`).
> Consequence for the statement: Theorem 3 lands **uniformly** for all 46 as
> `ψ' = ϕinv ∧ envLR ∧ mvValid` — the S1-honest envelope-conditioned form — one theorem
> shape for the whole suite, which is also the cleaner paper narrative.

---

## 1. Where the work actually is

Two independent axes. A benchmark needs both.

**Assembly** — building the response as (hops) ++ (k pieces) and closing the loop. **[M]**

| route | n | state |
|---|---|---|
| uniform, any k (`theorem3_uniform_from_covered`) | 9 | **built** — `rover_drag` |
| modal, k = 1 (`Hmulti_window1_prefixed`) | 16 | **built** — `watertank_modal_certified` |
| modal, k > 1 (`Hmulti_window_prefixed`) | 21 | blocked on `hdisH` |

**Existence** — supplying `HExistSegB`: the right system must flow for the left's duration
without leaving its evolve envelope. **[M]**

| landing-mode faces | n | route |
|---|---|---|
| all strict or non-strict over the whole box | 33 | `face_strict_from_verdict` + `nonstrict_antitone_raw`, both **exist** |
| an outward face | 5 | needs the B-first split coupling (§W3) |
| an equilibrium / face-only face | 7 | needs asymptotic or stratified non-strict (§W4) |
| no landing mode at all | 1 | not an existence problem — see §W5 |

Cross-tabulated:

| | existence OK | needs switch | needs non-strict | no landing |
|---|---|---|---|---|
| **uniform** | 7 | — | 2 | — |
| **modal k=1** | 12 | — | 3 | 1 |
| **modal k>1** | 14 | 5 | 2 | — |

---

## 2. Work items

### W1 — existence emission (unlocks 33; **19 immediately**)

`HExistSegB_of_viability` ([ViabilityWiring.lean:85](../RelCertifier/Proofs/Flow/ViabilityWiring.lean:85))
and its anchor-conditioning lemmas `anchor_face_from_verdict` / `anchor_budget_from_verdict`
are written. **[V]** What is missing is the data they consume, per (benchmark, landing mode):

- the face terms `gsS` (strict) / `gsG` (growth) and the growth bound `M`
- Lipschitz + field-bound data on a ball (`odeField_lipschitzOnWith`, polynomial fields)
- one Z3 verdict per face

`checkViability` and `--emit-viability` exist but emit only the **strict** census. Extending
emission to the bounded/non-strict variant is the job.

Face census over all 47 benchmarks, 1133 faces, evaluated **on the face** (not over the box —
that distinction inverts the answer for relaxation fields): **582 strict, 474 non-strict over
the whole box, 45 face-only, 32 outward, 0 ambiguous, 0 hopeless.** **[M]**

**19 benchmarks need only this** — their assembly route is already built and demonstrated:

> uniform: `attitude_rate`, `match_multi_rate`, `rover3tier_rung12`, `rover_4d_box`,
> `rover_drag`, `rover_tier_r1`, `story1_attdist_rung_a_6to8`
> modal k=1: `arm_chain_rung3`, `arm_fidelity_high`, `arm_fidelity_mid`, `plant_fan_high`,
> `plant_fan_mid`, `refinement_ladder_rover_rung1_2to3`,
> `refinement_ladder_rover_rung2_3to6`, `robot_braking`, `rover_dof_terrain_rung1/2/3/3_8d`

### W2 — hop-shape fix (unlocks 14 more, cumulative 33)

`Hmulti_window_prefixed` is vacuous for nonempty hop lists: its `hdisH` demands
`Disjoint (vars (h.prog domL)) (vars (clockedSeg …))`, and `RepoHop.prog` is a **frozen-left
joint** ODE binding every left coordinate with `domL` in its domain. **[V]**

Fix: state hops right-only, `ode (rightBlock fR lam) domR` — the shape the final response
already uses (`sem_rightBlock_frozen_iff` converts, and watertank does exactly this
conversion at [WatertankModal.lean:335](../RelCertifier/Instances/WatertankModal.lean:335)),
and the shape for which the identical disjointness already discharges in `emitWindows_self`.
**[V]**

Measured: hop paths of length ≤ 2 suffice for 45 of 46; the k-piece response can always be
`hop prefix → k self-loop residences` in a joint-certified mode. **[M]**

Touches `RepoPrefix.lean` and `EnvelopeChain.lean` — upstream of the instance layer, so batch
with anything else in those files. See [`KGT1-ASSEMBLY-SCOPE.md`](KGT1-ASSEMBLY-SCOPE.md).

### W3 — intra-piece switch (unlocks 5 more, cumulative 38)

`arm_chain_rung1`, `arm_chain_rung2`, `arm_fidelity_low`, `arm_refinement`, `plant_fan_low`.
Their landing modes have a genuinely outward face (`theta' = ±0.2/0.3/0.5` against
`theta ∈ [0,1]`), so a full-duration single-mode piece leaves the envelope.

**The response:** run `B` first for `t₂ = s·M_A/(M_A + M_B)`, then `A` for the rest. The rise
in `A` exactly cancels the drop in `B`, so `v_r` returns to the face and never exceeds it.
One switch. `A` is joint-certified and costs nothing; only the `B` stretch is charged.

Needed:
- a **budgeted-invariant certificate** — `UNSAT( env ∧ g ≤ 0 ∧ v_r = bound ∧ g + M_g·t₂ > 0 )`
  — new query family, new emission
- a split coupling at a **fixed fraction** of the left duration; `sem_ode_split`
  ([BridgeReposition.lean:371](../RelCertifier/Proofs/Encoding/BridgeReposition.lean:371)) exists

No first-exit/IVT lemma is needed — `t₂` is a constant ratio, not a state-dependent exit time.

Measured: **13/13 windows have a workable landing mode**, most with slack ≥ 0.02; `B`'s own faces stay well inside
during its stretch (0 violations). **[M]** See [`INTRA-PIECE-SWITCH-SCOPE.md`](INTRA-PIECE-SWITCH-SCOPE.md).

### W4 — non-strict / asymptotic existence (unlocks 7 more, cumulative 45)

`endurance_orderlift_2to3`, `refinement_ladder_rover_rung4_8to12`,
`story1_attdist_rung_b_12dof`, `story2_lateral_rung_a_8dof`, `story2_lateral_rung_b_12dof`,
`story3_rollover_ladder_rung_b`, `watertank`.

Their landing modes have a face where `Lie ≤ 0` holds **on the face but not over the whole
box**, so `nonstrict_antitone_raw` (which takes an along-curve premise) does not apply
directly, and the boundary-only check is unsound (`nonstrict_boundary_insufficient`, the t²
trap). Nagumo sub-tangency is not in the vendored Mathlib. **[V]**

All are relaxation/decay shapes — `y' = −y` at `y = 0`; `psi' = ω − psi` at `psi = 0.6`;
watertank `x' = 3(1 − 0.04x)` at `x = 25`. `asymptotic_invariance_raw` (PicardBridge) is the
affine-chase route already used for shapes of this kind. **[I]**

Likely escape: a stratified argument mirroring R4's sequential differential cuts — prove a
stronger invariant confining the state to where `Lie ≤ 0`, then apply the existing lemma.
**Not scoped.** This is the least-charted item.

### W5 — `refinement_ladder_rover_rung2c_6dof` (unlocks 1, cumulative 46)

Not an existence problem. Its right graph is a one-way chain `STEEP → MODER → FLAT` with no
return edges, so some (window, start mode) pairs have no declared path to a joint-certified
mode. Those pairs are exactly the **non-admissible** ones — `guardL ∧ guardR ∧ inv` is UNSAT
— so they discharge by **vacuity**, which requires the statement to carry admissibility
conditioning (R2's `gwindowSeg` guard gate plus a right-region conjunct in the loop
invariant). Watertank never needed this because free hops covered all its pairs
constructively. **[M]**

### W6 — parser hole (independent, soundness)

The parser silently drops unknown keys: a `reset = x := 1.0` line certifies green with the
reset discarded, and all 47 benchmarks carry an unread `max_depth`. Demonstrated, recorded in
[`COVER-AUDIT.md`](COVER-AUDIT.md), unfixed. Roughly an hour. Independent of everything above,
and the only item on this page that affects what is already claimed.

---

## 3. Order

```
W6  (independent, do whenever)
W1 ─────────────────► 19
 └─ W2 ─────────────► 33
     ├─ W3 ─────────► 38
     ├─ W4 ─────────► 45
     └─ W5 ─────────► 46
```

W1 is on every path. W2 is on every path except the 19. W3/W4/W5 are independent of each
other and can be done in any order or skipped.

Natural cut lines: **19** (existence emission only), **33** (+ the hop fix), **46** (all).

---

## 4. What is not established

- **W4 is the real unknown.** No route to it has been demonstrated on a single benchmark, and
  it is the one item whose shape I have not verified against working code.
- **W1's per-benchmark risk.** The face census says every face is classifiable, but the
  anchor verdicts for the growth faces have only been run for the 13 benchmarks carrying
  outward faces, not for the whole suite.
- **W3's margins.** Two of the 18 obligations clear by under 0.02. Both windows have a second
  landing mode with a comfortable margin, so the response can choose — but that choice has to
  be made in the instance, not left to a generic template.
- **The throughout guarantee does not depend on any of this.** 46/47 certified, relational
  invariant holds along co-executions under the covered strategy, kernel-verified given the
  verdicts. Nothing in this plan is needed to keep that claim.

## 5. Reliability note

The measurements in this document have been stable under re-checking; the judgements between
them have not. Over this session's analysis I was wrong four times on the connection between
the battery and Theorem 3, and three times on the W3 obligation specifically — alternating
optimistic and pessimistic, each time corrected by reading a definition or running a control
rather than by reasoning. Treat the counts as measured and the effort estimates as unvalidated.
