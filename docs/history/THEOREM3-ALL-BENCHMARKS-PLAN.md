> **COMPLETED — archived 2026-07-30.** This was the scope document for getting modal
> Theorem 3 onto every benchmark. The target was reached: all 46 certified benchmarks
> carry `rvalid (theorem3Form …)` (`RelCertifier/Instances/ModalBattery.lean`), and the
> reproduction recipe is `docs/CERTIFICATION-CHECK.md`. Read below for the measurements
> and the reasoning, not for the status: every "blocked", "next step", and per-class count
> in this file describes the situation *before* the arc, and several of the predicted
> obstacles were dissolved rather than solved (the 21 "blocked on `hdisH`" benchmarks went
> through `RepoPrefixR`'s derived disjointness; the six last ones went through the
> right-only catch-up form in `WindowGrowth.lean`, which needs no verdicts at all).

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

---

## STATUS LEDGER (updated 2026-07-29, end of build arc session 1)

**Lemma layer: COMPLETE.** L1/L1a (stratified faces + consumer), L1c (affine, both
polarities + four-class consumer), L2 (right-only hops, `Hmulti_windowR_prefixed`),
L3 (split coupling + choice dispatch; feasibility measured — 4 benchmarks single-band,
`arm_chain_rung2` at K=2 banded), L4 core (`lowR_preserved`), L6 (list-invariant
F-chain), L7 (λ-reparam), L2×L6 (`Hmulti_windowRF_prefixed`). All on the standard
three axioms. W6 parser gate landed (47/47 pass, unknown keys refused).

**Instances: Tier-0 COMPLETE (8/8), every one with existence DISCHARGED** (zero Z3
verdicts spent on existence): `arm_chain_rung3` (zero field), `rover_drag` (quadratic,
hand K/L), `arm_fidelity_high`/`plant_fan_high` (generator clones of rung3),
`arm_fidelity_mid` (affine landing) → `plant_fan_mid` (clone), `robot_braking`
(affine transform), `rover_4d_box` (closed-form drift witness). Residuals: the
tool-certified route verdicts only (2 per instance; 1 for the single-mode pair).

**Tooling:** `--emit-viability3` stratified tags; `scripts/gen_modal_clone.py`
(byte-identical-right-system clones — zero-error first generations).

**Recorded limitations:** the stratified consumer's Lipschitz/bound conditioning is
strict+growth-only (fields needing non-strict-face bounds take closed-form witnesses
or a future L1a variant); affine emission tags deferred (instances hand-supply
(λ, M, C)).

**k>1 landed:** `match_multi_eps` (6b82d18) — first `Hmulti_windowR_prefixed`
instance (hop prefix + four replicate pieces); first stratified existence with a
REAL conditioned non-strict stratum (`s' = −v ≤ 0` given the strict core).

**W5 landed:** `EnvelopeChainR.lean` (d6dc192) — the region-carrying modal chain
(`mvRegion` loop invariant, pinned-final-mode bridge, gwindowSeg-gated `hddF`) —
plus `rover_rung2c_6dof` (7e2a251): first list-invariant (multiF) + first
region-carrying (multiR) + first 6-dimensional existence instance. The three
backward (window, start) pairs of the one-way chain discharge by vacuity fully
in-kernel; the landing region rides the coupling as a ninth invariant conjunct.
Residuals: three 9-query stratified-DC verdict packs (semantic mirrors measured
27/27 unsat).

**L3 switch class CLOSED (4536485…4c3d56a):** all five switch benchmarks carry
modal Theorem 3 — the `arm_fidelity_low` pilot (first switch + first λ≠1 + first
dt-capped instance; drop-tracked B-first split, L3′), its `arm_refinement` /
`plant_fan_low` clones, `arm_chain_rung1` (per-window λ/k), and
`arm_chain_rung2` (asymmetric θ = 3/5 — single-band under L3′ where the
pre-L3′ measurement needed a banded θ-family). All existence Z3-free.

**Generator sweep (cb1fa6c):** signature sweep over the remaining suite found
exactly one exact clone — `rover3tier_M1` = `match_multi_eps` — landed.
**Seventeen instances total**; residual inventory in
[`VERDICTS.md`](VERDICTS.md) (mirrors measured; existence residuals zero).

**T3-6 CLOSED.** The remaining 29 benchmarks need genuinely new instance
arcs (the 19 multi-component/list-F, the λ≠1 × k>1 composites, the 8/12-dof
story benchmarks) over the completed lemma layer — every chain variant they
need ({k=1,k>1} × {single-g,list-F,region} × {hops,splits,λ-reparam}) is
landed and instantiated at least once.
