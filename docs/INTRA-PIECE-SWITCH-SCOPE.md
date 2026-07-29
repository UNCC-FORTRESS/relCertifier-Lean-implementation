# Scope — intra-piece mode switching (the Group A coupling)

**Status: SCOPE ONLY. Nothing built.**

Blocks 5 benchmarks: `arm_chain_rung1`, `arm_chain_rung2`, `arm_fidelity_low`,
`arm_refinement`, `plant_fan_low`. See [`VIABILITY-FACE-CENSUS.md`](VIABILITY-FACE-CENSUS.md)
for why these five and not others.

## 1. The obligation

For these windows the right system must leave its landing mode mid-piece to stay inside its
own evolve envelope, and the departure time is not a left piece boundary. The current
coupling composes **one right ODE per left piece**, so no witness exists in that shape.

Needed: a coupling for `Q = seq (ode A domR) (ode B domR)` against a single clocked left
segment — flow `A` for `s₁`, take the declared edge, flow `B` for `s − s₁`.

## 2. The assembly needs no change

`Hmulti_window_prefixed` / `Hmulti_window1_prefixed` take
`pieces : List (Program (Var n))` with `hcouple : ∀ Q ∈ pieces, faModalB … Q …`, and `Q` is
an arbitrary program. A composite `seq (ode A) (ode B)` drops in unchanged. **[VERIFIED]**

The work is entirely inside the per-piece coupling — today
`segment_faModalB_from_certB` ([ViabilityWiring.lean:296](../RelCertifier/Proofs/Flow/ViabilityWiring.lean:296)),
which wraps `faModal_ODE_G'_bounded` around a single joint ODE
`leftBlock fL ++ rightBlock fR lam` with `BoxLe` for the invariant and `HExistSegB` for
existence.

## 3. What the split coupling needs

| # | ingredient | state |
|---|---|---|
| 1 | split time `t₂ = s·M_A/(M_A+M_B)` — a **fixed fraction** of the left duration | no first-exit / IVT lemma needed |
| 2 | split the left run at `s₁` | `sem_ode_split` ([BridgeReposition.lean:371](../RelCertifier/Proofs/Encoding/BridgeReposition.lean:371)) — **exists** |
| 3 | invariant at the split state | falls out of `A`'s `BoxLe` on `[0, s₁]` |
| 4 | invariant preserved while in `B` | **`B` has no joint certificate** — see §4 |
| 5 | declared edge `A → B`, guard `tt` | structural, same discharge as the hop edges |
| 6 | bound on switches per piece | **[MEASURED]** per-piece displacement < box width for all 5, so **one** switch suffices |

Times are shared: the joint flow has a single time parameter and the clock `tg` tracks the
left, so `s₁` splits both sides at once. No re-synchronisation needed.

## 4. The real new content — a budgeted invariant certificate

`B` is not joint-certified for these windows (`jointOK = false`; only static `repoPre`/
`repoPost`). That is a genuine Z3 result, not an omission: for `arm_chain_rung1` window
`ApproachFast`, left `theta' = 0.5` against right `Return` at `λ = 2.5` gives
`dg/dt = 0.5 + 0.5 = 1.0 > 0` — the invariant gap grows uniformly.

But the response does not need uniform preservation. It needs the invariant to survive a
**bounded** stretch in `B`, from an anchor that already has slack. That is the same shape as
the viability anchor budget, applied to the invariant instead of a face:

```
UNSAT( guardL ∧ envL ∧ envR ∧ g ≤ 0 ∧ (right near its outward face) ∧ g + M_g·dt ≥ 0 )
```

This certificate shape does not exist in the tool or the proof layer. It is the piece to
design.

### Measured feasibility (Z3) — **5 of 5 benchmarks, 13/13 windows**

The obligation is anchored at the **switch state**, not the piece anchor.
`BoxLe α g ν := ∀ ω, sem α ν ω → g ω ≤ 0` ([DI.lean:46](../.lake/packages/dL-lean/DLLean/DI.lean))
— `A`'s certificate gives `g ≤ 0` along `A`, **not** `g ≤ g(anchor)`. No history of the anchor
survives. What does survive is that the switch state sits **on the face**, and the envelope
bounds `g` there directly.

**The response is `B` first, then `A`** — not `A` until it must leave, then `B`. Starting on
the face, run `B` for `t₂ = s·M_A/(M_A + M_B)`, then `A` for the rest: the rise in `A` exactly
cancels the drop in `B`, `v_r` returns to the face and never exceeds it, and only the `B`
stretch is charged.

```
UNSAT( envL ∧ envR ∧ g ≤ 0 ∧ v_r = bound ∧ g + M_g·t₂ > 0 )
```

No `guardL` — it holds at window entry, not at an arbitrary piece. Violation is strict
(`> 0`), since `invLe g` is `g ≤ 0`. `M_g` = interval max of `dg/dt` over the full envelope
boxes.

**Result: every window of all five has a workable landing mode.** **[M]**

| benchmark | windows | landing mode used |
|---|---|---|
| `arm_chain_rung1` | 3/3 | `Approach` (and `Return` for the `Return` window) |
| `arm_chain_rung2` | 4/4 | `ApproachSlow` |
| `arm_fidelity_low` | 2/2 | `Approach` |
| `arm_refinement` | 2/2 | `Approach` |
| `plant_fan_low` | 2/2 | `Approach` |

`B`'s own faces stay well inside during its stretch (0 violations). Controls: switch state
satisfiable for every reported pass; `M_g := 100` turns the query `sat`.

### Three earlier versions of this query were wrong

Recorded because the errors alternated in direction.

1. **Guard-narrowed `M_g`** — the guard region is not forward-invariant. In `arm_fidelity_low`
   `Brake`, `theta' = v ≤ 0` drives `theta` below `0.5`, after which
   `v' = (0.5 − theta) − 2v > 0` and `v` leaves `v ≤ 0`. Sound for the anchor, unsound as a
   bound over the piece. *(too optimistic)*
2. **`g` anchored at the piece start**, charge scaled by `s₂ = dt·(1 − d/(M_A·εR))`. Gave
   14/14. `BoxLe` is a sublevel box, not a monotonicity statement. *(too optimistic)*
3. **`A`-first with a full `dt` charge in `B`.** Gave 11/14 and failed `arm_chain_rung2`. The
   response is not obliged to stay in `B`. *(too pessimistic)*

## 5. Order of work

1. Design the budgeted-invariant certificate — the query above — plus its emission.
2. The split coupling (§3), whose only genuinely new lemma is the first-exit split time.
3. *(dropped — `arm_chain_rung2` needs no multi-switch response under the `B`-first ordering.)*

Feasibility: **5 of 5**, 13/13 windows, most with real slack. This remains the most expensive
of the three open items per benchmark recovered — a new certificate family plus a split
coupling, for five benchmarks.

## 6. Relation to the other open items

Independent of the k>1 hop-shape fix ([`KGT1-ASSEMBLY-SCOPE.md`](KGT1-ASSEMBLY-SCOPE.md))
and of the non-strict/asymptotic existence lemma needed by the 7 equilibrium-faced
benchmarks. All three can proceed in any order.

---

## 7. Re-verification with a strict formula parser (2026-07-29)

The measurement tooling silently mis-encoded any formula it could not parse. Made strict —
it now raises on s-expression formulas, on `or`/`not`, on a conjunct that is not a
comparison, and on a formula that parses to nothing.

**What the strict parser rejects:** 7 invariants across 3 benchmarks are `smt2:`
s-expressions using an `L_x`/`R_x` naming convention rather than `x[l]`/`x[r]` —
`refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`,
`rover3tier_rung12`. On these the old encoder returned `['(<= ( (+)']` with no error.

**Blast radius: none of the reported results.** Every invariant-using query ran on a
benchmark set disjoint from those three, and the face census, stratification, hop
reachability, cover-flag parsing and B-stretch checks use no invariant at all.

**Re-verified under the strict parser:**

| | result | previously |
|---|---|---|
| L3, per-window | **13/13 windows have a workable landing mode** | reported as "18/18 obligations" |
| L4 P1 (preservation) | unsat | unsat |
| L4 P2 (3 hop restorations) | unsat ×3 | unsat ×3 |
| L4 P3 (vacuity) | 3/9 unsat, 6/9 sat | 3/9, 6/9 |
| encoder round-trip | 470 random points, 0 mismatches | not previously run |

**Correction to the "18/18" figure.** That enumeration included `ApproachFast` as a landing
mode for `arm_chain_rung2`; it is not one (it fails the reachable-from-every-mode test). Its
4 obligations are not dischargeable and are also not needed — `ApproachSlow` covers all four
of that benchmark's windows. The accurate statement is per-window, and the conclusion is
unchanged: **5/5 benchmarks**.
