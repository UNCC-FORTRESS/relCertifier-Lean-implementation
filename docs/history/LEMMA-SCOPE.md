> **COMPLETED — archived 2026-07-30.** Every lemma group scoped here landed:
> L1 `Proofs/Flow/StratifiedFaces.lean`, L1c/L1d `AffineFaces{,2}.lean`,
> L2 `Proofs/Encoding/RepoPrefixR.lean`, L3 `SplitCoupling.lean`,
> L4 `ModeRegion.lean` + `EnvelopeChainR.lean`, L6 `EnvelopeChainM.lean`,
> L7 `Reparam.lean`, plus the later `WindowRF.lean` and `WindowGrowth.lean`.
> The file's "Nothing built" banner and its sizing estimates are historical. One
> projection was notably wrong in the good direction: it expected ~1130 new Z3 verdicts
> to enter the trust base, but the hardest benchmarks landed **Z3-free**.

# Lemma scope — what must be stated and proved for Theorem 3 across all 46

**Scope document. Nothing built.** Companion to
[`THEOREM3-ALL-BENCHMARKS-PLAN.md`](THEOREM3-ALL-BENCHMARKS-PLAN.md), which it **corrects**
in one place — see §0.

Signatures below are the intended shapes, written against the repo's existing conventions.
They are targets, not verified statements.

---

## 0. Correction to the plan's W1

The plan said W1 (existence) was "emission only" for 33 benchmarks, with a separate harder
item W4 for 7. **That split was wrong.**

`HExistSegB_of_viability` ([ViabilityWiring.lean:85](../RelCertifier/Proofs/Flow/ViabilityWiring.lean:85))
takes exactly two face classes:

```lean
(hbndS : ∀ gT ∈ gsS, ∀ x, (∀ gT' ∈ gsS ++ gsG, Term.eval gT' x ≤ 0) →
    Term.eval gT x = 0 → Lie … < 0)                                  -- STRICT on the face
(hbndG : ∀ gT ∈ gsG, ∀ x, (∀ gT' ∈ gsS ++ gsG, Term.eval gT' x ≤ 0) → Lie … ≤ M)
(hinitS  : ∀ gT ∈ gsS, Term.eval gT ν ≤ 0)
(hbudget : ∀ gT ∈ gsG, Term.eval gT ν + M * dt < 0)                  -- STRICT slack
```

A **non-strict inward** face fits neither. It fails `hbndS` (`Lie = 0` on the face is allowed),
and putting it in `gsG` with `M = 0` makes `hbudget` demand `gT ν < 0` — false at anchors
sitting on the face, which `inv ∧ env` admits.

`BoxViability.lean`'s header says so directly: *"Strictness is load-bearing: nonstrict
subtangency (Nagumo) is not in the vendored Mathlib."* **[V]**

So the census splits differently than the plan claims:

| | faces | benchmarks with such a face at a landing mode |
|---|---|---|
| strict on the face | 582 | — |
| **non-strict inward** | **519** (474 whole-box + 45 face-only) | **essentially all** |
| outward, budgeted | 32 | 5 |

**Only 2 of 47 benchmarks have all-strict faces.** **[M]** The non-strict class is therefore
on the critical path for nearly every benchmark, not a 7-benchmark tail. The plan's increment
"W1 unlocks 19 immediately" does not hold.

### Why it is still tractable

`nonstrict_antitone_raw` ([PicardBridge.lean:220](../RelCertifier/Proofs/Flow/PicardBridge.lean:220))
takes the premise **along the curve**, not on the face, and is already used for `s ≥ 0` faces
([PicardBridge.lean:340, 694, 1337](../RelCertifier/Proofs/Flow/PicardBridge.lean:340)). The
pattern there: prove `v ≥ 0` first by a strict or affine argument, then `s' = v ≥ 0` holds
genuinely along the curve, so `s ≥ 0` follows with no sub-tangency and no t² trap. **[V]**

That is a **stratification**, and it is the same shape as R4's sequential differential cuts
(`stratified_barrier_sound`, [StratifiedBarrier.lean:123](../RelCertifier/Proofs/Flow/StratifiedBarrier.lean:123)),
except that R4 proves *invariant components given the domain* while this must prove *the domain
itself*. The per-shape assemblies exist (`slab_invariance_rover`, `hstep_rover`); the generic
theorem does not.

---

## L1 — stratified face invariance (replaces the plan's W1 core)

The missing generic theorem. Mirrors `strict_faces_endpoint`
([BoxViability.lean:60](../RelCertifier/Proofs/Flow/BoxViability.lean:60)) with faces in
strata order, each stratum's condition discharged over the region cut out by earlier strata.

```lean
theorem stratified_faces_endpoint {sys : ODESystem V} (hwf : sys.WellFormed)
    (gs : List (State V → ℝ))                     -- faces, in STRATA ORDER
    (strict : List Bool) (hlen : strict.length = gs.length)
    (hg : ∀ g ∈ gs, Differentiable ℝ g)
    -- stratum i, STRICT: inward on its own boundary, over the earlier-narrowed region
    (hbndS : ∀ i (hi : i < gs.length), strict[i] = true → ∀ x,
        (∀ g ∈ gs.take i, g x ≤ 0) → gs[i] x = 0 → Lie sys gs[i] x < 0)
    -- stratum i, NON-STRICT: `Lie ≤ 0` on the whole earlier-narrowed region, not just the face
    (hbndN : ∀ i (hi : i < gs.length), strict[i] = false → ∀ x,
        (∀ g ∈ gs.take i, g x ≤ 0) → Lie sys gs[i] x ≤ 0)
    {r : ℝ} {Φ : ℝ → State V} (hr : 0 ≤ r)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinit : ∀ g ∈ gs, g (Φ 0) ≤ 0) :
    ∀ t ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gs, g (Φ t) ≤ 0
```

**Proof shape.** Strong induction on the stratum index, as in `stratified_barrier_sound`. For
stratum `i` the earlier strata hold pointwise on `[0,r]` by the IH, so the region premise is
available along the whole curve. Strict strata then use the `strict_faces_endpoint` first-exit
argument restricted to that region; non-strict strata use `nonstrict_antitone_raw` directly —
its premise is now a fact along the curve, not an assumption about a box, so the t² trap
(`nonstrict_boundary_insufficient`) does not arise.

**Load-bearing requirement:** the strata must bottom out. **MEASURED — they do, for all 47.**

Strict faces need no ordering: `strict_faces_endpoint`'s first-exit argument conditions on
**all** faces simultaneously, so mutually-dependent strict faces are fine. (`attitude_rate`'s
`p' = 1 − p + 0.05q`, `q' = 1 − q + 0.05p` is exactly this — a dependency cycle, and both
faces strict. An acyclicity criterion rejects it wrongly.)

The right construction: take the **greatest self-conditioned strict core** `S` — shrink from
all faces until every `g ∈ S` is strict conditioned on `S` alone — then stratify the
remaining faces on top of it.

| class | faces | resolved by |
|---|---|---|
| strict core `S` | 575 | `strict_faces_endpoint`, no ordering |
| non-strict, stratified over `S` | 481 | `nonstrict_antitone_raw` at its level |
| affine relaxation | 45 | L1c below |
| outward | 32 | L3 (the W3 switch) |
| **stuck** | **0** | — |

Strata depth beyond the strict core, per (benchmark, mode): **0** for 9, **1** for 100,
**2** for 17, **3** for 3. Max depth 3. **[M]**

**Every benchmark's envelope admits a closing stratification.** L1 is a well-posed lemma, not
a research problem.

### L1c — affine-relaxation face invariance (8 benchmarks, 45 faces)

The residual class: `x' = u − k·x` with `k > 0`, face at or beyond the equilibrium, so
`Lie = 0` exactly on the face and no stratification makes it negative.

```lean
theorem affine_relax_face_invariant {sys : ODESystem V} {r : ℝ} {Φ : ℝ → State V}
    (x : V) (k c : ℝ) (hk : 0 < k)
    (hfield : ∀ t ∈ Set.Icc (0:ℝ) r, odeField sys (Φ t) x ≤ k * (c - Φ t x))
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinit : Φ 0 x ≤ c) :
    ∀ t ∈ Set.Icc (0:ℝ) r, Φ t x ≤ c
```

Comparison argument on `w = x − c`: `w' ≤ −k·w`, so `w(t) ≤ e^{−kt} w(0) ≤ 0`. Mathlib has
the Gronwall family (`Mathlib/Analysis/ODE/Gronwall.lean`), and the repo already has
`asymptotic_invariance_raw` ([PicardBridge.lean:1003](../RelCertifier/Proofs/Flow/PicardBridge.lean:1003))
for shapes of this kind. **[V]**

Affected: `endurance_orderlift_2to3`, `refinement_ladder_rover_rung4_8to12`, `robot_braking`,
`story1_attdist_rung_b_12dof`, `story2_lateral_rung_a_8dof`, `story2_lateral_rung_b_12dof`,
`story3_rollover_ladder_rung_b`, `watertank`.

### L1a — the viability consumer

```lean
theorem HExistSegB_of_viability_stratified
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
    (gs : List (Term (Var n))) (strict : List Bool)
    (M : ℝ) (gsG : List (Term (Var n)))            -- growth faces keep the existing treatment
    … Lipschitz/ball data as in `HExistSegB_of_viability` …
    (hdomsat : ∀ x, (∀ gT ∈ gs ++ gsG, Term.eval gT x ≤ 0) → Formula.sat domR x)
    (dt : ℝ) (hdt0 : 0 ≤ dt) (ν : State (Var n))
    (hinit   : ∀ gT ∈ gs,  Term.eval gT ν ≤ 0)
    (hbudget : ∀ gT ∈ gsG, Term.eval gT ν + M * dt < 0) :
    HExistSegB fL fR lam domL domR dt ν
```

Same assembly as the existing proof — `picard_isPL_of_local` for the local step, `chainN` to
reach `dt`, L1 for staying in the box — with `strict_faces_endpoint` swapped for L1.

### L1b — tool side

`checkViability` emits only the strict census. Needs: per face, a stratum index and a
strict/non-strict tag, plus the corresponding query
(`UNSAT(region ∧ g = 0 ∧ ġ ≥ 0)` for strict, `UNSAT(region ∧ ġ > 0)` for non-strict, where
`region` is the box narrowed by earlier strata), and emission of the order. The stratified
fixpoint that computes such an order already exists for `checkSeg` — reuse it.

---

## L2 — right-only reposition hops (plan W2)

`Hmulti_window_prefixed` is vacuous for nonempty hops: `hdisH` demands disjointness of the hop
program from the clocked left segment, and `RepoHop.prog` is a frozen-left **joint** ODE
binding every left coordinate, with `domL` in its domain. **[V]**

```lean
def RepoHop.progR (h : RepoHop n) : Program (Var n) :=
  Program.ode (rightBlock h.fR h.lam) h.domR

theorem faModalB_repoPrefixR {fL fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {φ : Formula (Var n)} {Q : Program (Var n)}
    {a : Fin n} {dt : ℝ} {ω₀ : State (Var n)}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hdomR : domR.fv ⊆ range Rv)
    (hω₀tg : ω₀ ((Side.Aux, a) : Var n) = 0)
    (hR : ∃ ρ₁, Program.sem (Program.ode (rightBlock fR lam) domR) ω₀ ρ₁ ∧ Formula.sat φ ρ₁)
    (hQ : ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 → faModalB … Q φ … σ) :
    faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
      (Program.seq (Program.ode (rightBlock fR lam) domR) Q)
      φ ((Side.Aux, a) : Var n) dt ω₀
```

**Delta from `faModalB_repoPrefix`** ([RepoPrefix.lean:286](../RelCertifier/Proofs/Encoding/RepoPrefix.lean:286)),
which is the existing proof and carries every other step unchanged: **[V]**

| step | now | becomes |
|---|---|---|
| left coords constant along the hop | `frozen_left_constant hhop i` (zero left field) | `sem_ode_mask hhop (Lv i ∉ (rightBlock fR lam).bound)` |
| replay at the left endpoint | `sem_frozen_replay` (needs `hνdomL`) | right-only replay; `domL` drops out of the hop domain, so `hνdomL` is unused |
| `rpatch ω₀ ρ₁ = ρ₁` | case split L / R / Aux | same, L case now by masking |

Then `faModalB_repoPathR` (same induction as
[`faModalB_repoPath`](../RelCertifier/Proofs/Encoding/RepoPrefix.lean:363)),
`static_hop_existsR` (zero-duration witness, simpler — domain is right-only), and the payoff:

```lean
theorem hdisH_of_side_split (hops : List (RepoHop n))
    (hh : ∀ h ∈ hops, (∀ i, (h.fR i).fv ⊆ range Rv) ∧ h.lam.fv ⊆ range Rv
       ∧ h.domR.fv ⊆ range Rv)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv) :
    ∀ h ∈ hops, Disjoint (Program.vars h.progR)
      (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt))
```

— the same discharge `emitWindows_self` already performs for right modes. **[V]**

`Hmulti_window_prefixed` then applies with `hdisH` real rather than unsatisfiable, unlocking
k > 1 windows.

---

## L3 — intra-piece switch (plan W3, 5 benchmarks)

Response: mode `B` for `θ·s`, then mode `A` for the rest, where `θ = M_A/(M_A + M_B)`. The
rise in `A` exactly cancels the drop in `B`, so the switch coordinate returns to its face and
never exceeds it. `A` is joint-certified; only the `B` stretch is charged against the
invariant.

### L3a — budgeted invariant preservation

```lean
/-- `g` may rise along `(sys, dom)` runs, by at most `Mg` per unit time. -/
def SegBudgetOn (g : Term (Var n)) (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (Mg : ℝ) : Prop :=
  ∀ ν r Φ, 0 ≤ r → Φ 0 = ν →
    (∀ s ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
        HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ s)) (Set.Icc 0 r) s) →
    (∀ s ∈ Set.Icc (0:ℝ) r, Formula.sat dom (Φ s)) →
    Term.eval g (Φ r) ≤ Term.eval g ν + Mg * r

theorem segBudget_of_verdict (g : Term (Var n)) (sys : ODESystem (Var n))
    (dom : Formula (Var n)) (Mg : ℝ)
    (hz3 : z3solve (Formula.and dom (Formula.cmp .gt (lieTerm sys g) (Term.const Mg)))
        = Verdict.unsat) :
    SegBudgetOn g sys dom Mg
```

The analytic content is the mean-value inequality on `g ∘ Φ`, which the repo already has as
`growth_bound_raw` ([PicardBridge.lean:250](../RelCertifier/Proofs/Flow/PicardBridge.lean:250))
for a single coordinate — generalize it from a coordinate to a term. **[V]**

### L3b — the split coupling

```lean
theorem segment_faModalB_split (g : Term (Var n)) (fL fA fB : Fin n → Term (Var n))
    (lam : Term (Var n)) (domL domR : Formula (Var n)) (tg : Var n) (dt θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hcertA : SegPreservesOn g (jointSys fL fA lam) (Formula.and domL domR))
    (hbudB  : SegBudgetOn g (jointSys fL fB lam) (Formula.and domL domR) Mg)
    (hanchor : ∀ σ, Formula.sat (Formula.and (invLe g) env) σ →
        Term.eval g σ + Mg * (θ * dt) ≤ 0)          -- the Z3 obligation; 13/13 windows
    (hESB : HExistSegB fL fB lam domL domR (θ * dt) σ)
    (hESA : ∀ ρ, … → HExistSegB fL fA lam domL domR ((1 - θ) * dt) ρ)
    … freshness/side-split as in `segment_faModalB_from_certB` … :
    faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
      (Program.seq (Program.ode (rightBlock fB lam) domR)
                   (Program.ode (rightBlock fA lam) domR))
      (invLe g) tg dt σ
```

Split the left run at `θ·s` with `sem_ode_split`
([BridgeReposition.lean:371](../RelCertifier/Proofs/Encoding/BridgeReposition.lean:371)),
apply `hbudB` on the first stretch and `hcertA` on the second. **No first-exit lemma is
needed** — `θ` is a constant ratio, not a state-dependent exit time.

`Hmulti_window*` needs no change: `pieces : List (Program (Var n))` already accepts a
composite `Q`. **[V]**

---

## L4 — mode-region conditioning (plan W5, `rung2c`) — **MEASURED, closes**

`rung2c`'s right graph is the one-way chain `STEEP → MODER → FLAT`. Three (window, start)
pairs have no declared path to a joint-certified mode: `(STEEP, MODER)`, `(STEEP, FLAT)`,
`(MODER, FLAT)`. **[M]** They must discharge by vacuity.

### Why it works here: the invariant is an exact lockstep bisimulation

```
STEEP = v[l] <= v[r] and v[r] <= v[l] and s[l] <= s[r] and s[r] <= s[l] and …
```

— i.e. `s_l = s_r`, `v_l = v_r`, `psi_l = psi_r`, `theta_l = theta_r`. **[V]** The benchmark's
own header says the consequence outright: *"sL=sR (exact) makes all cross-terrain pairs
vacuous: L and R cross terrain boundaries simultaneously."*

So `guardL` on the left transfers to the right through the invariant, and the only missing
link is `mv = q ⟹ the right state is in q's region`.

### The device: the *forward-invariant* half of the guard

A mode's full guard band is not preserved — flows leave it by design, which is what sank the
`Gd`-anchored existence route. But its **lower** half is preserved here, because `s` is
non-decreasing (`s' = v·((1 − ½ψ²) − 0.3θ²)`, with `v ≥ 0` and the bracket `≥ 0.8` on the
envelope):

```
lowR(STEEP) := s_r ≥ 0     lowR(MODER) := s_r ≥ 0.6     lowR(FLAT) := s_r ≥ 1.4
```

Add to the loop invariant the conjunct

```lean
def modeRegion (mv : Var n) (k : ℕ) (low : ℕ → Formula (Var n)) : Formula (Var n) :=
  ⋀ q < k, (mv ≠ q ∨ low q)          -- "the right system is at or past its mode's entry"
```

### Three obligations, all discharged by Z3 **[M]**

| | obligation | result |
|---|---|---|
| **P1** preservation along a piece | `UNSAT( envR ∧ s' < 0 )` | **unsat** |
| **P2** restoration at each hop | `UNSAT( guardL_w ∧ inv ∧ env ∧ lowR(src) ∧ ¬lowR(tgt) )`, all 3 hops in all live responses | **unsat ×3** |
| **P3** vacuity of the bad pairs | `UNSAT( guardL_w ∧ inv ∧ env ∧ lowR(q) )` | **unsat for exactly the 3 bad pairs; all 6 live pairs remain sat** |

P2 needs no witness cleverness — `guardL(MODER)` gives `s_l ≥ 0.6`, the lockstep invariant
gives `s_r = s_l`, so `lowR(MODER)` holds at the hop. Same for `FLAT`.

### Lean pieces

**P1 needs no new analytic content.** `lowR(q)` as the term `bound − s_r`, preserved along the
joint ODE, is literally `SegPreservesOn` — a `BoxLe` from `flow_cert_sound`, the same
certificate shape the cover already uses:

```lean
theorem lowR_preserved (b : ℝ) (sr : Var n) (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (hcert : SegPreservesOn (Term.binop .sub (Term.const b) (Term.var sr)) sys dom) :
    ∀ ν ω, Program.sem (Program.ode sys dom) ν ω →
      Formula.sat (Formula.cmp .ge (Term.var sr) (Term.const b)) ν →
      Formula.sat (Formula.cmp .ge (Term.var sr) (Term.const b)) ω
```

**P2/P3 are `anchor_face_from_verdict`'s shape** — one Z3 verdict each, already a supported
pattern ([ViabilityWiring.lean](../RelCertifier/Proofs/Flow/ViabilityWiring.lean)).

**The statement side** threads `modeRegion` through the loop invariant, exactly as `envR` is
threaded today by `phiInvE`, and re-establishes it at each response mode switch from P2.

### Generality and risk

The conjunct is **per-instance**: `theorem3Form` takes `φ`, so only `rung2c`'s instance carries
it and no other benchmark is affected. Measured suite-wide, **95 of 129** right-mode guard
lower bounds are forward-invariant on their envelope and 34 are not (20 benchmarks) — so the
device does not generalise blindly, and should not be put in a shared template. **[M]**

Downgraded from "least charted" to **fully measured**. The remaining work is threading, not
discovery.

---

## L6 — list-generalized modal chain (19 benchmarks) — **found by the 46-check, previously recorded as R4/R5 debt and dropped from the plan**

The entire modal coupling layer is single-invariant-term: `phiInvE g env mv k`
([EnvelopeChain.lean:30](../RelCertifier/Proofs/Encoding/EnvelopeChain.lean:30)) takes one
`g : Term`, and `segment_faModalB_from_cert{,B}` conclude `faModalB … (invLe g)`. **[V]**
19 of 47 benchmarks have multi-component invariants (up to 8 conjuncts; the refinement
ladders, rover_dof_terrain, the stories). **[M]** The memory record is explicit that this
generalization never landed ("R4 LEAN DEBT … list-generalized invariant through modal chain").

Needed: `phiInvE` over `gs : List (Term …)` with `bigLe gs` in place of `invLe g`; the
coupling from `segPresAll_from_strata_verdicts'` (already list-shaped — watertank uses it
with the singleton `[gW]`); the encode identity per component + conjunction. Mostly a
mechanical generalization along the chain; the verdict layer already speaks lists.

## L7 — time-reparametrization of stretched right runs (23 benchmarks)

23 of 46 benchmarks certify with some window's λ ≠ 1, and λ varies **per window within one
benchmark** (`arm_chain_rung1`: 5/2, 3/2, 1). **[M]** The right automaton `Gr` has one fixed
`sys` per mode, but the response pieces run the mode's field at the window's λ. As built
(watertank) the mode sys is `rightBlock fR (Term.const 1)` — real field — which only works
because watertank's λ is 1 everywhere.

Needed:

```lean
theorem sem_ode_rightBlock_reparam (fR : Fin n → Term (Var n)) (c : ℚ) (hc : 0 < c)
    (dom : Formula (Var n)) :
    Program.sem (Program.ode (rightBlock fR (Term.const c)) dom)
      = Program.sem (Program.ode (rightBlock fR (Term.const 1)) dom)
```

Runs biject by `t ↦ t/c` — `sem` existentially quantifies the duration, the field is scaled
by a positive constant, and the domain/mask conditions transport pointwise. With it, the
statement quantifies over the **real** (λ = 1) automaton and each window's coupling converts
its stretched piece — a fidelity improvement, not just a fix: without it the theorem would be
about a λ-stretched automaton, which is not even well-defined when λ differs per window.
Analytic content: chain rule for `HasDerivWithinAt` under linear time scaling; moderate,
self-contained. **[I — not built]**

## 5. Dependency and honest ranking

```
L1  (stratified faces)  ── existence, critical path for ~all 46
L6  (list invariants)   ── modal chain for the 19 multi-component
L7  (λ reparam)         ── modal chain for the 23 with λ ≠ 1 (7 need both L6+L7)
 ├─ L2 (right-only hops) ── +21 k>1 windows
 ├─ L3 (split coupling)  ── +5
 └─ L4 (conditioning)    ── +1

Modal chain AS-BUILT covers only the single-component, all-λ=1 corner: 11 benchmarks.
The two pilots (watertank, rover_drag) both sit in that corner.
```

All four are now charted, and none is a research problem:

- **L1** — stratification measured to close for **47/47**, max depth 3, 0 stuck faces. The
  strict core (575 of 1133 faces) needs no ordering at all; 481 more resolve by stratified
  `nonstrict_antitone_raw`.
- **L1c** — 45 affine-relaxation faces across 8 benchmarks; comparison argument, Mathlib
  Gronwall available, repo precedent in `asymptotic_invariance_raw`.
- **L2** — shape change with a step-by-step delta against an existing proof; 3 steps differ.
- **L3** — analytic content already exists as `growth_bound_raw`; Z3 obligation discharged for
  13/13 windows across the 5 benchmarks (14 obligations; the 4 not discharged belong to
  `ApproachFast`, which is not a landing candidate for its benchmark).
- **L4** — 1 benchmark; all three obligations (preservation, hop restoration, vacuity)
  discharged by Z3, and P1 is an instance of the existing `SegPreservesOn` certificate.

**No item is a research problem, and none rests on an unmeasured assumption.** Every one has
either a Z3 measurement behind it or a worked precedent in the repo.

The residual risk is **volume, not discovery**. Sized below.

---

## 6. Sizing **[M]**

47 benchmarks · **129 right-mode instances** · **1133 envelope faces**.

| face class | count | needs |
|---|---|---|
| strict core | 575 | one Z3 verdict each, `strict_faces_endpoint` |
| non-strict, stratified | 481 | one Z3 verdict each, `nonstrict_antitone_raw` at its level |
| affine relaxation | 45 | one Z3 verdict each + L1c |
| outward | 32 | L3 (18 anchor-budget verdicts, measured) |

**New Z3 verdicts entering the trust base: ~1130** (1101 face verdicts + 18 for L3 + 13 for
L4). The suite carries **111** today. This is roughly a **tenfold growth of the
axiom-backed leaf set** — the single biggest consequence of the whole plan, and it is a
soundness-surface change, not just build time. It should be a deliberate decision, not a
side effect.

Strata depth per mode instance: 0 for 9, 1 for 100, 2 for 17, 3 for 3. Shallow.

Largest instances are the 12-dof stories at 69 faces each across 3 modes
(`refinement_ladder_rover_rung4_8to12`, `rover_attitude_cone_12dof`,
`rover_dof_terrain_rung3`, `story1_attdist_rung_b_12dof`, `story2_lateral_rung_b_12dof`,
`story3_rollover_base_12dof`).

### Shape of the work

- **Lean lemmas: 9** — L1, L1a, L1c, L2 (×4: `progR`, `repoPrefixR`, `repoPathR`,
  `static_hop_existsR`), L3 (×2), L4 (×2). Small count; L1 is the only large proof.
- **Tool: 2 emission extensions** — strata order + strict/non-strict/affine tags per face
  (`checkViability`); budgeted-invariant queries for L3/L4.
- **Instances: ~92 generated** — 46 existence wirings + 46 assembly theorems. Generator work,
  in the shape of the existing 238-leaf battery, not hand-written.
- **Build**: the initial pass elaborates ~1130 verdict-carrying leaves. After X0's
  modularization, per-benchmark iteration stays cheap; the first full build does not.

### Cut lines

| stop at | what you get | cost |
|---|---|---|
| **L1 + L1a + existing assembly** | Theorem 3 for the 9 uniform + 16 modal-k=1 that need no switch and no affine face | most of the 1101 verdicts |
| **+ L2** | + the 21 k>1 benchmarks | one shape change, one batched rebuild |
| **+ L1c, L3, L4** | all 46 | +45 affine faces, +5 switch benchmarks, +1 conditioning |
