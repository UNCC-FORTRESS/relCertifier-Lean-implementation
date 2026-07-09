# Path A scope — the sound route that certifies the Cat-1 class

Goal: certify the 22 Cat-1 declines (contraction + Lyapunov-energy invariants) **soundly**,
closing 24 → 46 with proof, not by weakening the invariant (no Path B).

## The reframe: superlevel (Lyapunov), not boundary + regularity

The natural ask was `DI_nonstrict_boundary`: `ġ ≤ 0` on a **regular** `{g=0}` ⟹ invariance
(Nagumo for regular boundaries). That route needs (a) a checkable regularity predicate and
(b) special handling of irregular-but-equilibrium points — and its proof needs
**subtangency / Nagumo**, which is **not in vendored Mathlib** (confirmed: Mathlib has
`tangentConeAt` / `posTangentConeAt` for optimization, and `Dynamics/Flow.lean` for abstract
flows, but no subtangency-⟹-forward-invariance for ODE fields).

There is a **strictly better route** that avoids all of that:

> **`DI_nonstrict_superlevel` (Lyapunov barrier).** If `g ν ≤ 0` and `Lie sys g x ≤ 0`
> **wherever `g x ≥ 0`** (within the domain `ψ`), then `g ≤ 0` is forward-invariant.

Hypothesis region: `{g ≥ 0} ∩ ψ` — the *superlevel* side, not just the boundary `{g=0}`.
This is elementary Lyapunov invariance (V̇ ≤ 0 on the escaping side ⟹ sublevel invariant),
**provable from vendored Mathlib**, and it dominates the three concerns:

| concern | boundary + regularity | **superlevel (this)** |
|---|---|---|
| checkable condition | need `∇g ≠ 0` query *and* `ġ≤0` on `{g=0}` | one query: `ψ ∧ g≥0 ∧ ġ>0` UNSAT |
| irregular boundary point | must detect + special-case | **automatic** — see below |
| equilibrium handling | must prove field stationary | **automatic** — see below |
| Mathlib reach | subtangency (not vendored) → build | **none** — adapts two existing DI proofs |
| soundness | needs regularity hypothesis | unconditional |

## (1) Theorem statement

```lean
theorem DI_nonstrict_superlevel {sys : ODESystem V} {ψ : Formula V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, Formula.sat ψ x → 0 ≤ g x → Lie sys g x ≤ 0)   -- ġ ≤ 0 on {g≥0} ∩ ψ
    {ν : State V} (hinit : g ν ≤ 0) : BoxLe (Program.ode sys ψ) g ν
```

Note the single hypothesis change vs `DI_nonstrict_domain` (which requires `ġ≤0` on **all**
of `ψ`): here `ġ≤0` is required **only where `g ≥ 0`**. That is the exact weakening that
lets it see contraction invariants (`ġ = −c·g ≤ 0` on `g≥0`, but `> 0` on `g<0`).

## (2) The checkable predicate = the query itself

No separate regularity check. The sound condition is directly the UNSAT of

```
flowQuerySuperlevel  :=  ψ  ∧  g ≥ 0  ∧  ġ > 0
```

a polynomial Z3-NRA query built from the same `tderiv`/`lieDeriv` the flow certificate
already uses. UNSAT ⟺ `ġ ≤ 0` on `{g≥0}∩ψ` ⟺ `DI_nonstrict_superlevel`'s hypothesis.
Verified empirically:

- **t² pathology** `g=x², ẋ=1, ġ=2x`: `x²≥0 ∧ 2x>0` is **SAT** ⟹ correctly **declines**
  (the pathology is rejected — soundness preserved, no regularity check needed).
- **contraction** `g=v_L−v_R, ġ=−3g` (λ=1): `g≥0 ∧ −3g>0` is **UNSAT** ⟹ **certifies**
  (where the strict route is SAT — `ġ=0` at the marginal boundary — and declines).
- **irregular rung3** `g=psi_R²−psi_L²−3ω²`, λ=3: **UNSAT** ⟹ certifies; λ=1: SAT (genuinely
  escapes there — a finer λ grid recovers λ≥2.16).

## (3) Irregular boundary + equilibrium: handled automatically

The one irregular point in the suite (`rung3_6to8`'s origin: `∇g=0` while `g=0`) needs **no
special case**. It lies in `{g≥0}` (`g=0 ≥ 0`) with `ġ=0 ≤ 0`, so it simply satisfies the
superlevel hypothesis. Equilibria are the same: at a fixed point on the boundary, `ġ=0≤0`,
inside the hypothesis region. The theorem never mentions regularity, so degenerate/tangent/
equilibrium points are covered by the same `ġ≤0`-on-`{g≥0}` condition — no `∇g≠0` obligation
to discharge, no "prove the field is stationary" side-goal.

## (4) Proof sketch (no subtangency; from vendored Mathlib)

A hybrid of the two proofs already in `DI.lean`:
- **Setup (from `DI_strict`)**: given a solution `Φ` on `[0,r]` with `g(Φ0)≤0`, suppose
  `g(Φr)>0`. Let `S = {t∈[0,r] : g(Φt)≤0}`, `s = sSup S` (closed set, `0∈S`). Then
  `g(Φs)=0` and `0 < g(Φt)` for `t ∈ Ioc s r` (the `hpos` step, verbatim).
- **Close (from `DI_nonstrict_domain`)**: on `[s,r]`, every `t` has `g(Φt) ≥ 0` (=0 at s,
  >0 after), so `Φt ∈ ψ` (domain) and `hbnd` gives `Lie(g)(Φt) = (g∘Φ)'(t) ≤ 0`. Hence
  `AntitoneOn (g∘Φ) (Icc s r)` via `antitoneOn_of_deriv_nonpos` ⟹ `g(Φr) ≤ g(Φs) = 0` —
  contradiction.

Both `sSup`-membership machinery and `antitoneOn_of_deriv_nonpos` are already used in
`DI.lean`; no new Mathlib import. **Estimate: ~40–60 lines, self-contained.**

## (5) Oracle integration (trusted layer; core stays sound)

- New verified route in `FlowCert.lean`:
  `flowQuerySuperlevel o := domain ∧ g ≥ 0 ∧ lieDeriv … > 0`, and
  `flow_cert_sound_superlevel : (∀σ ¬sat flowQuerySuperlevel σ) → g(ν)≤0 → BoxLe …`
  citing `DI_nonstrict_superlevel`. (Third route beside domain-`A` and strict-`B`.)
- Runner `checkSeg`: a segment passes if **any** of the three routes' queries is UNSAT
  (all three sound). The superlevel route is the one that fires for the Cat-1 class.
- **Coupling** (components needing others): the multi-barrier form — certify `gᵢ` on
  `{gᵢ≥0 ∧ ⋀_{j≠i} gⱼ≤0} ∩ ψ`. Same superlevel theorem with the other components added to
  the domain `ψ`; sound by the simultaneous first-escape argument. Query:
  `ψ ∧ (⋀_{j≠i} gⱼ≤0) ∧ gᵢ≥0 ∧ ġᵢ>0` UNSAT.
- **λ grid**: widen `lambdaCandidates` (rung3 needs `λ≥2.16`; the current
  `{λmin, εR/εL, λmax}` can miss the interior). A small fixed grid over `[λmin,λmax]`
  recovers the definite verdict.

Expected result: all 22 Cat-1 satisfy the superlevel condition at a proper λ (contraction
`ġ=−cg`, strict-Lyapunov energies `ġ<0`, matched-equality `ġ=−g`, rung3 `λ≥2.16`) ⟹
**24 → 46, every CERTIFIED sound**, regularity proven-by-hypothesis (the UNSAT), not assumed.

## Gate

Reporting before proving, per the three requested items:
1. **Theorem** — `DI_nonstrict_superlevel` (above).
2. **Checkable predicate** — the superlevel query `ψ ∧ g≥0 ∧ ġ>0` UNSAT (no separate
   regularity query; the UNSAT *is* the sound condition).
3. **Equilibrium / irregular handling** — automatic (such points are `g=0, ġ=0 ∈ {g≥0}`).
4. **Mathlib reach** — none needed; adapts `DI_strict` + `DI_nonstrict_domain` already in
   `DI.lean`. The subtangency gap is avoided, not filled.

`#print axioms` on the existing core stays identical (this ADDS a theorem + route; touches
no existing proof).
