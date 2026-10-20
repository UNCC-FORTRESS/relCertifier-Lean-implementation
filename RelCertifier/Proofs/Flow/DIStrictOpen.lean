/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Strict invariant components: open-sublevel preservation (`g < 0`)

Extension `strict-atoms`. An invariant row may contain a strict atom, lowered to a
component `g` with the meaning `g < 0` (instead of `g ≤ 0`). The existing chain proves
`g ≤ 0` per component (`BoxLe`); this file proves the strict conclusion `BoxLt` for the
two query routes that support it:

* **route A** (whole domain, `domain ∧ ġ > 0` UNSAT): `g` is antitone along the flow, so
  `g(ω) ≤ g(ν) < 0` (`DI_lt_domain`, by shifting `g` by its initial value and reusing
  dL-lean's `DI_nonstrict_domain`);
* **route B** (strict boundary, `domain ∧ g = 0 ∧ ġ ≥ 0` UNSAT): a first-touch argument
  (`DI_lt_strict`): at the infimum `s` of the times where `g ≥ 0`, `g = 0` and every slope
  from the left is positive, contradicting `Lie < 0` at the boundary.

Route C (superlevel, `domain ∧ g ≥ 0 ∧ ġ > 0` UNSAT) does NOT preserve `g < 0`:
`g = −(t−1)²` along `t' = 1` meets its hypothesis and reaches `0` at `t = 1`. Strict
components are therefore never certified by route C.

No new axiom; the only trusted leaf stays the Z3 UNSAT verdict in the IO shell.
-/
import RelCertifier.Core.FlowCert

set_option linter.unusedFintypeInType false

open DL Set

namespace RelCertifier

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Semantic box over the open sublevel predicate `g < 0`. -/
def BoxLt (α : Program V) (g : State V → ℝ) (ν : State V) : Prop :=
  ∀ ω, Program.sem α ν ω → g ω < 0

/-- `BoxLt` implies `BoxLe` (the closure); the weakening every existing consumer uses. -/
theorem BoxLt.toBoxLe {α : Program V} {g : State V → ℝ} {ν : State V}
    (h : BoxLt α g ν) : BoxLe α g ν :=
  fun ω hω => le_of_lt (h ω hω)

/-- The Lie derivative ignores an additive constant. -/
theorem Lie_sub_const (sys : ODESystem V) (g : State V → ℝ) (c : ℝ) (x : State V) :
    Lie sys (fun y => g y - c) x = Lie sys g x := by
  unfold Lie
  congr 1
  refine List.map_congr_left (fun p _ => ?_)
  rw [fderiv_sub_const]

/-- **Route A, strict.** `Lie ≤ 0` throughout the domain and `g ν < 0` give `g < 0`
after every run: `g` is antitone along the flow. -/
theorem DI_lt_domain {sys : ODESystem V} {ψ : Formula V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, Formula.sat ψ x → Lie sys g x ≤ 0)
    {ν : State V} (hinit : g ν < 0) : BoxLt (Program.ode sys ψ) g ν := by
  have hshift : BoxLe (Program.ode sys ψ) (fun y => g y - g ν) ν :=
    DI_nonstrict_domain hwf (hg.sub_const (g ν))
      (fun x hx => by rw [Lie_sub_const]; exact hbnd x hx) (by simp)
  intro ω hω
  have := hshift ω hω
  linarith

/-- **Route B, strict.** `Lie < 0` on the boundary `{g = 0}` within the domain and
`g ν < 0` give `g < 0` after every run (first-touch argument). -/
theorem DI_lt_strict {sys : ODESystem V} {ψ : Formula V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, Formula.sat ψ x → g x = 0 → Lie sys g x < 0)
    {ν : State V} (hinit : g ν < 0) : BoxLt (Program.ode sys ψ) g ν := by
  intro ω hrun
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hcurve, hdom⟩ := (sem_ode_iff_integralCurve hwf).mp hrun
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun t ht => hasDeriv_g_along_flow hwf hg hcurve ht
  have hcont : ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  rw [show ω = Φ r from hΦr.symm]
  by_contra hcon
  rw [not_lt] at hcon
  -- the times where the flow is at or above the boundary; nonempty (contains `r`)
  set S : Set ℝ := Set.Icc 0 r ∩ (fun s => g (Φ s)) ⁻¹' Set.Ici 0 with hSdef
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hrS : r ∈ S := ⟨Set.right_mem_Icc.mpr hr, hcon⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set s := sInf S with hsdef
  have hsS : s ∈ S := hSclosed.csInf_mem ⟨r, hrS⟩ hSbdd
  have hsIcc : s ∈ Set.Icc 0 r := hsS.1
  have hsge0 : 0 ≤ g (Φ s) := hsS.2
  have hs_lb : ∀ t ∈ S, s ≤ t := fun t htS => csInf_le hSbdd htS
  clear_value s
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hsIcc.1 with h | h
    · exact h
    · exfalso
      have : g (Φ s) < 0 := by rw [← h, hΦ0]; exact hinit
      linarith
  -- to the left of the infimum the flow is strictly below the boundary
  have hneg : ∀ t ∈ Set.Ico 0 s, g (Φ t) < 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 r := ⟨ht.1, le_trans (le_of_lt ht.2) hsIcc.2⟩
    have htnS : t ∉ S := fun htS => absurd (hs_lb t htS) (not_le.mpr ht.2)
    exact not_le.mp (fun h => htnS ⟨htIcc, h⟩)
  have hIcoIcc : Set.Ico 0 s ⊆ Set.Icc 0 r :=
    fun t ht => ⟨ht.1, le_trans (le_of_lt ht.2) hsIcc.2⟩
  have hmem : s ∈ closure (Set.Ico 0 s) := by
    rw [closure_Ico (ne_of_lt hspos)]; exact Set.right_mem_Icc.mpr (le_of_lt hspos)
  haveI : (nhdsWithin s (Set.Ico 0 s)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  -- the boundary value is exactly 0 (≥0 from S, ≤0 as a left limit)
  have hle0 : g (Φ s) ≤ 0 := by
    have htend := (hcont s hsIcc).mono_left (nhdsWithin_mono s hIcoIcc)
    exact le_of_tendsto htend
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => le_of_lt (hneg t ht)))
  have hgeq0 : g (Φ s) = 0 := le_antisymm hle0 hsge0
  have hLie : Lie sys g (Φ s) < 0 := hbnd (Φ s) (hdom s hsIcc) hgeq0
  -- but every slope from the left is positive, so the derivative cannot be negative
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv s hsIcc)).mono_left
    (nhdsWithin_mono s (fun t ht => ⟨hIcoIcc ht, ne_of_lt ht.2⟩))
  have hslopepos : ∀ᶠ t in nhdsWithin s (Set.Ico 0 s),
      0 < slope (fun t => g (Φ t)) s t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    have h1 : g (Φ t) - g (Φ s) < 0 := by rw [hgeq0]; simpa using hneg t ht
    have h2 : t - s < 0 := by linarith [ht.2]
    exact div_pos_of_neg_of_neg h1 h2
  exact absurd (ge_of_tendsto hslope (hslopepos.mono fun t h => le_of_lt h)) (not_le.mpr hLie)

end Generic

/-! ## Flow-certificate wrappers (the two strict-capable routes) -/

/-- **Route A, strict conclusion.** The domain query `domain ∧ ġ > 0` UNSAT and `g ν < 0`
give `g < 0` along the λ-stretched co-evolution. Same query as `flow_cert_sound`. -/
theorem flow_cert_sound_lt {n : ℕ} (o : FlowObligation n) {ν : State (Var n)}
    (hunsat : ∀ σ, ¬ Formula.sat (flowQuery o) σ)
    (hinit : Term.eval o.g ν < 0) :
    BoxLt (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) ν := by
  refine DI_lt_domain (jointSys_wellFormed o.fL o.fR o.lam)
    (term_differentiable o.g) ?_ hinit
  intro x hx
  rw [← lieDeriv_correct]
  by_contra hpos
  rw [not_le] at hpos
  exact hunsat x ⟨hx, by simpa [flowQuery, Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-- **Route B, strict conclusion.** The strict boundary query `domain ∧ g = 0 ∧ ġ ≥ 0`
UNSAT and `g ν < 0` give `g < 0`. Same query as `flow_cert_sound_strict`. -/
theorem flow_cert_sound_strict_lt {n : ℕ} (o : FlowObligation n) {ν : State (Var n)}
    (hunsat : ∀ σ, ¬ Formula.sat (flowQueryStrict o) σ)
    (hinit : Term.eval o.g ν < 0) :
    BoxLt (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) ν := by
  refine DI_lt_strict (jointSys_wellFormed o.fL o.fR o.lam)
    (term_differentiable o.g) ?_ hinit
  intro x hx hg0
  rw [← lieDeriv_correct]
  by_contra hpos
  rw [not_lt] at hpos
  exact hunsat x ⟨hx, hg0, by simpa [Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-! ## Route C does not preserve the open sublevel

`g = −(t−1)²` along `t' = 1` from `t = 0`: `g(0) = −1 < 0`; wherever `g ≥ 0` (only at
`t = 1`) the derivative `−2(t−1)` is `0`, so the superlevel query `g ≥ 0 ∧ ġ > 0` is
UNSAT, yet the flow reaches `g = 0` at `t = 1`. The arithmetic core: -/

theorem routeC_counterexample :
    (∀ t : ℝ, -(t - 1) ^ 2 ≥ 0 → ¬ (-2 * (t - 1) > 0)) ∧
    -((0:ℝ) - 1) ^ 2 < 0 ∧ -((1:ℝ) - 1) ^ 2 = 0 := by
  refine ⟨fun t ht hd => ?_, by norm_num, by norm_num⟩
  have h0 : (t - 1) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  have : t - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h0
  rw [this] at hd
  norm_num at hd

end RelCertifier
