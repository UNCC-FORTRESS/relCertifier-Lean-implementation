/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `DI_nonstrict_superlevel` — the Lyapunov-barrier differential invariant

The sound route that certifies the marginal contraction / Lyapunov-energy class (the 22
Cat-1 declines): `Lie(g) ≤ 0` **wherever `g ≥ 0`** (the superlevel side, within the domain
`ψ`) ⟹ `g ≤ 0` is forward-invariant. This is elementary Lyapunov invariance — strictly
weaker in hypothesis than `DI_nonstrict_domain` (which needs `Lie ≤ 0` on ALL of `ψ`), so
it sees contraction invariants whose Lie is `≤ 0` only on `{g ≥ 0}`.

Sound with NO regularity/subtangency hypothesis: the `t²` pathology is rejected because
`Lie = 2x > 0` on `{x > 0} ⊆ {g ≥ 0}` fails the hypothesis. Equilibria and irregular
boundary points need no special case — they lie in `{g ≥ 0}` (`g = 0`) with `Lie = 0 ≤ 0`.

Proven here from dL-lean's PUBLIC API (`sem_ode_iff_integralCurve`,
`hasDeriv_g_along_flow`, `Lie`, `BoxLe`) — dL-lean itself is untouched. The argument is a
hybrid of `DI_strict` (the `sSup` first-escape setup) and `DI_nonstrict_domain` (the
`antitoneOn_of_deriv_nonpos` close), both already in `DLLean/DI.lean`.
-/
import DLLean

namespace DL

open Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Differential invariant, non-strict superlevel (Lyapunov) form.** If `g ν ≤ 0` and
`Lie(g) ≤ 0` at every domain state with `g ≥ 0`, then `g ≤ 0` is preserved along the flow.
No regularity hypothesis; the `{g ≥ 0}` restriction is exactly what rejects the `t²`
degeneracy (interior positivity of `Lie`) while admitting `Lie = 0` on the boundary. -/
theorem DI_nonstrict_superlevel {sys : ODESystem V} {ψ : Formula V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, Formula.sat ψ x → 0 ≤ g x → Lie sys g x ≤ 0)
    {ν : State V} (hinit : g ν ≤ 0) : BoxLe (Program.ode sys ψ) g ν := by
  intro ω hrun
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hcurve, hdom⟩ := (sem_ode_iff_integralCurve hwf).mp hrun
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun t ht => hasDeriv_g_along_flow hwf hg hcurve ht
  have hcont : ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  rw [show ω = Φ r from hΦr.symm]
  by_contra hcon
  rw [not_le] at hcon
  -- first-escape supremum (verbatim from `DI_strict`)
  set S : Set ℝ := Set.Icc 0 r ∩ (fun s => g (Φ s)) ⁻¹' Set.Iic 0 with hSdef
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have h0S : (0:ℝ) ∈ S :=
    ⟨Set.left_mem_Icc.mpr hr, by simp only [Set.mem_preimage, Set.mem_Iic]; rw [hΦ0]; exact hinit⟩
  have hSbdd : BddAbove S := ⟨r, fun t ht => ht.1.2⟩
  set s := sSup S with hsdef
  have hsS : s ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hSbdd
  have hsIcc : s ∈ Set.Icc 0 r := hsS.1
  have hsle0 : g (Φ s) ≤ 0 := hsS.2
  have hs_ub : ∀ t ∈ S, t ≤ s := fun t htS => le_csSup hSbdd htS
  clear_value s
  have hsr : s < r :=
    lt_of_le_of_ne hsIcc.2 (by rintro rfl; exact absurd hsle0 (not_le.mpr hcon))
  have hpos : ∀ t ∈ Set.Ioc s r, 0 < g (Φ t) := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 r := ⟨le_trans hsIcc.1 (le_of_lt ht.1), ht.2⟩
    have htnS : t ∉ S := fun htS => absurd (hs_ub t htS) (not_le.mpr ht.1)
    exact not_le.mp (fun h => htnS ⟨htIcc, h⟩)
  -- boundary value is exactly 0
  have hIocIcc : Set.Ioc s r ⊆ Set.Icc 0 r :=
    fun t ht => ⟨le_trans hsIcc.1 (le_of_lt ht.1), ht.2⟩
  have hmem : s ∈ closure (Set.Ioc s r) := by
    rw [closure_Ioc (ne_of_lt hsr)]; exact Set.left_mem_Icc.mpr (le_of_lt hsr)
  haveI hneBot : (nhdsWithin s (Set.Ioc s r)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have hge0 : 0 ≤ g (Φ s) := by
    have htend := (hcont s hsIcc).mono_left (nhdsWithin_mono s hIocIcc)
    exact ge_of_tendsto htend
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => le_of_lt (hpos t ht)))
  have hgeq0 : g (Φ s) = 0 := le_antisymm hsle0 hge0
  -- KEY: on `[s,r]` the flow is on the superlevel side `g ≥ 0`, so `Lie ≤ 0` ⟹ antitone
  have hge0_on : ∀ t ∈ Set.Icc s r, 0 ≤ g (Φ t) := by
    intro t ht
    obtain h | h := ht.1.eq_or_lt
    · rw [← h]; exact hgeq0.ge
    · exact le_of_lt (hpos t ⟨h, ht.2⟩)
  have hanti : AntitoneOn (fun t => g (Φ t)) (Set.Icc s r) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s r)
      (hcont.mono (Set.Icc_subset_Icc hsIcc.1 le_rfl)) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      have hx0 : (0:ℝ) < x := lt_of_le_of_lt hsIcc.1 hx.1
      have hxIcc : x ∈ Set.Icc 0 r := ⟨le_of_lt hx0, le_of_lt hx.2⟩
      exact ((hderiv x hxIcc).hasDerivAt
        (Icc_mem_nhds hx0 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hx0 : (0:ℝ) < x := lt_of_le_of_lt hsIcc.1 hx.1
      have hxIcc : x ∈ Set.Icc 0 r := ⟨le_of_lt hx0, le_of_lt hx.2⟩
      rw [((hderiv x hxIcc).hasDerivAt (Icc_mem_nhds hx0 hx.2)).deriv]
      exact hbnd (Φ x) (hdom x hxIcc) (hge0_on x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hfin : g (Φ r) ≤ g (Φ s) :=
    hanti (Set.left_mem_Icc.mpr (le_of_lt hsr)) (Set.right_mem_Icc.mpr (le_of_lt hsr))
      (le_of_lt hsr)
  rw [hgeq0] at hfin
  exact absurd hfin (not_le.mpr hcon)

end DL
