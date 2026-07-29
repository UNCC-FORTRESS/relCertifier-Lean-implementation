/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L3 — the intra-piece switch coupling (B-first split)

Five benchmarks (`arm_chain_rung1/2`, `arm_fidelity_low`, `arm_refinement`,
`plant_fan_low`) have landing modes with a genuinely outward evolve face
(`θ' = const > 0` against a bounded band): a full-duration single-mode piece leaves
the envelope, so the response must SWITCH modes inside one left piece. The measured
design: run the escape mode `B` first for the FIXED fraction `θ = M_A/(M_A+M_B)` of
the left duration, then the certified mode `A` for the rest — the rise in `A` exactly
cancels the drop in `B`, and only the `B` stretch is charged against the invariant.

The construction mirrors `faModal_ODE_G'_bounded` with a TWO-PHASE right trajectory:

* phase 1 (`[0, θs]`): the `B`-witness pairs against the left run RESTRICTED to
  `[0, θs]`; the merged joint flow charges the invariant by at most `MgB·θs`
  (`growth_along_dom`), covered by the anchor budget `g(ω) + MgB·θ·dt ≤ 0`;
* phase 2 (`[θs, s]`): the switch state is a `g ≤ 0` state, so the `A`-mode joint
  certificate box (`hboxA`, anchored at ANY such state — the `segPresAll` shape)
  carries `φ'` to the end; the `A`-witness pairs against the left run SHIFTED to
  `[θs, s]`, frame-patched to the switch state's right coordinates;
* the response run `seq B A` from the left endpoint is assembled from the two
  witnesses by frame patching (`patched_run` — each phase's system reads only its
  own bound frame, so off-frame repatching preserves runs).

New leaf (imports `EnvelopeChain`); no upstream edits.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Flow.BoxViabilityBounded

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-! ## Frame patching -/

/-- The frame patch: keep the system's bound coordinates from `Φ`, freeze the rest
at `β`. -/
def framePatch (sys : ODESystem (Var n)) (Φ : ℝ → State (Var n))
    (β : State (Var n)) : ℝ → State (Var n) :=
  fun u x => if x ∈ sys.bound then Φ u x else β x

/-- Repatch a run's off-bound coordinates to a state agreeing on the bound frame:
still a run (the system reads only its bound frame), from the new base. -/
theorem patched_run (sys : ODESystem (Var n)) (hreads : sys.readVars ⊆ sys.boundSet)
    {r : ℝ} {Φ : ℝ → State (Var n)} {ω β : State (Var n)}
    (hΦ0 : Φ 0 = ω)
    (hder : ∀ t ∈ Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t)
    (hβ : ∀ x ∈ sys.bound, β x = ω x) :
    framePatch sys Φ β 0 = β ∧
    (∀ t ∈ Icc (0:ℝ) r, ∀ x ∈ sys.boundSet, framePatch sys Φ β t x = Φ t x) ∧
    (∀ t ∈ Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => framePatch sys Φ β u p.1)
        (p.2.eval (framePatch sys Φ β t)) (Icc 0 r) t) ∧
    (∀ t ∈ Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → framePatch sys Φ β t x = β x) := by
  have hbs : ∀ x, x ∈ sys.boundSet ↔ x ∈ sys.bound := fun x => Iff.rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    by_cases hx : x ∈ sys.bound
    · show (if x ∈ sys.bound then Φ 0 x else β x) = β x
      rw [if_pos hx, hΦ0, ← hβ x hx]
    · show (if x ∈ sys.bound then Φ 0 x else β x) = β x
      rw [if_neg hx]
  · intro t ht x hx
    show (if x ∈ sys.bound then Φ t x else β x) = Φ t x
    rw [if_pos ((hbs x).mp hx)]
  · intro t ht p hp
    have hpb : p.1 ∈ sys.bound := List.mem_map.mpr ⟨p, hp, rfl⟩
    have hfun : (fun u => framePatch sys Φ β u p.1) = fun u => Φ u p.1 := by
      funext u
      show (if p.1 ∈ sys.bound then Φ u p.1 else β p.1) = Φ u p.1
      rw [if_pos hpb]
    have hev : p.2.eval (framePatch sys Φ β t) = p.2.eval (Φ t) := by
      refine Term.coincidence _ ?_
      intro v hv
      have hvr : v ∈ sys.readVars := ⟨p, hp, hv⟩
      show (if v ∈ sys.bound then Φ t v else β v) = Φ t v
      rw [if_pos ((hbs v).mp (hreads hvr))]
    rw [hfun, hev]
    exact hder t ht p hp
  · intro t ht x hx
    show (if x ∈ sys.bound then Φ t x else β x) = β x
    rw [if_neg hx]

/-! ## Domain-conditioned linear growth along a joint run -/

/-- `growth_along` with FORMULA conditioning: along a joint run staying in `D`, if
`Lie g ≤ M` on `D`, then `g` grows at most linearly. -/
theorem growth_along_dom {sys : ODESystem (Var n)} (hwf : sys.WellFormed)
    (g : Term (Var n)) (M : ℝ) (D : Formula (Var n))
    (hbnd : ∀ x : State (Var n), Formula.sat D x →
      Lie sys (fun ω => Term.eval g ω) x ≤ M)
    {r : ℝ} {Φ : ℝ → State (Var n)} (hr : 0 ≤ r)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hdom : ∀ t ∈ Set.Icc (0:ℝ) r, Formula.sat D (Φ t)) :
    Term.eval g (Φ r) ≤ Term.eval g (Φ 0) + M * r := by
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => Term.eval g (Φ s))
        (Lie sys (fun ω => Term.eval g ω) (Φ t)) (Set.Icc 0 r) t :=
    fun t ht => hasDeriv_g_along_flow hwf (term_differentiable g) hcurve ht
  have hanti : AntitoneOn (fun u => Term.eval g (Φ u) - M * u) (Set.Icc 0 r) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) ?_ ?_ ?_
    · intro t ht
      exact ((hderiv t ht).sub ((hasDerivWithinAt_id t _).const_mul M)).continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have huIcc := Set.Ioo_subset_Icc_self hu
      have hd : HasDerivAt (fun v => Term.eval g (Φ v) - M * v)
          (Lie sys (fun ω => Term.eval g ω) (Φ u) - M) u := by
        refine HasDerivAt.sub ?_ (by simpa using (hasDerivAt_id u).const_mul M)
        exact (hderiv u huIcc).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
      exact hd.differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have huIcc := Set.Ioo_subset_Icc_self hu
      have hd : HasDerivAt (fun v => Term.eval g (Φ v) - M * v)
          (Lie sys (fun ω => Term.eval g ω) (Φ u) - M) u := by
        refine HasDerivAt.sub ?_ (by simpa using (hasDerivAt_id u).const_mul M)
        exact (hderiv u huIcc).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
      rw [hd.deriv]
      have := hbnd (Φ u) (hdom u huIcc)
      linarith
  have := hanti (Set.left_mem_Icc.mpr hr) (Set.right_mem_Icc.mpr hr) hr
  simp only [mul_zero, sub_zero] at this
  linarith

/-- Assemble a run tuple into an integral curve (the `sem_ode_iff_integralCurve` mp
body, exposed for SAME-CURVE reuse — the budget must integrate along the curve we
merged, not an existentially repackaged one). -/
theorem integralCurve_of_tuple {sys : ODESystem (Var n)} (hwf : sys.WellFormed)
    {r : ℝ} {Φ : ℝ → State (Var n)} {ν : State (Var n)}
    (hder : ∀ t ∈ Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t)
    (hmask : ∀ t ∈ Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = ν x) :
    IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r) := by
  intro t ht
  rw [hasDerivWithinAt_pi]
  intro i
  show HasDerivWithinAt (fun u => Φ u i) (odeField sys (Φ t) i) (Icc 0 r) t
  by_cases hi : i ∈ sys.bound
  · obtain ⟨p, hp_mem, hp1⟩ := List.mem_map.mp hi
    subst hp1
    have hfield : odeField sys (Φ t) p.1 = p.2.eval (Φ t) := by
      simp only [odeField, if_pos hi, ODESystem.rhs_eq_of_mem hwf hp_mem]
    rw [hfield]
    exact hder t ht p hp_mem
  · have hfield : odeField sys (Φ t) i = 0 := by simp only [odeField, if_neg hi]
    rw [hfield]
    exact (hasDerivWithinAt_const t (Set.Icc 0 r) (ν i)).congr
      (fun y hy => hmask y hy i hi) (hmask t ht i hi)

/-! ## The split coupling -/

/-- **The B-first split coupling, drop-tracked.** One clocked left piece against the
two-phase response `B ; A`: `B` for the fixed fraction `θ` of the left duration (the
invariant charged at most `MgB·θ·dt`, covered by the anchor budget), then the
certified `A` for the rest (the `A` joint box carries `φ'` from the switch state, a
`g ≤ 0` state).

The A-phase existence hypothesis additionally receives the QUANTITATIVE drop `B`
achieved on the tracked coordinate `xj` (`κ' xj ≤ ω xj − cB·s₁`, from `hjrow` via
`growth_along_dom`) together with the split fraction identity
`(1 − θ)·s₁ = θ·s₂` — with `θ = cA/(cA + cB)` the instance's A-rise then cancels
the B-drop from any anchor at or below the outward face (the §8 interface fix in
docs/INTRA-PIECE-SWITCH-SCOPE.md). -/
theorem faModal_ODE_split_bounded
    (sysX sysB sysA : ODESystem (Var n))
    (φx φyB φyA φ' : Formula (Var n))
    (g : Term (Var n)) (MgB : ℝ) (hMgB : 0 ≤ MgB)
    (xj : Var n) (cB : ℝ)
    (θ dt : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (tg : Var n) (htg : (tg, Term.const 1) ∈ sysX)
    (hwfXB : (sysX ++ sysB).WellFormed)
    (hdisjB : Disjoint (sysX.boundSet ∪ sysX.readVars)
      (sysB.boundSet ∪ sysB.readVars))
    (hdisjA : Disjoint (sysX.boundSet ∪ sysX.readVars)
      (sysA.boundSet ∪ sysA.readVars))
    (hφx : φx.fv ⊆ sysX.boundSet ∪ sysX.readVars)
    (hφyB : φyB.fv ⊆ sysB.boundSet)
    (hφyA : φyA.fv ⊆ sysA.boundSet ∪ sysA.readVars)
    (hXreads : sysX.readVars ⊆ sysX.boundSet)
    (hBreads : sysB.readVars ⊆ sysB.boundSet)
    (hAreads : sysA.readVars ⊆ sysA.boundSet)
    (hABb : ∀ x, x ∈ sysA.bound ↔ x ∈ sysB.bound)
    (ω : State (Var n))
    (hbndB : ∀ x : State (Var n), Formula.sat (Formula.and φx φyB) x →
      Lie (sysX ++ sysB) (fun ν => Term.eval g ν) x ≤ MgB)
    (hjrow : ∀ x : State (Var n), Formula.sat (Formula.and φx φyB) x →
      Lie (sysX ++ sysB) (fun ν => Term.eval (Term.var xj) ν) x ≤ -cB)
    (hg0 : Term.eval g ω + MgB * (θ * dt) ≤ 0)
    (hboxA : ∀ κ : State (Var n), Term.eval g κ ≤ 0 →
      Formula.sat (Formula.box (Program.ode (sysX ++ sysA)
        (Formula.and φx φyA)) φ') κ)
    (hExistB : ∀ (s1 : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s1 → s1 ≤ θ * dt →
      ΦL 0 = ω →
      (∀ t ∈ Icc (0:ℝ) s1, ∀ p ∈ sysX,
        HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s1) t) →
      (∀ t ∈ Icc (0:ℝ) s1, ∀ x, x ∉ sysX.bound → ΦL t x = ω x) →
      (∀ t ∈ Icc (0:ℝ) s1, Formula.sat φx (ΦL t)) →
      ∃ ΦB : ℝ → State (Var n), ΦB 0 = ΦL s1 ∧
        (∀ t ∈ Icc (0:ℝ) s1, ∀ p ∈ sysB,
          HasDerivWithinAt (fun u => ΦB u p.1) (p.2.eval (ΦB t)) (Icc 0 s1) t) ∧
        (∀ t ∈ Icc (0:ℝ) s1, ∀ x, x ∉ sysB.bound → ΦB t x = ΦL s1 x) ∧
        (∀ t ∈ Icc (0:ℝ) s1, Formula.sat φyB (ΦB t)))
    (hExistA : ∀ (s1 s2 : ℝ) (ΨL : ℝ → State (Var n)) (κ' : State (Var n)),
      0 ≤ s1 → 0 ≤ s2 → s2 ≤ dt → (1 - θ) * s1 = θ * s2 →
      κ' xj ≤ ω xj - cB * s1 → ΨL 0 = κ' →
      (∀ t ∈ Icc (0:ℝ) s2, ∀ p ∈ sysX,
        HasDerivWithinAt (fun u => ΨL u p.1) (p.2.eval (ΨL t)) (Icc 0 s2) t) →
      (∀ t ∈ Icc (0:ℝ) s2, ∀ x, x ∉ sysX.bound → ΨL t x = κ' x) →
      (∀ t ∈ Icc (0:ℝ) s2, Formula.sat φx (ΨL t)) →
      Formula.sat φyB κ' → Term.eval g κ' ≤ 0 →
      ∃ ΦA : ℝ → State (Var n), ΦA 0 = ΨL s2 ∧
        (∀ t ∈ Icc (0:ℝ) s2, ∀ p ∈ sysA,
          HasDerivWithinAt (fun u => ΦA u p.1) (p.2.eval (ΦA t)) (Icc 0 s2) t) ∧
        (∀ t ∈ Icc (0:ℝ) s2, ∀ x, x ∉ sysA.bound → ΦA t x = ΨL s2 x) ∧
        (∀ t ∈ Icc (0:ℝ) s2, Formula.sat φyA (ΦA t))) :
    faModalB (Equiv.refl (Var n)) (Program.ode sysX φx)
      (Program.seq (Program.ode sysB φyB) (Program.ode sysA φyA)) φ' tg dt ω := by
  classical
  intro ν hplant
  obtain ⟨⟨s, ΦL, hs, hΦL0, hΦLs, hLder, hLmaskF, hLdom⟩, hbound⟩ := hplant
  have hsdt : s ≤ dt := by
    have H : ODESol sysX φx ω s ΦL := ⟨hs, hΦL0, hLder, hLmaskF, hLdom⟩
    have haff := tg_track H htg
    have : ΦL s tg = ΦL 0 tg + s := haff s (right_mem_Icc.mpr hs)
    rw [hΦLs, hΦL0] at this
    have hνtg : ν tg = ω tg + s := this
    rw [hνtg] at hbound
    linarith
  set s1 := θ * s with hs1def
  have hs1 : 0 ≤ s1 := mul_nonneg hθ0 hs
  have hs1s : s1 ≤ s := by nlinarith
  have hs1dt : s1 ≤ θ * dt := by nlinarith
  set s2 := s - s1 with hs2def
  have hs2 : 0 ≤ s2 := by simp [hs2def]; linarith
  have hs2dt : s2 ≤ dt := by simp [hs2def]; linarith
  have hsub1 : Icc (0:ℝ) s1 ⊆ Icc (0:ℝ) s := Icc_subset_Icc_right hs1s
  -- phase 1: the B-witness against the restricted left run
  have hLder1 : ∀ t ∈ Icc (0:ℝ) s1, ∀ p ∈ sysX,
      HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s1) t :=
    fun t ht p hp => (hLder t (hsub1 ht) p hp).mono hsub1
  have hLmask1 : ∀ t ∈ Icc (0:ℝ) s1, ∀ x, x ∉ sysX.bound → ΦL t x = ω x :=
    fun t ht x hx => hLmaskF t (hsub1 ht) x hx
  have hLdom1 : ∀ t ∈ Icc (0:ℝ) s1, Formula.sat φx (ΦL t) :=
    fun t ht => hLdom t (hsub1 ht)
  obtain ⟨ΦB, hB0, hBder, hBmask, hBdom⟩ :=
    hExistB s1 ΦL hs1 hs1dt hΦL0 hLder1 hLmask1 hLdom1
  have hdlB := Set.disjoint_left.mp hdisjB
  have hnotXofB : ∀ x ∈ sysB.bound, x ∉ sysX.bound := fun x hxB hxX =>
    hdlB (Or.inl hxX) (Or.inl hxB)
  obtain ⟨hΦ10, hag1L, hag1R, hJ1der, hJ1mask⟩ :=
    ode_combine sysX sysB hdisjB ω s1 ΦL ΦB hΦL0
      (fun x hx => by rw [hB0]; exact hLmask1 s1 (right_mem_Icc.mpr hs1) x (hnotXofB x hx))
      (fun t ht x _ hxb => hLmask1 t ht x hxb)
      (fun t ht x hxr hxb => absurd (hBreads hxr) hxb)
      hLder1 hBder
  set Φ₁ := mergeTraj ω sysX sysB ΦL ΦB with hΦ₁
  have hφxΦ₁ : ∀ t ∈ Icc (0:ℝ) s1, Formula.sat φx (Φ₁ t) := fun t ht =>
    (Formula.coincidence φx ((hag1L t ht).mono hφx)).mpr (hLdom1 t ht)
  have hφyBΦ₁ : ∀ t ∈ Icc (0:ℝ) s1, Formula.sat φyB (Φ₁ t) := fun t ht =>
    (Formula.coincidence φyB ((hag1R t ht).mono
      (hφyB.trans Set.subset_union_left))).mpr (hBdom t ht)
  -- phase-1 budget along the merged curve
  have hcurve₁ : IsIntegralCurveOn Φ₁ (fun _ => odeField (sysX ++ sysB))
      (Set.Icc 0 s1) :=
    integralCurve_of_tuple hwfXB (ν := ω) hJ1der hJ1mask
  have hg1 : Term.eval g (Φ₁ s1) ≤ Term.eval g ω + MgB * s1 := by
    have := growth_along_dom hwfXB g MgB (Formula.and φx φyB)
      hbndB hs1 hcurve₁ (fun t ht => ⟨hφxΦ₁ t ht, hφyBΦ₁ t ht⟩)
    rwa [hΦ10] at this
  set κ' := Φ₁ s1 with hκ'
  have hκ'g : Term.eval g κ' ≤ 0 := by
    have h1 : MgB * s1 ≤ MgB * (θ * dt) := mul_le_mul_of_nonneg_left hs1dt hMgB
    linarith
  have hκ'x : Formula.sat φx κ' := hφxΦ₁ s1 (right_mem_Icc.mpr hs1)
  have hκ'yB : Formula.sat φyB κ' := hφyBΦ₁ s1 (right_mem_Icc.mpr hs1)
  -- the tracked drop along the B phase
  have hκ'drop : κ' xj ≤ ω xj - cB * s1 := by
    have hgrow := growth_along_dom hwfXB (Term.var xj) (-cB) (Formula.and φx φyB)
      hjrow hs1 hcurve₁ (fun t ht => ⟨hφxΦ₁ t ht, hφyBΦ₁ t ht⟩)
    rw [hΦ10] at hgrow
    simp only [Term.eval] at hgrow
    rw [hκ']
    linarith
  have hfr : (1 - θ) * s1 = θ * s2 := by
    simp only [hs1def, hs2def]
    ring
  -- phase 2: the shifted, frame-patched left run from the switch state
  have hshift : ∀ t ∈ Icc (0:ℝ) s2, ∀ p ∈ sysX,
      HasDerivWithinAt (fun u => ΦL (s1 + u) p.1) (p.2.eval (ΦL (s1 + t)))
        (Icc 0 s2) t := by
    intro t ht p hp
    have htin : s1 + t ∈ Icc (0:ℝ) s := by
      constructor
      · linarith [ht.1]
      · have := ht.2; simp only [hs2def] at this; linarith
    have hσ : HasDerivWithinAt (fun u : ℝ => s1 + u) 1 (Icc 0 s2) t := by
      simpa using ((hasDerivWithinAt_id t (Icc (0:ℝ) s2)).const_add s1)
    have hmaps : Set.MapsTo (fun u : ℝ => s1 + u) (Icc 0 s2) (Icc 0 s) := by
      intro u hu
      constructor
      · linarith [hu.1]
      · have := hu.2; simp only [hs2def] at this; linarith
    have hcomp := HasDerivWithinAt.scomp t (hLder (s1 + t) htin p hp) hσ hmaps
    have hfun : (fun u => ΦL (s1 + u) p.1) = (fun v => ΦL v p.1) ∘ (fun u => s1 + u) :=
      rfl
    rw [hfun]
    simpa using hcomp
  have hβX : ∀ x ∈ sysX.bound, κ' x = ΦL s1 x := fun x hx =>
    hag1L s1 (right_mem_Icc.mpr hs1) (Or.inl (by exact hx))
  obtain ⟨hΨ0, hΨag, hΨder, hΨmask⟩ :=
    patched_run sysX hXreads (r := s2) (Φ := fun u => ΦL (s1 + u)) (ω := ΦL s1)
      (β := κ') (by simp) hshift hβX
  set ΨL := framePatch sysX (fun u => ΦL (s1 + u)) κ' with hΨL
  have hΨdom : ∀ t ∈ Icc (0:ℝ) s2, Formula.sat φx (ΨL t) := by
    intro t ht
    have hfv : φx.fv ⊆ sysX.boundSet := by
      intro v hv
      rcases hφx hv with hv | hv
      · exact hv
      · exact hXreads hv
    refine (Formula.coincidence φx (fun v hv => hΨag t ht v (hfv hv))).mpr ?_
    have htin : s1 + t ∈ Icc (0:ℝ) s := by
      constructor
      · linarith [ht.1]
      · have := ht.2; simp only [hs2def] at this; linarith
    exact hLdom (s1 + t) htin
  obtain ⟨ΦA, hA0, hAder, hAmask, hAdom⟩ :=
    hExistA s1 s2 ΨL κ' hs1 hs2 hs2dt hfr hκ'drop hΨ0 hΨder hΨmask hΨdom hκ'yB hκ'g
  have hdlA := Set.disjoint_left.mp hdisjA
  have hnotXofA : ∀ x ∈ sysA.bound, x ∉ sysX.bound := fun x hxA hxX =>
    hdlA (Or.inl hxX) (Or.inl hxA)
  obtain ⟨hΦ20, hag2L, hag2R, hJ2der, hJ2mask⟩ :=
    ode_combine sysX sysA hdisjA κ' s2 ΨL ΦA hΨ0
      (fun x hx => by rw [hA0]; exact hΨmask s2 (right_mem_Icc.mpr hs2) x (hnotXofA x hx))
      (fun t ht x _ hxb => hΨmask t ht x hxb)
      (fun t ht x hxr hxb => absurd (hAreads hxr) hxb)
      hΨder hAder
  set Φ₂ := mergeTraj κ' sysX sysA ΨL ΦA with hΦ₂
  have hφxΦ₂ : ∀ t ∈ Icc (0:ℝ) s2, Formula.sat φx (Φ₂ t) := fun t ht =>
    (Formula.coincidence φx ((hag2L t ht).mono hφx)).mpr (hΨdom t ht)
  have hφyAΦ₂ : ∀ t ∈ Icc (0:ℝ) s2, Formula.sat φyA (Φ₂ t) := fun t ht =>
    (Formula.coincidence φyA ((hag2R t ht).mono hφyA)).mpr (hAdom t ht)
  have hφ'end : Formula.sat φ' (Φ₂ s2) := by
    have hbox := hboxA κ' hκ'g
    rw [sat_box] at hbox
    refine hbox (Φ₂ s2) ⟨s2, Φ₂, hs2, hΦ20, rfl, hJ2der, hJ2mask, ?_⟩
    intro t ht
    exact ⟨hφxΦ₂ t ht, hφyAΦ₂ t ht⟩
  -- the response run: B from ν, then A
  have hβB : ∀ x ∈ sysB.bound, ν x = ΦL s1 x := by
    intro x hx
    have hν : ν = ΦL s := hΦLs.symm
    rw [hν, hLmaskF s (right_mem_Icc.mpr hs) x (hnotXofB x hx),
      ← hLmask1 s1 (right_mem_Icc.mpr hs1) x (hnotXofB x hx)]
  obtain ⟨hB''0, hB''ag, hB''der, hB''mask⟩ :=
    patched_run sysB hBreads (r := s1) (Φ := ΦB) (ω := ΦL s1) (β := ν) hB0 hBder hβB
  set ΦB'' := framePatch sysB ΦB ν with hΦB''
  have hB''dom : ∀ t ∈ Icc (0:ℝ) s1, Formula.sat φyB (ΦB'' t) := fun t ht =>
    (Formula.coincidence φyB (fun v hv => hB''ag t ht v (hφyB hv))).mpr (hBdom t ht)
  set κ := ΦB'' s1 with hκdef
  have hsemB : Program.sem (Program.ode sysB φyB) ν κ :=
    ⟨s1, ΦB'', hs1, hB''0, rfl, hB''der, hB''mask, hB''dom⟩
  have hβA : ∀ x ∈ sysA.bound, κ x = ΦA 0 x := by
    intro x hx
    have hxB : x ∈ sysB.bound := (hABb x).mp hx
    have h1 : κ x = ΦB s1 x := hB''ag s1 (right_mem_Icc.mpr hs1) x hxB
    have h2 : ΦA 0 x = κ' x := by
      rw [hA0]
      exact hΨmask s2 (right_mem_Icc.mpr hs2) x (hnotXofA x hx)
    have h3 : κ' x = ΦB s1 x := by
      show mergeTraj ω sysX sysB ΦL ΦB s1 x = ΦB s1 x
      simp only [mergeTraj, if_neg (hnotXofB x hxB), if_pos hxB]
    rw [h1, h2, h3]
  obtain ⟨hA''0, hA''ag, hA''der, hA''mask⟩ :=
    patched_run sysA hAreads (r := s2) (Φ := ΦA) (ω := ΦA 0) (β := κ) rfl hAder hβA
  set ΦA'' := framePatch sysA ΦA κ with hΦA''
  have hA''dom : ∀ t ∈ Icc (0:ℝ) s2, Formula.sat φyA (ΦA'' t) := by
    intro t ht
    have hfvA : φyA.fv ⊆ sysA.boundSet := by
      intro v hv
      rcases hφyA hv with hv | hv
      · exact hv
      · exact hAreads hv
    exact (Formula.coincidence φyA (fun v hv => hA''ag t ht v (hfvA hv))).mpr
      (hAdom t ht)
  set μ := ΦA'' s2 with hμdef
  have hsemA : Program.sem (Program.ode sysA φyA) κ μ :=
    ⟨s2, ΦA'', hs2, hA''0, rfl, hA''der, hA''mask, hA''dom⟩
  refine ⟨μ, ?_, ?_⟩
  · rw [Program.rename_refl]
    exact ⟨κ, hsemB, hsemA⟩
  · -- μ = Φ₂ s2, coordinatewise
    have hμeq : μ = Φ₂ s2 := by
      funext x
      by_cases hxA : x ∈ sysA.bound
      · have h1 : μ x = ΦA s2 x := hA''ag s2 (right_mem_Icc.mpr hs2) x hxA
        have h2 : Φ₂ s2 x = ΦA s2 x := by
          rw [hΦ₂]
          simp only [mergeTraj, if_neg (hnotXofA x hxA), if_pos hxA]
        rw [h1, h2]
      · have hxB : x ∉ sysB.bound := fun hc => hxA ((hABb x).mpr hc)
        have h1 : μ x = κ x := hA''mask s2 (right_mem_Icc.mpr hs2) x hxA
        have h2 : κ x = ν x := hB''mask s1 (right_mem_Icc.mpr hs1) x hxB
        by_cases hxX : x ∈ sysX.bound
        · have h3 : ν x = ΦL s x := by rw [← hΦLs]
          have h4 : Φ₂ s2 x = ΨL s2 x := by
            rw [hΦ₂]
            simp only [mergeTraj, if_pos hxX]
          have h5 : ΨL s2 x = ΦL (s1 + s2) x := hΨag s2 (right_mem_Icc.mpr hs2) x hxX
          have h6 : s1 + s2 = s := by simp [hs2def]
          rw [h1, h2, h3, h4, h5, h6]
        · have h3 : ν x = ω x := by
            rw [← hΦLs]
            exact hLmaskF s (right_mem_Icc.mpr hs) x hxX
          have h4 : Φ₂ s2 x = κ' x := by
            rw [hΦ₂]
            simp only [mergeTraj, if_neg hxX, if_neg hxA]
          have h5 : κ' x = ω x := by
            rw [hκ', hΦ₁]
            simp only [mergeTraj, if_neg hxX, if_neg hxB]
          rw [h1, h2, h3, h4, h5]
    rw [hμeq]
    exact hφ'end

/-- Per-anchor branch selection for a `choice` response: whichever side's coupling
fires at this anchor covers the choice (the diamond is a union of runs). The
instance's branch condition is the anchor's face distance — decidable classically. -/
theorem faModalB_choice_cases {P QB QA : Program (Var n)} {φ : Formula (Var n)}
    {tg : Var n} {dt : ℝ} {ω : State (Var n)} (c : Prop)
    (h1 : c → faModalB (Equiv.refl (Var n)) P QB φ tg dt ω)
    (h2 : ¬c → faModalB (Equiv.refl (Var n)) P QA φ tg dt ω) :
    faModalB (Equiv.refl (Var n)) P (Program.choice QB QA) φ tg dt ω := by
  classical
  intro ν hplant
  by_cases hc : c
  · obtain ⟨μ, hsem, hφ⟩ := h1 hc ν hplant
    rw [Program.rename_refl] at hsem ⊢
    exact ⟨μ, Or.inl hsem, hφ⟩
  · obtain ⟨μ, hsem, hφ⟩ := h2 hc ν hplant
    rw [Program.rename_refl] at hsem ⊢
    exact ⟨μ, Or.inr hsem, hφ⟩

end RelCertifier
