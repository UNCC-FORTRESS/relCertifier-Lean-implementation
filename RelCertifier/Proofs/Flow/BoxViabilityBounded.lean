/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S3 — bounded-time box viability (growth faces with entry budgets)

R6's census: only 9/126 modes pass the ALL-strict face gate — most evolve boxes have a
face the field approaches tangentially or reaches at equilibrium, where strict inflow
(`ġ < 0` on the face) legitimately fails. But the chain never needs unbounded time:
every window piece is clock-capped at `dt`. Bounded-time viability rescues those modes:

* **strict faces** keep R6's first-exit slope contradiction;
* **growth faces** get a box-conditioned Lie BOUND `ġ ≤ M` (`M ≥ 0` allowed) and an
  ENTRY BUDGET `g(start) + M·T < 0`: within time `T` the face value cannot climb to
  `0`, so the first exit can never happen through a growth face.

The first-exit argument runs over the GOOD-PREFIX supremum (all faces hold at all
earlier times), so the growth faces' derivative bound integrates along the prefix
(`antitoneOn_of_deriv_nonpos` on `g∘Φ − M·t`, the recurring pattern). The Z3 leaves:
strict faces reuse `face_strict_from_verdict`; growth faces get
`face_growth_from_verdict` (`UNSAT(box ∧ ġ > M)`, frozen-left, same printer).
-/
import RelCertifier.Proofs.Flow.BoxViability

namespace RelCertifier
open DL Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Bounded endpoint form.** Strict faces (box-conditioned strict inflow) + growth
faces (box-conditioned Lie bound `≤ M` with entry budget `g₀ + M·r < 0`) keep a raw
integral curve of duration `r` in the box. -/
theorem bounded_faces_endpoint {sys : ODESystem V} (hwf : sys.WellFormed)
    (gsS gsG : List (State V → ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hgS : ∀ g ∈ gsS, Differentiable ℝ g) (hgG : ∀ g ∈ gsG, Differentiable ℝ g)
    (hbndS : ∀ g ∈ gsS, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    (hbndG : ∀ g ∈ gsG, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → Lie sys g x ≤ M)
    {r : ℝ} {Φ : ℝ → State V} (hr : 0 ≤ r)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinitS : ∀ g ∈ gsS, g (Φ 0) ≤ 0)
    (hbudget : ∀ g ∈ gsG, g (Φ 0) + M * r < 0) :
    ∀ g ∈ gsS ++ gsG, g (Φ r) ≤ 0 := by
  set gs := gsS ++ gsG with hgs
  have hgall : ∀ g ∈ gs, Differentiable ℝ g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hgS g h
    · exact hgG g h
  have hderiv : ∀ g ∈ gs, ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun g hgm t ht => hasDeriv_g_along_flow hwf (hgall g hgm) hcurve ht
  have hcont : ∀ g ∈ gs, ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun g hgm t ht => (hderiv g hgm t ht).continuousWithinAt
  have hinit : ∀ g ∈ gs, g (Φ 0) ≤ 0 := by
    intro g hgm
    rcases List.mem_append.mp hgm with h | h
    · exact hinitS g h
    · nlinarith [hbudget g h, hM, hr]
  -- the GOOD-PREFIX time set (an interval: all faces hold at all earlier times)
  set S : Set ℝ := {u ∈ Set.Icc (0:ℝ) r | ∀ t ∈ Set.Icc 0 u, ∀ g ∈ gs, g (Φ t) ≤ 0}
    with hSdef
  have hSsub : S ⊆ Set.Icc 0 r := fun u hu => hu.1
  have hSdown : ∀ u ∈ S, ∀ v ∈ Set.Icc 0 u, v ∈ S := by
    intro u hu v hv
    exact ⟨⟨hv.1, le_trans hv.2 hu.1.2⟩,
      fun t ht g hgm => hu.2 t ⟨ht.1, le_trans ht.2 hv.2⟩ g hgm⟩
  have h0S : (0:ℝ) ∈ S := by
    refine ⟨Set.left_mem_Icc.mpr hr, ?_⟩
    intro t ht g hgm
    have : t = 0 := le_antisymm ht.2 ht.1
    subst this
    exact hinit g hgm
  have hSbdd : BddAbove S := ⟨r, fun t ht => ht.1.2⟩
  set s := sSup S with hsdef
  have hs0 : 0 ≤ s := le_csSup hSbdd h0S
  have hsr : s ≤ r := csSup_le ⟨0, h0S⟩ (fun t ht => ht.1.2)
  -- every t < s is good (downward closure + approximation to the sup)
  have hgood_lt : ∀ t, 0 ≤ t → t < s → ∀ g ∈ gs, g (Φ t) ≤ 0 := by
    intro t ht0 hts g hgm
    obtain ⟨u, huS, hu⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hts
    exact huS.2 t ⟨ht0, hu.le⟩ g hgm
  -- the sup itself is good (continuity from the left)
  have hgood_s : ∀ g ∈ gs, g (Φ s) ≤ 0 := by
    intro g hgm
    rcases eq_or_lt_of_le hs0 with h0 | h0
    · rw [← h0]; exact hinit g hgm
    · have hsIcc : s ∈ Set.Icc (0:ℝ) r := ⟨hs0, hsr⟩
      haveI hne : (nhdsWithin s (Set.Ico (0:ℝ) s)).NeBot := by
        apply mem_closure_iff_nhdsWithin_neBot.mp
        rw [closure_Ico h0.ne]
        exact Set.right_mem_Icc.mpr h0.le
      have htend := (hcont g hgm s hsIcc).mono_left
        (nhdsWithin_mono s (fun t (ht : t ∈ Set.Ico (0:ℝ) s) =>
          (⟨ht.1, le_trans ht.2.le hsr⟩ : t ∈ Set.Icc (0:ℝ) r)))
      refine le_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hgood_lt t ht.1 ht.2 g hgm
  have hsS : s ∈ S := by
    refine ⟨⟨hs0, hsr⟩, ?_⟩
    intro t ht g hgm
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h; exact hgood_s g hgm
    · exact hgood_lt t ht.1 h g hgm
  -- growth faces are STRICTLY negative on [0, s] (budget integrates along the prefix)
  have hgrowth_neg : ∀ g ∈ gsG, ∀ t ∈ Set.Icc (0:ℝ) s, g (Φ t) < 0 := by
    intro g hgm t ht
    have hgm' : g ∈ gs := List.mem_append_right _ hgm
    have htr : t ≤ r := le_trans ht.2 hsr
    -- h u := g (Φ u) − M·u is antitone on [0, t]
    have hanti : AntitoneOn (fun u => g (Φ u) - M * u) (Set.Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
      · intro u hu
        exact ((hderiv g hgm' u ⟨hu.1, le_trans hu.2 htr⟩).mono
          (Set.Icc_subset_Icc_right htr)).continuousWithinAt.sub
          ((continuous_const.mul continuous_id).continuousOn u hu)
      · intro u hu
        rw [interior_Icc] at hu
        have hd := (hderiv g hgm' u ⟨hu.1.le, le_trans hu.2.le htr⟩)
        have hd' : HasDerivAt (fun v => g (Φ v)) (Lie sys g (Φ u)) u := by
          refine (hd.mono (Set.Icc_subset_Icc_right htr)).hasDerivAt ?_
          exact Icc_mem_nhds hu.1 hu.2
        have hDM : HasDerivAt (fun v : ℝ => M * v) M u := by
          simpa using (hasDerivAt_id u).const_mul M
        have hD : HasDerivAt (fun v => g (Φ v) - M * v) (Lie sys g (Φ u) - M) u :=
          hd'.sub hDM
        exact hD.differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hd := (hderiv g hgm' u ⟨hu.1.le, le_trans hu.2.le htr⟩)
        have hd' : HasDerivAt (fun v => g (Φ v)) (Lie sys g (Φ u)) u := by
          refine (hd.mono (Set.Icc_subset_Icc_right htr)).hasDerivAt ?_
          exact Icc_mem_nhds hu.1 hu.2
        have hDM : HasDerivAt (fun v : ℝ => M * v) M u := by
          simpa using (hasDerivAt_id u).const_mul M
        have hD : HasDerivAt (fun v => g (Φ v) - M * v) (Lie sys g (Φ u) - M) u :=
          hd'.sub hDM
        rw [hD.deriv]
        have huS : ∀ g' ∈ gs, g' (Φ u) ≤ 0 :=
          fun g' hg' => hsS.2 u ⟨hu.1.le, le_trans hu.2.le ht.2⟩ g' hg'
        have := hbndG g hgm (Φ u) huS
        linarith
    have h0t : (0:ℝ) ∈ Set.Icc 0 t := Set.left_mem_Icc.mpr ht.1
    have htt : t ∈ Set.Icc (0:ℝ) t := Set.right_mem_Icc.mpr ht.1
    have := hanti h0t htt ht.1
    have hMt : M * t ≤ M * r := mul_le_mul_of_nonneg_left htr hM
    have hb := hbudget g hgm
    simp only [mul_zero, sub_zero] at this
    linarith
  -- if the sup is short of r, some face exits just after — it must be strict, contradiction
  rcases eq_or_lt_of_le hsr with hEq | hlt
  · intro g hgm
    rw [← hEq]
    exact hgood_s g hgm
  · exfalso
    -- arbitrarily close past the sup, some face is positive
    have hwit : ∀ u, s < u → u ≤ r → ∃ t, s < t ∧ t ≤ u ∧ ∃ g ∈ gs, 0 < g (Φ t) := by
      intro u hsu hur
      have hunS : u ∉ S := fun huS => absurd (le_csSup hSbdd huS) (not_le.mpr hsu)
      have hnall : ¬ ∀ t ∈ Set.Icc (0:ℝ) u, ∀ g ∈ gs, g (Φ t) ≤ 0 :=
        fun hall => hunS ⟨⟨le_trans hs0 hsu.le, hur⟩, hall⟩
      push_neg at hnall
      obtain ⟨t, ht, g, hgm, hgt⟩ := hnall
      have hts : s < t := by
        by_contra hle
        rw [not_lt] at hle
        exact absurd (hsS.2 t ⟨ht.1, hle⟩ g hgm) (not_le.mpr hgt)
      exact ⟨t, hts, ht.2, g, hgm, hgt⟩
    have hclU : s ∈ closure (⋃ g ∈ gs, {t | s < t ∧ t ≤ r ∧ 0 < g (Φ t)}) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hu1 : s < min r (s + ε/2) := lt_min hlt (by linarith)
      obtain ⟨t, hts, htu, g, hgm, hgt⟩ := hwit _ hu1 (min_le_left _ _)
      refine ⟨t, Set.mem_biUnion hgm
        ⟨hts, le_trans htu (min_le_left _ _), hgt⟩, ?_⟩
      have htε : t ≤ s + ε/2 := le_trans htu (min_le_right _ _)
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    obtain ⟨g, hgm, hcl⟩ := mem_closure_biUnion_list gs _ hclU
    set W : Set ℝ := {t | s < t ∧ t ≤ r ∧ 0 < g (Φ t)} with hWdef
    haveI hneBot : (nhdsWithin s W).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hWIcc : W ⊆ Set.Icc 0 r := fun t ht => ⟨le_trans hs0 ht.1.le, ht.2.1⟩
    have hsIcc : s ∈ Set.Icc (0:ℝ) r := ⟨hs0, hsr⟩
    have hge0 : 0 ≤ g (Φ s) := by
      have htend := (hcont g hgm s hsIcc).mono_left (nhdsWithin_mono s hWIcc)
      exact ge_of_tendsto htend
        (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht.2.2.le))
    have hgeq0 : g (Φ s) = 0 := le_antisymm (hgood_s g hgm) hge0
    -- growth faces are strictly negative at s — the exiting face is strict
    have hgmS : g ∈ gsS := by
      rcases List.mem_append.mp hgm with h | h
      · exact h
      · exact absurd hgeq0
          (ne_of_lt (hgrowth_neg g h s (Set.right_mem_Icc.mpr hs0)))
    have hLie : Lie sys g (Φ s) < 0 := hbndS g hgmS (Φ s) hgood_s hgeq0
    have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp
      (hderiv g hgm s hsIcc)).mono_left
      (nhdsWithin_mono s (fun t ht => ⟨hWIcc ht, ne_of_gt ht.1⟩))
    have hslopepos : ∀ᶠ t in nhdsWithin s W, 0 < slope (fun t => g (Φ t)) s t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field]
      exact div_pos (by rw [hgeq0]; simpa using ht.2.2) (by linarith [ht.1])
    exact absurd (ge_of_tendsto hslope (hslopepos.mono fun t h => le_of_lt h))
      (not_le.mpr hLie)

/-- All-times form: every point of a budgeted bounded run stays in the box. -/
theorem bounded_faces_raw {sys : ODESystem V} (hwf : sys.WellFormed)
    (gsS gsG : List (State V → ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hgS : ∀ g ∈ gsS, Differentiable ℝ g) (hgG : ∀ g ∈ gsG, Differentiable ℝ g)
    (hbndS : ∀ g ∈ gsS, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    (hbndG : ∀ g ∈ gsG, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → Lie sys g x ≤ M)
    {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinitS : ∀ g ∈ gsS, g (Φ 0) ≤ 0)
    (hbudget : ∀ g ∈ gsG, g (Φ 0) + M * r < 0) :
    ∀ t ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gsS ++ gsG, g (Φ t) ≤ 0 := by
  intro t ht
  have hsub : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 t) :=
    fun u hu => (hcurve u ⟨hu.1, le_trans hu.2 ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2)
  refine bounded_faces_endpoint hwf gsS gsG M hM hgS hgG hbndS hbndG ht.1 hsub hinitS ?_
  intro g hgm
  have := hbudget g hgm
  nlinarith [mul_le_mul_of_nonneg_left ht.2 hM]

/-- **Bounded-time box viability (S3 core).** Strict + growth face certificates and an
entry budget give a run of ANY duration `T` within the budget horizon, staying in the
box throughout — a SINGLE Picard step per piece (window pieces are clock-capped, so
`T ≤ r₀` covers the chain's needs; longer horizons re-anchor with a fresh budget). -/
theorem box_viability_bounded {sys : ODESystem V} {dom : Formula V}
    (hwf : sys.WellFormed)
    (gsS gsG : List (State V → ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hgS : ∀ g ∈ gsS, Differentiable ℝ g) (hgG : ∀ g ∈ gsG, Differentiable ℝ g)
    (hbndS : ∀ g ∈ gsS, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    (hbndG : ∀ g ∈ gsG, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → Lie sys g x ≤ M)
    (hdomsat : ∀ x : State V, (∀ g ∈ gsS ++ gsG, g x ≤ 0) → Formula.sat dom x)
    (K L : NNReal) (a : ℝ) (ha : 0 < a)
    (hLipOn : ∀ ν : State V, (∀ g ∈ gsS ++ gsG, g ν ≤ 0) →
      LipschitzOnWith K (odeField sys) (Metric.closedBall ν a))
    (hfbnd : ∀ ν : State V, (∀ g ∈ gsS ++ gsG, g ν ≤ 0) →
      ∀ x ∈ Metric.closedBall ν a, ‖odeField sys x‖ ≤ (L : ℝ))
    (T : ℝ) (hT : 0 < T) (hTle : (L : ℝ) * T ≤ a) :
    ∀ ν : State V, (∀ g ∈ gsS, g ν ≤ 0) → (∀ g ∈ gsG, g ν + M * T < 0) →
      ∃ ν', (∀ g ∈ gsS ++ gsG, g ν' ≤ 0) ∧ RunFor sys dom T ν ν' := by
  intro ν hPS hPG
  have hP : ∀ g ∈ gsS ++ gsG, g ν ≤ 0 := by
    intro g hgm
    rcases List.mem_append.mp hgm with h | h
    · exact hPS g h
    · nlinarith [hPG g h, hM, hT.le]
  have hpl := picard_isPL_of_local K L ν a ha.le (hLipOn ν hP) (hfbnd ν hP) T hT hTle
  have hdomC : ∀ Φ : ℝ → State V, Φ 0 = ν →
      IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 T) →
      ∀ t ∈ Set.Icc (0:ℝ) T, Formula.sat dom (Φ t) := by
    intro Φ hΦ0 hcurve t ht
    refine hdomsat (Φ t) ?_
    exact bounded_faces_raw hwf gsS gsG M hM hgS hgG hbndS hbndG hcurve
      (fun g hgm => by rw [hΦ0]; exact hPS g hgm)
      (fun g hgm => by rw [hΦ0]; exact hPG g hgm) t ht
  obtain ⟨Φ, hΦ0, hcurve, hrun⟩ := picard_to_RunFor ν hT hpl hdomC
  refine ⟨Φ T, ?_, hrun⟩
  exact bounded_faces_raw hwf gsS gsG M hM hgS hgG hbndS hbndG hcurve
    (fun g hgm => by rw [hΦ0]; exact hPS g hgm)
    (fun g hgm => by rw [hΦ0]; exact hPG g hgm) T (Set.right_mem_Icc.mpr hT.le)

/-! ## The Z3 leaf: growth-face verdicts (frozen-left, `UNSAT(box ∧ ġ > M)`) -/

/-- A growth verdict gives the box-conditioned Lie bound in the assembly's form. -/
theorem face_growth_from_verdict {n : ℕ} (faces : List (Term (Var n)))
    (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (g : Term (Var n)) (M : ℝ)
    (hz3 : z3solve (Formula.and (bigLe faces)
      (Formula.cmp .gt (lieDeriv g (fun _ => Term.const 0) fR lam)
        (Term.const M))) = Verdict.unsat) :
    ∀ x : State (Var n), (∀ g' ∈ faces, Term.eval g' x ≤ 0) →
      Lie (jointSys (fun _ => Term.const 0) fR lam) (fun ω => Term.eval g ω) x ≤ M := by
  intro x hbox
  have hunsat := z3_unsat_sound hz3
  by_contra hpos
  rw [not_le] at hpos
  refine hunsat x ⟨(sat_bigLe_iff faces x).mpr hbox, ?_⟩
  rw [← lieDeriv_correct] at hpos
  simpa [Formula.sat, CompOp.interp, Term.eval] using hpos

end RelCertifier
