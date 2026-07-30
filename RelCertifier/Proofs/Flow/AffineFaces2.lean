/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L1d — monotone faces chained on the affine pass

`HExistSegB_of_viability_stratA` establishes its affine coordinate bounds
(`driven_bound_raw` / `driven_bound_lo_raw`) AFTER the strict/growth/non-strict
box, so their drive hypotheses may cite the box classes — but nothing may cite
the affine facts themselves. `endurance_orderlift_2to3` needs exactly that one
more step: its position row `s' = v` is nonnegative only because the velocity's
own lower bound `v ≥ 0` is an affine fact (`v' = a − 4v` with `a ≥ 0`), so the
position's `s ≥ 0` is a MONOTONE face conditioned on the affine pass.

This file adds that second pass:

* `monotone_bound_lo_raw`: a coordinate with nonnegative field derivative along
  the curve never drops below its start — the `λ = 0` case the driven lemmas
  exclude (their exponential weight needs `λ > 0`).
* `HExistSegB_of_viability_stratA2`: `stratA` extended with a list `gsML` of
  monotone lower faces `(coordinate, C)` whose nonnegativity hypothesis receives
  the pointwise strict/growth, non-strict, AND first-pass affine facts, and
  whose conclusions feed the evolve-domain rebuild.

New leaf over `AffineFaces` — no upstream edits, mirror structure throughout.
-/
import RelCertifier.Proofs.Flow.AffineFaces

namespace RelCertifier
open DL Set

variable {n : ℕ} {V : Type*} [DecidableEq V] [Fintype V]

/-- **Monotone lower face**: if the coordinate's field derivative is nonnegative
along the curve, the coordinate never drops below its start value. -/
theorem monotone_bound_lo_raw {sys : ODESystem V} {r : ℝ} {Φ : ℝ → State V}
    (si : V) (C : ℝ)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hdrive : ∀ t ∈ Set.Icc (0:ℝ) r, 0 ≤ odeField sys (Φ t) si)
    (h0 : C ≤ Φ 0 si) :
    ∀ t ∈ Set.Icc (0:ℝ) r, C ≤ Φ t si := by
  have hgd : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun u => Φ u si) (odeField sys (Φ t) si) (Set.Icc 0 r) t :=
    fun t ht => (hasDerivWithinAt_pi.mp (hcurve t ht)) si
  have hcont : ContinuousOn (fun u => Φ u si) (Set.Icc 0 r) :=
    fun t ht => (hgd t ht).continuousWithinAt
  have hmono : MonotoneOn (fun u => Φ u si) (Set.Icc 0 r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact ((hgd x (Set.Ioo_subset_Icc_self hx)).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hxIcc := Set.Ioo_subset_Icc_self hx
      rw [((hgd x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
      exact hdrive x hxIcc
  intro t ht
  have := hmono (Set.left_mem_Icc.mpr (le_trans ht.1 ht.2)) ht ht.1
  linarith

/-- **`stratA` with a monotone second pass.** Identical to
`HExistSegB_of_viability_stratA` plus a list `gsML` of monotone lower faces
`(coordinate, C)`: their field-nonnegativity hypothesis `hdriveM` receives the
pointwise box facts AND the first-pass affine bounds, and their conclusions
join the evolve-domain rebuild. -/
theorem HExistSegB_of_viability_stratA2
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
    (gsS gsG gsN : List (Term (Var n))) (M : ℝ) (hM : 0 ≤ M)
    (gsAU gsAL : List (Var n × ℝ × ℝ × ℝ))
    (gsML : List (Var n × ℝ))
    (hwf : (jointSys (fun _ => Term.const 0) fR lam).WellFormed)
    (hfacesL : ∀ gT ∈ gsS ++ gsG, ∀ x ∈ gT.fv, x ∉ (leftBlock fL).bound)
    (hfacesLN : ∀ gT ∈ gsN, ∀ x ∈ gT.fv, x ∉ (leftBlock fL).bound)
    (hAUb : ∀ p ∈ gsAU, p.1 ∉ (leftBlock fL).bound)
    (hALb : ∀ p ∈ gsAL, p.1 ∉ (leftBlock fL).bound)
    (hMLb : ∀ p ∈ gsML, p.1 ∉ (leftBlock fL).bound)
    (hAUlam : ∀ p ∈ gsAU, 0 < p.2.1) (hALlam : ∀ p ∈ gsAL, 0 < p.2.1)
    (hAUC : ∀ p ∈ gsAU, p.2.2.1 ≤ p.2.1 * p.2.2.2)
    (hALC : ∀ p ∈ gsAL, p.2.1 * p.2.2.2 ≤ p.2.2.1)
    (hbndS : ∀ gT ∈ gsS, ∀ x : State (Var n),
      (∀ gT' ∈ gsS ++ gsG, Term.eval gT' x ≤ 0) → Term.eval gT x = 0 →
      Lie (jointSys (fun _ => Term.const 0) fR lam) (fun ω => Term.eval gT ω) x < 0)
    (hbndG : ∀ gT ∈ gsG, ∀ x : State (Var n),
      (∀ gT' ∈ gsS ++ gsG, Term.eval gT' x ≤ 0) →
      Lie (jointSys (fun _ => Term.const 0) fR lam) (fun ω => Term.eval gT ω) x ≤ M)
    (hbndN : ∀ i (hi : i < gsN.length), ∀ x : State (Var n),
      (∀ gT' ∈ gsS ++ gsG, Term.eval gT' x ≤ 0) →
      (∀ gT' ∈ gsN.take i, Term.eval gT' x ≤ 0) →
      Lie (jointSys (fun _ => Term.const 0) fR lam)
        (fun ω => Term.eval gsN[i] ω) x ≤ 0)
    (hdriveU : ∀ p ∈ gsAU, ∀ x : State (Var n),
      (∀ gT ∈ gsS ++ gsG, Term.eval gT x ≤ 0) → (∀ gT ∈ gsN, Term.eval gT x ≤ 0) →
      odeField (jointSys (fun _ => Term.const 0) fR lam) x p.1
        ≤ p.2.2.1 - p.2.1 * x p.1)
    (hdriveL : ∀ p ∈ gsAL, ∀ x : State (Var n),
      (∀ gT ∈ gsS ++ gsG, Term.eval gT x ≤ 0) → (∀ gT ∈ gsN, Term.eval gT x ≤ 0) →
      p.2.2.1 - p.2.1 * x p.1
        ≤ odeField (jointSys (fun _ => Term.const 0) fR lam) x p.1)
    (hdriveM : ∀ p ∈ gsML, ∀ x : State (Var n),
      (∀ gT ∈ gsS ++ gsG, Term.eval gT x ≤ 0) → (∀ gT ∈ gsN, Term.eval gT x ≤ 0) →
      (∀ q ∈ gsAU, x q.1 ≤ q.2.2.2) → (∀ q ∈ gsAL, q.2.2.2 ≤ x q.1) →
      0 ≤ odeField (jointSys (fun _ => Term.const 0) fR lam) x p.1)
    (hdomsat : ∀ x : State (Var n),
      (∀ gT ∈ gsS ++ gsG, Term.eval gT x ≤ 0) →
      (∀ gT ∈ gsN, Term.eval gT x ≤ 0) →
      (∀ p ∈ gsAU, x p.1 ≤ p.2.2.2) →
      (∀ p ∈ gsAL, p.2.2.2 ≤ x p.1) →
      (∀ p ∈ gsML, p.2 ≤ x p.1) → Formula.sat domR x)
    (K L : NNReal) (a : ℝ) (ha : 0 < a)
    (hLipOn : ∀ ν : State (Var n), (∀ gT ∈ gsS ++ gsG, Term.eval gT ν ≤ 0) →
      LipschitzOnWith K (odeField (jointSys (fun _ => Term.const 0) fR lam))
        (Metric.closedBall ν a))
    (hfbnd : ∀ ν : State (Var n), (∀ gT ∈ gsS ++ gsG, Term.eval gT ν ≤ 0) →
      ∀ x ∈ Metric.closedBall ν a,
        ‖odeField (jointSys (fun _ => Term.const 0) fR lam) x‖ ≤ (L : ℝ))
    (dt : ℝ) (hdt0 : 0 ≤ dt)
    (ν : State (Var n))
    (hinitS : ∀ gT ∈ gsS, Term.eval gT ν ≤ 0)
    (hinitN : ∀ gT ∈ gsN, Term.eval gT ν ≤ 0)
    (hinitAU : ∀ p ∈ gsAU, ν p.1 ≤ p.2.2.2)
    (hinitAL : ∀ p ∈ gsAL, p.2.2.2 ≤ ν p.1)
    (hinitML : ∀ p ∈ gsML, p.2 ≤ ν p.1)
    (hbudget : ∀ gT ∈ gsG, Term.eval gT ν + M * dt < 0) :
    HExistSegB fL fR lam domL domR dt ν := by
  -- Run the stratA argument against a domR' that only asserts the classes it
  -- can rebuild, then upgrade: we cannot literally reuse stratA (its witness
  -- is opaque), so we mirror its skeleton and add the monotone pass.
  intro s ΦL hs0 hsdt hΦL0 hderL hmaskL hdomL
  have hcoin : ∀ gT ∈ gsS ++ gsG, Term.eval gT (ΦL s) = Term.eval gT ν :=
    fun gT hgT => Term.coincidence gT (fun y hy =>
      hmaskL s (right_mem_Icc.mpr hs0) y (hfacesL gT hgT y hy))
  have hcoinN : ∀ gT ∈ gsN, Term.eval gT (ΦL s) = Term.eval gT ν :=
    fun gT hgT => Term.coincidence gT (fun y hy =>
      hmaskL s (right_mem_Icc.mpr hs0) y (hfacesLN gT hgT y hy))
  have hcoinAU : ∀ p ∈ gsAU, ΦL s p.1 = ν p.1 :=
    fun p hp => hmaskL s (right_mem_Icc.mpr hs0) p.1 (hAUb p hp)
  have hcoinAL : ∀ p ∈ gsAL, ΦL s p.1 = ν p.1 :=
    fun p hp => hmaskL s (right_mem_Icc.mpr hs0) p.1 (hALb p hp)
  have hcoinML : ∀ p ∈ gsML, ΦL s p.1 = ν p.1 :=
    fun p hp => hmaskL s (right_mem_Icc.mpr hs0) p.1 (hMLb p hp)
  have hinitS' : ∀ gT ∈ gsS, Term.eval gT (ΦL s) ≤ 0 := by
    intro gT hgT
    rw [hcoin gT (List.mem_append_left _ hgT)]
    exact hinitS gT hgT
  have hinitN' : ∀ gT ∈ gsN, Term.eval gT (ΦL s) ≤ 0 := by
    intro gT hgT
    rw [hcoinN gT hgT]
    exact hinitN gT hgT
  have hbudget' : ∀ gT ∈ gsG, Term.eval gT (ΦL s) + M * s < 0 := by
    intro gT hgT
    rw [hcoin gT (List.mem_append_right _ hgT)]
    have := hbudget gT hgT
    nlinarith [mul_le_mul_of_nonneg_left hsdt hM]
  set fS : List (State (Var n) → ℝ) := gsS.map (fun gT ω => Term.eval gT ω) with hfS
  set fG : List (State (Var n) → ℝ) := gsG.map (fun gT ω => Term.eval gT ω) with hfG
  set fN : List (State (Var n) → ℝ) := gsN.map (fun gT ω => Term.eval gT ω) with hfN
  have hmemS : ∀ f ∈ fS, ∃ gT ∈ gsS, f = fun ω => Term.eval gT ω := by
    intro f hf
    obtain ⟨gT, hgT, rfl⟩ := List.mem_map.mp hf
    exact ⟨gT, hgT, rfl⟩
  have hmemG : ∀ f ∈ fG, ∃ gT ∈ gsG, f = fun ω => Term.eval gT ω := by
    intro f hf
    obtain ⟨gT, hgT, rfl⟩ := List.mem_map.mp hf
    exact ⟨gT, hgT, rfl⟩
  have happF : ∀ x : State (Var n), (∀ f ∈ fS ++ fG, f x ≤ 0) ↔
      (∀ gT ∈ gsS ++ gsG, Term.eval gT x ≤ 0) := by
    intro x
    constructor
    · intro h gT hgT
      rcases List.mem_append.mp hgT with hm | hm
      · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨gT, hm, rfl⟩))
      · exact h _ (List.mem_append_right _ (List.mem_map.mpr ⟨gT, hm, rfl⟩))
    · intro h f hf
      rcases List.mem_append.mp hf with hm | hm
      · obtain ⟨gT, hgT, rfl⟩ := hmemS f hm
        exact h gT (List.mem_append_left _ hgT)
      · obtain ⟨gT, hgT, rfl⟩ := hmemG f hm
        exact h gT (List.mem_append_right _ hgT)
  obtain ⟨ν'', hfaces'', hrun⟩ := box_viability_bounded_chain (dom := Formula.tt)
    hwf fS fG M hM
    (by
      intro f hf
      obtain ⟨gT, _, rfl⟩ := hmemS f hf
      exact term_differentiable gT)
    (by
      intro f hf
      obtain ⟨gT, _, rfl⟩ := hmemG f hf
      exact term_differentiable gT)
    (by
      intro f hf x hx hf0
      obtain ⟨gT, hgT, rfl⟩ := hmemS f hf
      exact hbndS gT hgT x ((happF x).mp hx) hf0)
    (by
      intro f hf x hx
      obtain ⟨gT, hgT, rfl⟩ := hmemG f hf
      exact hbndG gT hgT x ((happF x).mp hx))
    (fun x _ => by simp [Formula.sat])
    K L a ha
    (fun ν0 h0 => hLipOn ν0 ((happF ν0).mp h0))
    (fun ν0 h0 => hfbnd ν0 ((happF ν0).mp h0))
    s hs0 (ΦL s)
    (by
      intro f hf
      obtain ⟨gT, hgT, rfl⟩ := hmemS f hf
      exact hinitS' gT hgT)
    (by
      intro f hf
      obtain ⟨gT, hgT, rfl⟩ := hmemG f hf
      exact hbudget' gT hgT)
  obtain ⟨-, Φ, hΦ0, -, hcurve, -⟩ := hrun
  have hstrat := stratified_faces_raw hwf fS fG fN M hM
    (by
      intro f hf
      obtain ⟨gT, _, rfl⟩ := hmemS f hf
      exact term_differentiable gT)
    (by
      intro f hf
      obtain ⟨gT, _, rfl⟩ := hmemG f hf
      exact term_differentiable gT)
    (by
      intro f hf
      obtain ⟨gT, hgT, rfl⟩ := List.mem_map.mp hf
      exact term_differentiable gT)
    (by
      intro f hf x hx hf0
      obtain ⟨gT, hgT, rfl⟩ := hmemS f hf
      exact hbndS gT hgT x ((happF x).mp hx) hf0)
    (by
      intro f hf x hx
      obtain ⟨gT, hgT, rfl⟩ := hmemG f hf
      exact hbndG gT hgT x ((happF x).mp hx))
    (by
      intro i hi x hx hpre
      have hig : fN[i] = fun ω => Term.eval (gsN[i]'(by simpa [hfN] using hi)) ω := by
        simp [hfN]
      rw [hig]
      refine hbndN i (by simpa [hfN] using hi) x ((happF x).mp hx) ?_
      intro gT' hgT'
      have : (fun ω => Term.eval gT' ω) ∈ fN.take i := by
        rw [hfN, ← List.map_take]
        exact List.mem_map.mpr ⟨gT', hgT', rfl⟩
      exact hpre _ this)
    hcurve
    (by
      intro f hf
      obtain ⟨gT, hgT, rfl⟩ := hmemS f hf
      rw [hΦ0]
      exact hinitS' gT hgT)
    (by
      intro f hf
      obtain ⟨gT, hgT, rfl⟩ := List.mem_map.mp hf
      rw [hΦ0]
      exact hinitN' gT hgT)
    (by
      intro f hf
      obtain ⟨gT, hgT, rfl⟩ := hmemG f hf
      rw [hΦ0]
      exact hbudget' gT hgT)
  have hSGpt : ∀ t ∈ Set.Icc (0:ℝ) s, ∀ gT ∈ gsS ++ gsG,
      Term.eval gT (Φ t) ≤ 0 := by
    intro t ht gT hgT
    rcases List.mem_append.mp hgT with hm | hm
    · exact hstrat.1 t ht _ (List.mem_append_left _ (List.mem_map.mpr ⟨gT, hm, rfl⟩))
    · exact hstrat.1 t ht _ (List.mem_append_right _ (List.mem_map.mpr ⟨gT, hm, rfl⟩))
  have hNpt : ∀ t ∈ Set.Icc (0:ℝ) s, ∀ gT ∈ gsN, Term.eval gT (Φ t) ≤ 0 := by
    intro t ht gT hgT
    exact hstrat.2 t ht _ (List.mem_map.mpr ⟨gT, hgT, rfl⟩)
  have hAUpt : ∀ p ∈ gsAU, ∀ t ∈ Set.Icc (0:ℝ) s, Φ t p.1 ≤ p.2.2.2 := by
    intro p hp
    refine driven_bound_raw p.1 p.2.1 p.2.2.1 p.2.2.2 (hAUlam p hp) (hAUC p hp)
      hcurve ?_ ?_
    · intro t ht
      exact hdriveU p hp (Φ t) (hSGpt t ht) (hNpt t ht)
    · rw [hΦ0, hcoinAU p hp]
      exact hinitAU p hp
  have hALpt : ∀ p ∈ gsAL, ∀ t ∈ Set.Icc (0:ℝ) s, p.2.2.2 ≤ Φ t p.1 := by
    intro p hp
    refine driven_bound_lo_raw p.1 p.2.1 p.2.2.1 p.2.2.2 (hALlam p hp) (hALC p hp)
      hcurve ?_ ?_
    · intro t ht
      exact hdriveL p hp (Φ t) (hSGpt t ht) (hNpt t ht)
    · rw [hΦ0, hcoinAL p hp]
      exact hinitAL p hp
  have hMLpt : ∀ p ∈ gsML, ∀ t ∈ Set.Icc (0:ℝ) s, p.2 ≤ Φ t p.1 := by
    intro p hp
    refine monotone_bound_lo_raw p.1 p.2 hcurve ?_ ?_
    · intro t ht
      exact hdriveM p hp (Φ t) (hSGpt t ht) (hNpt t ht)
        (fun q hq => hAUpt q hq t ht) (fun q hq => hALpt q hq t ht)
    · rw [hΦ0, hcoinML p hp]
      exact hinitML p hp
  have hdomR : ∀ t ∈ Set.Icc (0:ℝ) s, Formula.sat domR (Φ t) := by
    intro t ht
    exact hdomsat (Φ t) (hSGpt t ht) (hNpt t ht)
      (fun p hp => hAUpt p hp t ht) (fun p hp => hALpt p hp t ht)
      (fun p hp => hMLpt p hp t ht)
  obtain ⟨hderJ, hmaskJ⟩ := integralCurve_coords hwf hcurve
  refine ⟨Φ, hΦ0, ?_, ?_, hdomR⟩
  · intro t ht p hp
    refine hderJ t ht p ?_
    rw [jointSys_split]
    exact List.mem_append_right _ hp
  · intro t ht x hx
    by_cases hxL : ∃ i : Fin n, x = Lv i
    · obtain ⟨i, rfl⟩ := hxL
      have hpair : (Lv i, (Term.const 0 : Term (Var n)))
          ∈ jointSys (fun _ => Term.const 0) fR lam := by
        rw [jointSys_split]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
      rw [integralCurve_zero_coord hwf hcurve hpair t ht, hΦ0]
    · refine (hmaskJ t ht x ?_).trans (by rw [hΦ0])
      rw [jointSys_split]
      intro hb
      simp only [ODESystem.bound, List.map_append, List.mem_append] at hb
      rcases hb with hb | hb
      · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fun _ => Term.const 0) _ hb
        exact hxL ⟨i, hi⟩
      · exact hx (by simpa [ODESystem.bound] using hb)

end RelCertifier
