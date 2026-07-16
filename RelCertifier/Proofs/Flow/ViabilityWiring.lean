/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S3 wiring — the bounded existence residual, viability-certified

`HExistSegB` — `HExistSeg` restricted to left durations `≤ dt` — is all the bounded
coupling ever consumes (`faModal_ODE_G'_bounded` invokes `hExist` only at `s ≤ dt`).
`HExistSegB_of_viability` discharges it from the bounded box-viability certificates:
the right response runs the frozen-left joint field from the left endpoint (whose right
coordinates are the anchor's — the left run masks them), stays in the `domR` face box
for the clock-capped duration by strict + budgeted growth faces, and its left rows are
inert (`0`-field). The instance-level residuals become the face verdicts + growth
budgets + the Picard data — Z3-checkable and analytic-hypothesis-free.
-/
import RelCertifier.Proofs.Flow.BoxViabilityBounded
import RelCertifier.Proofs.Encoding.RepositionDischarge
import RelCertifier.Proofs.Encoding.UniformFvDischarge
import RelCertifier.Proofs.Flow.WellFormedFlow

namespace RelCertifier
open DL DLCalTiming Function Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The coordinate facts of an integral curve (the `←` internals of
`sem_ode_iff_integralCurve`, duration-preserving). -/
theorem integralCurve_coords {sys : ODESystem V} (hwf : sys.WellFormed)
    {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r)) :
    (∀ t ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Set.Icc 0 r) t)
    ∧ (∀ t ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = Φ 0 x) := by
  constructor
  · intro t ht p hp
    have hi : p.1 ∈ sys.bound := List.mem_map_of_mem hp
    have hpi := (hasDerivWithinAt_pi.mp (hcurve t ht)) p.1
    simpa only [odeField, if_pos hi, ODESystem.rhs_eq_of_mem hwf hp] using hpi
  · intro t ht x hx
    have hcx : ∀ s ∈ Set.Icc (0:ℝ) r,
        HasDerivWithinAt (fun u => Φ u x) 0 (Set.Icc 0 r) s := by
      intro s hs
      have hpi := (hasDerivWithinAt_pi.mp (hcurve s hs)) x
      simpa only [odeField, if_neg hx] using hpi
    have hdiffOn : DifferentiableOn ℝ (fun u => Φ u x) (Set.Icc 0 r) :=
      fun s hs => (hcx s hs).differentiableWithinAt
    have hd0 : ∀ s ∈ Set.Ico (0:ℝ) r,
        derivWithin (fun u => Φ u x) (Set.Icc 0 r) s = 0 := by
      intro s hs
      have hlt : (0:ℝ) < r := lt_of_le_of_lt hs.1 hs.2
      exact (hcx s ⟨hs.1, le_of_lt hs.2⟩).derivWithin ((uniqueDiffOn_Icc hlt) s
        ⟨hs.1, le_of_lt hs.2⟩)
    exact constant_of_derivWithin_zero hdiffOn hd0 t ht

variable {n : ℕ}

/-- A coordinate with the constant-`0` field is constant along an integral curve
(bound, so masking is silent; the zero derivative integrates). -/
theorem integralCurve_zero_coord {sys : ODESystem V} (hwf : sys.WellFormed)
    {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    {x : V} (hx : (x, (Term.const 0 : Term V)) ∈ sys) :
    ∀ t ∈ Set.Icc (0:ℝ) r, Φ t x = Φ 0 x := by
  have hder := (integralCurve_coords hwf hcurve).1
  have hcx : ∀ s ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun u => Φ u x) 0 (Set.Icc 0 r) s := by
    intro s hs
    simpa [Term.eval] using hder s hs (x, (Term.const 0 : Term V)) hx
  have hdiffOn : DifferentiableOn ℝ (fun u => Φ u x) (Set.Icc 0 r) :=
    fun s hs => (hcx s hs).differentiableWithinAt
  have hd0 : ∀ s ∈ Set.Ico (0:ℝ) r,
      derivWithin (fun u => Φ u x) (Set.Icc 0 r) s = 0 := by
    intro s hs
    have hlt : (0:ℝ) < r := lt_of_le_of_lt hs.1 hs.2
    exact (hcx s ⟨hs.1, le_of_lt hs.2⟩).derivWithin ((uniqueDiffOn_Icc hlt) s
      ⟨hs.1, le_of_lt hs.2⟩)
  exact constant_of_derivWithin_zero hdiffOn hd0

/-- **The bounded existence residual, viability-certified.** From every anchor whose
strict faces hold and whose growth faces carry the `dt`-budget, the right response
exists for any left duration `≤ dt`: the frozen-left joint field runs from the left
endpoint (right coordinates = the anchor's, by the left mask), stays in the face box
(strict + budgeted growth first-exit), the box implies `domR`, and the left rows are
inert. Face data over the FROZEN-LEFT joint system — the R6/S3 verdict shapes. -/
theorem HExistSegB_of_viability
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
    (gsS gsG : List (Term (Var n))) (M : ℝ) (hM : 0 ≤ M)
    (hwf : (jointSys (fun _ => Term.const 0) fR lam).WellFormed)
    (hfacesL : ∀ gT ∈ gsS ++ gsG, ∀ x ∈ gT.fv, x ∉ (leftBlock fL).bound)
    (hbndS : ∀ gT ∈ gsS, ∀ x : State (Var n),
      (∀ gT' ∈ gsS ++ gsG, Term.eval gT' x ≤ 0) → Term.eval gT x = 0 →
      Lie (jointSys (fun _ => Term.const 0) fR lam) (fun ω => Term.eval gT ω) x < 0)
    (hbndG : ∀ gT ∈ gsG, ∀ x : State (Var n),
      (∀ gT' ∈ gsS ++ gsG, Term.eval gT' x ≤ 0) →
      Lie (jointSys (fun _ => Term.const 0) fR lam) (fun ω => Term.eval gT ω) x ≤ M)
    (hdomsat : ∀ x : State (Var n),
      (∀ gT ∈ gsS ++ gsG, Term.eval gT x ≤ 0) → Formula.sat domR x)
    (K L : NNReal) (a : ℝ) (ha : 0 < a)
    (hLipOn : ∀ ν : State (Var n), (∀ gT ∈ gsS ++ gsG, Term.eval gT ν ≤ 0) →
      LipschitzOnWith K (odeField (jointSys (fun _ => Term.const 0) fR lam))
        (Metric.closedBall ν a))
    (hfbnd : ∀ ν : State (Var n), (∀ gT ∈ gsS ++ gsG, Term.eval gT ν ≤ 0) →
      ∀ x ∈ Metric.closedBall ν a,
        ‖odeField (jointSys (fun _ => Term.const 0) fR lam) x‖ ≤ (L : ℝ))
    (dt : ℝ) (hdtle : (L : ℝ) * dt ≤ a)
    (ν : State (Var n))
    (hinitS : ∀ gT ∈ gsS, Term.eval gT ν ≤ 0)
    (hbudget : ∀ gT ∈ gsG, Term.eval gT ν + M * dt < 0) :
    HExistSegB fL fR lam domL domR dt ν := by
  intro s ΦL hs0 hsdt hΦL0 hderL hmaskL hdomL
  -- face values at the left endpoint are the anchor's (the left run masks them)
  have hcoin : ∀ gT ∈ gsS ++ gsG, Term.eval gT (ΦL s) = Term.eval gT ν :=
    fun gT hgT => Term.coincidence gT (fun y hy =>
      hmaskL s (right_mem_Icc.mpr hs0) y (hfacesL gT hgT y hy))
  have hinitS' : ∀ gT ∈ gsS, Term.eval gT (ΦL s) ≤ 0 := by
    intro gT hgT
    rw [hcoin gT (List.mem_append_left _ hgT)]
    exact hinitS gT hgT
  have hbudget' : ∀ gT ∈ gsG, Term.eval gT (ΦL s) + M * s < 0 := by
    intro gT hgT
    rw [hcoin gT (List.mem_append_right _ hgT)]
    have := hbudget gT hgT
    nlinarith [mul_le_mul_of_nonneg_left hsdt hM]
  have hallν' : ∀ gT ∈ gsS ++ gsG, Term.eval gT (ΦL s) ≤ 0 := by
    intro gT hgT
    rcases List.mem_append.mp hgT with h | h
    · exact hinitS' gT h
    · nlinarith [hbudget' gT h, hM, hs0]
  rcases eq_or_lt_of_le hs0 with hs0' | hspos
  · -- zero left duration: the constant response
    refine ⟨fun _ => ΦL s, rfl, ?_, ?_, ?_⟩
    · intro t ht p hp
      rw [← hs0'] at ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      rw [← hs0', hasDerivWithinAt_iff_tendsto_slope]
      rw [show (Set.Icc (0:ℝ) 0) \ {0} = (∅ : Set ℝ) from by simp [Set.Icc_self],
        nhdsWithin_empty]
      exact Filter.tendsto_bot
    · intro t ht x hx
      rfl
    · intro t ht
      exact hdomsat (ΦL s) hallν'
  · -- positive duration: bounded viability from the left endpoint
    -- semantic face lists
    set fS : List (State (Var n) → ℝ) := gsS.map (fun gT ω => Term.eval gT ω) with hfS
    set fG : List (State (Var n) → ℝ) := gsG.map (fun gT ω => Term.eval gT ω) with hfG
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
    obtain ⟨ν'', hfaces'', hrun⟩ := box_viability_bounded hwf fS fG M hM
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
      (fun x hx => hdomsat x ((happF x).mp hx))
      K L a ha
      (fun ν0 h0 => hLipOn ν0 ((happF ν0).mp h0))
      (fun ν0 h0 => hfbnd ν0 ((happF ν0).mp h0))
      s hspos (le_trans (mul_le_mul_of_nonneg_left hsdt L.coe_nonneg) hdtle)
      (ΦL s)
      (by
        intro f hf
        obtain ⟨gT, hgT, rfl⟩ := hmemS f hf
        exact hinitS' gT hgT)
      (by
        intro f hf
        obtain ⟨gT, hgT, rfl⟩ := hmemG f hf
        exact hbudget' gT hgT)
    obtain ⟨-, Φ, hΦ0, -, hcurve, hdomR⟩ := hrun
    obtain ⟨hderJ, hmaskJ⟩ := integralCurve_coords hwf hcurve
    refine ⟨Φ, hΦ0, ?_, ?_, hdomR⟩
    · -- right-block derivatives: right pairs are joint pairs
      intro t ht p hp
      refine hderJ t ht p ?_
      rw [jointSys_split]
      exact List.mem_append_right _ hp
    · -- mask off the right block: left rows are inert, others masked
      intro t ht x hx
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
