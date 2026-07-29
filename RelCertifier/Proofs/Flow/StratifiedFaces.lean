/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L1 — stratified face invariance and the stratified existence consumer

The bounded viability layer (`BoxViabilityBounded`) admits two face classes: STRICT
(box-conditioned strict inflow on the face) and GROWTH (Lie bound `≤ M` with an entry
budget). The suite-wide face census (docs/VIABILITY-FACE-CENSUS.md) shows the dominant
class is neither: NON-STRICT inward faces — `Lie ≤ 0` over a region, `= 0` allowed on
the face — 519 of 1133 faces, present at nearly every benchmark's landing modes.

A non-strict face cannot enter the strict list (its Lie vanishes on the face) nor the
growth list (`M = 0` makes the entry budget demand strictly negative face value, false
at anchors on the face). The sound route is STRATIFICATION: prove the strict core and
the growth faces first (`bounded_faces_raw` — the first-exit argument), then each
non-strict face in strata order, its `Lie ≤ 0` premise conditioned only on the faces
already proven. Because the earlier faces then hold POINTWISE along the whole curve,
`nonstrict_antitone_raw` applies directly — the premise is a fact along the curve, not
a boundary-only check, so the `nonstrict_boundary_insufficient` t² trap does not arise
and no Nagumo sub-tangency is needed.

`HExistSegB_of_viability_stratified` is the existence consumer: it reuses the EXISTING
`box_viability_bounded_chain` (with a trivial domain) purely to produce the right run,
then re-derives the full face box — including the non-strict faces — post hoc on that
run, and only then concludes the evolve domain. No re-proof of the Picard/chain layer.

Measured grounding (docs/LEMMA-SCOPE.md): the stratification closes for 47/47
benchmarks, strata depth ≤ 3 beyond the strict core, zero stuck faces.
-/
import RelCertifier.Proofs.Flow.ViabilityWiring

namespace RelCertifier
open DL Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The stratified faces argument -/

/-- **Stratified throughout-invariance.** Strict faces `gsS` and growth faces `gsG`
keep their `bounded_faces_raw` treatment; the non-strict faces `gsN` are proven in
LIST ORDER, face `i`'s `Lie ≤ 0` conditioned on the strict/growth sublevel region and
on the earlier non-strict faces `gsN.take i` — which hold pointwise along the curve by
strong induction, so `nonstrict_antitone_raw`'s along-curve premise is discharged. -/
theorem stratified_faces_raw {sys : ODESystem V} (hwf : sys.WellFormed)
    (gsS gsG gsN : List (State V → ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hgS : ∀ g ∈ gsS, Differentiable ℝ g) (hgG : ∀ g ∈ gsG, Differentiable ℝ g)
    (hgN : ∀ g ∈ gsN, Differentiable ℝ g)
    (hbndS : ∀ g ∈ gsS, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    (hbndG : ∀ g ∈ gsG, ∀ x, (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → Lie sys g x ≤ M)
    (hbndN : ∀ i (hi : i < gsN.length), ∀ x,
      (∀ g' ∈ gsS ++ gsG, g' x ≤ 0) → (∀ g' ∈ gsN.take i, g' x ≤ 0) →
      Lie sys gsN[i] x ≤ 0)
    {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinitS : ∀ g ∈ gsS, g (Φ 0) ≤ 0)
    (hinitN : ∀ g ∈ gsN, g (Φ 0) ≤ 0)
    (hbudget : ∀ g ∈ gsG, g (Φ 0) + M * r < 0) :
    (∀ t ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gsS ++ gsG, g (Φ t) ≤ 0) ∧
    (∀ t ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gsN, g (Φ t) ≤ 0) := by
  have hSG := bounded_faces_raw hwf gsS gsG M hM hgS hgG hbndS hbndG hcurve hinitS hbudget
  refine ⟨hSG, ?_⟩
  suffices h : ∀ i (hi : i < gsN.length), ∀ t ∈ Set.Icc (0:ℝ) r, gsN[i] (Φ t) ≤ 0 by
    intro t ht g hg
    obtain ⟨j, hj, hjg⟩ := List.getElem_of_mem hg
    rw [← hjg]
    exact h j hj t ht
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi t ht
      -- the earlier non-strict faces hold pointwise (strong IH)
      have hpre : ∀ u ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gsN.take i, g (Φ u) ≤ 0 := by
        intro u hu g hg
        obtain ⟨j, hj, hjg⟩ := List.getElem_of_mem hg
        rw [List.getElem_take] at hjg
        have hjlen : j < gsN.length := by
          have := List.length_take_le i gsN
          omega
        rw [← hjg]
        exact ih j (by
          have := hj
          rw [List.length_take] at this
          omega) hjlen u hu
      -- Lie ≤ 0 along the whole curve — the along-curve premise, discharged
      have hlie : ∀ u ∈ Set.Icc (0:ℝ) r, Lie sys gsN[i] (Φ u) ≤ 0 := by
        intro u hu
        exact hbndN i hi (Φ u) (fun g' hg' => hSG u hu g' hg') (hpre u hu)
      have hanti := nonstrict_antitone_raw hwf (hgN _ (List.getElem_mem hi))
        hcurve hlie t ht
      exact le_trans hanti (hinitN _ (List.getElem_mem hi))

/-! ## The stratified existence consumer -/

/-- **The bounded existence residual, stratified-viability-certified.** As
`HExistSegB_of_viability`, with a third face list `gsN` of non-strict inward faces in
strata order. The run is produced by the EXISTING `box_viability_bounded_chain` over a
trivial domain (the chain's own faces argument covers `gsS`/`gsG`); the full face box —
including `gsN` — is re-derived on that run by `stratified_faces_raw`, and the evolve
domain `domR` follows from the full box (`hdomsat`). Face data over the FROZEN-LEFT
joint system — the same verdict shapes as the R6/S3 layer, plus the non-strict query
`UNSAT(region ∧ ġ > 0)` per stratum. -/
theorem HExistSegB_of_viability_stratified
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
    (gsS gsG gsN : List (Term (Var n))) (M : ℝ) (hM : 0 ≤ M)
    (hwf : (jointSys (fun _ => Term.const 0) fR lam).WellFormed)
    (hfacesL : ∀ gT ∈ gsS ++ gsG, ∀ x ∈ gT.fv, x ∉ (leftBlock fL).bound)
    (hfacesLN : ∀ gT ∈ gsN, ∀ x ∈ gT.fv, x ∉ (leftBlock fL).bound)
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
    (hdomsat : ∀ x : State (Var n),
      (∀ gT ∈ gsS ++ gsG, Term.eval gT x ≤ 0) →
      (∀ gT ∈ gsN, Term.eval gT x ≤ 0) → Formula.sat domR x)
    (K L : NNReal) (a : ℝ) (ha : 0 < a)
    (hLipOn : ∀ ν : State (Var n), (∀ gT ∈ gsS ++ gsG, Term.eval gT ν ≤ 0) →
      LipschitzOnWith K (odeField (jointSys (fun _ => Term.const 0) fR lam))
        (Metric.closedBall ν a))
    (hfbnd : ∀ ν : State (Var n), (∀ gT ∈ gsS ++ gsG, Term.eval gT ν ≤ 0) →
      ∀ x ∈ Metric.closedBall ν a,
        ‖odeField (jointSys (fun _ => Term.const 0) fR lam) x‖ ≤ (L : ℝ))
    (dt : ℝ) (_hdt0 : 0 ≤ dt)
    (ν : State (Var n))
    (hinitS : ∀ gT ∈ gsS, Term.eval gT ν ≤ 0)
    (hinitN : ∀ gT ∈ gsN, Term.eval gT ν ≤ 0)
    (hbudget : ∀ gT ∈ gsG, Term.eval gT ν + M * dt < 0) :
    HExistSegB fL fR lam domL domR dt ν := by
  intro s ΦL hs0 hsdt hΦL0 hderL hmaskL hdomL
  -- face values at the left endpoint are the anchor's (the left run masks them)
  have hcoin : ∀ gT ∈ gsS ++ gsG, Term.eval gT (ΦL s) = Term.eval gT ν :=
    fun gT hgT => Term.coincidence gT (fun y hy =>
      hmaskL s (right_mem_Icc.mpr hs0) y (hfacesL gT hgT y hy))
  have hcoinN : ∀ gT ∈ gsN, Term.eval gT (ΦL s) = Term.eval gT ν :=
    fun gT hgT => Term.coincidence gT (fun y hy =>
      hmaskL s (right_mem_Icc.mpr hs0) y (hfacesLN gT hgT y hy))
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
  -- the run: the EXISTING bounded chain over the trivial domain
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
  -- the full face box — including the non-strict strata — post hoc on the run
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
  have hdomR : ∀ t ∈ Set.Icc (0:ℝ) s, Formula.sat domR (Φ t) := by
    intro t ht
    refine hdomsat (Φ t) ?_ ?_
    · intro gT hgT
      rcases List.mem_append.mp hgT with hm | hm
      · exact hstrat.1 t ht _ (List.mem_append_left _ (List.mem_map.mpr ⟨gT, hm, rfl⟩))
      · exact hstrat.1 t ht _ (List.mem_append_right _ (List.mem_map.mpr ⟨gT, hm, rfl⟩))
    · intro gT hgT
      exact hstrat.2 t ht _ (List.mem_map.mpr ⟨gT, hgT, rfl⟩)
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
