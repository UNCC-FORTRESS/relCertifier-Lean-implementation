/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# R6 — box viability: the last analytic hypothesis becomes certificates

The frozen hypothesis contract keeps ONE analytic obligation out of the trusted column:
right flows don't die early — from any admissible state, solutions of a mode's field
exist and stay in the evolve box for the piece duration. This file discharges it from
Z3-checkable face certificates:

* **face queries** — per evolve-box face `g ≤ 0`, the STRICT boundary query
  `UNSAT(box ∧ g = 0 ∧ ġ ≥ 0)` — literally `flowQueryStrict` with the LEFT FROZEN
  (`fL = 0`), the same shape (and printer) as every other flow query. Strictness is
  load-bearing: nonstrict subtangency (Nagumo) is not in the vendored Mathlib, and the
  strict per-face `DI` argument needs no regularity hypothesis.
* `strict_faces_endpoint` / `strict_faces_raw` — the multi-face, box-conditioned
  first-exit argument: at the first joint exit ALL faces still hold (so the
  box-conditioned Lie sign applies), the exiting face sits on its boundary, and its
  strictly negative Lie contradicts the exit slope. (Finitely many faces: the closure
  of the union of exit-witness sets is the union of closures.)
* `box_viability_step` / `box_viability` — Picard local existence from on-ball
  Lipschitz data (`picard_isPL_of_local`, polynomial fields are ball-Lipschitz by
  `odeField_lipschitzOnWith`), the step staying in the box by the faces argument,
  glued to ANY duration by `chainN`.

Equilibrium-on-a-face modes (the face query legitimately declines — e.g. the legacy
watertank's `Mid`, `3(1 − 0.04x)` vanishing at the evolve bound) take per-shape closed-form lemmas
(affine chase; follow-up), or remain a named per-mode single-system hypothesis —
within the frozen contract either way.
-/
import RelCertifier.Proofs.Flow.PicardBridge
import RelCertifier.Proofs.Flow.StratifiedBarrier

namespace RelCertifier
open DL Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Closure of a list-indexed union is covered by the closures (list induction). -/
theorem mem_closure_biUnion_list {α β : Type*} [TopologicalSpace β]
    (l : List α) (f : α → Set β) {x : β}
    (hx : x ∈ closure (⋃ a ∈ l, f a)) : ∃ a ∈ l, x ∈ closure (f a) := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      have hsplit : (⋃ b ∈ (a :: l), f b) = f a ∪ ⋃ b ∈ l, f b := by
        simp
      rw [hsplit, closure_union] at hx
      rcases hx with hx | hx
      · exact ⟨a, List.mem_cons_self, hx⟩
      · obtain ⟨b, hb, hxb⟩ := ih hx
        exact ⟨b, List.mem_cons_of_mem _ hb, hxb⟩

/-! ## The multi-face first-exit argument -/

/-- **Endpoint form.** Box-conditioned strict inflow on every face keeps a raw integral
curve in the box: at the first joint exit all faces hold (closedness), some face is on
its boundary with a strictly negative Lie derivative, contradicting the exit slope. -/
theorem strict_faces_endpoint {sys : ODESystem V} (hwf : sys.WellFormed)
    (gs : List (State V → ℝ))
    (hg : ∀ g ∈ gs, Differentiable ℝ g)
    (hbnd : ∀ g ∈ gs, ∀ x, (∀ g' ∈ gs, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    {r : ℝ} {Φ : ℝ → State V} (hr : 0 ≤ r)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinit : ∀ g ∈ gs, g (Φ 0) ≤ 0) :
    ∀ g ∈ gs, g (Φ r) ≤ 0 := by
  have hderiv : ∀ g ∈ gs, ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun g hgm t ht => hasDeriv_g_along_flow hwf (hg g hgm) hcurve ht
  have hcont : ∀ g ∈ gs, ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun g hgm t ht => (hderiv g hgm t ht).continuousWithinAt
  by_contra hcon
  push_neg at hcon
  obtain ⟨gbad, hgbad, hbadpos⟩ := hcon
  -- the joint sublevel-time set
  set S : Set ℝ := Set.Icc 0 r ∩ {t | ∀ g ∈ gs, g (Φ t) ≤ 0} with hSdef
  have hSclosed : IsClosed S := by
    have : {t | ∀ g ∈ gs, g (Φ t) ≤ 0} ∩ Set.Icc 0 r =
        (⋂ g ∈ gs, Set.Icc 0 r ∩ (fun s => g (Φ s)) ⁻¹' Set.Iic 0) ∩ Set.Icc 0 r := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
        Set.mem_Iic]
      constructor
      · rintro ⟨hall, ht⟩
        exact ⟨fun g hgm => ⟨ht, hall g hgm⟩, ht⟩
      · rintro ⟨hall, ht⟩
        exact ⟨fun g hgm => (hall g hgm).2, ht⟩
    rw [hSdef, Set.inter_comm, this]
    refine IsClosed.inter (isClosed_biInter ?_) isClosed_Icc
    intro g hgm
    exact ((hcont g hgm).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
  have h0S : (0:ℝ) ∈ S := ⟨Set.left_mem_Icc.mpr hr, hinit⟩
  have hSbdd : BddAbove S := ⟨r, fun t ht => ht.1.2⟩
  set s := sSup S with hsdef
  have hsS : s ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hSbdd
  have hsIcc : s ∈ Set.Icc 0 r := hsS.1
  have hsall : ∀ g ∈ gs, g (Φ s) ≤ 0 := hsS.2
  have hs_ub : ∀ t ∈ S, t ≤ s := fun t htS => le_csSup hSbdd htS
  clear_value s
  have hsr : s < r := by
    rcases lt_or_eq_of_le hsIcc.2 with h | h
    · exact h
    · subst h
      exact absurd (hsall gbad hgbad) (not_le.mpr hbadpos)
  -- right of the sup, some face is positive; finitely many faces ⟹ one face's
  -- exit-witness set has the sup in its closure
  have hUnion : Set.Ioc s r ⊆ ⋃ g ∈ gs, {t ∈ Set.Ioc s r | 0 < g (Φ t)} := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 r := ⟨le_trans hsIcc.1 ht.1.le, ht.2⟩
    have htnS : t ∉ S := fun htS => absurd (hs_ub t htS) (not_le.mpr ht.1)
    have : ¬ ∀ g ∈ gs, g (Φ t) ≤ 0 := fun hall => htnS ⟨htIcc, hall⟩
    push_neg at this
    obtain ⟨g, hgm, hgt⟩ := this
    exact Set.mem_biUnion hgm ⟨ht, hgt⟩
  have hmem : s ∈ closure (Set.Ioc s r) := by
    rw [closure_Ioc (ne_of_lt hsr)]
    exact Set.left_mem_Icc.mpr hsr.le
  have hmemU : s ∈ closure (⋃ g ∈ gs, {t ∈ Set.Ioc s r | 0 < g (Φ t)}) :=
    closure_mono hUnion hmem
  obtain ⟨g, hgm, hcl⟩ := mem_closure_biUnion_list gs _ hmemU
  -- the exiting face: value 0 at the sup, strictly negative Lie, positive exit slope
  set W : Set ℝ := {t ∈ Set.Ioc s r | 0 < g (Φ t)} with hWdef
  haveI hneBot : (nhdsWithin s W).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hWIcc : W ⊆ Set.Icc 0 r :=
    fun t ht => ⟨le_trans hsIcc.1 ht.1.1.le, ht.1.2⟩
  have hge0 : 0 ≤ g (Φ s) := by
    have htend := (hcont g hgm s hsIcc).mono_left (nhdsWithin_mono s hWIcc)
    exact ge_of_tendsto htend
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht.2.le))
  have hgeq0 : g (Φ s) = 0 := le_antisymm (hsall g hgm) hge0
  have hLie : Lie sys g (Φ s) < 0 := hbnd g hgm (Φ s) hsall hgeq0
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv g hgm s hsIcc)).mono_left
    (nhdsWithin_mono s (fun t ht => ⟨hWIcc ht, ne_of_gt ht.1.1⟩))
  have hslopepos : ∀ᶠ t in nhdsWithin s W, 0 < slope (fun t => g (Φ t)) s t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    exact div_pos (by rw [hgeq0]; simpa using ht.2) (by linarith [ht.1.1])
  exact absurd (ge_of_tendsto hslope (hslopepos.mono fun t h => le_of_lt h))
    (not_le.mpr hLie)

/-- All-times form (apply the endpoint form to every cut). -/
theorem strict_faces_raw {sys : ODESystem V} (hwf : sys.WellFormed)
    (gs : List (State V → ℝ))
    (hg : ∀ g ∈ gs, Differentiable ℝ g)
    (hbnd : ∀ g ∈ gs, ∀ x, (∀ g' ∈ gs, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinit : ∀ g ∈ gs, g (Φ 0) ≤ 0) :
    ∀ t ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gs, g (Φ t) ≤ 0 := by
  intro t ht
  have hsub : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 t) :=
    fun u hu => (hcurve u ⟨hu.1, le_trans hu.2 ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2)
  exact strict_faces_endpoint hwf gs hg hbnd ht.1 hsub hinit

/-! ## The viability assembly: Picard step + faces staying + chaining -/

/-- **Uniform viability step.** From any box point: a Picard run of length `r₀`
(on-ball Lipschitz + bound, uniform over the box), staying in the box by the strict
faces (`strict_faces_raw`), landing at another box point. -/
theorem box_viability_step {sys : ODESystem V} {dom : Formula V} (hwf : sys.WellFormed)
    (gs : List (State V → ℝ))
    (hg : ∀ g ∈ gs, Differentiable ℝ g)
    (hbnd : ∀ g ∈ gs, ∀ x, (∀ g' ∈ gs, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    (hdomsat : ∀ x : State V, (∀ g ∈ gs, g x ≤ 0) → Formula.sat dom x)
    (K L : NNReal) (a : ℝ) (ha : 0 < a)
    (hLipOn : ∀ ν : State V, (∀ g ∈ gs, g ν ≤ 0) →
      LipschitzOnWith K (odeField sys) (Metric.closedBall ν a))
    (hfbnd : ∀ ν : State V, (∀ g ∈ gs, g ν ≤ 0) →
      ∀ x ∈ Metric.closedBall ν a, ‖odeField sys x‖ ≤ (L : ℝ))
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hr₀le : (L : ℝ) * r₀ ≤ a) :
    ∀ ν : State V, (∀ g ∈ gs, g ν ≤ 0) →
      ∃ ν', (∀ g ∈ gs, g ν' ≤ 0) ∧ RunFor sys dom r₀ ν ν' := by
  intro ν hP
  have hpl := picard_isPL_of_local K L ν a ha.le (hLipOn ν hP) (hfbnd ν hP) r₀ hr₀ hr₀le
  have hdomC : ∀ Φ : ℝ → State V, Φ 0 = ν →
      IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r₀) →
      ∀ t ∈ Set.Icc (0:ℝ) r₀, Formula.sat dom (Φ t) := by
    intro Φ hΦ0 hcurve t ht
    refine hdomsat (Φ t) ?_
    exact strict_faces_raw hwf gs hg hbnd hcurve
      (fun g hgm => by rw [hΦ0]; exact hP g hgm) t ht
  obtain ⟨Φ, hΦ0, hcurve, hrun⟩ := picard_to_RunFor ν hr₀ hpl hdomC
  refine ⟨Φ r₀, ?_, hrun⟩
  exact strict_faces_raw hwf gs hg hbnd hcurve
    (fun g hgm => by rw [hΦ0]; exact hP g hgm) r₀ (Set.right_mem_Icc.mpr hr₀.le)

/-- **Box viability (R6 core).** Strict-face certificates + on-ball Picard data give
runs of ANY duration from any box point, staying in the box — the single-system
non-blocking fact the frozen contract requires, now certificate-backed. -/
theorem box_viability {sys : ODESystem V} {dom : Formula V} (hwf : sys.WellFormed)
    (gs : List (State V → ℝ))
    (hg : ∀ g ∈ gs, Differentiable ℝ g)
    (hbnd : ∀ g ∈ gs, ∀ x, (∀ g' ∈ gs, g' x ≤ 0) → g x = 0 → Lie sys g x < 0)
    (hdomsat : ∀ x : State V, (∀ g ∈ gs, g x ≤ 0) → Formula.sat dom x)
    (K L : NNReal) (a : ℝ) (ha : 0 < a)
    (hLipOn : ∀ ν : State V, (∀ g ∈ gs, g ν ≤ 0) →
      LipschitzOnWith K (odeField sys) (Metric.closedBall ν a))
    (hfbnd : ∀ ν : State V, (∀ g ∈ gs, g ν ≤ 0) →
      ∀ x ∈ Metric.closedBall ν a, ‖odeField sys x‖ ≤ (L : ℝ))
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hr₀le : (L : ℝ) * r₀ ≤ a) :
    ∀ ν : State V, (∀ g ∈ gs, g ν ≤ 0) → ∀ T : ℝ, 0 ≤ T →
      ∃ ν', RunFor sys dom T ν ν' := by
  intro ν hP T hT
  obtain ⟨n, hn⟩ := exists_nat_ge (T / r₀)
  refine chainN hr₀ (fun x => ∀ g ∈ gs, g x ≤ 0)
    (box_viability_step hwf gs hg hbnd hdomsat K L a ha hLipOn hfbnd r₀ hr₀ hr₀le)
    (fun x hx => hdomsat x hx) n T hT ?_ ν hP
  calc T = (T / r₀) * r₀ := by field_simp
    _ ≤ (n : ℝ) * r₀ := by
        exact mul_le_mul_of_nonneg_right hn hr₀.le

/-! ## The Z3 leaf: strict face verdicts (frozen-left `flowQueryStrict`) -/

/-- A strict face verdict — `flowQueryStrict` with the LEFT FROZEN over the box domain —
gives the box-conditioned strict inflow of that face, in the `Term`-level form the
assembly consumes. `bigLe faces` is the box formula; `sat_bigLe_iff` mediates. -/
theorem face_strict_from_verdict {n : ℕ} (faces : List (Term (Var n)))
    (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (g : Term (Var n))
    (hz3 : z3solve (flowQueryStrict ⟨g, (fun _ => Term.const 0), fR, lam,
      bigLe faces⟩) = Verdict.unsat) :
    ∀ x : State (Var n), (∀ g' ∈ faces, Term.eval g' x ≤ 0) →
      Term.eval g x = 0 →
      Lie (jointSys (fun _ => Term.const 0) fR lam) (fun ω => Term.eval g ω) x < 0 := by
  intro x hbox hg0
  have hunsat := z3_unsat_sound hz3
  by_contra hpos
  rw [not_lt] at hpos
  refine hunsat x ⟨(sat_bigLe_iff faces x).mpr hbox, ?_, ?_⟩
  · simpa [Formula.sat, CompOp.interp, Term.eval] using hg0
  · rw [← lieDeriv_correct] at hpos
    simpa [Formula.sat, CompOp.interp, Term.eval] using hpos

end RelCertifier
