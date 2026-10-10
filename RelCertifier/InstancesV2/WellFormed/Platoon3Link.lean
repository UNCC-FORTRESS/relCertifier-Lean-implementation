/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The platoon3 link along the reference's own flow: the operating range is kept; the latched AEB sink

Shared by `WellFormed/Platoon3Linkloss` and `WellFormed/Platoon3Profiles`. Along any run of a
damped link `x' = y`, `y' = −(1/8)(x − c) − (3/4) y` with `21 ≤ c ≤ 59` (the right
blocks' links), a start in the operating range's link conjuncts `x ≥ 20`,
`21 ≤ x + 2y ≤ 59` ends in them: the projected gap `x + 2y` is (twice) the slow form
`y + (x − c)/2`, which decays toward 0 (`boxle_Ronly_of_super` with `super_linear_ge_R` /
`super_linear_le_R`, root `1/2`), and the gap floor repels (`gap_floor_Ronly`). The rest of
the operating range (`x ≤ 60`, `|y| ≤ 10`) is the evolve box, which every run keeps.

**The latched AEB sink** (the 2026-10-10 repair, `docs/SUITE-REDESIGN.md` §21). In a sink
`BRAKEk` the braking link follows `x' = y`, `y' = −y/2` (speed matching): the projected gap
`x + 2y` is conserved and `y` decays, so the sink's guard part `x < 20`, `0 ≤ x + 2y < 20` is
kept (`brake_guard_Ronly`); the other two links keep their operating range
(`link_guard_Ronly`). Existence: the explicit solution `solB` (the braking link's closed form
`x + 2y (1 − e^{−t/2})`, `y e^{−t/2}`; the damped links' `gS`, `rS`), inside the evolve box
(`solB_box`). Z3-free.
-/
import RelCertifier.InstancesV2.Modal.Platoon3Link
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace Platoon3Link

open DL DLCalTiming DLRel Set

/-- **The link's operating-range conjuncts are kept by the reference's own flow.** -/
theorem link_guard_Ronly (fR : Fin 6 → Term (Var 6)) (dom : Formula (Var 6)) (jx jy : Fin 6)
    (c : ℝ) (hc21 : 21 ≤ c) (hc59 : c ≤ 59) (hF : LinkField Rv fR jx jy c)
    {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (rightBlock fR (Term.const 1)) dom x t Φ)
    (hg : 20 ≤ x (Rv jx)) (hp1 : 21 ≤ x (Rv jx) + 2 * x (Rv jy))
    (hp2 : x (Rv jx) + 2 * x (Rv jy) ≤ 59) :
    20 ≤ Φ t (Rv jx) ∧ 21 ≤ Φ t (Rv jx) + 2 * Φ t (Rv jy) ∧
      Φ t (Rv jx) + 2 * Φ t (Rv jy) ≤ 59 := by
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  have hfv : ∀ (K : ℝ) (i : Fin 6), Lv i ∉ (linGe (Rv jx) (Rv jy) (1/2) c K).fv := by
    intro K i hi; simp [linGe, linQ, Term.fv, Lv, Rv] at hi
  have hfv' : ∀ (K : ℝ) (i : Fin 6), Lv i ∉ (linLe (Rv jx) (Rv jy) (1/2) c K).fv := by
    intro K i hi; simp [linLe, linQ, Term.fv, Lv, Rv] at hi
  refine ⟨?_, ?_, ?_⟩
  · refine gap_floor_Ronly fR dom jx jy c 20 21 (by norm_num) hc21 hF H.sem ?_ hg
    simp only [pgGe, Term.eval, AOp.interp]; linarith
  · have hbox := boxle_Ronly_of_super (linGe (Rv jx) (Rv jy) (1/2) c ((21 - c)/2)) fR 1
      zero_le_one dom dom (hfv _) (fun z hz => hz)
      (super_linear_ge_R (a := 1/8) (b := 3/4) hroot2 hs2 (by linarith) fR dom
        (fun z _ => hF.1 z) (fun z _ => hF.2 z))
      (ν := x) (by simp only [linGe, eval_linQ, Term.eval, AOp.interp]; linarith)
    have := hbox (Φ t) H.sem
    simp only [linGe, eval_linQ, Term.eval, AOp.interp] at this
    linarith
  · have hbox := boxle_Ronly_of_super (linLe (Rv jx) (Rv jy) (1/2) c ((59 - c)/2)) fR 1
      zero_le_one dom dom (hfv' _) (fun z hz => hz)
      (super_linear_le_R (a := 1/8) (b := 3/4) hroot2 hs2 (by linarith) fR dom
        (fun z _ => hF.1 z) (fun z _ => hF.2 z))
      (ν := x) (by simp only [linLe, eval_linQ, Term.eval, AOp.interp]; linarith)
    have := hbox (Φ t) H.sem
    simp only [linLe, eval_linQ, Term.eval, AOp.interp] at this
    linarith

/-! ## The latched AEB sink -/

/-- One link's operating range on the right (the reference's operating-mode guard). -/
def OpR (x : State (Var 6)) (jx jy : Fin 6) : Prop :=
  20 ≤ x (Rv jx) ∧ x (Rv jx) ≤ 60 ∧ -10 ≤ x (Rv jy) ∧ x (Rv jy) ≤ 10 ∧
    21 ≤ x (Rv jx) + 2 * x (Rv jy) ∧ x (Rv jx) + 2 * x (Rv jy) ≤ 59

/-- The braking link's part of a latched AEB guard: below the floor, the projected gap below
the floor and nonnegative. -/
def BrkR (x : State (Var 6)) (jx jy : Fin 6) : Prop :=
  x (Rv jx) < 20 ∧ x (Rv jx) + 2 * x (Rv jy) < 20 ∧ 0 ≤ x (Rv jx) + 2 * x (Rv jy)

/-- The right evolve box. -/
def BoxR (x : State (Var 6)) : Prop :=
  (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60 ∧ -10 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 10) ∧
  (0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 60 ∧ -10 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 10) ∧
  (0 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 60 ∧ -10 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 10)

/-- The braking link `jx, jy` on the right: `x' = y`, `y' = (1/2)(0 − y)`. -/
def BrakeField (fR : Fin 6 → Term (Var 6)) (jx jy : Fin 6) : Prop :=
  (∀ z, Term.eval (fR jx) z = z (Rv jy)) ∧ (∀ z, Term.eval (fR jy) z = 1/2 * (0 - z (Rv jy)))

/-- **The latched AEB guard part is kept by the braking link's own flow**: `x + 2y` is
conserved, `y` decays toward 0, so `x` moves monotonically from `x₀` toward `x₀ + 2y₀`, both
below 20. -/
theorem brake_guard_Ronly (fR : Fin 6 → Term (Var 6)) (dom : Formula (Var 6)) (jx jy : Fin 6)
    (hB : BrakeField fR jx jy) {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (rightBlock fR (Term.const 1)) dom x t Φ) (h : BrkR x jx jy) :
    BrkR (Φ t) jx jy := by
  obtain ⟨hg, hp, hp0⟩ := h
  have hx := rightBlock_mem' fR (Term.const 1) jx
  have hy := rightBlock_mem' fR (Term.const 1) jy
  have hc := H.affine_const hx hy 1 2 (fun s _ => by
    rw [eval_unit_mul, eval_unit_mul, hB.1, hB.2]; ring)
  have hb := H.linear_between hy (1/2) 0 (by norm_num) (fun s _ => by
    rw [eval_unit_mul, hB.2])
  refine ⟨?_, by linarith, by linarith⟩
  rcases le_total (x (Rv jy)) 0 with h0 | h0
  · rw [min_eq_left h0] at hb; linarith [hb.1]
  · rw [min_eq_right h0] at hb; linarith [hb.1]

/-! ### Existence in the sink: the explicit solution -/

/-- The braking link's closed form (`x' = y`, `y' = −y/2`). -/
noncomputable def bG (x y t : ℝ) : ℝ := x + 2 * y * (1 - E1 t)
noncomputable def bR (y t : ℝ) : ℝ := y * E1 t

/-- One link's solution: braking (`true`) or the damped link at set point 30 (`false`). -/
noncomputable def lG (brk : Bool) (x y t : ℝ) : ℝ := if brk then bG x y t else gS 30 x y t
noncomputable def lR (brk : Bool) (x y t : ℝ) : ℝ := if brk then bR y t else rS 30 x y t
/-- One link's closing-rate field. -/
noncomputable def lF (brk : Bool) (g r : ℝ) : ℝ :=
  if brk then 1/2 * (0 - r) else -(1/8) * (g - 30) - 3/4 * r

theorem lG_zero (brk : Bool) (x y : ℝ) : lG brk x y 0 = x := by
  cases brk <;> simp [lG, bG, E1_zero, gS_zero]
theorem lR_zero (brk : Bool) (x y : ℝ) : lR brk x y 0 = y := by
  cases brk <;> simp [lR, bR, E1_zero, rS_zero]

theorem lG_hasDeriv (brk : Bool) (x y t : ℝ) :
    HasDerivAt (fun u => lG brk x y u) (lR brk x y t) t := by
  cases brk
  · simpa [lG, lR] using gS_hasDeriv 30 x y t
  · simp only [lG, lR, bG, bR, if_true]
    exact ((((hasDerivAt_E1 t).const_sub 1).const_mul (2 * y)).const_add x).congr_deriv
      (by ring)

theorem lR_hasDeriv (brk : Bool) (x y t : ℝ) :
    HasDerivAt (fun u => lR brk x y u) (lF brk (lG brk x y t) (lR brk x y t)) t := by
  cases brk
  · simpa [lG, lR, lF] using rS_hasDeriv 30 x y t
  · simp only [lG, lR, lF, bG, bR, if_true]
    exact ((hasDerivAt_E1 t).const_mul y).congr_deriv (by ring)

/-- The three links' fields on the right, link `k` braking iff flag `bk`. -/
def BField3 (fR : Fin 6 → Term (Var 6)) (b0 b1 b2 : Bool) : Prop :=
  ∀ z : State (Var 6),
    Term.eval (fR 0) z = z (Rv 1) ∧ Term.eval (fR 1) z = lF b0 (z (Rv 0)) (z (Rv 1)) ∧
    Term.eval (fR 2) z = z (Rv 3) ∧ Term.eval (fR 3) z = lF b1 (z (Rv 2)) (z (Rv 3)) ∧
    Term.eval (fR 4) z = z (Rv 5) ∧ Term.eval (fR 5) z = lF b2 (z (Rv 4)) (z (Rv 5))

/-- The explicit solution, coordinatewise. -/
noncomputable def solB (b0 b1 b2 : Bool) (b : State (Var 6)) : Fin 6 → ℝ → ℝ
  | ⟨0, _⟩ => fun t => lG b0 (b (Rv 0)) (b (Rv 1)) t
  | ⟨1, _⟩ => fun t => lR b0 (b (Rv 0)) (b (Rv 1)) t
  | ⟨2, _⟩ => fun t => lG b1 (b (Rv 2)) (b (Rv 3)) t
  | ⟨3, _⟩ => fun t => lR b1 (b (Rv 2)) (b (Rv 3)) t
  | ⟨4, _⟩ => fun t => lG b2 (b (Rv 4)) (b (Rv 5)) t
  | ⟨5, _⟩ => fun t => lR b2 (b (Rv 4)) (b (Rv 5)) t

/-- One link's box along its solution: from the box, with the projected gap in `[0, 60]`
(braking) or in `[21, 60]` (the damped link). -/
theorem l_box (brk : Bool) (x y t : ℝ) (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x ≤ 60)
    (hy0 : -10 ≤ y) (hy1 : y ≤ 10) (hp1 : x + 2 * y ≤ 60)
    (hp0 : (if brk then (0:ℝ) else 21) ≤ x + 2 * y) :
    (0 ≤ lG brk x y t ∧ lG brk x y t ≤ 60) ∧ (-10 ≤ lR brk x y t ∧ lR brk x y t ≤ 10) := by
  cases brk
  · simp at hp0
    have := link_bounds 30 (9/2) x y t ht (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx0 hx1 hy0 hy1 (by simp only [Q2]; linarith) (by simp only [Q2]; linarith)
    simpa [lG, lR] using this
  · simp at hp0
    have he0 : 0 < E1 t := Real.exp_pos _
    have he1 : E1 t ≤ 1 := by unfold E1; rw [Real.exp_le_one_iff]; linarith
    simp only [lG, lR, bG, bR, if_true]
    rcases le_total y 0 with hy | hy
    · refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
    · refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-- **Existence in a sink** (clause (i)): the explicit solution solves the right block and
stays in the evolve box. -/
theorem solB_sol (b0 b1 b2 : Bool) (fR : Fin 6 → Term (Var 6)) (hF : BField3 fR b0 b1 b2)
    (dom : Formula (Var 6)) (hdom : ∀ z, BoxR z → Formula.sat dom z) (b : State (Var 6))
    (hb : BoxR b)
    (h0 : (if b0 then (0:ℝ) else 21) ≤ b (Rv 0) + 2 * b (Rv 1) ∧ b (Rv 0) + 2 * b (Rv 1) ≤ 60)
    (h1 : (if b1 then (0:ℝ) else 21) ≤ b (Rv 2) + 2 * b (Rv 3) ∧ b (Rv 2) + 2 * b (Rv 3) ≤ 60)
    (h2 : (if b2 then (0:ℝ) else 21) ≤ b (Rv 4) + 2 * b (Rv 5) ∧ b (Rv 4) + 2 * b (Rv 5) ≤ 60)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (rightBlock fR (Term.const 1)) dom b τ (trajR b (solB b0 b1 b2 b)) := by
  refine explicit_sol b (solB b0 b1 b2 b) τ hτ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [solB, lG_zero, lR_zero]
  · intro i t _ _
    obtain ⟨f0, f1, f2, f3, f4, f5⟩ := hF (trajR b (solB b0 b1 b2 b) t)
    fin_cases i
    · show HasDerivAt (solB b0 b1 b2 b 0) _ t
      rw [show ((⟨0, by norm_num⟩ : Fin 6)) = (0 : Fin 6) from rfl, f0, trajR_R]
      exact lG_hasDeriv b0 _ _ t
    · show HasDerivAt (solB b0 b1 b2 b 1) _ t
      rw [show ((⟨1, by norm_num⟩ : Fin 6)) = (1 : Fin 6) from rfl, f1, trajR_R, trajR_R]
      exact lR_hasDeriv b0 _ _ t
    · show HasDerivAt (solB b0 b1 b2 b 2) _ t
      rw [show ((⟨2, by norm_num⟩ : Fin 6)) = (2 : Fin 6) from rfl, f2, trajR_R]
      exact lG_hasDeriv b1 _ _ t
    · show HasDerivAt (solB b0 b1 b2 b 3) _ t
      rw [show ((⟨3, by norm_num⟩ : Fin 6)) = (3 : Fin 6) from rfl, f3, trajR_R, trajR_R]
      exact lR_hasDeriv b1 _ _ t
    · show HasDerivAt (solB b0 b1 b2 b 4) _ t
      rw [show ((⟨4, by norm_num⟩ : Fin 6)) = (4 : Fin 6) from rfl, f4, trajR_R]
      exact lG_hasDeriv b2 _ _ t
    · show HasDerivAt (solB b0 b1 b2 b 5) _ t
      rw [show ((⟨5, by norm_num⟩ : Fin 6)) = (5 : Fin 6) from rfl, f5, trajR_R, trajR_R]
      exact lR_hasDeriv b2 _ _ t
  · intro t ht _
    apply hdom
    obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hb
    have k0 := l_box b0 _ _ t ht x0 x1 y0 y1 h0.2 h0.1
    have k1 := l_box b1 _ _ t ht x2 x3 y2 y3 h1.2 h1.1
    have k2 := l_box b2 _ _ t ht x4 x5 y4 y5 h2.2 h2.1
    simp only [BoxR, trajR_R]
    exact ⟨⟨k0.1.1, k0.1.2, k0.2.1, k0.2.2⟩, ⟨k1.1.1, k1.1.2, k1.2.1, k1.2.2⟩,
      ⟨k2.1.1, k2.1.2, k2.2.1, k2.2.2⟩⟩

end Platoon3Link
end RelCertifier
