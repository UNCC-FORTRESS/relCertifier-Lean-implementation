/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Explicit contraction runs and their band crossings

A right mode `x_j' = k (c − x_j)` (every other right field zero) moves `x_j` monotonically
toward its set point `c` along `c + (x₀ − c) e^{−k t}`. A cover replay over such modes needs the
run as an `ODESol` (`contract_sol`, the explicit solution of `exists_contract_run`, kept) and
the instant at which it crosses a band boundary `h` strictly between `x₀` and `c`
(`contract_hit`), with the monotonicity that places that instant inside a stretch whose end is
past `h` (`contract_hit_le`). Only the existence of the runs and the switch instants come from
here; the flow facts of a replay are its packs'.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- The explicit contraction of right coordinate `j` from `x`. -/
noncomputable def cΦ (x : State (Var n)) (j : Fin n) (k c : ℝ) : ℝ → State (Var n) :=
  trajJ x j (fun t => c + (x (Rv j) - c) * Real.exp (-(k * t)))

theorem cΦ_j (x : State (Var n)) (j : Fin n) (k c t : ℝ) :
    cΦ x j k c t (Rv j) = c + (x (Rv j) - c) * Real.exp (-(k * t)) := by
  simp [cΦ]

theorem cΦ_ne (x : State (Var n)) (j : Fin n) (k c t : ℝ) {y : Var n} (hy : y ≠ Rv j) :
    cΦ x j k c t y = x y := trajJ_ne x j _ t hy

/-- **The contraction is a run** of the right block for every duration, as soon as the domain
admits every state agreeing with `x` off `x_j` with `x_j` between `x_j(0)` and `c`. -/
theorem contract_sol {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    (x : State (Var n)) (j : Fin n) (k c : ℝ) (hk : 0 ≤ k)
    (hfj : ∀ s, Term.eval (fR j) s = k * (c - s (Rv j)))
    (hfo : ∀ i, i ≠ j → ∀ s, Term.eval (fR i) s = 0)
    (hdom : ∀ v, min (x (Rv j)) c ≤ v → v ≤ max (x (Rv j)) c →
      Formula.sat domR (trajJ x j (fun _ => v) 0))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ODESol (rightBlock fR (Term.const 1)) domR x ε (cΦ x j k c) := by
  refine trajJ_sol x j (fun t => c + (x (Rv j) - c) * Real.exp (-(k * t))) ε hε
    (by simp) (fun t _ _ => ?_) (fun i hi t _ _ => hfo i hi _) (fun t ht _ => ?_)
  · rw [hfj]; simp only [trajJ_j]
    exact hasDerivAt_expApproach k c (x (Rv j)) t
  · obtain ⟨h1, h2⟩ := exp_approach_between k c (x (Rv j)) t hk ht
    have h := hdom _ h1 h2
    have he : trajJ x j (fun _ => c + (x (Rv j) - c) * Real.exp (-(k * t))) 0
        = trajJ x j (fun t => c + (x (Rv j) - c) * Real.exp (-(k * t))) t := by
      funext y; simp [trajJ]
    rwa [he] at h

/-- The crossing instant of the level `h` (strictly between `x₀` and `c` on the same side). -/
noncomputable def hitTime (k c x0 h : ℝ) : ℝ := Real.log ((c - x0) / (c - h)) / k

/-- **The contraction crosses `h` at `hitTime`** (approach from below: `x₀ ≤ h < c`). -/
theorem contract_hit_up (k c x0 h : ℝ) (hk : 0 < k) (hx : x0 ≤ h) (hc : h < c) :
    0 ≤ hitTime k c x0 h ∧
      c + (x0 - c) * Real.exp (-(k * hitTime k c x0 h)) = h := by
  have hpos : 0 < (c - x0) / (c - h) := div_pos (by linarith) (by linarith)
  refine ⟨div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)) hk.le, ?_⟩
  unfold hitTime
  rw [show -(k * (Real.log ((c - x0) / (c - h)) / k)) = -Real.log ((c - x0) / (c - h)) by
    field_simp, Real.exp_neg, Real.exp_log hpos, inv_div]
  have : c - x0 ≠ 0 := by linarith
  field_simp
  ring

/-- **The contraction crosses `h` at `hitTime`** (approach from above: `c < h ≤ x₀`). -/
theorem contract_hit_down (k c x0 h : ℝ) (hk : 0 < k) (hx : h ≤ x0) (hc : c < h) :
    0 ≤ hitTime k c x0 h ∧
      c + (x0 - c) * Real.exp (-(k * hitTime k c x0 h)) = h := by
  have hpos : 0 < (c - x0) / (c - h) := div_pos_of_neg_of_neg (by linarith) (by linarith)
  refine ⟨div_nonneg (Real.log_nonneg ?_) hk.le, ?_⟩
  · rw [le_div_iff_of_neg (by linarith)]; linarith
  unfold hitTime
  rw [show -(k * (Real.log ((c - x0) / (c - h)) / k)) = -Real.log ((c - x0) / (c - h)) by
    field_simp, Real.exp_neg, Real.exp_log hpos, inv_div]
  have : c - x0 ≠ 0 := by linarith
  field_simp
  ring

/-- Approach from below is strictly increasing in time. -/
theorem contract_strictMono_up (k c x0 : ℝ) (hk : 0 < k) (hx : x0 < c) {s t : ℝ} (hst : s < t) :
    c + (x0 - c) * Real.exp (-(k * s)) < c + (x0 - c) * Real.exp (-(k * t)) := by
  have he : Real.exp (-(k * t)) < Real.exp (-(k * s)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  nlinarith

/-- Approach from above is strictly decreasing in time. -/
theorem contract_strictAnti_down (k c x0 : ℝ) (hk : 0 < k) (hx : c < x0) {s t : ℝ}
    (hst : s < t) :
    c + (x0 - c) * Real.exp (-(k * t)) < c + (x0 - c) * Real.exp (-(k * s)) := by
  have he : Real.exp (-(k * t)) < Real.exp (-(k * s)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  nlinarith

/-- A stretch whose end is at or past the level reaches it within the stretch (from below). -/
theorem contract_hit_le_up (k c x0 h T : ℝ) (hk : 0 < k) (hx : x0 ≤ h) (hc : h < c)
    (hT : h ≤ c + (x0 - c) * Real.exp (-(k * T))) : hitTime k c x0 h ≤ T := by
  by_contra hlt
  push Not at hlt
  have hx0 : x0 < c := lt_of_le_of_lt hx hc
  have := contract_strictMono_up k c x0 hk hx0 hlt
  rw [(contract_hit_up k c x0 h hk hx hc).2] at this
  linarith

/-- A stretch whose end is at or past the level reaches it within the stretch (from above). -/
theorem contract_hit_le_down (k c x0 h T : ℝ) (hk : 0 < k) (hx : h ≤ x0) (hc : c < h)
    (hT : c + (x0 - c) * Real.exp (-(k * T)) ≤ h) : hitTime k c x0 h ≤ T := by
  by_contra hlt
  push Not at hlt
  have hx0 : c < x0 := lt_of_lt_of_le hc hx
  have := contract_strictAnti_down k c x0 hk hx0 hlt
  rw [(contract_hit_down k c x0 h hk hx hc).2] at this
  linarith

end RelCertifier
