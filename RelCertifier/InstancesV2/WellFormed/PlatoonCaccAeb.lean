/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The CACC/AEB platoon follower along its own flow (Assumption 1 support)

Shared by `WellFormed/PlatoonLinkloss` and `WellFormed/PlatoonLatency`, whose right models are
the same follower: gap `g` (coordinate `jx`), range rate `r` (coordinate `jy`), every other
right field zero, evolve box `0 ≤ g ≤ 60`, `|r| ≤ 10`.

* `CACC`: `g' = r`, `r' = −(1/8)(g − 20) − (3/4) r` (poles `1/4`, `1/2`). The projected stop
  gap `w = g + 2r` is the slow modal coordinate, `w' = −(1/4)(w − 20)` (`cacc_w_band`), and
  `z = r + (g − 20)/4` the fast one, `z' = −z/2`. The explicit solution `gS`, `rS`
  (`u = e^{−t/4}`: `g − 20 = 4 (a u − b u²)`, `r = 2 b u² − a u` with `a = w/2 − 10`,
  `b = z`) stays in the evolve box for all time from every box state with `0 ≤ w ≤ 60`
  (`cacc_box`; the gap floor uses the interior minimum `gap_lo_aux`), so a run of every
  duration exists (`cacc_exists`).
* `AEB`: `g' = r`, `r' = −r/2` (speed matching): `w` is conserved (`aeb_w_const`), `r`
  decays; the explicit solution `bG`, `bR` moves `g` monotonically from `g₀` toward `w₀`,
  so it stays in the box from every box state with `0 ≤ w ≤ 60` (`aeb_exists`).

Stated over an abstract right field `fR : Fin n → Term (Var n)` and domain `dom` whose
evaluations are hypotheses (`CaccField`, `AebField`, a box-to-domain map); independent of
any IR literal. Z3-free; the closed-form combination lemma is the one of
`WellFormed/AccSpoofLag`, the link solution and its aux bounds those of
`WellFormed/Platoon3Link` at set point 20 (the gap floor re-proved for the wider
`w ≥ 0` start).
-/
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace PlatoonCaccAeb

open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## The follower's field shapes and the evolve box -/

/-- The evolve box of the follower: gap `jx` in `[0, 60]`, range rate `jy` in `[−10, 10]`. -/
def Box (z : State (Var n)) (jx jy : Fin n) : Prop :=
  0 ≤ z (Rv jx) ∧ z (Rv jx) ≤ 60 ∧ -10 ≤ z (Rv jy) ∧ z (Rv jy) ≤ 10

/-- The CACC loop `g' = r`, `r' = −(1/8)(g − 20) − (3/4) r`; every other right field 0. -/
def CaccField (fR : Fin n → Term (Var n)) (jx jy : Fin n) : Prop :=
  (∀ z, Term.eval (fR jx) z = z (Rv jy)) ∧
  (∀ z, Term.eval (fR jy) z = -(1/8) * (z (Rv jx) - 20) - 3/4 * z (Rv jy)) ∧
  (∀ i, i ≠ jx → i ≠ jy → ∀ z, Term.eval (fR i) z = 0)

/-- The AEB (speed matching) `g' = r`, `r' = −r/2`; every other right field 0. -/
def AebField (fR : Fin n → Term (Var n)) (jx jy : Fin n) : Prop :=
  (∀ z, Term.eval (fR jx) z = z (Rv jy)) ∧
  (∀ z, Term.eval (fR jy) z = -(1/2) * z (Rv jy)) ∧
  (∀ i, i ≠ jx → i ≠ jy → ∀ z, Term.eval (fR i) z = 0)

/-! ## A decaying affine combination of two coordinates -/

/-- **Closed form of a decaying affine combination of two coordinates**: if
`α f₁ + β f₂ = k (c − (α y₁ + β y₂))` on the domain, `w = α y₁ + β y₂` satisfies
`w(r) = c + (w₀ − c) e^{−k r}`. -/
theorem affine_linear_exact {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y₁ y₂ : Var n} {f₁ f₂ : Term (Var n)} (h₁ : (y₁, f₁) ∈ sys) (h₂ : (y₂, f₂) ∈ sys)
    (α β k c : ℝ)
    (hf : ∀ s, Formula.sat dom s →
      α * Term.eval f₁ s + β * Term.eval f₂ s = k * (c - (α * s y₁ + β * s y₂))) :
    α * Φ r y₁ + β * Φ r y₂ = c + (α * x y₁ + β * x y₂ - c) * Real.exp (-(k * r)) := by
  set G : ℝ → ℝ := fun t => (c - (α * Φ t y₁ + β * Φ t y₂)) * Real.exp (k * t) with hG
  have hGder : ∀ t ∈ Set.Icc (0:ℝ) r, HasDerivWithinAt G 0 (Set.Icc 0 r) t := by
    intro t ht
    have d1 := (H.hder t ht (y₁, f₁) h₁).const_mul α
    have d2 := (H.hder t ht (y₂, f₂) h₂).const_mul β
    have h2 : HasDerivWithinAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1))
        (Set.Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul k).exp).hasDerivWithinAt
    have hft := hf _ (H.hdom t ht)
    exact (((d1.add d2).const_sub c).mul h2).congr_deriv
      (by simp only [Pi.add_apply]; linear_combination (-(Real.exp (k * t))) * hft)
  have hcont : ContinuousOn G (Set.Icc 0 r) := fun t ht => (hGder t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht =>
    (hGder t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    r ⟨H.hr, le_refl r⟩
  simp only [hG, H.hΦ0, mul_zero, Real.exp_zero, mul_one] at hconst
  have hexp : Real.exp (k * r) * Real.exp (-(k * r)) = 1 := by
    rw [← Real.exp_add]; simp
  have : c - (α * Φ r y₁ + β * Φ r y₂) = (c - (α * x y₁ + β * x y₂)) * Real.exp (-(k * r)) := by
    calc c - (α * Φ r y₁ + β * Φ r y₂)
        = (c - (α * Φ r y₁ + β * Φ r y₂)) * (Real.exp (k * r) * Real.exp (-(k * r))) := by
          rw [hexp, mul_one]
      _ = ((c - (α * Φ r y₁ + β * Φ r y₂)) * Real.exp (k * r)) * Real.exp (-(k * r)) := by ring
      _ = (c - (α * x y₁ + β * x y₂)) * Real.exp (-(k * r)) := by rw [hconst]
  linarith

/-- A value scaled by a factor in `(0, 1]` stays in a band containing `0` and the value. -/
theorem scale_band {lo hi p e : ℝ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hp1 : lo ≤ p) (hp2 : p ≤ hi)
    (he0 : 0 < e) (he1 : e ≤ 1) : lo ≤ p * e ∧ p * e ≤ hi := by
  rcases le_total p 0 with h | h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- **A modal coordinate keeps its band**: a decaying affine combination (`k ≥ 0`) whose set
point `c` and start lie in `[lo, hi]` ends in `[lo, hi]`. -/
theorem affine_band {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y₁ y₂ : Var n} {f₁ f₂ : Term (Var n)} (h₁ : (y₁, f₁) ∈ sys) (h₂ : (y₂, f₂) ∈ sys)
    (α β k c lo hi : ℝ) (hk : 0 ≤ k)
    (hf : ∀ s, Formula.sat dom s →
      α * Term.eval f₁ s + β * Term.eval f₂ s = k * (c - (α * s y₁ + β * s y₂)))
    (hc1 : lo ≤ c) (hc2 : c ≤ hi) (hx1 : lo ≤ α * x y₁ + β * x y₂)
    (hx2 : α * x y₁ + β * x y₂ ≤ hi) :
    lo ≤ α * Φ r y₁ + β * Φ r y₂ ∧ α * Φ r y₁ + β * Φ r y₂ ≤ hi := by
  rw [affine_linear_exact H h₁ h₂ α β k c hf]
  have he0 : 0 < Real.exp (-(k * r)) := Real.exp_pos _
  have he1 : Real.exp (-(k * r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [H.hr]
  have := scale_band (lo := lo - c) (hi := hi - c) (p := α * x y₁ + β * x y₂ - c)
    (by linarith) (by linarith) (by linarith) (by linarith) he0 he1
  constructor <;> linarith [this.1, this.2]

/-! ## Clause (ii): the guards along the follower's own flow -/

/-- **Along CACC the projected stop gap keeps every band around 20**: `w = g + 2r` obeys
`w' = −(1/4)(w − 20)`. -/
theorem cacc_w_band {fR : Fin n → Term (Var n)} {dom : Formula (Var n)} {jx jy : Fin n}
    (hF : CaccField fR jx jy) {x : State (Var n)} {t : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) dom x t Φ) (lo hi : ℝ) (hlo : lo ≤ 20)
    (hhi : 20 ≤ hi) (h1 : lo ≤ x (Rv jx) + 2 * x (Rv jy))
    (h2 : x (Rv jx) + 2 * x (Rv jy) ≤ hi) :
    lo ≤ Φ t (Rv jx) + 2 * Φ t (Rv jy) ∧ Φ t (Rv jx) + 2 * Φ t (Rv jy) ≤ hi := by
  have hb := affine_band H (rightBlock_mem' fR (Term.const 1) jx)
    (rightBlock_mem' fR (Term.const 1) jy) 1 2 (1/4) 20 lo hi (by norm_num)
    (fun s _ => by rw [eval_unit_mul, eval_unit_mul, hF.1, hF.2.1]; ring) hlo hhi
    (by linarith) (by linarith)
  constructor <;> linarith [hb.1, hb.2]

/-- **Along AEB the projected stop gap is conserved** (`w' = r + 2 (−r/2) = 0`). -/
theorem aeb_w_const {fR : Fin n → Term (Var n)} {dom : Formula (Var n)} {jx jy : Fin n}
    (hF : AebField fR jx jy) {x : State (Var n)} {t : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) dom x t Φ) :
    Φ t (Rv jx) + 2 * Φ t (Rv jy) = x (Rv jx) + 2 * x (Rv jy) := by
  have hc := H.affine_const (rightBlock_mem' fR (Term.const 1) jx)
    (rightBlock_mem' fR (Term.const 1) jy) 1 2
    (fun s _ => by rw [eval_unit_mul, eval_unit_mul, hF.1, hF.2.1]; ring)
  linarith

/-! ## Clause (i): explicit solutions -/

noncomputable def E1 (t : ℝ) : ℝ := Real.exp (-(1/2) * t)

noncomputable def E2 (t : ℝ) : ℝ := Real.exp (-(1/4) * t)

theorem hasDerivAt_E1 (t : ℝ) : HasDerivAt E1 (-(1/2) * E1 t) t := by
  have hin : HasDerivAt (fun u : ℝ => -(1/2) * u) (-(1/2)) t := by
    have h := (hasDerivAt_id t).const_mul (-(1/2 : ℝ))
    simp only [id, mul_one] at h
    exact h
  have h := (Real.hasDerivAt_exp (-(1/2) * t)).comp t hin
  rw [mul_comm] at h
  exact h

theorem hasDerivAt_E2 (t : ℝ) : HasDerivAt E2 (-(1/4) * E2 t) t := by
  have hin : HasDerivAt (fun u : ℝ => -(1/4) * u) (-(1/4)) t := by
    have h := (hasDerivAt_id t).const_mul (-(1/4 : ℝ))
    simp only [id, mul_one] at h
    exact h
  have h := (Real.hasDerivAt_exp (-(1/4) * t)).comp t hin
  rw [mul_comm] at h
  exact h

theorem E1_zero : E1 0 = 1 := by simp [E1]

theorem E2_zero : E2 0 = 1 := by simp [E2]

theorem E1_pos (t : ℝ) : 0 < E1 t := Real.exp_pos _

theorem E2_pos (t : ℝ) : 0 < E2 t := Real.exp_pos _

theorem E1_le (t : ℝ) (ht : 0 ≤ t) : E1 t ≤ 1 := by
  unfold E1; rw [Real.exp_le_one_iff]; linarith

theorem E2_le (t : ℝ) (ht : 0 ≤ t) : E2 t ≤ 1 := by
  unfold E2; rw [Real.exp_le_one_iff]; linarith

theorem E1_sq (t : ℝ) : E1 t = E2 t * E2 t := by
  unfold E1 E2; rw [← Real.exp_add]; ring_nf

/-! ### CACC: the two-exponential solution -/

/-- The fast modal coordinate `z = r + (g − 20)/4` (`z' = −z/2`). -/
noncomputable def Q1 (x y : ℝ) : ℝ := y + 1/4 * (x - 20)

/-- The slow modal coordinate `w/2 − 10 = r + (g − 20)/2` (`' = −(1/4)·`). -/
noncomputable def Q2 (x y : ℝ) : ℝ := y + 1/2 * (x - 20)

/-- The CACC solution from `(g₀, r₀) = (x, y)`: gap. -/
noncomputable def gS (x y t : ℝ) : ℝ := 20 + 4 * (Q2 x y * E2 t - Q1 x y * E1 t)

/-- The CACC solution from `(g₀, r₀) = (x, y)`: range rate. -/
noncomputable def rS (x y t : ℝ) : ℝ := 2 * Q1 x y * E1 t - Q2 x y * E2 t

theorem gS_zero (x y : ℝ) : gS x y 0 = x := by
  simp only [gS, Q1, Q2, E1_zero, E2_zero]; ring

theorem rS_zero (x y : ℝ) : rS x y 0 = y := by
  simp only [rS, Q1, Q2, E1_zero, E2_zero]; ring

theorem gS_hasDeriv (x y t : ℝ) : HasDerivAt (gS x y) (rS x y t) t := by
  have h : HasDerivAt (fun u => 20 + 4 * (Q2 x y * E2 u - Q1 x y * E1 u))
      (4 * (Q2 x y * (-(1/4) * E2 t) - Q1 x y * (-(1/2) * E1 t))) t :=
    ((((hasDerivAt_E2 t).const_mul (Q2 x y)).sub
      ((hasDerivAt_E1 t).const_mul (Q1 x y))).const_mul 4).const_add 20
  have e : rS x y t = 4 * (Q2 x y * (-(1/4) * E2 t) - Q1 x y * (-(1/2) * E1 t)) := by
    simp only [rS]; ring
  rw [e]
  exact h

theorem rS_hasDeriv (x y t : ℝ) :
    HasDerivAt (rS x y) (-(1/8) * (gS x y t - 20) - 3/4 * rS x y t) t := by
  have h : HasDerivAt (fun u => 2 * Q1 x y * E1 u - Q2 x y * E2 u)
      (2 * Q1 x y * (-(1/2) * E1 t) - Q2 x y * (-(1/4) * E2 t)) t :=
    ((hasDerivAt_E1 t).const_mul (2 * Q1 x y)).sub ((hasDerivAt_E2 t).const_mul (Q2 x y))
  have e : -(1/8) * (gS x y t - 20) - 3/4 * rS x y t
      = 2 * Q1 x y * (-(1/2) * E1 t) - Q2 x y * (-(1/4) * E2 t) := by
    simp only [gS, rS]; ring
  rw [e]
  exact h

/-- Gap ceiling: `4 (a u − b u²) ≤ K` on `(0, 1]` from its value at `u = 1` and the vertex. -/
theorem gap_hi_aux (a b u K : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (h1 : 2 * a ≤ K) (h2 : 4 * (a - b) ≤ K) : 4 * (a * u - b * (u * u)) ≤ K := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  have hid : 4 * (a * u - b * (u * u)) = u * (4 * (a - b)) + 4 * b * (u * (1 - u)) := by ring
  rcases le_or_gt b 0 with hb0 | hb0
  · have e1 : 4 * b * (u * (1 - u)) ≤ 0 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -(4 * b)) huu; linarith
    rcases le_or_gt (4 * (a - b)) 0 with hn | hn
    · have : u * (4 * (a - b)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0.le hn
      linarith
    · have : u * (4 * (a - b)) ≤ 4 * (a - b) := by
        have := mul_le_mul_of_nonneg_right hu1 hn.le; linarith
      linarith
  · rcases le_or_gt a (2 * b) with hab2 | hab2
    · rcases le_or_gt a 0 with ha0 | ha0
      · have e1 : a * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hu0.le
        have e2 : 0 ≤ b * (u * u) := by positivity
        linarith
      · have e1 : 2 * a * (u * u) ≤ 4 * b * (u * u) := by
          have := mul_le_mul_of_nonneg_right (by linarith : 2 * a ≤ 4 * b)
            (by positivity : (0:ℝ) ≤ u * u)
          linarith
        have e2 : u * (2 - u) ≤ 1 := by nlinarith [sq_nonneg (1 - u)]
        have e3 : 2 * a * (u * (2 - u)) ≤ 2 * a := by
          have := mul_le_mul_of_nonneg_left e2 (by linarith : (0:ℝ) ≤ 2 * a); linarith
        nlinarith
    · have hid2 : 4 * (a * u - b * (u * u)) - 4 * (a - b) =
          4 * ((u - 1) * (a - b * (u + 1))) := by
        ring
      have hx : 0 ≤ a - b * (u + 1) := by
        have : b * (u + 1) ≤ b * 2 := by
          have := mul_le_mul_of_nonneg_left (by linarith : u + 1 ≤ 2) hb0.le; linarith
        linarith
      have : (u - 1) * (a - b * (u + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
      linarith

/-- **Gap floor**: `4 (a u − b u²) ≥ −20` on `(0, 1]` when it holds at `u = 1` (the gap
`≥ 0`) and `a ≥ −10` (the projected stop gap `≥ 0`). At an interior minimum (`2b < a < 0`)
the value is `−a²/(−b) ≥ 10 a/(−b) > −20`. -/
theorem gap_lo_aux (a b u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (h1 : -10 ≤ a)
    (h2 : -20 ≤ 4 * (a - b)) : -20 ≤ 4 * (a * u - b * (u * u)) := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  rcases le_or_gt 0 b with hb0 | hb0
  · -- concave in `u`: above the chord `u ↦ 4 (a − b) u`
    have hid : 4 * (a * u - b * (u * u)) = u * (4 * (a - b)) + 4 * b * (u * (1 - u)) := by
      ring
    have e1 : 0 ≤ 4 * b * (u * (1 - u)) := by positivity
    rcases le_or_gt 0 (4 * (a - b)) with hn | hn
    · have : 0 ≤ u * (4 * (a - b)) := mul_nonneg hu0.le hn
      linarith
    · have : 4 * (a - b) ≤ u * (4 * (a - b)) := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -(4 * (a - b)))
        linarith
      linarith
  · rcases le_or_gt 0 a with ha0 | ha0
    · have e1 : 0 ≤ a * u := mul_nonneg ha0 hu0.le
      have e2 : b * (u * u) ≤ 0 := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ -b) (by positivity : (0:ℝ) ≤ u * u)
        linarith
      linarith
    · rcases le_or_gt a (2 * b) with hab | hab
      · -- decreasing on `[0, 1]`: above the value at `u = 1`
        have hid : 4 * (a * u - b * (u * u)) - 4 * (a - b) =
            4 * ((u - 1) * (a - b * (u + 1))) := by
          ring
        have hx : a - b * (u + 1) ≤ 0 := by
          have : b * 2 ≤ b * (u + 1) := by
            have := mul_le_mul_of_nonneg_left (by linarith : u + 1 ≤ 2)
              (by linarith : (0:ℝ) ≤ -b)
            linarith
          linarith
        have : 0 ≤ (u - 1) * (a - b * (u + 1)) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) hx
        linarith
      · -- completing the square: `(−b) · 4 (a u − b u²) = (2 b u − a)² − a² ≥ 10 a > 20 b`
        have hsq : 0 ≤ (2 * b * u - a) ^ 2 := sq_nonneg _
        have e1 : a * a ≤ -10 * a := by nlinarith
        have e2 : 20 * b ≤ -b * (4 * (a * u - b * (u * u))) := by nlinarith
        by_contra hc
        have := mul_lt_mul_of_pos_left (not_le.mp hc) (by linarith : (0:ℝ) < -b)
        linarith

/-- Rate ceiling `2 b u² − a u ≤ 10` on `(0, 1]`. -/
theorem rate_hi_aux (a b u y : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hy : y = 2 * b - a)
    (hy1 : y ≤ 10) (ha : -10 ≤ a) : 2 * b * (u * u) - a * u ≤ 10 := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  rcases le_or_gt 0 b with hb0 | hb0
  · -- convex in `u`: below the chord `u ↦ u y`
    have hid : 2 * b * (u * u) - a * u = u * y - 2 * b * (u * (1 - u)) := by rw [hy]; ring
    have e1 : 0 ≤ 2 * b * (u * (1 - u)) := by positivity
    rcases le_or_gt y 0 with hy0 | hy0
    · have : u * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0.le hy0
      linarith
    · have : u * y ≤ y := by have := mul_le_mul_of_nonneg_right hu1 hy0.le; linarith
      linarith
  · have e1 : 2 * b * (u * u) ≤ 0 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -(2 * b)) (by positivity : (0:ℝ) ≤ u * u)
      linarith
    rcases le_or_gt 0 a with ha0 | ha0
    · have : 0 ≤ a * u := mul_nonneg ha0 hu0.le
      linarith
    · have : -(a * u) ≤ -a := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -a); linarith
      linarith

/-- Rate floor `2 b u² − a u ≥ −10` on `(0, 1]`. -/
theorem rate_lo_aux (a b u y : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hy : y = 2 * b - a)
    (hy0 : -10 ≤ y) (ha : a ≤ 20) : -10 ≤ 2 * b * (u * u) - a * u := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  rcases le_or_gt b 0 with hb0 | hb0
  · -- concave in `u`: above the chord
    have hid : 2 * b * (u * u) - a * u = u * y - 2 * b * (u * (1 - u)) := by rw [hy]; ring
    have e1 : 2 * b * (u * (1 - u)) ≤ 0 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -(2 * b)) huu; linarith
    rcases le_or_gt 0 y with hy0' | hy0'
    · have : 0 ≤ u * y := mul_nonneg hu0.le hy0'
      linarith
    · have : y ≤ u * y := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -y); linarith
      linarith
  · rcases le_or_gt a (4 * b) with ha4 | ha4
    · -- completing the square: `≥ −a² / (8 b) ≥ −a / 2 ≥ −10`
      rcases le_or_gt a 0 with ha0 | ha0
      · have e1 : 0 ≤ 2 * b * (u * u) := by positivity
        have e2 : a * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hu0.le
        linarith
      · have hsq : 0 ≤ (4 * b * u - a) ^ 2 := sq_nonneg _
        have hkey : 8 * b * (2 * b * (u * u) - a * u) = (4 * b * u - a) ^ 2 - a * a := by ring
        have e1 : a * a ≤ 4 * b * a := by
          have := mul_le_mul_of_nonneg_right ha4 ha0.le; linarith
        have e2 : -(4 * b * a) ≤ 8 * b * (2 * b * (u * u) - a * u) := by nlinarith
        have e3 : -(a / 2) ≤ 2 * b * (u * u) - a * u := by
          by_contra hc
          have := mul_lt_mul_of_pos_left (not_le.mp hc) (by linarith : (0:ℝ) < 8 * b)
          nlinarith
        linarith
    · -- decreasing on `[0, 1]`: above the value at `u = 1`
      have hid : 2 * b * (u * u) - a * u - y = (u - 1) * (2 * b * (u + 1) - a) := by
        rw [hy]; ring
      have hx : 2 * b * (u + 1) - a ≤ 0 := by
        have : b * (u + 1) ≤ b * 2 := by
          have := mul_le_mul_of_nonneg_left (by linarith : u + 1 ≤ 2) hb0.le; linarith
        linarith
      have : 0 ≤ (u - 1) * (2 * b * (u + 1) - a) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hx
      linarith

/-- **The CACC solution stays in the evolve box for all time** from every box state whose
projected stop gap `x + 2y` lies in `[0, 60]`. -/
theorem cacc_box (x y t : ℝ) (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x ≤ 60) (hy0 : -10 ≤ y)
    (hy1 : y ≤ 10) (hw0 : 0 ≤ x + 2 * y) (hw1 : x + 2 * y ≤ 60) :
    (0 ≤ gS x y t ∧ gS x y t ≤ 60) ∧ (-10 ≤ rS x y t ∧ rS x y t ≤ 10) := by
  have hu0 : 0 < E2 t := E2_pos t
  have hu1 : E2 t ≤ 1 := E2_le t ht
  have hyab : y = 2 * Q1 x y - Q2 x y := by simp only [Q1, Q2]; ring
  have hg : gS x y t = 20 + 4 * (Q2 x y * E2 t - Q1 x y * (E2 t * E2 t)) := by
    unfold gS; rw [E1_sq]
  have hr : rS x y t = 2 * Q1 x y * (E2 t * E2 t) - Q2 x y * E2 t := by
    unfold rS; rw [E1_sq]
  have hQ2a : -10 ≤ Q2 x y := by simp only [Q2]; linarith
  have hQ2b : Q2 x y ≤ 20 := by simp only [Q2]; linarith
  have hd0 : -20 ≤ 4 * (Q2 x y - Q1 x y) := by simp only [Q1, Q2]; linarith
  have hd1 : 4 * (Q2 x y - Q1 x y) ≤ 40 := by simp only [Q1, Q2]; linarith
  rw [hg, hr]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have := gap_lo_aux (Q2 x y) (Q1 x y) (E2 t) hu0 hu1 hQ2a hd0
    linarith
  · have := gap_hi_aux (Q2 x y) (Q1 x y) (E2 t) 40 hu0 hu1 (by norm_num) (by linarith) hd1
    linarith
  · exact rate_lo_aux _ _ _ y hu0 hu1 hyab hy0 hQ2b
  · exact rate_hi_aux _ _ _ y hu0 hu1 hyab hy1 hQ2a

/-! ### AEB: the speed-matching solution -/

/-- The AEB solution from `(g₀, r₀) = (x, y)`: gap `x + 2y (1 − e^{−t/2})`. -/
noncomputable def bG (x y t : ℝ) : ℝ := x + 2 * y * (1 - E1 t)

/-- The AEB solution from `(g₀, r₀) = (x, y)`: range rate `y e^{−t/2}`. -/
noncomputable def bR (y t : ℝ) : ℝ := y * E1 t

theorem bG_zero (x y : ℝ) : bG x y 0 = x := by simp [bG, E1_zero]

theorem bR_zero (y : ℝ) : bR y 0 = y := by simp [bR, E1_zero]

theorem bG_hasDeriv (x y t : ℝ) : HasDerivAt (bG x y) (bR y t) t :=
  ((((hasDerivAt_E1 t).const_sub 1).const_mul (2 * y)).const_add x).congr_deriv
    (by simp only [bR]; ring)

theorem bR_hasDeriv (y t : ℝ) : HasDerivAt (bR y) (-(1/2) * bR y t) t :=
  ((hasDerivAt_E1 t).const_mul y).congr_deriv (by simp only [bR]; ring)

/-- **The AEB solution stays in the evolve box for all time** from every box state whose
projected stop gap lies in `[0, 60]` (`g` moves from `x` toward `x + 2y`, `|r|` decays). -/
theorem aeb_box (x y t : ℝ) (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x ≤ 60) (hy0 : -10 ≤ y)
    (hy1 : y ≤ 10) (hw0 : 0 ≤ x + 2 * y) (hw1 : x + 2 * y ≤ 60) :
    (0 ≤ bG x y t ∧ bG x y t ≤ 60) ∧ (-10 ≤ bR y t ∧ bR y t ≤ 10) := by
  have he0 : 0 < E1 t := E1_pos t
  have he1 : E1 t ≤ 1 := E1_le t ht
  simp only [bG, bR]
  rcases le_total y 0 with hy | hy
  · refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-! ### The explicit run of the right block -/

/-- The link trajectory: gap `jx` along `G`, rate `jy` along `R`, every other right
coordinate frozen at the start. -/
noncomputable def linkSol (G R : ℝ → ℝ) (x : State (Var n)) (jx jy : Fin n) :
    Fin n → ℝ → ℝ :=
  fun i => if i = jx then G else if i = jy then R else fun _ => x (Rv i)

theorem linkSol_x (G R : ℝ → ℝ) (x : State (Var n)) (jx jy : Fin n) :
    linkSol G R x jx jy jx = G := by simp [linkSol]

theorem linkSol_y (G R : ℝ → ℝ) (x : State (Var n)) {jx jy : Fin n} (hxy : jx ≠ jy) :
    linkSol G R x jx jy jy = R := by simp [linkSol, Ne.symm hxy]

theorem linkSol_o (G R : ℝ → ℝ) (x : State (Var n)) {jx jy i : Fin n} (h1 : i ≠ jx)
    (h2 : i ≠ jy) : linkSol G R x jx jy i = fun _ => x (Rv i) := by simp [linkSol, h1, h2]

/-- **An explicit link run**: if `G`, `R` start at the state's gap and rate, solve
`G' = R`, `R' = F(G, R)` (the link's fields), every other right field vanishes, and the
trajectory stays in the box, it solves the right block over the domain. -/
theorem link_sol {fR : Fin n → Term (Var n)} {dom : Formula (Var n)} (x : State (Var n))
    {jx jy : Fin n} (hxy : jx ≠ jy) (G R : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hfx : ∀ z, Term.eval (fR jx) z = z (Rv jy))
    (hfy : ∀ z, Term.eval (fR jy) z = F (z (Rv jx)) (z (Rv jy)))
    (hfo : ∀ i, i ≠ jx → i ≠ jy → ∀ z, Term.eval (fR i) z = 0)
    (hdom : ∀ z, Box z jx jy → Formula.sat dom z)
    (hG0 : G 0 = x (Rv jx)) (hR0 : R 0 = x (Rv jy))
    (hG : ∀ t, HasDerivAt G (R t) t) (hR : ∀ t, HasDerivAt R (F (G t) (R t)) t)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hbox : ∀ t, 0 ≤ t → t ≤ τ → (0 ≤ G t ∧ G t ≤ 60) ∧ (-10 ≤ R t ∧ R t ≤ 10)) :
    ODESol (rightBlock fR (Term.const 1)) dom x τ (trajRs x (linkSol G R x jx jy)) := by
  refine trajRs_sol x (linkSol G R x jx jy) τ hτ ?_ ?_ ?_
  · intro i
    by_cases h1 : i = jx
    · rw [h1, linkSol_x, hG0]
    · by_cases h2 : i = jy
      · rw [h2, linkSol_y G R x hxy, hR0]
      · simp only [linkSol_o G R x h1 h2]
  · intro i t _ _
    by_cases h1 : i = jx
    · rw [h1, hfx, trajRs_R, linkSol_x, linkSol_y G R x hxy]
      exact hG t
    · by_cases h2 : i = jy
      · rw [h2, hfy, trajRs_R, trajRs_R, linkSol_x, linkSol_y G R x hxy]
        exact hR t
      · rw [hfo i h1 h2, linkSol_o G R x h1 h2]
        exact hasDerivAt_const t _
  · intro t ht hte
    apply hdom
    obtain ⟨⟨g0, g1⟩, r0, r1⟩ := hbox t ht hte
    simp only [Box, trajRs_R, linkSol_x, linkSol_y G R x hxy]
    exact ⟨g0, g1, r0, r1⟩

/-- **Existence along CACC** (clause (i)): from every box state with projected stop gap in
`[0, 60]` (the CACC guard has `[5, 60]`), a run of every duration exists. -/
theorem cacc_exists {fR : Fin n → Term (Var n)} {dom : Formula (Var n)} {jx jy : Fin n}
    (hxy : jx ≠ jy) (hF : CaccField fR jx jy) (hdom : ∀ z, Box z jx jy → Formula.sat dom z)
    (x : State (Var n)) (hb : Box x jx jy) (hw0 : 0 ≤ x (Rv jx) + 2 * x (Rv jy))
    (hw1 : x (Rv jx) + 2 * x (Rv jy) ≤ 60) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) dom x τ Φ := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hb
  exact ⟨_, link_sol x hxy (gS (x (Rv jx)) (x (Rv jy))) (rS (x (Rv jx)) (x (Rv jy)))
    (fun g r => -(1/8) * (g - 20) - 3/4 * r) hF.1 hF.2.1 hF.2.2 hdom (gS_zero _ _)
    (rS_zero _ _) (gS_hasDeriv _ _) (rS_hasDeriv _ _) τ hτ
    (fun t ht _ => cacc_box _ _ t ht hx0 hx1 hy0 hy1 hw0 hw1)⟩

/-- **Existence along AEB** (clause (i)): from every box state with projected stop gap in
`[0, 60]` (the AEB guard has `[0, 5)`), a run of every duration exists. -/
theorem aeb_exists {fR : Fin n → Term (Var n)} {dom : Formula (Var n)} {jx jy : Fin n}
    (hxy : jx ≠ jy) (hF : AebField fR jx jy) (hdom : ∀ z, Box z jx jy → Formula.sat dom z)
    (x : State (Var n)) (hb : Box x jx jy) (hw0 : 0 ≤ x (Rv jx) + 2 * x (Rv jy))
    (hw1 : x (Rv jx) + 2 * x (Rv jy) ≤ 60) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) dom x τ Φ := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hb
  exact ⟨_, link_sol x hxy (bG (x (Rv jx)) (x (Rv jy))) (bR (x (Rv jy)))
    (fun _ r => -(1/2) * r) hF.1 hF.2.1 hF.2.2 hdom (bG_zero _ _) (bR_zero _)
    (bG_hasDeriv _ _) (bR_hasDeriv _) τ hτ
    (fun t ht _ => aeb_box _ _ t ht hx0 hx1 hy0 hy1 hw0 hw1)⟩

end PlatoonCaccAeb
end RelCertifier
