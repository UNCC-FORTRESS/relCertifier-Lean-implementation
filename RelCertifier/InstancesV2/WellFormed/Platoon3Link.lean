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

Self-contained: the link shape (`LinkField`, `pgGe`), the explicit link solution and its box
(`E1`, `E2`, `gS`, `rS`, `link_bounds`) and the guard barrier along the reference's own flow
(`gap_floor_Ronly`) live here (moved from the Theorem 3 leaf `Modal/Platoon3Link`, which
imports this file).
-/
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace Platoon3Link

open DL DLCalTiming DLRel Set

/-! ## One link: the shape and the projected-gap atom -/

/-- The damped link on side `W` at coordinates `jx` (gap), `jy` (closing rate). -/
def LinkField (W : Fin 6 → Var 6) (f : Fin 6 → Term (Var 6)) (jx jy : Fin 6) (c : ℝ) :
    Prop :=
  (∀ z, Term.eval (f jx) z = z (W jy)) ∧
  (∀ z, Term.eval (f jy) z = -(1/8) * (z (W jx) - c) - 3/4 * z (W jy))

/-- The narrowing formula of a term (`t ≤ 0`). -/
def leF (t : Term (Var 6)) : Formula (Var 6) := Formula.cmp CompOp.le t (Term.const 0)

theorem sat_leF (t : Term (Var 6)) (z : State (Var 6)) :
    Formula.sat (leF t) z ↔ Term.eval t z ≤ 0 := by
  simp [leF, Formula.sat, CompOp.interp, Term.eval]

theorem hroot2 : (1/2 : ℝ) * (1/2) - 3/4 * (1/2) + 1/8 = 0 := by norm_num

/-- Safe-side term of `x + 2y ≥ P`. -/
def pgGe (wx wy : Var 6) (P : ℝ) : Term (Var 6) :=
  Term.binop .sub (Term.const P)
    (Term.binop .add (Term.var wx) (Term.binop .mul (Term.const 2) (Term.var wy)))

theorem eval_pgGe (wx wy : Var 6) (P c : ℝ) (z : State (Var 6)) :
    Term.eval (pgGe wx wy P) z = 2 * Term.eval (linGe wx wy (1/2) c ((P - c)/2)) z := by
  simp only [pgGe, linGe, eval_linQ, Term.eval, AOp.interp]; ring

/-! ## The explicit link solution and its box -/

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

theorem E2_pos (t : ℝ) : 0 < E2 t := Real.exp_pos _

theorem E2_le (t : ℝ) (ht : 0 ≤ t) : E2 t ≤ 1 := by
  unfold E2; rw [Real.exp_le_one_iff]; linarith

theorem E1_zero : E1 0 = 1 := by simp [E1]

theorem E2_zero : E2 0 = 1 := by simp [E2]

theorem E1_sq (t : ℝ) : E1 t = E2 t * E2 t := by
  unfold E1 E2; rw [← Real.exp_add]; ring_nf

/-- The two modal coordinates of a link at set point `c`. -/
noncomputable def Q1 (c x y : ℝ) : ℝ := y + 1/4 * (x - c)

noncomputable def Q2 (c x y : ℝ) : ℝ := y + 1/2 * (x - c)

/-- The explicit link solution. -/
noncomputable def gS (c x y t : ℝ) : ℝ := c + 4 * (Q2 c x y * E2 t - Q1 c x y * E1 t)

noncomputable def rS (c x y t : ℝ) : ℝ := 2 * Q1 c x y * E1 t - Q2 c x y * E2 t

theorem gS_zero (c x y : ℝ) : gS c x y 0 = x := by
  simp only [gS, Q1, Q2, E1_zero, E2_zero]; ring

theorem rS_zero (c x y : ℝ) : rS c x y 0 = y := by
  simp only [rS, Q1, Q2, E1_zero, E2_zero]; ring

theorem gS_hasDeriv (c x y t : ℝ) : HasDerivAt (fun u => gS c x y u) (rS c x y t) t := by
  have h : HasDerivAt (fun u => c + 4 * (Q2 c x y * E2 u - Q1 c x y * E1 u))
      (4 * (Q2 c x y * (-(1/4) * E2 t) - Q1 c x y * (-(1/2) * E1 t))) t :=
    ((((hasDerivAt_E2 t).const_mul (Q2 c x y)).sub
      ((hasDerivAt_E1 t).const_mul (Q1 c x y))).const_mul 4).const_add c
  have e : rS c x y t = 4 * (Q2 c x y * (-(1/4) * E2 t) - Q1 c x y * (-(1/2) * E1 t)) := by
    simp only [rS]; ring
  rw [e]
  exact h

theorem rS_hasDeriv (c x y t : ℝ) : HasDerivAt (fun u => rS c x y u)
    (-(1/8) * (gS c x y t - c) - 3/4 * rS c x y t) t := by
  have h : HasDerivAt (fun u => 2 * Q1 c x y * E1 u - Q2 c x y * E2 u)
      (2 * Q1 c x y * (-(1/2) * E1 t) - Q2 c x y * (-(1/4) * E2 t)) t :=
    ((hasDerivAt_E1 t).const_mul (2 * Q1 c x y)).sub ((hasDerivAt_E2 t).const_mul (Q2 c x y))
  have e : -(1/8) * (gS c x y t - c) - 3/4 * rS c x y t
      = 2 * Q1 c x y * (-(1/2) * E1 t) - Q2 c x y * (-(1/4) * E2 t) := by
    simp only [gS, rS]; ring
  rw [e]
  exact h

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
          have := mul_le_mul_of_nonneg_right (by linarith : 2 * a ≤ 4 * b) (by positivity : (0:ℝ) ≤ u * u)
          linarith
        have e2 : u * (2 - u) ≤ 1 := by nlinarith [sq_nonneg (1 - u)]
        have e3 : 2 * a * (u * (2 - u)) ≤ 2 * a := by
          have := mul_le_mul_of_nonneg_left e2 (by linarith : (0:ℝ) ≤ 2 * a); linarith
        nlinarith
    · have hid2 : 4 * (a * u - b * (u * u)) - 4 * (a - b) = 4 * ((u - 1) * (a - b * (u + 1))) := by
        ring
      have hx : 0 ≤ a - b * (u + 1) := by
        have : b * (u + 1) ≤ b * 2 := by
          have := mul_le_mul_of_nonneg_left (by linarith : u + 1 ≤ 2) hb0.le; linarith
        linarith
      have : (u - 1) * (a - b * (u + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
      linarith

theorem gap_lo_aux (a b u K : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (h1 : -K ≤ 4 * a) (h2 : -K ≤ 4 * (a - b)) : -K ≤ 4 * (a * u - b * (u * u)) := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  have hid : 4 * (a * u - b * (u * u)) = u * (4 * (a - b)) + 4 * b * (u * (1 - u)) := by ring
  rcases le_or_gt 0 b with hb0 | hb0
  · have e1 : 0 ≤ 4 * b * (u * (1 - u)) := by positivity
    rcases le_or_gt 0 (4 * (a - b)) with hn | hn
    · have : 0 ≤ u * (4 * (a - b)) := mul_nonneg hu0.le hn
      linarith
    · have : 4 * (a - b) ≤ u * (4 * (a - b)) := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -(4 * (a - b))); linarith
      linarith
  · have e1 : 0 ≤ -(b * (u * u)) := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -b) (by positivity : (0:ℝ) ≤ u * u); linarith
    rcases le_or_gt 0 a with ha0 | ha0
    · have : 0 ≤ a * u := mul_nonneg ha0 hu0.le
      linarith
    · have : a ≤ a * u := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -a); linarith
      linarith

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
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -(2 * b)) (by positivity : (0:ℝ) ≤ u * u); linarith
    rcases le_or_gt 0 a with ha0 | ha0
    · have : 0 ≤ a * u := mul_nonneg ha0 hu0.le
      linarith
    · have : -(a * u) ≤ -a := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -a); linarith
      linarith

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
        -- `8 b (2 b u² − a u) = (4 b u − a)² − a²  ≥ −a² ≥ −4 b a`
        have hkey : 8 * b * (2 * b * (u * u) - a * u) = (4 * b * u - a) ^ 2 - a * a := by ring
        have e1 : a * a ≤ 4 * b * a := by
          have := mul_le_mul_of_nonneg_right ha4 ha0.le; linarith
        have e2 : -(4 * b * a) ≤ 8 * b * (2 * b * (u * u) - a * u) := by nlinarith
        -- divide by `8 b > 0`
        have e3 : -(a / 2) ≤ 2 * b * (u * u) - a * u := by
          by_contra hc
          push_neg at hc
          have := mul_lt_mul_of_pos_left hc (by linarith : (0:ℝ) < 8 * b)
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

/-- **The link stays in the evolve box** (`0 ≤ x ≤ 60`, `|y| ≤ 10`) for all time when it
starts there with the slow form `Q2 = y + (x − c)/2` in `[−K, (60 − c)/2]` (the
projected-gap guard; `4 K ≤ c`, `K ≤ 10`). `u = e^{−t/4}`: `x − c = 4 (Q2 u − Q1 u²)`, `y = 2 Q1 u² − Q2 u`. -/
theorem link_bounds (c K x y t : ℝ) (ht : 0 ≤ t) (hc1 : 20 ≤ c) (hc2 : c ≤ 60)
    (hK1 : 4 * K ≤ c) (hK2 : K ≤ 10)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 60) (hy0 : -10 ≤ y) (hy1 : y ≤ 10)
    (hq0 : -K ≤ Q2 c x y) (hq1 : 2 * Q2 c x y ≤ 60 - c) :
    (0 ≤ gS c x y t ∧ gS c x y t ≤ 60) ∧ (-10 ≤ rS c x y t ∧ rS c x y t ≤ 10) := by
  have hu0 : 0 < E2 t := E2_pos t
  have hu1 : E2 t ≤ 1 := E2_le t ht
  have hab : 4 * (Q2 c x y - Q1 c x y) = x - c := by simp only [Q1, Q2]; ring
  have hyab : y = 2 * Q1 c x y - Q2 c x y := by simp only [Q1, Q2]; ring
  have hg : gS c x y t = c + 4 * (Q2 c x y * E2 t - Q1 c x y * (E2 t * E2 t)) := by
    unfold gS; rw [E1_sq]
  have hr : rS c x y t = 2 * Q1 c x y * (E2 t * E2 t) - Q2 c x y * E2 t := by
    unfold rS; rw [E1_sq]
  rw [hg, hr]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have := gap_lo_aux (Q2 c x y) (Q1 c x y) (E2 t) c hu0 hu1 (by linarith) (by linarith)
      (by linarith)
    linarith
  · have := gap_hi_aux (Q2 c x y) (Q1 c x y) (E2 t) (60 - c) hu0 hu1 (by linarith) hq1
      (by linarith)
    linarith
  · exact rate_lo_aux _ _ _ y hu0 hu1 hyab hy0 (by linarith)
  · exact rate_hi_aux _ _ _ y hu0 hu1 hyab hy1 (by linarith)

/-! ## The guard barrier along the reference's own flow -/

/-- **The AEB floor repels.** Along a run of the reference's own flow (a link at set point
`c`), a gap that starts at `x ≥ G` with `x + 2y ≥ P` (`G ≤ P ≤ c`) stays at `x ≥ G`: the slow
form `y + (x − c)/2 ≥ (P − c)/2` only decays toward `0`, and on it `x' = y ≥ (G − x)/2 + …`
points away from the floor. -/
theorem gap_floor_Ronly (fR : Fin 6 → Term (Var 6)) (dom : Formula (Var 6)) (jx jy : Fin 6)
    (c G P : ℝ) (hGP : G ≤ P) (hPc : P ≤ c) (hF : LinkField Rv fR jx jy c)
    {ν μ : State (Var 6)}
    (hrun : Program.sem (Program.ode (rightBlock fR (Term.const 1)) dom) ν μ)
    (hP : Term.eval (pgGe (Rv jx) (Rv jy) P) ν ≤ 0) (hG : G ≤ ν (Rv jx)) :
    G ≤ μ (Rv jx) := by
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  have hq : Term.eval (linGe (Rv jx) (Rv jy) (1/2) c ((P - c)/2)) ν ≤ 0 := by
    have := (eval_pgGe (Rv jx) (Rv jy) P c ν) ▸ hP
    linarith
  have hx : Term.eval (thrGe (Rv jx) G) ν ≤ 0 := by
    simp only [thrGe, Term.eval, AOp.interp]; linarith
  have hbox := stay_given (sys := rightBlock fR (Term.const 1)) (dom := dom)
    (Fq := leF (linGe (Rv jx) (Rv jy) (1/2) c ((P - c)/2))) (fun z => sat_leF _ z)
    (fun ν' h' => boxle_Ronly_of_super _ fR 1 zero_le_one dom dom
      (fun i hi => by simp [linGe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_linear_ge_R (a := 1/8) (b := 3/4) hroot2 hs2 (by linarith) fR dom
        (fun z _ => hF.1 z) (fun z _ => hF.2 z)) h')
    (fun ν' h' => boxle_Ronly_of_super _ fR 1 zero_le_one _ _
      (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_ge_R (r := 1/2) (by norm_num) (by linarith) fR
        (Formula.and dom (leF (linGe (Rv jx) (Rv jy) (1/2) c ((P - c)/2))))
        (fun z _ => hF.1 z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq hx
  have := hbox μ hrun
  simp only [thrGe, Term.eval, AOp.interp] at this
  linarith

/-! ## The operating range along the reference's own flow -/

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
