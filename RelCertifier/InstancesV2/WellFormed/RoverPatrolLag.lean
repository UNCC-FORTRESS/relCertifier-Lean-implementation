/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_lag`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG`, the lowered right guards, `ε_r = 1`. The nominal
rover's zones run the lagged loop `v' = a`, `s' = v`, `a' = (16/3) ((c − v) − a)`
(`c` = the zone command 0.6, 0.9, 1.1, 1.5). The characteristic polynomial
`s² + (16/3) s + 16/3 = (s + 4/3)(s + 4)` gives the two decaying modal coordinates
`p − 4c` and `r − 4c` with `p = 3a + 4v` (rate 4) and `r = a + 4v` (rate 4/3).
Every right guard is the zone's odometer band intersected with the operating envelope
`p ∈ [−0.3, 7.5]`, `r ∈ [0.7, 6.5]` and the box `v ∈ [0, 2]`, `a ∈ [−2, 2]`.
* Envelope: each of `p`, `r` is a convex combination of its start and `4c`, and `4c` lies
  in both bands for every zone, so the envelope is kept (`modal_exact`).
* Box: in the explicit run (`x = e^{−4t/3}`, `e^{−4t} = x³`)
  `v = c (1 − x³) + v₀ x³ + (3/8) (r₀ − 4c) x (1 − x²)` and
  `a = a₀ x³ − ((r₀ − 4c)/2) x (1 − x²)`, bounded by `box_bounds`.
* Odometer: `0 ≤ s' = v ≤ 2`, so over one interval `s` grows by at most `2`.
* `SLOW` (`0 ≤ s < 20`): ends in `SLOW` or `MEDIUM_BRISK`; `MEDIUM_ECO` / `MEDIUM_BRISK`
  (`20 ≤ s < 50`): end in the zone itself or `FAST`; `FAST` (`s ≥ 50`): ends in `FAST`.
Existence: the explicit zone runs (`trajRs_sol`). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_patrol_lag
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolLag

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle


def vs : List String := ["v", "s", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := rover_patrol_lag_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp16_0 : Run.parseRat "16.0" = some ((16 : ℚ)) := by
  have h : parseQ "16.0" = some (⟨160, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp3_0 : Run.parseRat "3.0" = some ((3 : ℚ)) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp4_0 : Run.parseRat "4.0" = some ((4 : ℚ)) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_7 : Run.parseRat "0.7" = some ((7/10 : ℚ)) := by
  have h : parseQ "0.7" = some (⟨7, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp6_5 : Run.parseRat "6.5" = some ((13/2 : ℚ)) := by
  have h : parseQ "6.5" = some (⟨65, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp7_5 : Run.parseRat "7.5" = some ((15/2 : ℚ)) := by
  have h : parseQ "7.5" = some (⟨75, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_6 : Run.parseRat "0.6" = some ((3/5 : ℚ)) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_9 : Run.parseRat "0.9" = some ((9/10 : ℚ)) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_1 : Run.parseRat "1.1" = some ((11/10 : ℚ)) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_5 : Run.parseRat "1.5" = some ((3/2 : ℚ)) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm2_0 : Run.parseRat "-2.0" = some ((-2 : ℚ)) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp2_0 : Run.parseRat "2.0" = some ((2 : ℚ)) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_0 : Run.parseRat "0.0" = some ((0 : ℚ)) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp20_0 : Run.parseRat "20.0" = some ((20 : ℚ)) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp50_0 : Run.parseRat "50.0" = some ((50 : ℚ)) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_3 : Run.parseRat "0.3" = some ((3/10 : ℚ)) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_0 : Run.parseRat "1.0" = some ((1 : ℚ)) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

def loQ : ℕ → ℚ
  | 0 => 0 | 1 => 20 | 2 => 20 | _ => 50
def capQ : ℕ → ℚ
  | 0 => 3/5 | 1 => 9/10 | 2 => 11/10 | _ => 3/2
noncomputable def loL (l : ℕ) : ℝ := (loQ l : ℝ)
noncomputable def capL (l : ℕ) : ℝ := (capQ l : ℝ)
theorem cap_bounds (l : ℕ) (hl : l < 4) : 3/5 ≤ capL l ∧ capL l ≤ 3/2 := by
  interval_cases l <;> norm_num [capL, capQ]

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = x (Rv 2) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp16_0, hp3_0,
      hp0_6, hp0_9, hp1_1, hp1_5, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp16_0, hp3_0,
      hp0_6, hp0_9, hp1_1, hp1_5, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 16/3 * ((capL q - x (Rv 0)) - x (Rv 2)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp16_0, hp3_0,
      hp0_6, hp0_9, hp1_1, hp1_5, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, capL, capQ]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 2 ∧ 0 ≤ x (Rv 1) ∧ -2 ≤ x (Rv 2) ∧
      x (Rv 2) ≤ 2) := by
  simp only [domR, hostEvolve, mR, rover_patrol_lag_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm2_0, hp2_0, hp0_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared transitions, as indices (`SLOW` 0, `MEDIUM_ECO` 1, `MEDIUM_BRISK` 2,
`FAST` 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 0), (1, 3), (1, 1), (2, 3), (2, 2), (3, 3)]

/-! ## The operating envelope and the box, along the explicit run -/

/-- The box `v ∈ [0, 2]`, `a ∈ [−2, 2]` and the envelope `3a + 4v ∈ [−0.3, 7.5]`,
`a + 4v ∈ [0.7, 6.5]` (the right guards without the odometer band). -/
def boxEnv (v a : ℝ) : Prop :=
  0 ≤ v ∧ v ≤ 2 ∧ -2 ≤ a ∧ a ≤ 2 ∧ -3/10 ≤ 3 * a + 4 * v ∧ 3 * a + 4 * v ≤ 15/2 ∧
    7/10 ≤ a + 4 * v ∧ a + 4 * v ≤ 13/2

/-- **The box along the explicit run**, with `x = e^{−4t/3} ∈ [0, 1]` and `e^{−4t} = x³`:
the speed and the acceleration stay in the box for every zone command `c ∈ [0.6, 1.5]`. -/
theorem box_bounds (c v₀ a₀ x : ℝ) (hc0 : 3/5 ≤ c) (hc1 : c ≤ 3/2) (h : boxEnv v₀ a₀)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ c + (3 * (a₀ + 4 * v₀ - 4 * c) * x - (3 * a₀ + 4 * v₀ - 4 * c) * x ^ 3) / 8 ∧
      c + (3 * (a₀ + 4 * v₀ - 4 * c) * x - (3 * a₀ + 4 * v₀ - 4 * c) * x ^ 3) / 8 ≤ 2 ∧
      -2 ≤ ((3 * a₀ + 4 * v₀ - 4 * c) * x ^ 3 - (a₀ + 4 * v₀ - 4 * c) * x) / 2 ∧
      ((3 * a₀ + 4 * v₀ - 4 * c) * x ^ 3 - (a₀ + 4 * v₀ - 4 * c) * x) / 2 ≤ 2 := by
  obtain ⟨hv0, hv1, ha0, ha1, hp0, hp1, hr0, hr1⟩ := h
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
  have hx31 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
  have hw : 0 ≤ x * (1 - x ^ 2) := mul_nonneg hx0 (by nlinarith)
  have hq : 0 ≤ (1 - x) ^ 2 * (x + 2) := mul_nonneg (sq_nonneg _) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hv0 hx3, mul_nonneg (by linarith : (0:ℝ) ≤ a₀ + 4 * v₀ - 7/10) hw,
      mul_nonneg (by linarith : (0:ℝ) ≤ c) hq]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - v₀) hx3,
      mul_nonneg (by linarith : (0:ℝ) ≤ 13/2 - (a₀ + 4 * v₀)) hw,
      mul_nonneg (by linarith : (0:ℝ) ≤ 3/2 - c) hq]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a₀ + 2) hx3,
      mul_nonneg (by linarith : (0:ℝ) ≤ 13/2 - (a₀ + 4 * v₀)) hw,
      mul_nonneg (by linarith : (0:ℝ) ≤ c - 3/5) hw,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x)
        (by nlinarith : (0:ℝ) ≤ 2 - x / 20 - x ^ 2 / 20)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - a₀) hx3,
      mul_nonneg (by linarith : (0:ℝ) ≤ a₀ + 4 * v₀ - 7/10) hw,
      mul_nonneg (by linarith : (0:ℝ) ≤ 3/2 - c) hw,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x)
        (by nlinarith : (0:ℝ) ≤ 2 - 13 * x / 20 - 13 * x ^ 2 / 20)]

/-! ## Existence: each zone's flow, explicitly

With `P = 3a₀ + 4v₀ − 4c` and `R = a₀ + 4v₀ − 4c`: `p(t) − 4c = P e^{−4t}`,
`r(t) − 4c = R e^{−4t/3}`, hence `v = c + (3R e^{−4t/3} − P e^{−4t})/8`,
`a = (P e^{−4t} − R e^{−4t/3})/2` and `s = s₀ + c t + (9/32) R (1 − e^{−4t/3})
− (1/32) P (1 − e^{−4t})`. -/

noncomputable def ex (k t : ℝ) : ℝ := Real.exp (-(k * t))

theorem ex_hasDeriv (k t : ℝ) : HasDerivAt (ex k) (-k * ex k t) t := by
  have h := ((hasDerivAt_id t).const_mul k).neg.exp
  have h' : HasDerivAt (ex k) (Real.exp (-(k * id t)) * (-(k * 1))) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring
theorem ex_zero (k : ℝ) : ex k 0 = 1 := by simp [ex]
theorem ex_pos (k t : ℝ) : 0 < ex k t := Real.exp_pos _
theorem ex_le_one {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) : ex k t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; nlinarith
theorem ex_cube (t : ℝ) : ex 4 t = ex (4/3) t ^ 3 := by
  unfold ex; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

noncomputable def PP (c : ℝ) (b : State (Var 3)) : ℝ := 3 * b (Rv 2) + 4 * b (Rv 0) - 4 * c
noncomputable def RR (c : ℝ) (b : State (Var 3)) : ℝ := b (Rv 2) + 4 * b (Rv 0) - 4 * c

noncomputable def vF (c : ℝ) (b : State (Var 3)) (t : ℝ) : ℝ :=
  c + (3 * RR c b * ex (4/3) t - PP c b * ex 4 t) / 8
noncomputable def sF (c : ℝ) (b : State (Var 3)) (t : ℝ) : ℝ :=
  b (Rv 1) + c * t + 9/32 * RR c b * (1 - ex (4/3) t) - 1/32 * PP c b * (1 - ex 4 t)
noncomputable def aF (c : ℝ) (b : State (Var 3)) (t : ℝ) : ℝ :=
  (PP c b * ex 4 t - RR c b * ex (4/3) t) / 2

noncomputable def solφ (c : ℝ) (b : State (Var 3)) : Fin 3 → ℝ → ℝ := ![vF c b, sF c b, aF c b]

theorem vF_der (c : ℝ) (b : State (Var 3)) (t : ℝ) : HasDerivAt (vF c b) (aF c b t) t := by
  have h := (((ex_hasDeriv (4/3) t).const_mul (3 * RR c b)).sub
    ((ex_hasDeriv 4 t).const_mul (PP c b))).div_const 8 |>.const_add c
  exact h.congr_deriv (by simp only [aF]; ring)

theorem aF_der (c : ℝ) (b : State (Var 3)) (t : ℝ) :
    HasDerivAt (aF c b) (16/3 * ((c - vF c b t) - aF c b t)) t := by
  have h := (((ex_hasDeriv 4 t).const_mul (PP c b)).sub
    ((ex_hasDeriv (4/3) t).const_mul (RR c b))).div_const 2
  exact h.congr_deriv (by simp only [aF, vF]; ring)

theorem sF_der (c : ℝ) (b : State (Var 3)) (t : ℝ) : HasDerivAt (sF c b) (vF c b t) t := by
  have h := ((((hasDerivAt_id t).const_mul c).const_add (b (Rv 1))).add
    (((ex_hasDeriv (4/3) t).const_sub 1).const_mul (9/32 * RR c b))).sub
    (((ex_hasDeriv 4 t).const_sub 1).const_mul (1/32 * PP c b))
  exact h.congr_deriv (by simp only [vF, id]; ring)

theorem vF_aF_box (q : ℕ) (hq : q < 4) (b : State (Var 3)) (hb : boxEnv (b (Rv 0)) (b (Rv 2)))
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ vF (capL q) b t ∧ vF (capL q) b t ≤ 2 ∧ -2 ≤ aF (capL q) b t ∧ aF (capL q) b t ≤ 2 := by
  have hc := cap_bounds q hq
  have hx := box_bounds (capL q) (b (Rv 0)) (b (Rv 2)) (ex (4/3) t) hc.1 hc.2 hb
    (ex_pos _ _).le (ex_le_one (by norm_num) ht)
  simp only [vF, aF, PP, RR, ex_cube]
  exact hx

theorem sF_mono (q : ℕ) (hq : q < 4) (b : State (Var 3)) (hb : boxEnv (b (Rv 0)) (b (Rv 2)))
    {t : ℝ} (ht : 0 ≤ t) : b (Rv 1) ≤ sF (capL q) b t := by
  have hmono : MonotoneOn (sF (capL q) b) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun u _ => (sF_der _ b u).continuousAt.continuousWithinAt)
      (fun u _ => (sF_der _ b u).differentiableAt.differentiableWithinAt) (fun u hu => ?_)
    rw [interior_Ici] at hu
    rw [(sF_der _ b u).deriv]
    exact (vF_aF_box q hq b hb (le_of_lt hu)).1
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have h0 : sF (capL q) b 0 = b (Rv 1) := by simp only [sF, ex_zero]; ring
  rwa [h0] at h

/-- **The explicit run of a zone** (any duration `ε ≥ 0`, from any guard state). -/
theorem flowR_run (q : ℕ) (hq : q < 4) (b : State (Var 3)) (hb : boxEnv (b (Rv 0)) (b (Rv 2)))
    (hs : 0 ≤ b (Rv 1)) (ε : ℝ) (hε : 0 ≤ ε) :
    ODESol (rightBlock (fR q) (Term.const 1)) domR b ε (trajRs b (solφ (capL q) b)) := by
  refine trajRs_sol b _ ε hε (fun i => ?_) (fun i t _ _ => ?_) (fun t ht _ => ?_)
  · fin_cases i <;> simp [solφ, vF, sF, aF, PP, RR, ex_zero] <;> ring
  · fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, solφ, Matrix.cons_val_zero]
      rw [fR0_eval q hq, trajRs_R]
      exact vF_der _ b t
    · simp only [Fin.mk_one, Fin.isValue, solφ, Matrix.cons_val_one, Matrix.head_cons]
      rw [fR1_eval q hq, trajRs_R]
      exact sF_der _ b t
    · simp only [Fin.reduceFinMk, Fin.isValue, solφ, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      rw [fR2_eval q hq, trajRs_R, trajRs_R]
      exact aF_der _ b t
  · have hbox := vF_aF_box q hq b hb ht
    have hsm := sF_mono q hq b hb ht
    rw [sat_domR]
    simp only [trajRs_R, solφ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    exact ⟨hbox.1, hbox.2.1, by linarith, hbox.2.2.1, hbox.2.2.2⟩

/-! ## The modal coordinates along any run -/

/-- **A decaying modal coordinate**: if `α f₁ + β f₂ = −k (α y₁ + β y₂ − κ)` on the domain,
then `α y₁ + β y₂ − κ` decays as `e^{−k t}` along the run. -/
theorem modal_exact {sys : ODESystem (Var 3)} {dom : Formula (Var 3)} {x : State (Var 3)}
    {r : ℝ} {Φ : ℝ → State (Var 3)} (H : ODESol sys dom x r Φ) {y₁ y₂ : Var 3}
    {f₁ f₂ : Term (Var 3)} (h₁ : (y₁, f₁) ∈ sys) (h₂ : (y₂, f₂) ∈ sys) (α β κ k : ℝ)
    (h0 : ∀ s, Formula.sat dom s →
      α * Term.eval f₁ s + β * Term.eval f₂ s = -k * (α * s y₁ + β * s y₂ - κ)) :
    α * Φ r y₁ + β * Φ r y₂ - κ = (α * x y₁ + β * x y₂ - κ) * Real.exp (-(k * r)) := by
  set G : ℝ → ℝ := fun t => (α * Φ t y₁ + β * Φ t y₂ - κ) * Real.exp (k * t) with hG
  have hGder : ∀ t ∈ Set.Icc (0:ℝ) r, HasDerivWithinAt G 0 (Set.Icc 0 r) t := by
    intro t ht
    have d1 := (H.hder t ht (y₁, f₁) h₁).const_mul α
    have d2 := (H.hder t ht (y₂, f₂) h₂).const_mul β
    have h2 : HasDerivWithinAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1))
        (Set.Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul k).exp).hasDerivWithinAt
    have h3 := ((d1.add d2).sub_const κ).mul h2
    refine h3.congr_deriv ?_
    simp only [Pi.add_apply]
    rw [h0 _ (H.hdom t ht)]; ring
  have hcont : ContinuousOn G (Set.Icc 0 r) := fun t ht => (hGder t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht =>
    (hGder t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    r ⟨H.hr, le_refl r⟩
  simp only [hG, H.hΦ0, mul_zero, Real.exp_zero, mul_one] at hconst
  have hexp : Real.exp (k * r) * Real.exp (-(k * r)) = 1 := by
    rw [← Real.exp_add]; simp
  calc α * Φ r y₁ + β * Φ r y₂ - κ
      = (α * Φ r y₁ + β * Φ r y₂ - κ) * (Real.exp (k * r) * Real.exp (-(k * r))) := by
        rw [hexp, mul_one]
    _ = ((α * Φ r y₁ + β * Φ r y₂ - κ) * Real.exp (k * r)) * Real.exp (-(k * r)) := by ring
    _ = (α * x y₁ + β * x y₂ - κ) * Real.exp (-(k * r)) := by rw [hconst]

/-- **The envelope and the box are kept** by every zone's flow. -/
theorem run_boxEnv (q : ℕ) (hq : q < 4) {x : State (Var 3)} {t : ℝ} {Φ : ℝ → State (Var 3)}
    (H : ODESol (rightBlock (fR q) (Term.const 1)) domR x t Φ)
    (hx : boxEnv (x (Rv 0)) (x (Rv 2))) : boxEnv (Φ t (Rv 0)) (Φ t (Rv 2)) := by
  have hc := cap_bounds q hq
  have hd := (sat_domR _).mp H.end_dom
  have mv := rightBlock_mem' (fR q) (Term.const 1) 0
  have ma := rightBlock_mem' (fR q) (Term.const 1) 2
  have hp := modal_exact H ma mv 3 4 (4 * capL q) 4 (fun s _ => by
    rw [eval_unit_mul, eval_unit_mul, fR2_eval q hq, fR0_eval q hq]; ring)
  have hr := modal_exact H ma mv 1 4 (4 * capL q) (4/3) (fun s _ => by
    rw [eval_unit_mul, eval_unit_mul, fR2_eval q hq, fR0_eval q hq]; ring)
  have e1p : 0 < Real.exp (-(4 * t)) := Real.exp_pos _
  have e1l : Real.exp (-(4 * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [H.hr]
  have e2p : 0 < Real.exp (-(4/3 * t)) := Real.exp_pos _
  have e2l : Real.exp (-(4/3 * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [H.hr]
  obtain ⟨_, _, _, _, hp0, hp1, hr0, hr1⟩ := hx
  refine ⟨hd.1, hd.2.1, hd.2.2.2.1, hd.2.2.2.2, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * x (Rv 2) + 4 * x (Rv 0) + 3/10) e1p.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ 4 * capL q + 3/10) (sub_nonneg.mpr e1l)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 15/2 - (3 * x (Rv 2) + 4 * x (Rv 0))) e1p.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ 15/2 - 4 * capL q) (sub_nonneg.mpr e1l)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x (Rv 2) + 4 * x (Rv 0) - 7/10) e2p.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ 4 * capL q - 7/10) (sub_nonneg.mpr e2l)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 13/2 - (x (Rv 2) + 4 * x (Rv 0))) e2p.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ 13/2 - 4 * capL q) (sub_nonneg.mpr e2l)]

end V2RoverPatrolLag

namespace V2RoverPatrolLagGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolLag


/-! ## The guarded right graph -/

noncomputable def edgeG (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_modeAt (q : ℕ) (hq : q < 4) : GrG.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrG_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : GrG.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])

theorem edgeG_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeG s t ∈ GrG.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

/-- The zone guards: `lo ≤ s < hi` (no ceiling in `FAST`), and the box and envelope. -/
theorem sat_guardR (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) x ↔
      (loL q ≤ x (Rv 1) ∧ (q < 3 → x (Rv 1) < (if q = 0 then 20 else 50)) ∧
        boxEnv (x (Rv 0)) (x (Rv 2))) := by
  interval_cases q <;>
    simp [hostGuard, mR, rover_patrol_lag_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0,
      hp50_0, hp0_3, hp2_0, hp3_0, hp4_0, hp0_7, hp6_5, hp7_5, vs, Run.resolveVar,
      List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
      AOp.interp, Rv, and_assoc, loL, loQ, boxEnv] <;> norm_num

theorem epsR_eq : epsR rover_patrol_lag_IRv2 = 1 := by
  simp [epsR, rover_patrol_lag_IRv2, hp1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- **Assumption 1 for `rover_patrol_lag`**, every mode, Z3-free. -/
theorem rover_patrol_lag_wellFormedR :
    WellFormedR GrG guardR (epsR rover_patrol_lag_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨h4, rfl⟩ := GrG_modeAt_inv hm
  have hg' := (sat_guardR q h4 x).mp hg
  have hs0 := ((sat_domR x).mp hd).2.2.1
  refine ⟨⟨_, flowR_run q h4 x hg'.2.2 hs0 1 zero_le_one⟩, ?_⟩
  intro t Φ ht H
  have hbe := run_boxEnv q h4 H hg'.2.2
  have hsup := H.rate_le (rightBlock_mem' (fR q) (Term.const 1) 1) 2
    (fun s hs => by rw [eval_unit_mul, fR1_eval q h4]; exact ((sat_domR s).mp hs).2.1)
  have hslo := H.mono (rightBlock_mem' (fR q) (Term.const 1) 1)
    (fun s hs => by rw [eval_unit_mul, fR1_eval q h4]; exact ((sat_domR s).mp hs).1)
  have hr := H.hr
  obtain ⟨hlo, hhi, -⟩ := hg'
  interval_cases q
  · -- SLOW: stays, or crosses into MEDIUM_BRISK
    have hlo' : (0:ℝ) ≤ x (Rv 1) := by simpa [loL, loQ] using hlo
    have hhi' : x (Rv 1) < 20 := by simpa using hhi
    by_cases h20 : Φ t (Rv 1) < 20
    · exact ⟨edgeG 0 0, edgeG_mem 0 0 (by simp [edgeList]),
        (sat_guardR 0 (by norm_num) _).mpr ⟨by simp [loL, loQ]; linarith, fun _ => by simpa using h20, hbe⟩⟩
    · exact ⟨edgeG 0 2, edgeG_mem 0 2 (by simp [edgeList]),
        (sat_guardR 2 (by norm_num) _).mpr ⟨by simp [loL, loQ]; linarith,
          fun _ => by simp; nlinarith, hbe⟩⟩
  · -- MEDIUM_ECO: stays, or crosses into FAST
    have hlo' : (20:ℝ) ≤ x (Rv 1) := by simpa [loL, loQ] using hlo
    have hhi' : x (Rv 1) < 50 := by simpa using hhi
    by_cases h50 : Φ t (Rv 1) < 50
    · exact ⟨edgeG 1 1, edgeG_mem 1 1 (by simp [edgeList]),
        (sat_guardR 1 (by norm_num) _).mpr ⟨by simp [loL, loQ]; linarith, fun _ => by simpa using h50, hbe⟩⟩
    · exact ⟨edgeG 1 3, edgeG_mem 1 3 (by simp [edgeList]),
        (sat_guardR 3 (by norm_num) _).mpr ⟨by simp [loL, loQ]; linarith, by norm_num, hbe⟩⟩
  · -- MEDIUM_BRISK: stays, or crosses into FAST
    have hlo' : (20:ℝ) ≤ x (Rv 1) := by simpa [loL, loQ] using hlo
    have hhi' : x (Rv 1) < 50 := by simpa using hhi
    by_cases h50 : Φ t (Rv 1) < 50
    · exact ⟨edgeG 2 2, edgeG_mem 2 2 (by simp [edgeList]),
        (sat_guardR 2 (by norm_num) _).mpr ⟨by simp [loL, loQ]; linarith, fun _ => by simpa using h50, hbe⟩⟩
    · exact ⟨edgeG 2 3, edgeG_mem 2 3 (by simp [edgeList]),
        (sat_guardR 3 (by norm_num) _).mpr ⟨by simp [loL, loQ]; linarith, by norm_num, hbe⟩⟩
  · -- FAST: invariant
    have hlo' : (50:ℝ) ≤ x (Rv 1) := by simpa [loL, loQ] using hlo
    exact ⟨edgeG 3 3, edgeG_mem 3 3 (by simp [edgeList]),
      (sat_guardR 3 (by norm_num) _).mpr ⟨by simp [loL, loQ]; linarith, by norm_num, hbe⟩⟩

end V2RoverPatrolLagGuarded
end RelCertifier
