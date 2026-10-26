/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_lag`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (one mode, `CLIMB`, with its self-loop),
the lowered right guard, `ε_r = 1`. `CLIMB` (`w' = a − w²`, `a' = 5 (4 − a)`, guard = evolve
= `0 ≤ w ≤ 3.5 ∧ 0 ≤ a ≤ 4`) has a forward-invariant guard (style (a)).

Existence: the viability route over a larger box `B` with four STRICT faces,
`w ≥ −a/4`, `w ≤ 7/2`, `a ≥ 0`, `a ≤ 5` (the slanted lower face turns the non-strict
`w = 0` face at `a = 0` into strict inflow: on it `Lie = λ (a²/16 + a/4 − 5) < 0`), with the
left held still and a time rescaling of the stretched run. The run in `B` then stays in the
evolve domain by two non-strict superlevel barriers over `B`: `w ≥ 0` (on `B ∧ w ≤ 0`,
`w² ≤ a²/16 ≤ a`, so `w' ≥ 0`) and `a ≤ 4` (`a' = 5 (4 − a) ≤ 0` for `a ≥ 4`). Since the
guard equals the evolve domain, every run ends in the guard. Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.quad_light_lag
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightLag

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["w", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := quad_light_lag_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp35 : Run.parseRat "3.5" = some ((7:ℚ)/2) := by
  have h : parseQ "3.5" = some (⟨35, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hne10 : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]

/-- Right climb field: `w' = a − w²`. -/
theorem fR0_eval (x : State (Var 2)) :
    Term.eval (fR 0 0) x = x (Rv 1) - x (Rv 0) * x (Rv 0) := by
  simp [fR, hostDyn, mR, quad_light_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp40, hp50, hp0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- Right thrust lag: `a' = 5 (4 − a)`. -/
theorem fR1_eval (x : State (Var 2)) :
    Term.eval (fR 0 1) x = 5 * (4 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, quad_light_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp40, hp50, hp0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (((0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 7/2) ∧ 0 ≤ x (Rv 1)) ∧
      x (Rv 1) ≤ 4) := by
  simp only [domR, hostEvolve, mR, quad_light_lag_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp35, hp40, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CLIMB 0). -/
def edgeList : List (ℕ × ℕ) := [(0, 0)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 1) : Gr.modeAt q = some (modeW q) := by
  obtain rfl : q = 0 := by omega
  rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 1 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 1 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The stretch of the left window (the emitted cover's λ) -/

noncomputable def lam (_l : ℕ) : ℝ := 7/4

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; norm_num

/-! ## Existence: a strict box `B` around the evolve domain (Z3-free) -/

/-- The faces of `B`: `−w − a/4`, `w − 7/2`, `−a`, `a − 5`. -/
noncomputable def f1 : Term (Var 2) :=
  Term.binop AOp.sub (Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0)))
    (Term.binop AOp.mul (Term.const ((1:ℝ)/4)) (Term.var (Rv 1)))
noncomputable def f2 : Term (Var 2) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((7:ℝ)/2))
noncomputable def f3 : Term (Var 2) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 1))
noncomputable def f4 : Term (Var 2) :=
  Term.binop AOp.sub (Term.var (Rv 1)) (Term.const 5)

noncomputable def faces : List (Term (Var 2)) := [f1, f2, f3, f4]

/-- The box `B` as a formula (each face `≤ 0`). -/
noncomputable def domB : Formula (Var 2) :=
  Formula.and (Formula.and (Formula.and (Formula.cmp CompOp.le f1 (Term.const 0))
    (Formula.cmp CompOp.le f2 (Term.const 0))) (Formula.cmp CompOp.le f3 (Term.const 0)))
    (Formula.cmp CompOp.le f4 (Term.const 0))

theorem faces_fv : ∀ gT ∈ faces, ∀ x ∈ gT.fv, x ∈ range Rv := by
  intro gT hgT x hx
  simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl <;>
    simp [f1, f2, f3, f4, Term.fv] at hx
  · rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
  · exact ⟨_, hx.symm⟩
  · exact ⟨_, hx.symm⟩
  · exact ⟨_, hx.symm⟩

theorem faces_val (x : State (Var 2)) (h : ∀ gT ∈ faces, Term.eval gT x ≤ 0) :
    -x (Rv 0) - x (Rv 1) / 4 ≤ 0 ∧ x (Rv 0) ≤ 7/2 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 5 := by
  have h1 := h f1 (by simp [faces])
  have h2 := h f2 (by simp [faces])
  have h3 := h f3 (by simp [faces])
  have h4 := h f4 (by simp [faces])
  simp only [f1, f2, f3, f4, Term.eval, AOp.interp] at h1 h2 h3 h4
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem of_domB {x : State (Var 2)} (h : Formula.sat domB x) :
    -x (Rv 0) - x (Rv 1) / 4 ≤ 0 ∧ x (Rv 0) ≤ 7/2 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 5 := by
  simp only [domB, Formula.sat, CompOp.interp, f1, f2, f3, f4, Term.eval, AOp.interp] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem domB_of {x : State (Var 2)} (h : ∀ gT ∈ faces, Term.eval gT x ≤ 0) :
    Formula.sat domB x := by
  obtain ⟨h1, h2, h3, h4⟩ := faces_val x h
  simp only [domB, Formula.sat, CompOp.interp, f1, f2, f3, f4, Term.eval, AOp.interp]
  refine ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩

/-- The frozen-left joint system, stretched by `λ`: the `w_R` row is `λ (a_R − w_R²)`, the
`a_R` row is `λ · 5 (4 − a_R)`, every other row is zero. -/
theorem odeField_R (l : ℕ) (x : State (Var 2)) :
    odeField (jointSys (fun _ => Term.const 0) (fR 0) (Term.const (lam l))) x
      = fun c => if c = Rv 0 then lam l * (x (Rv 1) - x (Rv 0) * x (Rv 0))
          else if c = Rv 1 then lam l * (5 * (4 - x (Rv 1))) else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fR 0) (Term.const (lam l))).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fR 0) (Term.const (lam l))) x c
        = ((jointSys (fun _ => Term.const 0) (fR 0) (Term.const (lam l))).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fR 0) (Term.const (lam l)),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have h0 : (Lv j : Var 2) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      have h1 : (Lv j : Var 2) ≠ Rv 1 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, h0, h1]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fR0_eval]
      · simp [Term.eval, AOp.interp, fR1_eval, hne10]
  · have hmem : ∀ j : Fin 2, c ≠ Rv j := by
      intro j hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨j, List.mem_finRange j, rfl⟩)
    simp only [odeField, if_neg hc, if_neg (hmem 0), if_neg (hmem 1)]

/-- **Lie of a function affine in two coordinates.** -/
theorem lie_lin2 (sys : ODESystem (Var 2)) (hwf : sys.WellFormed) (i j : Var 2) (a b c : ℝ)
    (x : State (Var 2)) :
    Lie sys (fun y => a * y i + b * y j + c) x
      = a * odeField sys x i + b * odeField sys x j := by
  rw [← Lie_eq_fderiv hwf]
  have hi : HasFDerivAt (fun y : State (Var 2) => y i) (ContinuousLinearMap.proj i) x :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Var 2 => ℝ) i x
  have hj : HasFDerivAt (fun y : State (Var 2) => y j) (ContinuousLinearMap.proj j) x :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Var 2 => ℝ) j x
  have h : HasFDerivAt (fun y : State (Var 2) => a * y i + b * y j + c)
      (a • ContinuousLinearMap.proj i + b • ContinuousLinearMap.proj j) x :=
    ((hi.const_mul a).add (hj.const_mul b)).add_const c
  rw [h.fderiv]
  simp [ContinuousLinearMap.proj_apply]

/-- Strict inflow on every face of `B` (conditioned on `B`). -/
theorem hbndS (gT : Term (Var 2)) (hgT : gT ∈ faces) (x : State (Var 2))
    (hB : ∀ gT' ∈ faces ++ [], Term.eval gT' x ≤ 0) (hface : Term.eval gT x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fR 0) (Term.const (lam 0)))
      (fun ω => Term.eval gT ω) x < 0 := by
  obtain ⟨b1, b2, b3, b4⟩ := faces_val x (fun g hg => hB g (by simpa using hg))
  have hwf := jointSys_wellFormed (fun _ => Term.const 0) (fR 0) (Term.const (lam 0))
  have hl : lam 0 = 7/4 := rfl
  simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hgT
  rcases hgT with rfl | rfl | rfl | rfl
  · have hfun : (fun ω : State (Var 2) => Term.eval f1 ω)
        = fun y => (-1 : ℝ) * y (Rv 0) + (-1/4 : ℝ) * y (Rv 1) + 0 := by
      funext y; simp [f1, Term.eval, AOp.interp]; ring
    simp only [f1, Term.eval, AOp.interp] at hface
    rw [hfun, lie_lin2 _ hwf, odeField_R]
    simp only [if_pos rfl, if_neg hne10, if_true, hl]
    have hw : x (Rv 0) = -(x (Rv 1)) / 4 := by linarith
    rw [hw]
    nlinarith
  · have hfun : (fun ω : State (Var 2) => Term.eval f2 ω)
        = fun y => (1 : ℝ) * y (Rv 0) + (-(7/2)) := by
      funext y; simp [f2, Term.eval, AOp.interp]; ring
    simp only [f2, Term.eval, AOp.interp] at hface
    rw [hfun, lie_affine_coord _ hwf, odeField_R]
    simp only [if_pos rfl, if_true, hl]
    have hw : x (Rv 0) = 7/2 := by linarith
    rw [hw]
    nlinarith
  · have hfun : (fun ω : State (Var 2) => Term.eval f3 ω)
        = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
      funext y; simp [f3, Term.eval, AOp.interp]
    simp only [f3, Term.eval, AOp.interp] at hface
    rw [hfun, lie_affine_coord _ hwf, odeField_R]
    simp only [if_neg hne10, if_true, hl]
    nlinarith
  · have hfun : (fun ω : State (Var 2) => Term.eval f4 ω)
        = fun y => (1 : ℝ) * y (Rv 1) + (-5) := by
      funext y; simp [f4, Term.eval, AOp.interp]; ring
    simp only [f4, Term.eval, AOp.interp] at hface
    rw [hfun, lie_affine_coord _ hwf, odeField_R]
    simp only [if_neg hne10, if_true, hl]
    nlinarith

/-- Coordinate bounds on a unit ball around an anchor of `B`. -/
theorem ball_bnd (ν x : State (Var 2)) (hν : ∀ gT ∈ faces, Term.eval gT ν ≤ 0)
    (hx : x ∈ Metric.closedBall ν 1) :
    |x (Rv 0)| ≤ 9/2 ∧ -1 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := faces_val ν hν
  rw [Metric.mem_closedBall] at hx
  have hw : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hx
  have ha : |x (Rv 1) - ν (Rv 1)| ≤ 1 := by
    have h := dist_le_pi_dist x ν (Rv 1)
    rw [Real.dist_eq] at h
    exact le_trans h hx
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Hand Lipschitz bound on unit balls around anchors of `B`: `λ · 10 = 35/2 ≤ 18`. -/
theorem hLip (ν : State (Var 2)) (hν : ∀ gT ∈ faces, Term.eval gT ν ≤ 0) :
    LipschitzOnWith 18 (odeField (jointSys (fun _ => Term.const 0) (fR 0)
      (Term.const (lam 0)))) (Metric.closedBall ν 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  obtain ⟨hxw, -, -⟩ := ball_bnd ν x hν hx
  obtain ⟨hyw, -, -⟩ := ball_bnd ν y hν hy
  rw [odeField_R, odeField_R]
  have hdw : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
    have h := dist_le_pi_dist x y (Rv 0)
    rwa [Real.dist_eq] at h
  have hda : |x (Rv 1) - y (Rv 1)| ≤ dist x y := by
    have h := dist_le_pi_dist x y (Rv 1)
    rwa [Real.dist_eq] at h
  have hd : (0:ℝ) ≤ dist x y := dist_nonneg
  have hcoe : ((18 : NNReal) : ℝ) = 18 := by norm_num
  have hl : lam 0 = 7/4 := rfl
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [if_true]
    rw [Real.dist_eq, hcoe, hl]
    have hdiff : 7/4 * (x (Rv 1) - x (Rv 0) * x (Rv 0)) - 7/4 * (y (Rv 1) - y (Rv 0) * y (Rv 0))
        = 7/4 * ((x (Rv 1) - y (Rv 1)) - (x (Rv 0) + y (Rv 0)) * (x (Rv 0) - y (Rv 0))) := by
      ring
    rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 7/4)]
    have hs : |x (Rv 0) + y (Rv 0)| ≤ 9 := by
      calc |x (Rv 0) + y (Rv 0)| ≤ |x (Rv 0)| + |y (Rv 0)| := abs_add_le _ _
        _ ≤ 9 := by linarith
    have h1 : |(x (Rv 1) - y (Rv 1)) - (x (Rv 0) + y (Rv 0)) * (x (Rv 0) - y (Rv 0))|
        ≤ |x (Rv 1) - y (Rv 1)| + |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)| := by
      rw [← abs_mul]; exact abs_sub _ _
    have h2 : |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)| ≤ 9 * dist x y :=
      mul_le_mul hs hdw (abs_nonneg _) (by norm_num)
    nlinarith
  · by_cases hc1 : c = Rv 1
    · subst hc1
      simp only [if_neg hne10, if_true]
      rw [Real.dist_eq, hcoe, hl]
      have hdiff : 7/4 * (5 * (4 - x (Rv 1))) - 7/4 * (5 * (4 - y (Rv 1)))
          = -(35/4) * (x (Rv 1) - y (Rv 1)) := by ring
      rw [hdiff, abs_mul]
      norm_num
      nlinarith
    · simp only [if_neg hc0, if_neg hc1]
      simp [dist_nonneg]

/-- Hand field bound `‖field‖ ≤ 44` on the same balls (`λ · 25 = 175/4`). -/
theorem hfbnd (ν : State (Var 2)) (hν : ∀ gT ∈ faces, Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fR 0) (Term.const (lam 0))) x‖
        ≤ (44:NNReal) := by
  intro x hx
  obtain ⟨hxw, ha1, ha2⟩ := ball_bnd ν x hν hx
  have hl : lam 0 = 7/4 := rfl
  rw [odeField_R]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  have hsq : x (Rv 0) * x (Rv 0) ≤ (9/2) * (9/2) := by
    have := abs_le.mp hxw
    nlinarith
  have hsq0 : 0 ≤ x (Rv 0) * x (Rv 0) := mul_self_nonneg _
  by_cases hc0 : c = Rv 0
  · subst hc0
    simp only [if_pos rfl, Real.norm_eq_abs, hl]
    rw [abs_le]
    push_cast
    refine ⟨by nlinarith, by nlinarith⟩
  · by_cases hc1 : c = Rv 1
    · subst hc1
      simp only [if_neg hne10, if_true, Real.norm_eq_abs, hl]
      rw [abs_le]
      push_cast
      refine ⟨by nlinarith, by nlinarith⟩
    · simp only [if_neg hc0, if_neg hc1]
      norm_num

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR quad_light_lag_IRv2 = 1 := by
  simp [epsR, quad_light_lag_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem sat_guardR0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (((0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 7/2) ∧ 0 ≤ ν (Rv 1)) ∧ ν (Rv 1) ≤ 4) := by
  simp [hostGuard, mR, quad_light_lag_IRv2, Run.lowerF, Run.lowerE, hp00, hp35, hp40, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- The viability existence over `B`, with the left held still (`fL = 0`). -/
theorem es0 (dt : ℝ) (hdt : 0 ≤ dt) (σ : State (Var 2)) (hσ : Formula.sat domB σ) :
    HExistSegB (fun _ => Term.const 0) (fR 0) (Term.const (lam 0)) Formula.tt domB dt σ := by
  obtain ⟨s1, s2, s3, s4⟩ := of_domB hσ
  refine HExistSegB_of_viability_stratified (fun _ => Term.const 0) (fR 0)
    (Term.const (lam 0)) Formula.tt domB faces [] [] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fun _ => Term.const 0) _ hb
      obtain ⟨j, hj⟩ := faces_fv gT (by simpa using hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (fun gT hgT x hB hface => hbndS gT hgT x hB hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro i hi; simp at hi)
    (fun x hS _ => domB_of (fun gT hgT => hS gT (by simpa using hgT)))
    18 44 1 one_pos
    (fun ν0 h0 => hLip ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    (fun ν0 h0 => hfbnd ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    dt hdt σ
    (by
      intro gT hgT
      simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hgT
      rcases hgT with rfl | rfl | rfl | rfl <;>
        simp only [f1, f2, f3, f4, Term.eval, AOp.interp] <;> linarith)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-- **Assumption 1 for `quad_light_lag`** (style (a), Z3-free). -/
theorem quad_light_lag_wellFormedR : WellFormedR Gr guardR (epsR quad_light_lag_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq1, rfl⟩ := Gr_modeAt_inv hm
  obtain rfl : q = 0 := by omega
  have hdx := (sat_domR x).mp hd
  refine ⟨?_, ?_⟩
  · have hB : Formula.sat domB x := domB_of (by
      intro gT hgT
      simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hgT
      rcases hgT with rfl | rfl | rfl | rfl <;>
        simp only [f1, f2, f3, f4, Term.eval, AOp.interp] <;> linarith [hdx.1.1.1, hdx.1.1.2,
          hdx.1.2, hdx.2])
    obtain ⟨Φ, H⟩ := exists_of_HExistSegB_zero (lam_pos 0) (es0 (4/7) (by norm_num) x hB)
      (s := 4/7) (by norm_num) le_rfl
    rw [show (4/7 : ℝ) * lam 0 = 1 from by simp [lam]] at H
    refine ⟨Φ, ⟨H.hr, H.hΦ0, H.hder, H.hmask, fun t ht => ?_⟩⟩
    have Ht := H.restrict ht.1 ht.2
    have hw := Ht.coord_ge_barrier 0 0 (fun s hs hs0 => by
      obtain ⟨b1, -, b3, b4⟩ := of_domB hs
      rw [fR0_eval]
      have hsq : (-(s (Rv 0))) * (-(s (Rv 0))) ≤ (s (Rv 1) / 4) * (s (Rv 1) / 4) :=
        mul_self_le_mul_self (by linarith) (by linarith)
      nlinarith) hdx.1.1.1
    have ha := Ht.coord_le_barrier 1 4 (fun s _ hs4 => by
      rw [fR1_eval]; linarith) hdx.2
    obtain ⟨-, b2, b3, -⟩ := of_domB (H.hdom t ht)
    exact (sat_domR _).mpr ⟨⟨⟨hw, b2⟩, b3⟩, ha⟩
  · intro t Φ _ H
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
      (sat_guardR0 _).mpr ((sat_domR _).mp (H.hdom t ⟨H.hr, le_rfl⟩))⟩

end V2QuadLightLag
end RelCertifier
