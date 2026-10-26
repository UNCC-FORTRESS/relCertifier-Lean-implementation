/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_profiles`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` holds** (`quad_light_profiles_wellFormedR`, Z3-free):

* `NORMAL`, `ECO`, `SPORT` (style (a)): the guard `0 ≤ w ≤ 3.2` (the climb controller's
  operating range up to the limiter threshold, the 2026-10-10 repair; it was `0 ≤ w ≤ 2.6`)
  is forward invariant under `w' = c − w²`, `c ∈ {3.6, 4, 4.4}` (barriers at both faces).
  Existence: the instance's viability route with the left held still, rescaled.
* `LIMIT` (`w > 3.2`, `w' = −2 w`, declared successors `[LIMIT, NORMAL]`: the limiter hands
  back to the NORMAL profile, `docs/SUITE-REDESIGN.md` §21): style (b). A run decays toward
  0 inside `[0, w₀] ⊆ [0, 3.5]`: it ends in `LIMIT`'s guard if above 3.2, else in `NORMAL`'s.

(Until 2026-10-10 `LIMIT`'s only successor was itself and the model was refuted here, from
`w = 3.3`: the run of duration 1 ends at `3.3 e^{−2} < 3.2`.)
-/
import RelCertifier.InstancesV2.BenchIR.quad_light_profiles
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightProfiles

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["w"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := quad_light_profiles_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
theorem hp36 : Run.parseRat "3.6" = some ((18:ℚ)/5) := by
  have h : parseQ "3.6" = some (⟨36, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp44 : Run.parseRat "4.4" = some ((22:ℚ)/5) := by
  have h : parseQ "4.4" = some (⟨44, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp35 : Run.parseRat "3.5" = some ((7:ℚ)/2) := by
  have h : parseQ "3.5" = some (⟨35, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp32 : Run.parseRat "3.2" = some ((16:ℚ)/5) := by
  have h : parseQ "3.2" = some (⟨32, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
/-- Right climb fields: `w' = c_q − w²` (`NORMAL` 4, `ECO` 18/5, `SPORT` 22/5). -/
noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 4 else if q = 1 then 18/5 else 22/5

theorem cRc_pos (q : ℕ) (hq : q < 3) : 0 < cRc q := by
  interval_cases q <;> norm_num [cRc]
theorem cRc_lt (q : ℕ) (hq : q < 3) : cRc q < 49/4 := by
  interval_cases q <;> norm_num [cRc]
theorem cRc_le (q : ℕ) (hq : q < 3) : cRc q ≤ 22/5 := by
  interval_cases q <;> norm_num [cRc]

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = cRc q - x (Rv 0) * x (Rv 0) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hp40, hp36, hp44,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hp40, hp36, hp44,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hp40, hp36, hp44,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 7/2) := by
  simp only [domR, hostEvolve, mR, quad_light_profiles_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp35, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, ECO 1, SPORT 2, LIMIT 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 0), (1, 3), (2, 2), (2, 0), (2, 3), (3, 3), (3, 0)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## An auxiliary stretch for the existence argument (any `λ > 0` serves) -/

noncomputable def lam (_l : ℕ) : ℝ := 5/2

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; norm_num

/-! ## Existence: both evolve faces strict for the stretched drag field (Z3-free) -/

/-- The faces (`w_R ∈ [0, 7/2]`): `−w_R` and `w_R − 7/2`. -/
noncomputable def faceLo : Term (Var 3) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceHi : Term (Var 3) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((7:ℝ)/2))

theorem faces_fv : ∀ gT ∈ [faceLo, faceHi], ∀ x ∈ gT.fv, x ∈ range Rv := by
  intro gT hgT x hx
  rcases List.mem_cons.mp hgT with rfl | hgT
  · simp only [faceLo, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩
  · rw [List.mem_singleton] at hgT
    subst hgT
    simp only [faceHi, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩

theorem faces_val (x : State (Var 3)) (h : ∀ gT ∈ [faceLo, faceHi], Term.eval gT x ≤ 0) :
    0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 7/2 := by
  have h0 := h faceLo List.mem_cons_self
  have h1 := h faceHi (by simp)
  simp only [faceLo, faceHi, Term.eval, AOp.interp] at h0 h1
  constructor <;> linarith

/-- The frozen-left joint system at right mode `q`, stretched by `λ`: the `w_R` row is
`λ (c_q − w_R²)`, every other row is zero. -/
theorem odeField_R (l q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))) x
      = fun c => if c = Rv 0 then lam l * (cRc q - x (Rv 0) * x (Rv 0)) else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))) x c
        = ((jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have : (Lv j : Var 3) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, this]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fR0_eval q hq]
      · have : (Rv (1 : Fin 3) : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR1_eval q hq, this]
      · have : (Rv (2 : Fin 3) : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR2_eval q hq, this]
  · have hcR : c ≠ Rv 0 := by
      intro hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp only [odeField, if_neg hc, if_neg hcR]

/-- Strict inflow on the lower face (`w_R = 0` ⟹ `Lie = −λ c_q < 0`). -/
theorem hbndS_lo (l q : ℕ) (hq : q < 3) (x : State (Var 3))
    (hface : Term.eval faceLo x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)))
      (fun ω => Term.eval faceLo ω) x < 0 := by
  have hx0 : x (Rv 0) = 0 := by
    simp only [faceLo, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 3) => Term.eval faceLo ω)
      = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
    funext y
    simp [faceLo, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
    odeField_R l q hq]
  simp only [if_pos rfl, if_true, hx0]
  have h1 := lam_pos l
  have h2 := cRc_pos q hq
  nlinarith

/-- Strict inflow on the upper face (`w_R = 7/2` ⟹ `Lie = λ (c_q − 49/4) < 0`). -/
theorem hbndS_hi (l q : ℕ) (hq : q < 3) (x : State (Var 3))
    (hface : Term.eval faceHi x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)))
      (fun ω => Term.eval faceHi ω) x < 0 := by
  have hx0 : x (Rv 0) = 7/2 := by
    simp only [faceHi, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 3) => Term.eval faceHi ω)
      = fun y => (1 : ℝ) * y (Rv 0) + (-(7/2)) := by
    funext y
    simp [faceHi, Term.eval, AOp.interp]
    ring
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(7/2)) x,
    odeField_R l q hq]
  simp only [if_pos rfl, if_true, hx0]
  have h1 := lam_pos l
  have h2 := cRc_lt q hq
  nlinarith

/-- Hand Lipschitz bound: on unit balls around face-region anchors (`|w_R| ≤ 9/2`), the
field is `23`-Lipschitz (`λ · 9 = 45/2`). -/
theorem hLip (l q : ℕ) (hq : q < 3) (ν : State (Var 3))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    LipschitzOnWith 23 (odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))))
      (Metric.closedBall ν 1) := by
  obtain ⟨hν0, hν1⟩ := faces_val ν hν
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_R l q hq, odeField_R l q hq]
  rw [Metric.mem_closedBall] at hx hy
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hx
  have hyc : |y (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist y ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hy
  have hνb : |ν (Rv 0)| ≤ 7/2 := abs_le.mpr ⟨by linarith, hν1⟩
  have hxb : |x (Rv 0)| ≤ 9/2 := by
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith
  have hyb : |y (Rv 0)| ≤ 9/2 := by
    have h2 := abs_sub_abs_le_abs_sub (y (Rv 0)) (ν (Rv 0))
    linarith
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_true]
    rw [Real.dist_eq]
    have hdiff : lam l * (cRc q - x (Rv 0) * x (Rv 0))
        - lam l * (cRc q - y (Rv 0) * y (Rv 0))
        = -(lam l) * (x (Rv 0) + y (Rv 0)) * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul, abs_mul]
    have h2 : |x (Rv 0) + y (Rv 0)| ≤ 9 := by
      calc |x (Rv 0) + y (Rv 0)| ≤ |x (Rv 0)| + |y (Rv 0)| := abs_add_le _ _
        _ ≤ 9 := by linarith
    have h3 : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
      have h := dist_le_pi_dist x y (Rv 0)
      rwa [Real.dist_eq] at h
    have hd : (0:ℝ) ≤ dist x y := dist_nonneg
    have habs : |(-(lam l) : ℝ)| = 5/2 := by simp only [lam]; norm_num
    have hstep : |(-(lam l) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (5/2) * 9 * dist x y := by
      rw [habs]
      have hnn : (0:ℝ) ≤ |x (Rv 0) - y (Rv 0)| := abs_nonneg _
      nlinarith [abs_nonneg (x (Rv 0) + y (Rv 0))]
    have hcoe : ((23 : NNReal) : ℝ) = 23 := by norm_num
    calc |(-(lam l) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (5/2) * 9 * dist x y := hstep
      _ ≤ ((23 : NNReal) : ℝ) * dist x y := by rw [hcoe]; nlinarith
  · simp only [if_neg hc]
    simp [dist_nonneg]

/-- Hand field bound: `‖field‖ ≤ 62` on the same balls (`λ (c_q + 81/4) ≤ 5/2 · 493/20`). -/
theorem hfbnd (l q : ℕ) (hq : q < 3) (ν : State (Var 3))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))) x‖
        ≤ (62:NNReal) := by
  intro x hx
  obtain ⟨hν0, hν1⟩ := faces_val ν hν
  rw [Metric.mem_closedBall] at hx
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at this
    linarith
  have hxb : |x (Rv 0)| ≤ 9/2 := by
    have := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    have hνb : |ν (Rv 0)| ≤ 7/2 := abs_le.mpr ⟨by linarith, hν1⟩
    linarith [abs_le.mp hνb]
  rw [odeField_R l q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_pos rfl, Real.norm_eq_abs]
    have hsq : x (Rv 0) * x (Rv 0) ≤ (9/2) * (9/2) := by
      have := abs_le.mp hxb
      nlinarith
    have hsq0 : 0 ≤ x (Rv 0) * x (Rv 0) := mul_self_nonneg _
    have hc0 := cRc_pos q hq
    have hc4 := cRc_le q hq
    have hl : lam l = 5/2 := rfl
    rw [abs_le, hl]
    push_cast
    refine ⟨by nlinarith [hsq, hsq0], by nlinarith [hsq, hsq0]⟩
  · simp only [if_neg hc]
    norm_num


theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR quad_light_profiles_IRv2 = 1 := by
  simp [epsR, quad_light_profiles_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem sat_guardR0 (q : ℕ) (hq : q < 3) (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) ν ↔ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 16/5 := by
  interval_cases q <;>
  simp [hostGuard, mR, quad_light_profiles_IRv2, Run.lowerF, Run.lowerE, hp00, hp32, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guardR3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔ 16/5 < ν (Rv 0) := by
  simp [hostGuard, mR, quad_light_profiles_IRv2, Run.lowerF, Run.lowerE, hp32, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fR0_limit (x : State (Var 3)) : Term.eval (fR 3 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR1_limit (x : State (Var 3)) : Term.eval (fR 3 1) x = 0 := by
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR2_limit (x : State (Var 3)) : Term.eval (fR 3 2) x = 0 := by
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 3)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- The instance's viability existence, with the left held still (`fL = 0`). -/
theorem es0 (q : ℕ) (hq : q < 3) (dt : ℝ) (hdt : 0 ≤ dt) (σ : State (Var 3))
    (hσ : Formula.sat domR σ) :
    HExistSegB (fun _ => Term.const 0) (fR q) (Term.const (lam 0)) Formula.tt domR dt σ := by
  have hR := (sat_domR σ).mp hσ
  refine HExistSegB_of_viability_stratified (fun _ => Term.const 0) (fR q)
    (Term.const (lam 0)) Formula.tt domR [faceLo, faceHi] [] [] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fun _ => Term.const 0) _ hb
      obtain ⟨j, hj⟩ := faces_fv gT (by simpa using hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro gT hgT x _ hface
      rcases List.mem_cons.mp hgT with rfl | hgT
      · exact hbndS_lo 0 q hq x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_hi 0 q hq x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro i hi; exact absurd hi (by simp))
    (by
      intro x hS _
      rw [sat_domR]
      exact faces_val x (fun gT hgT => hS gT (by simpa using hgT)))
    23 62 1 one_pos
    (fun ν0 h0 => hLip 0 q hq ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    (fun ν0 h0 => hfbnd 0 q hq ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    dt hdt σ
    (by
      intro gT hgT
      rcases List.mem_cons.mp hgT with rfl | hgT
      · simp only [faceLo, Term.eval, AOp.interp]; linarith [hR.1]
      · rw [List.mem_singleton] at hgT
        subst hgT
        simp only [faceHi, Term.eval, AOp.interp]; linarith [hR.2])
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-- **Assumption 1 at `NORMAL`, `ECO`, `SPORT`** (style (a), Z3-free). -/
theorem quad_light_profiles_wellFormedR_modes (q : ℕ) (hq : q < 3) :
    WellFormedRMode Gr guardR (epsR quad_light_profiles_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR0 q hq x).mp hg
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, H⟩ := exists_of_HExistSegB_zero (lam_pos 0) (es0 q hq (2/5) (by norm_num) x hd)
      (s := 2/5) (by norm_num) le_rfl
    rw [show (2/5 : ℝ) * lam 0 = 1 from by simp [lam]] at H
    exact ⟨Φ, H⟩
  · intro t Φ _ H
    have hf := fR0_eval q hq
    have hc := cRc_pos q hq
    have hc2 : cRc q ≤ 22/5 := cRc_le q hq
    have hup := H.coord_le_barrier 0 (16/5) (fun s _ hs => by
      rw [hf]; nlinarith) hgx.2
    have hlo := H.coord_ge_barrier 0 0 (fun s hs hs0 => by
      have := ((sat_domR s).mp hs).1
      rw [hf]; nlinarith) hgx.1
    exact ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide),
      (sat_guardR0 q hq _).mpr ⟨hlo, hup⟩⟩

/-- **Assumption 1 at `LIMIT`** (style (b)): the climb rate decays toward 0; every run of at
most one interval ends in `LIMIT`'s guard (`w > 3.2`) or in `NORMAL`'s (`0 ≤ w ≤ 3.2`). -/
theorem quad_light_profiles_wellFormedR_limit :
    WellFormedRMode Gr guardR (epsR quad_light_profiles_IRv2) 3 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR3 x).mp hg
  have hdx := (sat_domR x).mp hd
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 2 0 (by norm_num) fR0_limit ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_limit s
      | 2, _ => exact fR2_limit s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      rw [min_eq_right (by linarith)] at h1
      rw [max_eq_left (by linarith)] at h2
      exact ⟨h1, le_trans h2 hdx.2⟩
  · intro t Φ _ H
    have hmem : (Rv 0, Term.binop .mul (Term.const 1) (fR 3 0)) ∈ (modeW 3).sys :=
      rightBlock_mem' _ _ 0
    have hdn := H.linear_down hmem 2 0 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fR0_limit]) (by linarith)
    by_cases h3 : 16/5 < Φ t (Rv 0)
    · exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR3 _).mpr h3⟩
    · push_neg at h3
      exact ⟨edgeW 3 0, edge_mem 3 0 (by decide), (sat_guardR0 0 (by norm_num) _).mpr
        ⟨hdn.1, h3⟩⟩

/-- **`quad_light_profiles` satisfies Assumption 1** (every mode, Z3-free). -/
theorem quad_light_profiles_wellFormedR :
    WellFormedR Gr guardR (epsR quad_light_profiles_IRv2) := by
  intro q hq
  have hq4 : q < 4 := by simpa [Gr] using hq
  rcases (by omega : q < 3 ∨ q = 3) with h | rfl
  · exact quad_light_profiles_wellFormedR_modes q h
  · exact quad_light_profiles_wellFormedR_limit

end V2QuadLightProfiles
end RelCertifier
