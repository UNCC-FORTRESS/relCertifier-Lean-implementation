/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_airframe_20`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` holds** (`quad_light_airframe_20_wellFormedR`, Z3-free):

* `CLIMB` (style (a)): the guard `0 ≤ w ≤ 3` (the climb controller's operating range up to
  the limiter threshold, the 2026-10-10 repair; it was `0 ≤ w ≤ 2.6`) is forward invariant
  under `w' = 4 − w²` (barriers at both faces: `4 − w² ≤ 0` at `w ≥ 3`, `4 − w² ≥ 0` at
  `w = 0`). Existence: the instance's viability route (both evolve faces strict, hand
  Lipschitz data), taken with the left held still, and a time rescaling of the stretched run.
* `LIMIT` (`w > 3`, `w' = −2 w`, declared successors `[LIMIT, CLIMB]`: the limiter hands
  back to the climb controller, `docs/SUITE-REDESIGN.md` §21): style (b). A run decays
  toward 0 and stays in `[0, w₀] ⊆ [0, 3.5]`: it ends in `LIMIT`'s guard if above 3, else in
  `CLIMB`'s. Existence: the explicit exponential decay.

(Until 2026-10-10 `LIMIT`'s only successor was itself and the model was refuted here, from
`w = 3.1`: the run of duration 1 ends at `3.1 e^{−2} < 3`.)
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.InstancesV2.BenchIR.quad_light_airframe_20
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightAirframe20

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["w"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := quad_light_airframe_20_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp35 : Run.parseRat "3.5" = some ((7:ℚ)/2) := by
  have h : parseQ "3.5" = some (⟨35, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp30 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
/-- Right climb field: `w' = c_q − w²` (`CLIMB`: `c = 4`). -/
noncomputable def cRc (_q : ℕ) : ℝ := 4

theorem cRc_pos (q : ℕ) (hq : q < 1) : 0 < cRc q := by
  obtain rfl : q = 0 := by omega
  norm_num [cRc]
theorem cRc_lt (q : ℕ) (hq : q < 1) : cRc q < 49/4 := by
  obtain rfl : q = 0 := by omega
  norm_num [cRc]
theorem cRc_le (q : ℕ) (hq : q < 1) : cRc q ≤ 4 := by
  obtain rfl : q = 0 := by omega
  norm_num [cRc]

theorem fR0_eval (q : ℕ) (hq : q < 1) (x : State (Var 2)) :
    Term.eval (fR q 0) x = cRc q - x (Rv 0) * x (Rv 0) := by
  interval_cases q
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hp40,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 1) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hp40,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 7/2) := by
  simp only [domR, hostEvolve, mR, quad_light_airframe_20_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp35, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CLIMB 0, LIMIT 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1), (1, 0)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The stretch of the left window (the emitted cover's λ) -/

noncomputable def lam (_l : ℕ) : ℝ := 7/4

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; norm_num

/-! ## Existence: both evolve faces strict for the stretched drag field (Z3-free) -/

/-- The faces (`w_R ∈ [0, 7/2]`): `−w_R` and `w_R − 7/2`. -/
noncomputable def faceLo : Term (Var 2) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceHi : Term (Var 2) :=
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

theorem faces_val (x : State (Var 2)) (h : ∀ gT ∈ [faceLo, faceHi], Term.eval gT x ≤ 0) :
    0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 7/2 := by
  have h0 := h faceLo List.mem_cons_self
  have h1 := h faceHi (by simp)
  simp only [faceLo, faceHi, Term.eval, AOp.interp] at h0 h1
  constructor <;> linarith

/-- The frozen-left joint system at right mode `q`, stretched by `λ`: the `w_R` row is
`λ (c_q − w_R²)`, every other row is zero. -/
theorem odeField_R (l q : ℕ) (hq : q < 1) (x : State (Var 2)) :
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
      have : (Lv j : Var 2) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, this]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fR0_eval q hq]
      · have : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR1_eval q hq, this]
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
theorem hbndS_lo (l q : ℕ) (hq : q < 1) (x : State (Var 2))
    (hface : Term.eval faceLo x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)))
      (fun ω => Term.eval faceLo ω) x < 0 := by
  have hx0 : x (Rv 0) = 0 := by
    simp only [faceLo, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceLo ω)
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
theorem hbndS_hi (l q : ℕ) (hq : q < 1) (x : State (Var 2))
    (hface : Term.eval faceHi x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)))
      (fun ω => Term.eval faceHi ω) x < 0 := by
  have hx0 : x (Rv 0) = 7/2 := by
    simp only [faceHi, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceHi ω)
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
field is `16`-Lipschitz (`λ · 9 = 63/4`). -/
theorem hLip (l q : ℕ) (hq : q < 1) (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    LipschitzOnWith 16 (odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))))
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
    have habs : |(-(lam l) : ℝ)| = 7/4 := by simp only [lam]; norm_num
    have hstep : |(-(lam l) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (7/4) * 9 * dist x y := by
      rw [habs]
      have hnn : (0:ℝ) ≤ |x (Rv 0) - y (Rv 0)| := abs_nonneg _
      nlinarith [abs_nonneg (x (Rv 0) + y (Rv 0))]
    have hcoe : ((16 : NNReal) : ℝ) = 16 := by norm_num
    calc |(-(lam l) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (7/4) * 9 * dist x y := hstep
      _ ≤ ((16 : NNReal) : ℝ) * dist x y := by rw [hcoe]; nlinarith
  · simp only [if_neg hc]
    simp [dist_nonneg]

/-- Hand field bound: `‖field‖ ≤ 43` on the same balls (`λ (c_q + 81/4) ≤ 7/4 · 97/4`). -/
theorem hfbnd (l q : ℕ) (hq : q < 1) (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))) x‖
        ≤ (43:NNReal) := by
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
    have hl : lam l = 7/4 := rfl
    rw [abs_le, hl]
    push_cast
    refine ⟨by nlinarith [hsq, hsq0], by nlinarith [hsq, hsq0]⟩
  · simp only [if_neg hc]
    norm_num


theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR quad_light_airframe_20_IRv2 = 1 := by
  simp [epsR, quad_light_airframe_20_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem sat_guardR0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 3 := by
  simp [hostGuard, mR, quad_light_airframe_20_IRv2, Run.lowerF, Run.lowerE, hp00, hp30, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guardR1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔ 3 < ν (Rv 0) := by
  simp [hostGuard, mR, quad_light_airframe_20_IRv2, Run.lowerF, Run.lowerE, hp30, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fR0_limit (x : State (Var 2)) : Term.eval (fR 1 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR1_limit (x : State (Var 2)) : Term.eval (fR 1 1) x = 0 := by
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- The instance's viability existence, with the left held still (`fL = 0`). -/
theorem es0 (dt : ℝ) (hdt : 0 ≤ dt) (σ : State (Var 2)) (hσ : Formula.sat domR σ) :
    HExistSegB (fun _ => Term.const 0) (fR 0) (Term.const (lam 0)) Formula.tt domR dt σ := by
  have hR := (sat_domR σ).mp hσ
  refine HExistSegB_of_viability_stratified (fun _ => Term.const 0) (fR 0)
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
      · exact hbndS_lo 0 0 (by norm_num) x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_hi 0 0 (by norm_num) x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro i hi; exact absurd hi (by simp))
    (by
      intro x hS _
      rw [sat_domR]
      exact faces_val x (fun gT hgT => hS gT (by simpa using hgT)))
    16 43 1 one_pos
    (fun ν0 h0 => hLip 0 0 (by norm_num) ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    (fun ν0 h0 => hfbnd 0 0 (by norm_num) ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
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

/-- **Assumption 1 at `CLIMB`** (style (a), Z3-free). -/
theorem quad_light_airframe_20_wellFormedR_climb :
    WellFormedRMode Gr guardR (epsR quad_light_airframe_20_IRv2) 0 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR0 x).mp hg
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, H⟩ := exists_of_HExistSegB_zero (lam_pos 0) (es0 (4/7) (by norm_num) x hd)
      (s := 4/7) (by norm_num) le_rfl
    rw [show (4/7 : ℝ) * lam 0 = 1 from by simp [lam]] at H
    exact ⟨Φ, H⟩
  · intro t Φ _ H
    have hf := fR0_eval 0 (by norm_num)
    have hup := H.coord_le_barrier 0 3 (fun s _ hs => by
      rw [hf]; simp only [cRc]; nlinarith) hgx.2
    have hlo := H.coord_ge_barrier 0 0 (fun s hs hs0 => by
      have := ((sat_domR s).mp hs).1
      rw [hf]; simp only [cRc]; nlinarith) hgx.1
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr ⟨hlo, hup⟩⟩

/-- **Assumption 1 at `LIMIT`** (style (b)): the climb rate decays toward 0; every run of at
most one interval ends in `LIMIT`'s guard (`w > 3`) or in `CLIMB`'s (`0 ≤ w ≤ 3`). -/
theorem quad_light_airframe_20_wellFormedR_limit :
    WellFormedRMode Gr guardR (epsR quad_light_airframe_20_IRv2) 1 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR1 x).mp hg
  have hdx := (sat_domR x).mp hd
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 2 0 (by norm_num) fR0_limit ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_limit s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      rw [min_eq_right (by linarith)] at h1
      rw [max_eq_left (by linarith)] at h2
      exact ⟨h1, le_trans h2 hdx.2⟩
  · intro t Φ _ H
    have hmem : (Rv 0, Term.binop .mul (Term.const 1) (fR 1 0)) ∈ (modeW 1).sys :=
      rightBlock_mem' _ _ 0
    have hdn := H.linear_down hmem 2 0 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fR0_limit]) (by linarith)
    by_cases h3 : 3 < Φ t (Rv 0)
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR1 _).mpr h3⟩
    · push_neg at h3
      exact ⟨edgeW 1 0, edge_mem 1 0 (by decide), (sat_guardR0 _).mpr ⟨hdn.1, h3⟩⟩

/-- **`quad_light_airframe_20` satisfies Assumption 1** (every mode, Z3-free). -/
theorem quad_light_airframe_20_wellFormedR :
    WellFormedR Gr guardR (epsR quad_light_airframe_20_IRv2) := by
  intro q hq
  have hq2 : q < 2 := by simpa [Gr] using hq
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · exact quad_light_airframe_20_wellFormedR_climb
  · exact quad_light_airframe_20_wellFormedR_limit

end V2QuadLightAirframe20
end RelCertifier
