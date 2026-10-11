/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_slow` (suite_v2) — modal Theorem 3 by catch-up

An overdamped PD arm (left; `θ' = v`, `v' = −(θ − 0.5) − 2.5v`, modes `Accelerate`,
`Brake`) tracked against a ramp-to-plateau reference (right; one variable `θ`, modes
`ApproachA/B/C` at rates 0.5, 0.35, 0.2 and `Hold` at 0), invariant `θ_L ≤ θ_R + 0.0775`.

The response is the WindowGrowth CATCH-UP: the left's guard-gated window runs first; the
linear-form chain `q = v + 2(θ − 0.5) ≤ 0.355` (`q' = −0.5q`) and its derived bound `θ ≤ 0.6775`
hold at the window's start (the guard's arithmetic) and stay along the clocked left flow
(differential invariants through the `lie_clk_left` adapter, CutLiftX's `linearShape` /
`derivedShape` superlevel conditions); after the window the right, untouched by it, stays
flows at the constant rates of the bands it crosses up to `θ_R = θ_L − 0.0775 ≤ 0.6` (or does
nothing when already there; in `Hold` its guard gives `θ_R ≥ 0.6`). The right automaton is
GUARDED (every edge tests the lowered guard of the band it enters, `Gr_guards`): the climb
switches at each band floor (`0.35`, `0.5`) and at the target, every switch legal by the
explicit end state; the loop invariant's right region is the current band's guard and kept
cut atoms (`gregion`). Until 2026-10-10 the statement over the cut-only region was false
(`θ_R = 0.51` in `ApproachA`, admitted by its cut `θ_R ≥ 0`, has no step); the guard
conjunct excludes it. No verdict pack; Z3-free.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.arm_plateau_slow
import RelCertifier.Proofs.Encoding.ReplayOne
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ArmPlateauSlow

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["theta", "v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := arm_plateau_slow_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := arm_plateau_slow_IRv2.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (arm_plateau_slow_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 2)) := []

noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX arm_plateau_slow_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm1 : Run.parseRat "-1" = some (-1 : ℚ) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm25 : Run.parseRat "-2.5" = some (-(5:ℚ)/2) := by
  have h : parseQ "-2.5" = some (⟨-25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp12 : Run.parseRat "1.2" = some ((6:ℚ)/5) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm10 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp0355 : Run.parseRat "0.355" = some ((71:ℚ)/200) := by
  have h : parseQ "0.355" = some (⟨355, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp06775 : Run.parseRat "0.6775" = some ((271:ℚ)/400) := by
  have h : parseQ "0.6775" = some (⟨6775, 10000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp035 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp115 : Run.parseRat "1.15" = some ((23:ℚ)/20) := by
  have h : parseQ "1.15" = some (⟨115, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00775 : Run.parseRat "0.0775" = some ((31:ℚ)/400) := by
  have h : parseQ "0.0775" = some (⟨775, 10000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Evaluations of the lowered data -/

theorem fL0_eval (l : ℕ) (hl : l < 2) (x : State (Var 2)) :
    Term.eval (fL l 0) x = x (Lv 1) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, arm_plateau_slow_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hpm1,
      hpm25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]

theorem fL1_eval (l : ℕ) (hl : l < 2) (x : State (Var 2)) :
    Term.eval (fL l 1) x = -1 * (x (Lv 0) - 1/2) - 5/2 * x (Lv 1) := by
  interval_cases l <;>
  · simp [fL, hostDyn, mL, arm_plateau_slow_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hpm1,
      hpm25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]
    ring

/-- Right rates: ApproachA 0.5, ApproachB 0.35, ApproachC 0.2, Hold 0. -/
noncomputable def rate (q : ℕ) : ℝ :=
  if q = 0 then 1/2 else if q = 1 then 7/20 else if q = 2 then 1/5 else 0

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = rate q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, arm_plateau_slow_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp035,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, rate]

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, arm_plateau_slow_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp035,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_domL (x : State (Var 2)) :
    Formula.sat domL x ↔
      (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 6/5 ∧ -1 ≤ x (Lv 1) ∧ x (Lv 1) ≤ 1) := by
  simp only [domL, hostEvolve, mL, arm_plateau_slow_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp12, hpm10, hp10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]
  tauto

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 6/5) := by
  simp only [domR, hostEvolve, mR, arm_plateau_slow_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp12, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 2) : hostEvolve vs 2 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem sat_guardL (l : ℕ) (hl : l < 2) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.L (mL l)) ν ↔
      (if l = 0 then 0 ≤ ν (Lv 0) ∧ ν (Lv 0) < 1/2 ∧ 0 ≤ ν (Lv 1) ∧ ν (Lv 1) < 71/200
       else 1/2 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ 271/400 ∧ ν (Lv 1) ≤ 0) := by
  interval_cases l <;>
    simp [hostGuard, mL, arm_plateau_slow_IRv2, Run.lowerF, Run.lowerE, hp00, hp05, hp0355,
      hp06775, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Lv] <;> tauto

theorem comps_eq : comps =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0))
      (Term.const (31/400)))] := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [comps, hostComps, arm_plateau_slow_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp00775, ITerm.toHost, Lv, Rv]

/-- The declared row has exactly one component: `gs = comps.tail`. -/
theorem gs_eq : gs = comps.tail := by rw [comps_eq]; rfl

theorem eval_g (x : State (Var 2)) : Term.eval g x = x (Lv 0) - (x (Rv 0) + 31/400) := by
  simp [g, comps_eq, Term.eval, AOp.interp]

/-! ## Side splits -/

theorem fL_pipe (l : ℕ) (i : Fin 2) : fL l i =
    (((some (mL l)).bind (Run.dynOf vs 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fR_pipe (q : ℕ) (i : Fin 2) : fR q i =
    (((some (mR q)).bind (Run.dynOf vs 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL_pipe : domL =
    (((some (mL 0)).bind (fun m => Run.lowerF vs 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domR_pipe : domR =
    (((some (mR 0)).bind (fun m => Run.lowerF vs 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL (l : ℕ) (hl : l < 2) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, arm_plateau_slow_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, arm_plateau_slow_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, arm_plateau_slow_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, arm_plateau_slow_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 2) : (hostGuard vs 2 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by interval_cases l <;>
      simp [mL, arm_plateau_slow_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, comps_eq, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  subst hc
  intro x hx
  simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false] at hx
  rcases hx with rfl | rfl <;> simp

/-! ## The right regions: the kept cut atoms of each right mode -/

theorem gR_thr0 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0"))
    = thrGe (Rv 0) 0 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp00, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_thr1 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35"))
    = thrGe (Rv 0) (7/20) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp035, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_thr2 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5"))
    = thrGe (Rv 0) (1/2) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp05, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_thr3 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6"))
    = thrGe (Rv 0) (3/5) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp06, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_thr4 : hostAtomG vs 2 Side.R (.cmp "<=" (.var "theta") (.num "1.15"))
    = thrLe (Rv 0) (23/20) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp115, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]

theorem cR_0 : cR 0 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")), thrGe (Rv 0) 0)] := by
  rw [← gR_thr0]; rfl
theorem cR_1 : cR 1 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")), thrGe (Rv 0) (7/20))] := by
  rw [← gR_thr1]; rfl
theorem cR_2 : cR 2 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")), thrGe (Rv 0) (1/2))] := by
  rw [← gR_thr2]; rfl
theorem cR_3 : cR 3 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")), thrGe (Rv 0) (3/5)),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "theta") (.num "1.15")), thrLe (Rv 0) (23/20))] := by
  rw [← gR_thr3, ← gR_thr4]; rfl

theorem atomsNonstrictR (q : ℕ) (hq : q < 4) :
    ∀ x ∈ cutAtomsOfX arm_plateau_slow_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, arm_plateau_slow_cutsV2X, mR, arm_plateau_slow_IRv2] at hx
    first
      | (subst hx; exact ⟨_, _, _, rfl, by simp⟩)
      | (rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩)

theorem hiffR (q : ℕ) (hq : q < 4) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

/-- The lower edge of each right mode's region (ApproachA/B/C, Hold). -/
noncomputable def lowR (q : ℕ) : ℝ :=
  if q = 0 then 0 else if q = 1 then 7/20 else if q = 2 then 1/2 else 3/5

noncomputable def region (q : ℕ) : Formula (Var 2) := cutF (cR q)

theorem sat_region (q : ℕ) (hq : q < 4) (ν : State (Var 2)) :
    Formula.sat (region q) ν ↔ (lowR q ≤ ν (Rv 0) ∧ (q = 3 → ν (Rv 0) ≤ 23/20)) := by
  rw [region, sat_cutF]
  have hc : CutSat (cR q) ν ↔ ∀ a ∈ cR q, Term.eval a.2 ν ≤ 0 :=
    ⟨fun h a ha => (hiffR q hq a ha ν).mp (h a ha),
     fun h a ha => (hiffR q hq a ha ν).mpr (h a ha)⟩
  rw [hc]
  interval_cases q
  · rw [cR_0]; simp [thrGe, Term.eval, AOp.interp, lowR]
  · rw [cR_1]; simp [thrGe, Term.eval, AOp.interp, lowR]
  · rw [cR_2]; simp [thrGe, Term.eval, AOp.interp, lowR]
  · rw [cR_3]; simp [thrGe, thrLe, Term.eval, AOp.interp, lowR]

theorem cR_nil (q : ℕ) (hq : ¬ q < 4) : cR q = [] := by
  have hm : mR q = dm := by
    unfold mR
    rw [List.getD_eq_default]
    simp [arm_plateau_slow_IRv2]; omega
  simp only [cR, hm, dm]
  rfl

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  by_cases h4 : q < 4
  · simp only [region]
    intro x hx
    unfold cutF at hx
    have key : ∀ (L : List (CutAtomP 2)) (acc : Formula (Var 2)),
        acc.fv ⊆ range Rv → (∀ a ∈ L, a.1.fv ⊆ range Rv) →
        (L.foldl (fun d a => Formula.and d a.1) acc).fv ⊆ range Rv := by
      intro L
      induction L with
      | nil => intro acc hacc _; simpa using hacc
      | cons a L ih =>
          intro acc hacc hL
          simp only [List.foldl_cons]
          refine ih _ ?_ (fun b hb => hL b (List.mem_cons_of_mem _ hb))
          intro y hy
          rcases hy with hy | hy
          · exact hacc hy
          · exact hL a List.mem_cons_self hy
    refine key (cR q) Formula.tt (by simp [Formula.fv]) ?_ hx
    intro a ha y hy
    interval_cases q <;>
      simp only [cR_0, cR_1, cR_2, cR_3, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      first
        | (subst ha
           exact side_eq_R_mem (by
            simp only at hy
            unfold hostAtomF at hy
            exact hostForm_side (resolvesTo_R vs) _
              (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy))
        | (rcases ha with rfl | rfl <;>
           exact side_eq_R_mem (by
            simp only at hy
            unfold hostAtomF at hy
            exact hostForm_side (resolvesTo_R vs) _
              (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy))
  · simp only [region, cR_nil q h4, cutF, List.foldl_nil]
    simp [Formula.fv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions (ApproachA 0, ApproachB 1, ApproachC 2, Hold 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 0), (0, 2), (0, 3), (1, 2), (1, 1), (1, 3), (2, 3), (2, 2), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range arm_plateau_slow_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (arm_plateau_slow_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 4 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [edgeW, Gr]

theorem hRv : ∀ q m, Gr.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fR q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fR q) (Term.const 1) (hfR q hq) (by simp [Term.fv]) hy
  · exact hdomR hy

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

theorem hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRv q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR (q : ℕ) (hq : q < 4) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R vs (mR q) (by
    interval_cases q <;> simp [mR, arm_plateau_slow_IRv2, Parse.PForm.namesFree,
      Parse.PExpr.namesFree])

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 4 := by decide

theorem hgR : GuardsRight Gr := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact hguardR p.2 (edgeList_tgt p hp)

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of
the mode it enters. -/
theorem Gr_guards : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = hostGuard vs 2 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

/-! ## O2 along the left window: the linear-form chain on the clocked left flow -/

theorem leftBlock_wf (f : Fin 2 → Term (Var 2)) : (leftBlock f).WellFormed := by
  have hLinj : Function.Injective (Lv (n := 2)) := by
    intro a b h; simpa [Lv, Prod.ext_iff] using h
  unfold ODESystem.WellFormed leftBlock
  simp only [List.map_map, Function.comp_def]
  exact (List.nodup_finRange 2).map hLinj

theorem htg_leftBlock (f : Fin 2 → Term (Var 2)) : tg ∉ (leftBlock f).bound := by
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub f _ h
  exact aux_ne_Lv 1 i hi

/-- **The adapter**: along the clocked left system, the Lie derivative of a clock-free
term is its one-sided left Lie derivative `lie1L` (the clock row contributes
`∂g/∂tg · 1 = 0`). -/
theorem lie_clk_left (f : Fin 2 → Term (Var 2)) (t : Term (Var 2)) (ht : tg ∉ t.fv)
    (x : State (Var 2)) :
    Lie (DLCalTiming.clk tg (leftBlock f)) (fun ω => Term.eval t ω) x
      = Term.eval (lie1L t f) x := by
  rw [eval_lie1L]
  unfold Lie DLCalTiming.clk leftBlock
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_map,
    Function.comp_def]
  rw [tderiv_fderiv t tg x, tderiv_not_free ht x, Fin.sum_univ_def]
  simp only [Term.eval, zero_mul, add_zero]
  congr 1
  refine List.map_congr_left ?_
  intro i _
  rw [tderiv_fderiv]

/-- The linear form's safe-side term: `q − 0.355` with `q = v + 2·(θ − 0.5)` (the larger
root `r = 2` of `r² − 2.5 r + 1 = 0`). -/
noncomputable def qT : Term (Var 2) := linLe (Lv 0) (Lv 1) 2 (1/2) (71/200)
/-- The derived bound's safe-side term: `θ − 0.6775`. -/
noncomputable def bT : Term (Var 2) := thrLe (Lv 0) (271/400)
noncomputable def Fq : Formula (Var 2) := Formula.cmp CompOp.le qT (Term.const 0)

theorem tg_qT : tg ∉ qT.fv := by
  simp [qT, linLe, linQ, Term.fv, Lv, Prod.ext_iff]
theorem tg_bT : tg ∉ bT.fv := by
  simp [bT, thrLe, Term.fv, Lv, Prod.ext_iff]

theorem eval_qT (x : State (Var 2)) :
    Term.eval qT x = x (Lv 1) + 2 * (x (Lv 0) - 1/2) - 71/200 := by
  simp [qT, linLe, linQ, Term.eval, AOp.interp]
theorem eval_bT (x : State (Var 2)) : Term.eval bT x = x (Lv 0) - 271/400 := by
  simp [bT, thrLe, Term.eval, AOp.interp]

theorem wf_clk (l : ℕ) : (DLCalTiming.clk tg (leftBlock (fL l))).WellFormed :=
  clk_wellFormed tg _ (leftBlock_wf _) (htg_leftBlock _)

/-- `q ≤ 0.355` stays along the clocked left flow (`q' = −0.5 q`, `linearShape`). -/
theorem boxle_qT (l : ℕ) (hl : l < 2) : ∀ ν, Term.eval qT ν ≤ 0 →
    BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
      (fun ω => Term.eval qT ω) ν := by
  intro ν hν
  refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable qT) ?_ hν
  intro x hx hge
  rw [lie_clk_left _ _ tg_qT]
  exact super_linear_le_L (jx := 0) (jy := 1) (a := 1) (b := 5/2) (c := 1/2) (r := 2)
    (K := 71/200) (by norm_num) (by norm_num) (by norm_num) (fL l) domL
    (fun z _ => fL0_eval l hl z) (fun z _ => by rw [fL1_eval l hl]) x hx hge

/-- `θ ≤ 0.6775` stays along the clocked left flow from inside `q ≤ 0.355`
(`derivedShape`, stratified on the linear form). -/
theorem boxle_bT (l : ℕ) (hl : l < 2) : ∀ ν, Term.eval qT ν ≤ 0 → Term.eval bT ν ≤ 0 →
    BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
      (fun ω => Term.eval bT ω) ν := by
  refine stay_given (Fq := Fq) (gq := qT)
    (fun z => by simp [Fq, Formula.sat, CompOp.interp, Term.eval]) (boxle_qT l hl) ?_
  intro ν hν
  refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable bT) ?_ hν
  intro x hx hge
  rw [lie_clk_left _ _ tg_bT]
  exact super_derived_le_L (jx := 0) (jy := 1) (r := 2) (c := 1/2) (K := 71/200)
    (K' := 271/400) (by norm_num) (by norm_num) (fL l) (Formula.and domL Fq)
    (fun z _ => fL0_eval l hl z)
    (fun z hz => by
      have h2 := hz.2
      simpa [Fq, qT, Formula.sat, CompOp.interp, Term.eval] using h2) x hx hge

/-- **The left window's end**: from a start inside the chain (`q ≤ 0.355`, `θ ≤ 0.6775`),
the window ends with `θ_L ≤ 0.6775`, inside the evolve domain, the right state untouched. -/
theorem window_end (l : ℕ) (hl : l < 2) (dt : ℝ) {σ ν : State (Var 2)}
    (hsem : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν)
    (hq : Term.eval qT σ ≤ 0) (hb : Term.eval bT σ ≤ 0) :
    ν (Lv 0) ≤ 271/400 := by
  simp only [windowSeg, List.replicate_succ, List.replicate_zero, bigSeq] at hsem
  obtain ⟨mid, hseg, hrest⟩ := hsem
  rw [sem_test] at hrest
  obtain ⟨rfl, -⟩ := hrest
  obtain ⟨σ₁, hassign, ν₀, hode, htest⟩ := hseg
  rw [sem_test] at htest
  obtain ⟨rfl, -⟩ := htest
  rw [sem_assign] at hassign
  have hco : ∀ t : Term (Var 2), tg ∉ t.fv → Term.eval t σ₁ = Term.eval t σ :=
    fun t ht => Term.coincidence t (fun y hy => hassign.2 y (fun h => ht (h ▸ hy)))
  have : Term.eval bT ν₀ ≤ 0 :=
    boxle_bT l hl σ₁ (by rw [hco qT tg_qT]; exact hq) (by rw [hco bT tg_bT]; exact hb) ν₀ hode
  rw [eval_bT] at this
  linarith

theorem window_maskR (l : ℕ) (dt : ℝ) {σ ν : State (Var 2)}
    (hsem : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν) (j : Fin 2) :
    ν (Rv j) = σ (Rv j) := by
  refine windowSeg_mask (leftBlock (fL l)) domL tg dt 1 (leftBlock_wf (fL l))
    (htg_leftBlock (fL l)) hsem (Rv j) ?_
  intro h
  simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL l) _ (by simpa [ODESystem.bound] using h)
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [Rv, tg, Prod.ext_iff])

/-- O1, by the guard's own arithmetic: every left guard puts the start inside the chain. -/
theorem chain_of_guard (l : ℕ) (hl : l < 2) {σ : State (Var 2)}
    (hg : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ) :
    Term.eval qT σ ≤ 0 ∧ Term.eval bT σ ≤ 0 := by
  rw [sat_guardL l hl] at hg
  rw [eval_qT, eval_bT]
  interval_cases l
  · simp only [if_true] at hg
    obtain ⟨h1, h2, h3, h4⟩ := hg
    constructor <;> linarith
  · simp only [show (1:ℕ) ≠ 0 from by decide, if_false] at hg
    obtain ⟨h1, h2, h3⟩ := hg
    constructor <;> linarith

/-! ## The right's constant-rate run -/

theorem rate_nonneg (q : ℕ) : 0 ≤ rate q := by
  unfold rate; split_ifs <;> norm_num

/-- A run of right mode `q < 4` for any duration `τ ≥ 0` that stays below the top of the
evolve domain: `θ_R(t) = θ_R + c_q t`, the right's unused second slot frozen. -/
theorem sem_right_run (q : ℕ) (hq : q < 4) (τ : ℝ) (hτ : 0 ≤ τ) {μ : State (Var 2)}
    (hdom : Formula.sat domR μ) (htop : μ (Rv 0) + rate q * τ ≤ 6/5) :
    Program.sem (Program.ode (rightBlock (fR q) (Term.const 1)) domR) μ
      (fun x => if x = Rv 0 then μ (Rv 0) + rate q * τ else μ x) := by
  have hR := (sat_domR μ).mp hdom
  have hne10 : (Rv 1 : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hc := rate_nonneg q
  classical
  refine ⟨τ, fun t x => if x = Rv 0 then μ (Rv 0) + rate q * t else μ x,
    hτ, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp
    · simp [if_neg h0]
  · rfl
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    fin_cases i
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fR q ⟨0, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + rate q * t else μ x) = rate q := by
        simp [Term.eval, AOp.interp, show fR q ⟨0, by norm_num⟩ = fR q 0 from rfl,
          fR0_eval q hq]
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => μ (Rv 0) + rate q * u)
          (rate q * 1) (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (rate q)).const_add (μ (Rv 0))
      rw [mul_one] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp
      · simp
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fR q ⟨1, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + rate q * t else μ x) = 0 := by
        simp [Term.eval, AOp.interp, show fR q ⟨1, by norm_num⟩ = fR q 1 from rfl,
          fR1_eval q hq]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 1))) ?_ ?_
      · intro y _; simp [if_neg hne10]
      · simp [if_neg hne10]
  · intro t ht x hx
    have hx0 : x ≠ Rv 0 := by
      intro h; subst h
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [if_neg hx0]
  · intro t ht
    refine (sat_domR _).mpr ?_
    show 0 ≤ (if Rv 0 = Rv 0 then μ (Rv 0) + rate q * t else μ (Rv 0)) ∧
      (if Rv 0 = Rv 0 then μ (Rv 0) + rate q * t else μ (Rv 0)) ≤ 6/5
    rw [if_pos rfl]
    have h1 : 0 ≤ rate q * t := mul_nonneg hc ht.1
    have h2 : rate q * t ≤ rate q * τ := mul_le_mul_of_nonneg_left ht.2 hc
    constructor <;> linarith [hR.1]

/-! ## The left windows (guard-gated, one clocked piece) -/

/-! ## The mode-consistent region: the right mode's guard and its kept cut atoms -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard (the state a guarded
jump into `q` leaves the right in) and its checked cuts (`region`). -/
noncomputable def gregion (q : ℕ) : Formula (Var 2) :=
  regionG (fun q => hostGuard vs 2 Side.R (mR q)) region q

theorem hguardR_all (q : ℕ) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [arm_plateau_slow_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q)

noncomputable def leftData : List (Formula (Var 2) × (Fin 2 → Term (Var 2))
    × Formula (Var 2) × ℕ) :=
  [(hostGuard vs 2 Side.L (mL 0), fL 0, domL, 1), (hostGuard vs 2 Side.L (mL 1), fL 1, domL, 1)]

noncomputable def leftProgs (dt : ℝ) : List (Program (Var 2)) :=
  leftData.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2)

theorem hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftData, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfL 0 (by norm_num), hdomL⟩
  · exact ⟨hguardL 1 (by norm_num), hfL 1 (by norm_num), hdomL⟩

theorem hframes (dt : ℝ) : ∀ P ∈ leftProgs dt, FramesMv P mv := by
  intro P hP
  simp only [leftProgs, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg dt d.2.2.2 mv (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

theorem rate_pos (q : ℕ) (hq : q < 3) : 0 < rate q := by
  interval_cases q <;> norm_num [rate]

/-- The right guards, evaluated. -/
theorem sat_guardR (q : ℕ) (hq : q < 4) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 7/20
       else if q = 1 then 7/20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 1/2
       else if q = 2 then 1/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 3/5
       else 3/5 ≤ ν (Rv 0) ∧ ν (Rv 0) < 23/20) := by
  interval_cases q <;>
    simp [hostGuard, mR, arm_plateau_slow_IRv2, Run.lowerF, Run.lowerE, hp00, hp035, hp05, hp06, hp115, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

/-! ## The emitted cover's data: the left windows' kept cut atoms -/

theorem hp1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp2 : Run.parseRat "2" = some (2 : ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm025 : Run.parseRat "-0.25" = some (-(1:ℚ)/4) := by
  have h : parseQ "-0.25" = some (⟨-25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp008875 : Run.parseRat "0.08875" = some ((71:ℚ)/800) := by
  have h : parseQ "0.08875" = some (⟨8875, 100000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

noncomputable def cL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.L (cutAtomsOfX arm_plateau_slow_cutsV2X.L (mL l).name)

def AvLe : PForm := .cmp "<=" (.var "v") (.num "0.355")
def AhLe : PForm := .cmp "<=" (.bin "+" (.var "v") (.bin "*" (.num "0.5")
  (.bin "-" (.var "theta") (.num "0.5")))) (.num "0.355")
def AhGe : PForm := .cmp ">=" (.bin "+" (.var "v") (.bin "*" (.num "0.5")
  (.bin "-" (.var "theta") (.num "0.5")))) (.num "-0.25")
def AqLe : PForm := .cmp "<=" (.bin "+" (.var "v") (.bin "*" (.num "2")
  (.bin "-" (.var "theta") (.num "0.5")))) (.num "0.355")
def AqGe : PForm := .cmp ">=" (.bin "+" (.var "v") (.bin "*" (.num "2")
  (.bin "-" (.var "theta") (.num "0.5")))) (.num "-1")
def AbLe : PForm := .cmp "<=" (.var "theta") (.num "0.6775")
def AkLe : PForm := .cmp "<=" (.bin "+" (.var "v") (.bin "*" (.num "0.5")
  (.bin "-" (.var "theta") (.num "0.5")))) (.num "0.08875")

theorem gL_vle : hostAtomG vs 2 Side.L AvLe = thrLe (Lv 1) (71/200) := by
  simp [AvLe, hostAtomG, cutAtomG, Run.lowerE, hp0355, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_hle : hostAtomG vs 2 Side.L AhLe = linLe (Lv 0) (Lv 1) (1/2) (1/2) (71/200) := by
  simp [AhLe, hostAtomG, cutAtomG, Run.lowerE, hp05, hp0355, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linLe, linQ, Lv]
theorem gL_hge : hostAtomG vs 2 Side.L AhGe = linGe (Lv 0) (Lv 1) (1/2) (1/2) (-1/4) := by
  simp [AhGe, hostAtomG, cutAtomG, Run.lowerE, hp05, hpm025, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linGe, linQ, Lv]
theorem gL_qle : hostAtomG vs 2 Side.L AqLe = linLe (Lv 0) (Lv 1) 2 (1/2) (71/200) := by
  simp [AqLe, hostAtomG, cutAtomG, Run.lowerE, hp2, hp05, hp0355, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linLe, linQ, Lv]
theorem gL_qge : hostAtomG vs 2 Side.L AqGe = linGe (Lv 0) (Lv 1) 2 (1/2) (-1) := by
  simp [AqGe, hostAtomG, cutAtomG, Run.lowerE, hp2, hp05, hpm1, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linGe, linQ, Lv]
theorem gL_ble : hostAtomG vs 2 Side.L AbLe = thrLe (Lv 0) (271/400) := by
  simp [AbLe, hostAtomG, cutAtomG, Run.lowerE, hp06775, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_kle : hostAtomG vs 2 Side.L AkLe = linLe (Lv 0) (Lv 1) (1/2) (1/2) (71/800) := by
  simp [AkLe, hostAtomG, cutAtomG, Run.lowerE, hp05, hp008875, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linLe, linQ, Lv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 2 Side.L AvLe, thrLe (Lv 1) (71/200)),
     (hostAtomF vs 2 Side.L AhLe, linLe (Lv 0) (Lv 1) (1/2) (1/2) (71/200)),
     (hostAtomF vs 2 Side.L AhGe, linGe (Lv 0) (Lv 1) (1/2) (1/2) (-1/4)),
     (hostAtomF vs 2 Side.L AqLe, linLe (Lv 0) (Lv 1) 2 (1/2) (71/200)),
     (hostAtomF vs 2 Side.L AqGe, linGe (Lv 0) (Lv 1) 2 (1/2) (-1)),
     (hostAtomF vs 2 Side.L AbLe, thrLe (Lv 0) (271/400))] := by
  rw [← gL_vle, ← gL_hle, ← gL_hge, ← gL_qle, ← gL_qge, ← gL_ble]; rfl
theorem cL_1 : cL 1 =
    [(hostAtomF vs 2 Side.L AkLe, linLe (Lv 0) (Lv 1) (1/2) (1/2) (71/800)),
     (hostAtomF vs 2 Side.L AqLe, linLe (Lv 0) (Lv 1) 2 (1/2) (71/200)),
     (hostAtomF vs 2 Side.L AbLe, thrLe (Lv 0) (271/400))] := by
  rw [← gL_kle, ← gL_qle, ← gL_ble]; rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 2) :
    ∀ x ∈ cutAtomsOfX arm_plateau_slow_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, arm_plateau_slow_cutsV2X, mL, arm_plateau_slow_IRv2] at hx
    first
      | (rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩)
      | (rcases hx with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩)

theorem hiffL (l : ℕ) (hl : l < 2) : AtomsIff (cL l) := atomsIff_cutPairsX (atomsNonstrictL l hl)

/-! ## O1: the guards imply the kept atoms (the extended certificate, kernel-checked; the
linear forms' rational entry is `CutLiftX.entry_linear`) -/

theorem hO1L (l : ℕ) (hl : l < 2) :
    ∀ ν, Formula.sat (hostGuard vs 2 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard arm_plateau_slow_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, arm_plateau_slow_cutsV2X, mL, arm_plateau_slow_IRv2] at hx
      first
        | (rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        | (rcases hx with rfl | rfl | rfl <;> simp)
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, arm_plateau_slow_cutsV2X, mL, arm_plateau_slow_IRv2] at hx
      first
        | (rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [Run.lowerF, Run.lowerE, hp1, hp2, hp05, hpm1, hpm025, hp008875, hp0355, hp06775, vs,
              Run.resolveVar, List.findIdx?_cons])
        | (rcases hx with rfl | rfl | rfl <;>
            simp [Run.lowerF, Run.lowerE, hp1, hp2, hp05, hpm1, hpm025, hp008875, hp0355, hp06775, vs,
              Run.resolveVar, List.findIdx?_cons])
  · interval_cases l <;>
      simp [mL, arm_plateau_slow_IRv2, Run.lowerF, Run.lowerE, hp00, hp05, hp0355, hp06775, vs,
        Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 4) :
    ∀ ν, Formula.sat (hostGuard vs 2 Side.R (mR q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard arm_plateau_slow_cutsV2X_wf (mR q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, arm_plateau_slow_cutsV2X, mR, arm_plateau_slow_IRv2] at hx
      first
        | (subst hx; simp)
        | (rcases hx with rfl | rfl <;> simp)
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, arm_plateau_slow_cutsV2X, mR, arm_plateau_slow_IRv2] at hx
      first
        | (subst hx; simp [Run.lowerF, Run.lowerE, hp00, hp035, hp05, hp06, hp115, vs,
            Run.resolveVar, List.findIdx?_cons])
        | (rcases hx with rfl | rfl <;>
            simp [Run.lowerF, Run.lowerE, hp00, hp035, hp05, hp06, hp115, vs, Run.resolveVar,
              List.findIdx?_cons])
  · interval_cases q <;>
      simp [mR, arm_plateau_slow_IRv2, Run.lowerF, Run.lowerE, hp00, hp035, hp05, hp06, hp115, vs,
        Run.resolveVar, List.findIdx?_cons]

/-! ## O2: the kept atoms stay along the flows the cover certifies

The left field is the over-damped pair `θ' = v`, `v' = −(θ − 0.5) − 2.5 v` (`a = 1`,
`b = 2.5`, `c = 0.5`, roots `r = 0.5` and `r = 2`): the linear forms `v + r (θ − 0.5)` stay
(`super_linear_le_L` / `_ge_L`), the derived bound `θ ≤ 0.6775` stays inside its given linear
form (`super_derived_le_L`, composed by `stay_given`), and `v ≤ 0.355` stays since
`v' = 0.5 − θ − 2.5 v < 0` there (`θ ≥ 0` on the envelope). -/

theorem stay_lin_le (l : ℕ) (hl : l < 2) (r K : ℝ) (hroot : r * r - 5/2 * r + 1 = 0) (hrb : r ≤ 5/2)
    (hK : 0 ≤ K) (s : Term (Var 2)) (fR' : Fin 2 → Term (Var 2))
    (dom : Formula (Var 2)) (ν : State (Var 2))
    (hinit : Term.eval (linLe (Lv 0) (Lv 1) r (1/2) K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys (fL l) fR' s) dom)
      (fun ω => Term.eval (linLe (Lv 0) (Lv 1) r (1/2) K) ω) ν :=
  boxle_L_of_super _ (fL l) fR' _ dom dom
    (fun i h => by simp [linLe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
    (super_linear_le_L (jx := 0) (jy := 1) (a := 1) (b := 5/2) (c := 1/2) (r := r)
      hroot (by linarith) hK (fL l) dom
      (fun z _ => fL0_eval l hl z) (fun z _ => by rw [fL1_eval l hl])) hinit

theorem stay_lin_ge (l : ℕ) (hl : l < 2) (r K : ℝ) (hroot : r * r - 5/2 * r + 1 = 0) (hrb : r ≤ 5/2)
    (hK : K ≤ 0) (s : Term (Var 2)) (fR' : Fin 2 → Term (Var 2))
    (dom : Formula (Var 2)) (ν : State (Var 2))
    (hinit : Term.eval (linGe (Lv 0) (Lv 1) r (1/2) K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys (fL l) fR' s) dom)
      (fun ω => Term.eval (linGe (Lv 0) (Lv 1) r (1/2) K) ω) ν :=
  boxle_L_of_super _ (fL l) fR' _ dom dom
    (fun i h => by simp [linGe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
    (super_linear_ge_L (jx := 0) (jy := 1) (a := 1) (b := 5/2) (c := 1/2) (r := r)
      hroot (by linarith) hK (fL l) dom
      (fun z _ => fL0_eval l hl z) (fun z _ => by rw [fL1_eval l hl])) hinit

/-- `θ ≤ 0.855` inside the given linear form `v + r (θ − 0.5) ≤ K` (`r (0.6775 − 0.5) ≥ K`). -/
theorem stay_ble (l : ℕ) (hl : l < 2) (r K : ℝ) (hroot : r * r - 5/2 * r + 1 = 0) (hrb : r ≤ 5/2)
    (hr : 0 ≤ r) (hK : 0 ≤ K) (hKK : K ≤ r * (271/400 - 1/2)) (Fq : Formula (Var 2))
    (hFq : ∀ z, Formula.sat Fq z ↔ Term.eval (linLe (Lv 0) (Lv 1) r (1/2) K) z ≤ 0)
    (s : Term (Var 2)) (fR' : Fin 2 → Term (Var 2)) (dom : Formula (Var 2)) :
    ∀ ν, Term.eval (linLe (Lv 0) (Lv 1) r (1/2) K) ν ≤ 0 →
      Term.eval (thrLe (Lv 0) (271/400)) ν ≤ 0 →
      BoxLe (Program.ode (jointSys (fL l) fR' s) dom)
        (fun ω => Term.eval (thrLe (Lv 0) (271/400)) ω) ν :=
  stay_given (Fq := Fq) hFq
    (fun ν h => stay_lin_le l hl r K hroot hrb hK s fR' dom ν h)
    (fun ν h => boxle_L_of_super _ (fL l) fR' _ (Formula.and dom Fq) (Formula.and dom Fq)
      (fun i h => by simp [thrLe, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
      (super_derived_le_L (jx := 0) (jy := 1) (r := r) (c := 1/2) (K := K) (K' := 271/400)
        hr hKK (fL l) _ (fun z _ => fL0_eval l hl z)
        (fun z hz => (hFq z).mp hz.2)) h)

theorem stay_vle (l : ℕ) (hl : l < 2) (s : Term (Var 2)) (fR' : Fin 2 → Term (Var 2))
    (ν : State (Var 2)) (hinit : Term.eval (thrLe (Lv 1) (71/200)) ν ≤ 0) :
    BoxLe (Program.ode (jointSys (fL l) fR' s) (Formula.and domL domR))
      (fun ω => Term.eval (thrLe (Lv 1) (71/200)) ω) ν :=
  boxle_thrLe_L 1 (71/200) _ _ _ _ (Formula.and domL domR) (fun x h => h)
    (fun z hz hK => by
      rw [fL1_eval l hl]
      have := ((sat_domL z).mp hz.1).1
      linarith) hinit

theorem hFqle (z : State (Var 2)) : Formula.sat (hostAtomF vs 2 Side.L AqLe) z ↔
    Term.eval (linLe (Lv 0) (Lv 1) 2 (1/2) (71/200)) z ≤ 0 := by
  rw [← gL_qle]
  exact hostAtom_iff (vars := vs) (side := Side.L) (op := "<=") (Or.inl rfl) z
theorem hFkle (z : State (Var 2)) : Formula.sat (hostAtomF vs 2 Side.L AkLe) z ↔
    Term.eval (linLe (Lv 0) (Lv 1) (1/2) (1/2) (71/800)) z ≤ 0 := by
  rw [← gL_kle]
  exact hostAtom_iff (vars := vs) (side := Side.L) (op := "<=") (Or.inl rfl) z

theorem stayL (l q : ℕ) (hl : l < 2) (s : Term (Var 2)) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) s) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  interval_cases l
  · have hmq : (hostAtomF vs 2 Side.L AqLe, linLe (Lv 0) (Lv 1) 2 (1/2) (71/200)) ∈ cL 0 := by
      rw [cL_0]; simp
    have hq := (hiffL 0 (by norm_num) _ hmq ν).mp (hν _ hmq)
    rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact stay_vle 0 (by norm_num) s (fR q) ν hinit
    · exact stay_lin_le 0 (by norm_num) (1/2) (71/200) (by norm_num) (by norm_num) (by norm_num) s (fR q) _ ν
        hinit
    · exact stay_lin_ge 0 (by norm_num) (1/2) (-1/4) (by norm_num) (by norm_num) (by norm_num) s (fR q) _ ν
        hinit
    · exact stay_lin_le 0 (by norm_num) 2 (71/200) (by norm_num) (by norm_num) (by norm_num) s (fR q) _ ν hinit
    · exact stay_lin_ge 0 (by norm_num) 2 (-1) (by norm_num) (by norm_num) (by norm_num) s (fR q) _ ν hinit
    · exact stay_ble 0 (by norm_num) 2 (71/200) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) _ hFqle s (fR q) _ ν hq hinit
  · have hmk : (hostAtomF vs 2 Side.L AkLe, linLe (Lv 0) (Lv 1) (1/2) (1/2) (71/800)) ∈ cL 1 := by
      rw [cL_1]; simp
    have hk := (hiffL 1 (by norm_num) _ hmk ν).mp (hν _ hmk)
    rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact stay_lin_le 1 (by norm_num) (1/2) (71/800) (by norm_num) (by norm_num) (by norm_num) s (fR q) _ ν
        hinit
    · exact stay_lin_le 1 (by norm_num) 2 (71/200) (by norm_num) (by norm_num) (by norm_num) s (fR q) _ ν hinit
    · exact stay_ble 1 (by norm_num) (1/2) (71/800) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) _ hFkle s (fR q) _ ν hk hinit

/-- The right atoms stay along every flow of the right mode (joint, or with the left frozen):
`θ_R' = c · rate ≥ 0` raises the floors' safe side, and `Hold` is frozen. -/
theorem stayR_gen (q : ℕ) (hq : q < 4) (fL' : Fin 2 → Term (Var 2)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 2)) :
    AtomsStayC (cR q) (jointSys fL' (fR q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hr := rate_nonneg q
  interval_cases q
  · rw [cR_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 0 0 _ _ c hc D D (fun x h => h)
      (fun z _ _ => by rw [fR0_eval 0 (by norm_num)]; exact hr) hinit
  · rw [cR_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 0 (7/20) _ _ c hc D D (fun x h => h)
      (fun z _ _ => by rw [fR0_eval 1 (by norm_num)]; exact hr) hinit
  · rw [cR_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 0 (1/2) _ _ c hc D D (fun x h => h)
      (fun z _ _ => by rw [fR0_eval 2 (by norm_num)]; exact hr) hinit
  · rw [cR_3] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 (3/5) _ _ c hc D D (fun x h => h)
        (fun z _ _ => by rw [fR0_eval 3 (by norm_num)]; exact hr) hinit
    · exact boxle_thrLe_R 0 (23/20) _ _ c hc D D (fun x h => h)
        (fun z _ _ => by rw [fR0_eval 3 (by norm_num)]; simp [rate]) hinit

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 1, the row of `l`,
strata `[0]`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX arm_plateau_slow_IRv2 arm_plateau_slow_cutsV2X 2 l [0] 1 l q

/-- The reposition pack of window `l` at right mode `q` (`dynPre`: the left held at the
window's start, inside its guard). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX arm_plateau_slow_IRv2 arm_plateau_slow_cutsV2X 2 l [0] true l q

theorem row_eq (l : ℕ) (hl : l < 2) :
    (arm_plateau_slow_IRv2.invariants.getD l ("", PForm.tt)).2 =
      (arm_plateau_slow_IRv2.invariants.getD 0 ("", PForm.tt)).2 := by
  interval_cases l <;> rfl

theorem packComps (l : ℕ) (hl : l < 2) :
    ([0] : List ℕ).map (fun i => (hostComps vs 2
      (arm_plateau_slow_IRv2.invariants.getD l ("", PForm.tt)).2).getD i (Term.const 0))
      = g :: gs := by
  rw [row_eq l hl]
  rfl

theorem verd_core (l q : ℕ) (hl : l < 2) (hq : q < 4) (h : Verd l q) :
    VerdXCore (g :: gs) (fL l) (fR q) 1
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq, ← packComps l hl]
  exact h'

theorem verdD_core (l q : ℕ) (hl : l < 2) (hq : q < 4) (h : VerdD l q) :
    VerdDynCore true (g :: gs) (fR q)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) (hostGuard vs 2 Side.L (mL l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [← domL_univ l hl, ← domR_univ q hq, ← packComps l hl]
  exact h'

/-! ## The anchors of the cover's pairs -/

noncomputable def anc (l q : ℕ) : Formula (Var 2) := FM g (gs ++ atomTerms (cL l) (cR q))

theorem cL_fv (l : ℕ) (hl : l < 2) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv := by
  intro a ha
  interval_cases l
  · rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · intro x hx
      simp [thrLe, linLe, linGe, linQ, Term.fv] at hx
      rcases hx with rfl | rfl <;> simp
  · rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;>
    · intro x hx
      simp [thrLe, linLe, linGe, linQ, Term.fv] at hx
      rcases hx with rfl | rfl <;> simp

theorem cR_fv (q : ℕ) : ∀ a ∈ cR q, a.2.fv ⊆ range Rv := by
  intro a ha
  by_cases hq : q < 4
  · interval_cases q
    · rw [cR_0] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha; intro x hx; simp [thrGe, Term.fv] at hx; subst hx; simp
    · rw [cR_1] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha; intro x hx; simp [thrGe, Term.fv] at hx; subst hx; simp
    · rw [cR_2] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha; intro x hx; simp [thrGe, Term.fv] at hx; subst hx; simp
    · rw [cR_3] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;>
        subst hx <;> simp
  · rw [cR_nil q hq] at ha; simp at ha

theorem anc_fv (l q : ℕ) (hl : l < 2) : (anc l q).fv ⊆ range Lv ∪ range Rv := by
  intro x hx
  by_contra hS
  refine notMem_FM_fv (fun g' hg' hxg => hS ?_) hx
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact comps_fv _ List.mem_cons_self hxg
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact comps_fv _ (List.mem_cons_of_mem _ hg') hxg
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
  rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl (cL_fv l hl a ha hxg)
  · exact Or.inr (cR_fv q a ha hxg)

theorem anc_box (l q : ℕ) (hl : l < 2) (hq : q < 4) (hv : Verd l q) :
    ∀ σ ω, Formula.sat (anc l q) σ →
      Program.sem (Program.ode (jointSys (fL l) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX g gs (g :: gs) (cL l) (cR q) (fL l) (fR q) 1 domL domR
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl _)
    (stayR_gen q hq (fL l) 1 (by norm_num) _) (verd_core l q hl hq hv)

theorem anc_boxD (l q : ℕ) (hl : l < 2) (hq : q < 4) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vs 2 Side.L (mL l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (anc l q) ω := by
  intro σ ω h1 h2 h3
  exact couple_box_dyn true g gs (g :: gs) (cL l) (cR q) (fR q) domL domR
    (hostGuard vs 2 Side.L (mL l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fv l hl) (hguardL l hl) (stayR_gen q hq _ 1 (by norm_num) _)
    (verdD_core l q hl hq hv) σ ω h1 (fun _ => h2) h3

theorem anc_hand (l q : ℕ) (hl : l < 2) (hq : q < 4) :
    ∀ e ∈ Gr.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 4 := hlt q e he
  have hg : Formula.sat (hostGuard vs 2 Side.R (mR e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [Gr_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

theorem anc_iff (l q : ℕ) (hl : l < 2) (hq : q < 4) (x : State (Var 2)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM g gs) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem FM_fv : (FM g gs).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => hn (comps_fv c hc hvc)) hv

/-! ## The right's moves: the ramp `ApproachA → ApproachB → ApproachC → Hold`

Each approach band flows at its rate up to its ceiling, where the next band's guard starts;
`Hold` is frozen. The explicit constant-rate runs give only the runs' existence and the
switch instants. -/

/-- The explicit run of right mode `q` from `ρ`: `θ_R(t) = θ_R + rate · t`. -/
noncomputable def runΦ (q : ℕ) (ρ : State (Var 2)) : ℝ → State (Var 2) :=
  trajJ ρ 0 (fun t => ρ (Rv 0) + rate q * t)

theorem runΦ_R0 (q : ℕ) (ρ : State (Var 2)) (t : ℝ) :
    runΦ q ρ t (Rv 0) = ρ (Rv 0) + rate q * t := by simp [runΦ]

theorem run_sol (q : ℕ) (hq : q < 4) (ρ : State (Var 2)) (ε : ℝ) (hε : 0 ≤ ε)
    (hlo : 0 ≤ ρ (Rv 0)) (hhi : ρ (Rv 0) + rate q * ε ≤ 6/5) :
    ODESol (modeW q).sys (modeW q).dom ρ ε (runΦ q ρ) := by
  have hr := rate_nonneg q
  exact exists_rate_run (fR := fR q) (domR := domR) ρ 0 (rate q) (fR0_eval q hq)
    (fun i hi s => by
      match i, hi with
      | 1, _ => exact fR1_eval q hq s) ε hε
    (fun t ht hte => by
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      have : rate q * t ≤ rate q * ε := mul_le_mul_of_nonneg_left hte hr
      constructor <;> nlinarith)

theorem run_dom (q : ℕ) (hq : q < 4) (ρ : State (Var 2)) (ε : ℝ) (hε : 0 ≤ ε)
    (hlo : 0 ≤ ρ (Rv 0)) (hhi : ρ (Rv 0) + rate q * ε ≤ 6/5) :
    Formula.sat domR (runΦ q ρ ε) := by
  simpa [modeW] using (run_sol q hq ρ ε hε hlo hhi).hdom ε ⟨hε, le_rfl⟩

/-- A right state of mode `q` for window `l`: in its guard and the envelope; in the
`Accelerate` window `ApproachA` keeps flowing up to `0.5` (its joint segment continues past its
guard's ceiling `0.35`, since `ApproachB` is only a reposition node of that window). -/
def Pre (l q : ℕ) (x : State (Var 2)) : Prop :=
  q < 4 ∧ (if l = 0 ∧ q = 0 then 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1/2
    else Formula.sat (hostGuard vs 2 Side.R (mR q)) x) ∧ Formula.sat domR x

theorem pre_R (l q : ℕ) (x y : State (Var 2)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : Pre l q x) : Pre l q y := by
  obtain ⟨hq, hg, hd⟩ := h
  refine ⟨hq, ?_, ?_⟩
  · split_ifs at hg ⊢ with h0
    · rw [← hxy 0]; exact hg
    · refine (Formula.coincidence _ (fun v hv => ?_)).mp hg
      obtain ⟨i, rfl⟩ := hguardR q hq hv
      exact hxy i
  · refine (Formula.coincidence domR (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomR hv
    exact hxy i

theorem g0 (y : State (Var 2)) : Formula.sat (hostGuard vs 2 Side.R (mR 0)) y ↔
    0 ≤ y (Rv 0) ∧ y (Rv 0) ≤ 7/20 := by rw [sat_guardR 0 (by norm_num)]; simp
theorem g1 (y : State (Var 2)) : Formula.sat (hostGuard vs 2 Side.R (mR 1)) y ↔
    7/20 ≤ y (Rv 0) ∧ y (Rv 0) ≤ 1/2 := by rw [sat_guardR 1 (by norm_num)]; simp
theorem g2 (y : State (Var 2)) : Formula.sat (hostGuard vs 2 Side.R (mR 2)) y ↔
    1/2 ≤ y (Rv 0) ∧ y (Rv 0) ≤ 3/5 := by rw [sat_guardR 2 (by norm_num)]; simp
theorem g3 (y : State (Var 2)) : Formula.sat (hostGuard vs 2 Side.R (mR 3)) y ↔
    3/5 ≤ y (Rv 0) ∧ y (Rv 0) < 23/20 := by rw [sat_guardR 3 (by norm_num)]; simp

theorem pre_guard (l q : ℕ) (hq : q < 4) (x : State (Var 2)) (hn : ¬ (l = 0 ∧ q = 0))
    (hg : Formula.sat (hostGuard vs 2 Side.R (mR q)) x) (hd : Formula.sat domR x) :
    Pre l q x := ⟨hq, by rw [if_neg hn]; exact hg, hd⟩

/-- **One climbing band** `q → q + 1` (a mode other than the `Accelerate` window's
`ApproachA`). -/
theorem climb (l q : ℕ) (hq : q < 3) (hn : ¬ (l = 0 ∧ q = 0)) (hn1 : ¬ (l = 0 ∧ q + 1 = 0))
    (lo hi : ℝ) (hlo0 : 0 ≤ lo) (hhi : hi ≤ 3/5)
    (hb : ∀ y : State (Var 2), Formula.sat (hostGuard vs 2 Side.R (mR q)) y ↔
      lo ≤ y (Rv 0) ∧ y (Rv 0) ≤ hi)
    (hb' : ∀ y : State (Var 2), y (Rv 0) = hi →
      Formula.sat (hostGuard vs 2 Side.R (mR (q + 1))) y)
    (hstay : (q, q) ∈ edgeList) (hup : (q, q + 1) ∈ edgeList)
    (J : ℕ → Prop) (hJ1 : J (q + 1))
    (E : ℕ → State (Var 2) → Prop) (hE : ∀ x, Pre l q x → E q x)
    (ρ : State (Var 2)) (hpre : Pre l q ρ) (T : ℝ) (hT : 0 ≤ T) :
    (∃ Φ, ODESol (modeW q).sys (modeW q).dom ρ T Φ ∧
      ∃ e ∈ Gr.edgesFrom q, SwitchLegal e (Φ T) ∧ E e.tgt (Φ T)) ∨
    (∃ τ, 0 ≤ τ ∧ τ ≤ T ∧ ∃ Φ, ODESol (modeW q).sys (modeW q).dom ρ τ Φ ∧
      ∃ e ∈ Gr.edgesFrom q, SwitchLegal e (Φ τ) ∧ J e.tgt ∧ (fun q => q) q < (fun q => q) e.tgt ∧
        Pre l e.tgt (Φ τ)) := by
  obtain ⟨-, hg, hd⟩ := hpre
  rw [if_neg hn] at hg
  have hg' := (hb ρ).mp hg
  have hr := rate_pos q hq
  by_cases hin : ρ (Rv 0) + rate q * T ≤ hi
  · have hgT : Formula.sat (hostGuard vs 2 Side.R (mR q)) (runΦ q ρ T) := by
      refine (hb _).mpr ⟨?_, ?_⟩ <;> rw [runΦ_R0] <;> nlinarith [mul_nonneg hr.le hT]
    refine Or.inl ⟨runΦ q ρ, run_sol q (by omega) ρ T hT (by linarith [hg'.1]) (by linarith),
      edgeW q q, edge_mem q q hstay, hgT, hE _ (pre_guard l q (by omega) _ hn hgT
        (run_dom q (by omega) ρ T hT (by linarith [hg'.1]) (by linarith)))⟩
  · push Not at hin
    set τ := (hi - ρ (Rv 0)) / rate q with hτ
    have hτ0 : 0 ≤ τ := div_nonneg (by linarith [hg'.2]) hr.le
    have hτT : τ ≤ T := by rw [hτ, div_le_iff₀ hr]; linarith
    have hend : runΦ q ρ τ (Rv 0) = hi := by
      rw [runΦ_R0, hτ, mul_div_cancel₀ _ hr.ne']; ring
    have hhiτ : ρ (Rv 0) + rate q * τ ≤ 6/5 := by
      have : ρ (Rv 0) + rate q * τ = hi := by rw [← runΦ_R0]; exact hend
      linarith
    refine Or.inr ⟨τ, hτ0, hτT, runΦ q ρ, run_sol q (by omega) ρ τ hτ0 (by linarith [hg'.1]) hhiτ,
      edgeW q (q + 1), edge_mem q (q + 1) hup, hb' _ hend, hJ1, (Nat.lt_succ_self q : q < q + 1),
      pre_guard l (q + 1) (by omega) _ hn1 (hb' _ hend)
        (run_dom q (by omega) ρ τ hτ0 (by linarith [hg'.1]) hhiτ)⟩

/-- The cover's joint nodes (`Accelerate`: `ApproachA`, `ApproachC`, `Hold`, with `ApproachB` a
reposition node only; `Brake`: `ApproachB`, `ApproachC`, `Hold`, its `ApproachA` start being
inadmissible) and the reposition node. -/
def J (l q : ℕ) : Prop := q < 4 ∧ q ≠ (if l = 0 then 1 else 0)
def D (l q : ℕ) : Prop := l = 0 ∧ q = 1

theorem hmove (l : ℕ) (E : ℕ → State (Var 2) → Prop) (hE : ∀ q x, Pre l q x → E q x) :
    HMove Gr modeW (J l) (fun q => q) (Pre l) E := by
  intro q hJ ρ hpre T hT
  have hq4 : q < 4 := hJ.1
  interval_cases q
  · -- `ApproachA`: only a joint node of the `Accelerate` window
    have hl0 : l = 0 := by
      by_contra h
      exact hJ.2 (by simp [h])
    subst hl0
    obtain ⟨-, hg, hd⟩ := hpre
    simp only [and_self, if_true] at hg
    have hr : rate 0 = 1/2 := by simp [rate]
    by_cases hin : ρ (Rv 0) + rate 0 * T ≤ 1/2
    · have hdT := run_dom 0 (by norm_num) ρ T hT hg.1 (by linarith)
      have hlo : 0 ≤ runΦ 0 ρ T (Rv 0) := by rw [runΦ_R0, hr]; nlinarith [hg.1]
      have hhi : runΦ 0 ρ T (Rv 0) ≤ 1/2 := by rw [runΦ_R0]; exact hin
      by_cases h35 : runΦ 0 ρ T (Rv 0) ≤ 7/20
      · exact Or.inl ⟨runΦ 0 ρ, run_sol 0 (by norm_num) ρ T hT hg.1 (by linarith), edgeW 0 0,
          edge_mem 0 0 (by decide), (g0 _).mpr ⟨hlo, h35⟩,
          hE 0 _ ⟨by norm_num, by simp only [and_self, if_true]; exact ⟨hlo, hhi⟩, hdT⟩⟩
      · push Not at h35
        exact Or.inl ⟨runΦ 0 ρ, run_sol 0 (by norm_num) ρ T hT hg.1 (by linarith), edgeW 0 1,
          edge_mem 0 1 (by decide), (g1 _).mpr ⟨h35.le, hhi⟩,
          hE 1 _ (pre_guard 0 1 (by norm_num) _ (by simp)
            ((g1 _).mpr ⟨h35.le, hhi⟩) hdT)⟩
    · push Not at hin
      set τ := (1/2 - ρ (Rv 0)) / rate 0 with hτ
      have hτ0 : 0 ≤ τ := div_nonneg (by linarith [hg.2]) (by rw [hr]; norm_num)
      have hτT : τ ≤ T := by rw [hτ, div_le_iff₀ (by rw [hr]; norm_num)]; linarith
      have hend : runΦ 0 ρ τ (Rv 0) = 1/2 := by
        rw [runΦ_R0, hτ, mul_div_cancel₀ _ (by rw [hr]; norm_num)]; ring
      have hhiτ : ρ (Rv 0) + rate 0 * τ ≤ 6/5 := by
        have : ρ (Rv 0) + rate 0 * τ = 1/2 := by rw [← runΦ_R0]; exact hend
        linarith
      have hgC : Formula.sat (hostGuard vs 2 Side.R (mR 2)) (runΦ 0 ρ τ) := by
        rw [g2, hend]; norm_num
      exact Or.inr ⟨τ, hτ0, hτT, runΦ 0 ρ, run_sol 0 (by norm_num) ρ τ hτ0 hg.1 hhiτ,
        edgeW 0 2, edge_mem 0 2 (by decide), hgC, (show J 0 2 by unfold J; simp),
        (by show (0:ℕ) < 2; norm_num),
        pre_guard 0 2 (by norm_num) _ (by simp) hgC
          (run_dom 0 (by norm_num) ρ τ hτ0 hg.1 hhiτ)⟩
  · -- `ApproachB`: only a joint node of the `Brake` window
    have hl1 : l ≠ 0 := by
      intro h
      exact hJ.2 (by simp [h])
    exact climb l 1 (by norm_num) (by omega) (by omega) (7/20) (1/2) (by norm_num) (by norm_num)
      g1 (fun y hy => (g2 y).mpr ⟨by rw [hy], by rw [hy]; norm_num⟩) (by decide) (by decide)
      (J l) ⟨by norm_num, by split_ifs <;> norm_num⟩ E (fun x hx => hE 1 x hx) ρ hpre T hT
  · exact climb l 2 (by norm_num) (by omega) (by omega) (1/2) (3/5) (by norm_num) le_rfl
      g2 (fun y hy => (g3 y).mpr ⟨by rw [hy], by rw [hy]; norm_num⟩) (by decide) (by decide)
      (J l) ⟨by norm_num, by split_ifs <;> norm_num⟩ E (fun x hx => hE 2 x hx) ρ hpre T hT
  · -- `Hold` is frozen: the self-loop is legal at the end
    obtain ⟨-, hg, hd⟩ := hpre
    rw [if_neg (by omega)] at hg
    have hg' := (g3 ρ).mp hg
    have hr3 : rate 3 = 0 := by simp [rate]
    have hend : runΦ 3 ρ T (Rv 0) = ρ (Rv 0) := by rw [runΦ_R0, hr3]; ring
    have hgT : Formula.sat (hostGuard vs 2 Side.R (mR 3)) (runΦ 3 ρ T) := by
      rw [g3, hend]; exact hg'
    exact Or.inl ⟨runΦ 3 ρ, run_sol 3 (by norm_num) ρ T hT (by linarith [hg'.1])
      (by rw [hr3]; linarith [hg'.2]), edgeW 3 3, edge_mem 3 3 (by decide), hgT,
      hE 3 _ (pre_guard l 3 (by norm_num) _ (by omega) hgT
        (run_dom 3 (by norm_num) ρ T hT (by linarith [hg'.1]) (by rw [hr3]; linarith [hg'.2])))⟩

/-- The reposition exit of `ApproachB` (the `Accelerate` window): the right alone climbs to
`0.5` and switches into `ApproachC`, a joint node. -/
theorem hexit (l : ℕ) : HExit Gr modeW (J l) (D l) (fun q => 3 - q) (Pre l) (Pre l) := by
  intro q hD hnJ ρ hpre
  obtain ⟨rfl, rfl⟩ := hD
  obtain ⟨-, hg, hd⟩ := hpre
  rw [if_neg (by simp)] at hg
  have hg' := (g1 ρ).mp hg
  have hr : rate 1 = 7/20 := by simp [rate]
  set τ := (1/2 - ρ (Rv 0)) / rate 1 with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith [hg'.2]) (by rw [hr]; norm_num)
  have hend : runΦ 1 ρ τ (Rv 0) = 1/2 := by
    rw [runΦ_R0, hτ, mul_div_cancel₀ _ (by rw [hr]; norm_num)]; ring
  have hhiτ : ρ (Rv 0) + rate 1 * τ ≤ 6/5 := by
    have : ρ (Rv 0) + rate 1 * τ = 1/2 := by rw [← runΦ_R0]; exact hend
    linarith
  have hgC : Formula.sat (hostGuard vs 2 Side.R (mR 2)) (runΦ 1 ρ τ) := by
    rw [g2, hend]; norm_num
  refine ⟨τ, runΦ 1 ρ, run_sol 1 (by norm_num) ρ τ hτ0 (by linarith [hg'.1]) hhiτ,
    edgeW 1 2, edge_mem 1 2 (by decide), hgC, by simp [edgeW], by simp [edgeW],
    Or.inl ⟨⟨by simp [edgeW], by simp [edgeW]⟩, pre_guard 0 2 (by norm_num) _ (by simp) hgC
      (run_dom 1 (by norm_num) ρ τ hτ0 (by linarith [hg'.1]) hhiτ)⟩⟩

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem respondR (l : ℕ) (hl : l < 2) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 4) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hg : Formula.sat (hostGuard vs 2 Side.R (mR q)) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt (0 + 1))
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  have hJD : ∀ q, J l q ∨ D l q → q < 4 := by
    intro q h; rcases h with h | h
    · exact h.1
    · rw [h.2]; norm_num
  refine replay_gresp_k Gr modeW fR domR (fL l) domL (hostGuard vs 2 Side.L (mL l)) 1
    hgR (hfL l hl) hdomL hdomR (hguardL l hl) 1 one_pos (J l) (D l)
    (fun q h => hfR q (hJD q h)) (fun q => q) (fun q => 3 - q) 4 (fun q h => h.1)
    (fun q h => Gr_modeAt q (hJD q h)) (fun _ _ => rfl) (fun _ _ => rfl)
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.1 (hJv q h))
    (fun q h => anc_boxD l q hl (hJD q (Or.inr h)) (hDv q h))
    (fun q h => anc_hand l q hl (hJD q h))
    (Pre l) (Pre l) (Pre l) (pre_R l) (pre_R l)
    (hmove l _ (fun _ _ h => h)) (hexit l) dt 0 (fun h => absurd h (lt_irrefl 0)) q σ ?_
    hσ.2.1 _ ?_
  · intro hgL
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    have hpre : Pre l q σ := by
      refine ⟨hq, ?_, hσ.2.2⟩
      split_ifs with h0
      · obtain ⟨-, rfl⟩ := h0
        have := (g0 σ).mp hg
        exact ⟨this.1, by linarith [this.2]⟩
      · exact hg
    by_cases hJq : J l q
    · exact Or.inl ⟨hJq, hpre⟩
    · have hq' : q = (if l = 0 then 1 else 0) := by
        by_contra h; exact hJq ⟨hq, h⟩
      by_cases hl0 : l = 0
      · subst hl0
        simp only [if_true] at hq'
        exact Or.inr ⟨⟨rfl, hq'⟩, hJq, hpre⟩
      · -- the `Brake` window from `ApproachA` is inadmissible: the left guard, the right
        -- guard and the row contradict (`θ_L ≥ 0.5`, `θ_R ≤ 0.35`, `θ_L ≤ θ_R + 0.0775`)
        exfalso
        rw [if_neg hl0] at hq'
        subst hq'
        have hl1 : l = 1 := by omega
        subst hl1
        have hgl := (sat_guardL 1 (by norm_num) σ).mp hgL
        simp only [show (1:ℕ) ≠ 0 from by decide, if_false] at hgl
        have hgr := (g0 σ).mp hg
        have hrow := (sat_FM_iff g gs σ).mp hσ.1 g (by simp)
        rw [eval_g] at hrow
        linarith [hgl.1, hgr.2]
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domL ν :=
      windowSeg_end_domL (leftBlock (fL l)) domL tg dt (0 + 1) (by norm_num) hwin
    obtain ⟨hq', hgq, hdR⟩ := hpre
    have hA' := (anc_iff l q' hl hq' _).mp hA
    have hF : Formula.sat (FM g gs) μ := by
      refine (sat_of_agree FM_fv (fun i => ?_) (fun i => ?_)).mp hA'.1
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hdR⟩, ?_⟩
    · refine (Formula.coincidence domL (fun v hv => ?_)).mpr hdomLν
      obtain ⟨i, rfl⟩ := hdomL hv
      exact hμL i
    · split_ifs at hgq with h0
      · obtain ⟨-, rfl⟩ := h0
        rw [sat_region 0 (by norm_num)]
        exact ⟨by simpa [lowR] using hgq.1, fun h => absurd h (by norm_num)⟩
      · rw [region, sat_cutF]
        exact hO1R q' hq' μ hgq

theorem Hmulti (dt : ℝ) (hJv : ∀ l < 2, ∀ q, J l q → Verd l q)
    (hDv : ∀ l < 2, ∀ q, D l q → VerdD l q) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ →
      Formula.sat (hostGuard vs 2 Side.R (mR q)) σ →
      GResp Gr q P (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl
  · exact respondR 0 (by norm_num) dt (hJv 0 (by norm_num)) (hDv 0 (by norm_num)) q hq hσ hg
  · exact respondR 1 (by norm_num) dt (hJv 1 (by norm_num)) (hDv 1 (by norm_num)) q hq hσ hg

/-! ## Theorem 3 -/

/-- **`arm_plateau_slow` (suite_v2), modal Theorem 3 at the declared invariant, by replaying
the emitted cover** (`InstancesV2/BenchCovers/arm_plateau_slow.lean`, λ = 1). Left: the two
guard-gated PD windows; right: the four-mode reference automaton (declared edges); loop
invariant: the declared row `θ_L ≤ θ_R + 0.0775`, the evolve envelope, the right mode's guard
and region (its kept cut atoms). Response: the right keeps time with the window in the joint
nodes, climbing at the band ceilings (`Accelerate`: `ApproachA` keeps flowing to `0.5` and
switches into `ApproachC`, since `ApproachB` is only a reposition node of that window, whose
start repositions the right alone to `0.5` under the reposition pack `VerdD 0 1`; `Brake`:
`ApproachB → ApproachC → Hold`, its `ApproachA` start being contradictory), every stretch
preserved by its joint pack `Verd l q`; every switch is legal against the entered band's
guard; the explicit constant-rate runs give only the runs' existence. -/
theorem arm_plateau_slow_modal (dt : ℝ)
    (h00 : Verd 0 0) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (d01 : VerdD 0 1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g []) (envLR domL domR))
        (mvRegionR mv gregion Gr.modes.length))) := by
  have hJv : ∀ l < 2, ∀ q, J l q → Verd l q := by
    intro l hl q hJ
    obtain ⟨hq, hlq⟩ := hJ
    match l, q, hl, hq with
    | 0, 0, _, _ => exact h00
    | 0, 1, _, _ => exact absurd rfl hlq
    | 0, 2, _, _ => exact h02
    | 0, 3, _, _ => exact h03
    | 1, 0, _, _ => exact absurd rfl hlq
    | 1, 1, _, _ => exact h11
    | 1, 2, _, _ => exact h12
    | 1, 3, _, _ => exact h13
  have hDv : ∀ l < 2, ∀ q, D l q → VerdD l q := by
    intro l _ q hD
    obtain ⟨rfl, rfl⟩ := hD
    exact d01
  have hmvF : mv ∉ (FM g gs).fv := notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have hmvenv : mv ∉ env.fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 0 (hdomL h)
    · exact aux_notin_range_Rv 0 (hdomR h)
  have hmvreg0 : ∀ q, mv ∉ (region q).fv := fun q h => aux_notin_range_Rv 0 (region_fv q h)
  have hmvreg : ∀ q, mv ∉ (gregion q).fv := fun q =>
    notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) (hmvreg0 q)
  refine theorem3_faithful_multiR_LR Gr mv (FM g gs) domL domR gregion
    (leftProgs dt) (canonInvM g gs) (encode_canonInvM g gs) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgs, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL d hd).1
        (hL d hd).2.1 (hL d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub Gr _ hgR hRv hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · exact hstep_assembled_GR Gr mv (FM g gs) env gregion (leftProgs dt) hmvF hmvenv hmvreg
      hfresh (guardsFresh_of_right Gr 0 hgR) hlt (hframes dt)
      (Hmulti_regionG Gr mv _ region Gr_guards (FM g gs) env (leftProgs dt)
        (fun P hP q _ σ ν hrun => by
          simp only [leftProgs, List.mem_map] at hP
          obtain ⟨d, hd, rfl⟩ := hP
          exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL d hd).1
            (hL d hd).2.1 (hL d hd).2.2) (hguardR_all q) hrun)
        (fun P hP q hq σ hmv hσ hg _ => Hmulti dt hJv hDv P hP q hq σ hmv hσ hg))
  · exact hddF_multiR_G Gr 0 1 dt leftData gregion (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2ArmPlateauSlow
end RelCertifier
