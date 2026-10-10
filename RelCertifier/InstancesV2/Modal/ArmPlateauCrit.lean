/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_crit` (suite_v2) — modal Theorem 3 by catch-up

A critically damped PD arm (left; `θ' = v`, `v' = −(θ − 0.5) − 2v`, modes `Accelerate`,
`Brake`) tracked against a ramp-to-plateau reference (right; one variable `θ`, modes
`ApproachA/B/C` at rates 0.5, 0.35, 0.2 and `Hold` at 0), invariant `θ_L ≤ θ_R + 0.255`.

The response is the WindowGrowth CATCH-UP: the left's guard-gated window runs first; the
linear-form chain `q = v + (θ − 0.5) ≤ 0.355` (`q' = −q`) and its derived bound `θ ≤ 0.855`
hold at the window's start (the guard's arithmetic) and stay along the clocked left flow
(differential invariants through the `lie_clk_left` adapter, CutLiftX's `linearShape` /
`derivedShape` superlevel conditions); after the window the right, untouched by it, stays
in its mode and flows at its constant rate until `θ_R = θ_L − 0.255 ≤ 0.6` (or does
nothing when already there; in `Hold` its region gives `θ_R ≥ 0.6`). No verdict pack;
Z3-free.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.arm_plateau_crit

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ArmPlateauCrit

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["theta", "v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := arm_plateau_crit_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := arm_plateau_crit_IRv2.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (arm_plateau_crit_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 2)) := []

noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX arm_plateau_crit_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm1 : Run.parseRat "-1" = some (-1 : ℚ) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
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
theorem hp0855 : Run.parseRat "0.855" = some ((171:ℚ)/200) := by
  have h : parseQ "0.855" = some (⟨855, 1000⟩ : QF) := by decide
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
theorem hp0255 : Run.parseRat "0.255" = some ((51:ℚ)/200) := by
  have h : parseQ "0.255" = some (⟨255, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Evaluations of the lowered data -/

theorem fL0_eval (l : ℕ) (hl : l < 2) (x : State (Var 2)) :
    Term.eval (fL l 0) x = x (Lv 1) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, arm_plateau_crit_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hpm1,
      hpm20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]

theorem fL1_eval (l : ℕ) (hl : l < 2) (x : State (Var 2)) :
    Term.eval (fL l 1) x = -1 * (x (Lv 0) - 1/2) - 2 * x (Lv 1) := by
  interval_cases l <;>
  · simp [fL, hostDyn, mL, arm_plateau_crit_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hpm1,
      hpm20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]
    ring

/-- Right rates: ApproachA 0.5, ApproachB 0.35, ApproachC 0.2, Hold 0. -/
noncomputable def rate (q : ℕ) : ℝ :=
  if q = 0 then 1/2 else if q = 1 then 7/20 else if q = 2 then 1/5 else 0

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = rate q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, arm_plateau_crit_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp035,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, rate]

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, arm_plateau_crit_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp035,
      hp02, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_domL (x : State (Var 2)) :
    Formula.sat domL x ↔
      (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 6/5 ∧ -1 ≤ x (Lv 1) ∧ x (Lv 1) ≤ 1) := by
  simp only [domL, hostEvolve, mL, arm_plateau_crit_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp12, hpm10, hp10, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]
  tauto

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 6/5) := by
  simp only [domR, hostEvolve, mR, arm_plateau_crit_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp12, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 2) : hostEvolve vs 2 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem sat_guardL (l : ℕ) (hl : l < 2) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.L (mL l)) ν ↔
      (if l = 0 then 0 ≤ ν (Lv 0) ∧ ν (Lv 0) < 1/2 ∧ 0 ≤ ν (Lv 1) ∧ ν (Lv 1) < 71/200
       else 1/2 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ 171/200 ∧ ν (Lv 1) ≤ 0) := by
  interval_cases l <;>
    simp [hostGuard, mL, arm_plateau_crit_IRv2, Run.lowerF, Run.lowerE, hp00, hp05, hp0355,
      hp0855, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Lv] <;> tauto

theorem comps_eq : comps =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0))
      (Term.const (51/200)))] := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [comps, hostComps, arm_plateau_crit_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp0255, ITerm.toHost, Lv, Rv]

/-- The declared row has exactly one component: `gs = comps.tail`. -/
theorem gs_eq : gs = comps.tail := by rw [comps_eq]; rfl

theorem eval_g (x : State (Var 2)) : Term.eval g x = x (Lv 0) - (x (Rv 0) + 51/200) := by
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
    (by interval_cases l <;> simp [mL, arm_plateau_crit_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, arm_plateau_crit_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, arm_plateau_crit_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, arm_plateau_crit_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 2) : (hostGuard vs 2 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by interval_cases l <;>
      simp [mL, arm_plateau_crit_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

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
    ∀ x ∈ cutAtomsOfX arm_plateau_crit_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, arm_plateau_crit_cutsV2X, mR, arm_plateau_crit_IRv2] at hx
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
    simp [arm_plateau_crit_IRv2]; omega
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
  [(0, 1), (0, 0), (1, 2), (1, 1), (2, 3), (2, 2), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range arm_plateau_crit_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (arm_plateau_crit_IRv2.R.modes.findIdx (·.name == nm))))) := by
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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [edgeW, Gr]

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
    interval_cases q <;> simp [mR, arm_plateau_crit_IRv2, Parse.PForm.namesFree,
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

/-- The linear form's safe-side term: `q − 0.355` with `q = v + 1·(θ − 0.5)`. -/
noncomputable def qT : Term (Var 2) := linLe (Lv 0) (Lv 1) 1 (1/2) (71/200)
/-- The derived bound's safe-side term: `θ − 0.855`. -/
noncomputable def bT : Term (Var 2) := thrLe (Lv 0) (171/200)
noncomputable def Fq : Formula (Var 2) := Formula.cmp CompOp.le qT (Term.const 0)

theorem tg_qT : tg ∉ qT.fv := by
  simp [qT, linLe, linQ, Term.fv, Lv, Prod.ext_iff]
theorem tg_bT : tg ∉ bT.fv := by
  simp [bT, thrLe, Term.fv, Lv, Prod.ext_iff]

theorem eval_qT (x : State (Var 2)) :
    Term.eval qT x = x (Lv 1) + 1 * (x (Lv 0) - 1/2) - 71/200 := by
  simp [qT, linLe, linQ, Term.eval, AOp.interp]
theorem eval_bT (x : State (Var 2)) : Term.eval bT x = x (Lv 0) - 171/200 := by
  simp [bT, thrLe, Term.eval, AOp.interp]

theorem wf_clk (l : ℕ) : (DLCalTiming.clk tg (leftBlock (fL l))).WellFormed :=
  clk_wellFormed tg _ (leftBlock_wf _) (htg_leftBlock _)

/-- `q ≤ 0.355` stays along the clocked left flow (`q' = −q`, `linearShape`). -/
theorem boxle_qT (l : ℕ) (hl : l < 2) : ∀ ν, Term.eval qT ν ≤ 0 →
    BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
      (fun ω => Term.eval qT ω) ν := by
  intro ν hν
  refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable qT) ?_ hν
  intro x hx hge
  rw [lie_clk_left _ _ tg_qT]
  exact super_linear_le_L (jx := 0) (jy := 1) (a := 1) (b := 2) (c := 1/2) (r := 1)
    (K := 71/200) (by norm_num) (by norm_num) (by norm_num) (fL l) domL
    (fun z _ => fL0_eval l hl z) (fun z _ => by rw [fL1_eval l hl]) x hx hge

/-- `θ ≤ 0.855` stays along the clocked left flow from inside `q ≤ 0.355`
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
  exact super_derived_le_L (jx := 0) (jy := 1) (r := 1) (c := 1/2) (K := 71/200)
    (K' := 171/200) (by norm_num) (by norm_num) (fL l) (Formula.and domL Fq)
    (fun z _ => fL0_eval l hl z)
    (fun z hz => by
      have h2 := hz.2
      simpa [Fq, qT, Formula.sat, CompOp.interp, Term.eval] using h2) x hx hge

/-- **The left window's end**: from a start inside the chain (`q ≤ 0.355`, `θ ≤ 0.855`),
the window ends with `θ_L ≤ 0.855`, inside the evolve domain, the right state untouched. -/
theorem window_end (l : ℕ) (hl : l < 2) (dt : ℝ) {σ ν : State (Var 2)}
    (hsem : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν)
    (hq : Term.eval qT σ ≤ 0) (hb : Term.eval bT σ ≤ 0) :
    ν (Lv 0) ≤ 171/200 := by
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
  hostGuard_fv_R_getD vs _ dm rfl (by simp [arm_plateau_crit_IRv2, Parse.PForm.namesFree,
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

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 2)) (ψ : Formula (Var 2))
    {σ : State (Var 2)}
    (hbody : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 2))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

/-! ## The catch-up response -/

/-- **The catch-up**: after the left window, the right (untouched by it) either does
nothing (a zero-duration run of its mode, when `θ_R ≥ θ_L − 0.255` already) or flows in
its own mode at its constant rate until `θ_R = θ_L − 0.255 ≤ 0.6`. -/
theorem catchUp (l : ℕ) (hl : l < 2) (q : ℕ) (hq : q < 4) (dt : ℝ) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ) (hreg : Formula.sat (region q) σ)
    (hguard : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq [Program.ode (rightBlock (fR q) (Term.const 1)) domR])
      (Formula.and (Formula.and (FM g gs) env) (region q))) σ := by
  rw [faModal_sat]
  intro ν hleft
  obtain ⟨hq0, hb0⟩ := chain_of_guard l hl hguard
  have hθL : ν (Lv 0) ≤ 171/200 := window_end l hl dt hleft hq0 hb0
  have hRν : ν (Rv 0) = σ (Rv 0) := window_maskR l dt hleft 0
  have hdomLν : Formula.sat domL ν :=
    windowSeg_end_domL (leftBlock (fL l)) domL tg dt 1 (by norm_num) hleft
  have hdR : 0 ≤ σ (Rv 0) ∧ σ (Rv 0) ≤ 6/5 := (sat_domR σ).mp hσ.2.2
  have hdomRν : Formula.sat domR ν := by
    rw [sat_domR, hRν]; exact hdR
  have hlow := (sat_region q hq σ).mp hreg
  obtain ⟨τ, hτ0, hcatch, hgain, htop⟩ : ∃ τ : ℝ, 0 ≤ τ ∧
      ν (Lv 0) - 51/200 ≤ ν (Rv 0) + rate q * τ ∧ 0 ≤ rate q * τ ∧
      ν (Rv 0) + rate q * τ ≤ 6/5 := by
    by_cases hc : ν (Lv 0) - 51/200 ≤ ν (Rv 0)
    · exact ⟨0, le_refl _, by simpa using hc, by simp, by simp; linarith⟩
    · rw [not_le] at hc
      have hq3 : q ≠ 3 := by
        rintro rfl
        have : (3:ℝ)/5 ≤ σ (Rv 0) := by simpa [lowR] using hlow.1
        linarith
      have hrpos : 0 < rate q := by
        interval_cases q <;> first | exact absurd rfl hq3 | norm_num [rate]
      refine ⟨(ν (Lv 0) - 51/200 - ν (Rv 0)) / rate q, div_nonneg (by linarith) hrpos.le,
        ?_, ?_, ?_⟩ <;> rw [mul_div_cancel₀ _ hrpos.ne'] <;> linarith
  have hrun := sem_right_run q hq τ hτ0 hdomRν htop
  set μfin : State (Var 2) :=
    (fun x => if x = Rv 0 then ν (Rv 0) + rate q * τ else ν x) with hμfin
  have hL0 : μfin (Lv 0) = ν (Lv 0) := by
    simp [hμfin, if_neg (show (Lv 0 : Var 2) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff])]
  have hL1 : μfin (Lv 1) = ν (Lv 1) := by
    simp [hμfin, if_neg (show (Lv 1 : Var 2) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff])]
  have hR0 : μfin (Rv 0) = ν (Rv 0) + rate q * τ := by simp [hμfin]
  refine ⟨μfin, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [Program.rename_refl]
    exact ⟨μfin, hrun, by rw [bigSeq, sem_test]; exact ⟨rfl, trivial⟩⟩
  · rw [sat_FM_iff]
    intro g' hg'
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg'
    subst hg'
    rw [eval_g, hL0, hR0]
    linarith
  · refine ⟨?_, sem_ode_ends_in_domain hrun⟩
    rw [sat_domL, hL0, hL1]
    exact (sat_domL ν).mp hdomLν
  · rw [sat_region q hq, hR0, hRν]
    refine ⟨by linarith [hlow.1], fun h3 => ?_⟩
    subst h3
    have : rate 3 = 0 := by simp [rate]
    rw [this, zero_mul, add_zero]
    exact hlow.2 rfl

/-! ## The sharp end-of-window bound

The guarded response needs more than `θ_L ≤ 0.855` at the window's end: a right execution
in `ApproachA` above `0.5` has no enabled successor (both of its successors' guards end at
`0.5`), so where it lags it cannot climb, and the row must already hold. Two more links of
the chain give that bound:

* an `Accelerate` window ends with `θ_L ≤ 0.755` (`W = v + 1.5 (θ − 0.5) ≤ 0.355` stays
  inside `q ≤ 0.355`, and `θ ≤ 0.755` stays inside `W ≤ 0.355`);
* a `Brake` window ends below where it started (`v + (θ − 0.5) ≤ k` and `θ ≤ 0.5 + k`
  stay, with `k = θ_L − 0.5 ≥ 0` at the start, where `v ≤ 0`). -/

/-- `W − 0.355 = v + 1.5 (θ − 0.5) − 0.355` (safe-side term of `W ≤ 0.355`). -/
noncomputable def wT : Term (Var 2) := linLe (Lv 0) (Lv 1) (3/2) (1/2) (71/200)
noncomputable def Fw : Formula (Var 2) := Formula.cmp CompOp.le wT (Term.const 0)
/-- `θ − 0.755`. -/
noncomputable def eT : Term (Var 2) := thrLe (Lv 0) (151/200)

theorem tg_wT : tg ∉ wT.fv := by
  simp [wT, linLe, linQ, Term.fv, Lv, Prod.ext_iff]
theorem tg_eT : tg ∉ eT.fv := by
  simp [eT, thrLe, Term.fv, Lv, Prod.ext_iff]
theorem eval_wT (x : State (Var 2)) :
    Term.eval wT x = x (Lv 1) + 3/2 * (x (Lv 0) - 1/2) - 71/200 := by
  simp [wT, linLe, linQ, Term.eval, AOp.interp]
theorem eval_eT (x : State (Var 2)) : Term.eval eT x = x (Lv 0) - 151/200 := by
  simp [eT, thrLe, Term.eval, AOp.interp]

theorem sat_Fq (z : State (Var 2)) : Formula.sat Fq z ↔ Term.eval qT z ≤ 0 := by
  simp [Fq, Formula.sat, CompOp.interp, Term.eval]
theorem sat_Fw (z : State (Var 2)) : Formula.sat Fw z ↔ Term.eval wT z ≤ 0 := by
  simp [Fw, Formula.sat, CompOp.interp, Term.eval]

/-- `W ≤ 0.355` stays along the clocked left flow inside `q ≤ 0.355`. -/
theorem boxle_wT (l : ℕ) (hl : l < 2) : ∀ ν, Term.eval wT ν ≤ 0 →
    BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) (Formula.and domL Fq))
      (fun ω => Term.eval wT ω) ν := by
  intro ν hν
  refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable wT) ?_ hν
  intro x hx hge
  rw [lie_clk_left _ _ tg_wT]
  have hlie : Term.eval (lie1L wT (fL l)) x
      = Term.eval (lie1L (linQ (Lv 0) (Lv 1) (3/2) (1/2)) (fL l)) x := by
    rw [eval_lie1L, eval_lie1L]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [wT, linLe, tderiv, Term.eval, AOp.interp]
  rw [hlie, eval_lie1L_linQ 0 1, fL0_eval l hl, fL1_eval l hl]
  have hq := (sat_Fq x).mp hx.2
  rw [eval_qT] at hq
  rw [eval_wT] at hge
  linarith

/-- `θ ≤ 0.755` stays along the clocked left flow inside `W ≤ 0.355`. -/
theorem boxle_eT (l : ℕ) (hl : l < 2) : ∀ ν, Term.eval eT ν ≤ 0 →
    BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l)))
      (Formula.and (Formula.and domL Fq) Fw)) (fun ω => Term.eval eT ω) ν := by
  intro ν hν
  refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable eT) ?_ hν
  intro x hx hge
  rw [lie_clk_left _ _ tg_eT]
  exact super_derived_le_L (jx := 0) (jy := 1) (r := 3/2) (c := 1/2) (K := 71/200)
    (K' := 151/200) (by norm_num) (by norm_num) (fL l) _
    (fun z _ => fL0_eval l hl z)
    (fun z hz => by simpa [wT] using (sat_Fw z).mp hz.2) x hx hge

/-- `q ≤ k` (`k ≥ 0`) stays along the clocked left flow (`q' = −q`). -/
noncomputable def qK (k : ℝ) : Term (Var 2) := linLe (Lv 0) (Lv 1) 1 (1/2) k
noncomputable def FqK (k : ℝ) : Formula (Var 2) := Formula.cmp CompOp.le (qK k) (Term.const 0)
noncomputable def eK (k : ℝ) : Term (Var 2) := thrLe (Lv 0) (1/2 + k)

theorem tg_qK (k : ℝ) : tg ∉ (qK k).fv := by
  simp [qK, linLe, linQ, Term.fv, Lv, Prod.ext_iff]
theorem tg_eK (k : ℝ) : tg ∉ (eK k).fv := by
  simp [eK, thrLe, Term.fv, Lv, Prod.ext_iff]
theorem sat_FqK (k : ℝ) (z : State (Var 2)) :
    Formula.sat (FqK k) z ↔ Term.eval (qK k) z ≤ 0 := by
  simp [FqK, Formula.sat, CompOp.interp, Term.eval]

theorem boxle_qK (l : ℕ) (hl : l < 2) (k : ℝ) (hk : 0 ≤ k) : ∀ ν, Term.eval (qK k) ν ≤ 0 →
    BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
      (fun ω => Term.eval (qK k) ω) ν := by
  intro ν hν
  refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable (qK k)) ?_ hν
  intro x hx hge
  rw [lie_clk_left _ _ (tg_qK k)]
  exact super_linear_le_L (jx := 0) (jy := 1) (a := 1) (b := 2) (c := 1/2) (r := 1)
    (K := k) (by norm_num) (by norm_num) hk (fL l) domL
    (fun z _ => fL0_eval l hl z) (fun z _ => by rw [fL1_eval l hl]) x hx hge

theorem boxle_eK (l : ℕ) (hl : l < 2) (k : ℝ) : ∀ ν, Term.eval (eK k) ν ≤ 0 →
    BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) (Formula.and domL (FqK k)))
      (fun ω => Term.eval (eK k) ω) ν := by
  intro ν hν
  refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable (eK k)) ?_ hν
  intro x hx hge
  rw [lie_clk_left _ _ (tg_eK k)]
  exact super_derived_le_L (jx := 0) (jy := 1) (r := 1) (c := 1/2) (K := k)
    (K' := 1/2 + k) (by norm_num) (by ring_nf; rfl) (fL l) _
    (fun z _ => fL0_eval l hl z)
    (fun z hz => by simpa [qK] using (sat_FqK k z).mp hz.2) x hx hge

/-- **The sharp end of a window**: `θ_L` ends at most at `max(θ_L(start), 0.755)`. -/
theorem window_end_sharp (l : ℕ) (hl : l < 2) (dt : ℝ) {σ ν : State (Var 2)}
    (hsem : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν)
    (hg : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ) :
    ν (Lv 0) ≤ max (σ (Lv 0)) (151/200) := by
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
  have hσ₁L0 : σ₁ (Lv 0) = σ (Lv 0) := hassign.2 _ (by simp [Lv, Prod.ext_iff])
  have hσ₁L1 : σ₁ (Lv 1) = σ (Lv 1) := hassign.2 _ (by simp [Lv, Prod.ext_iff])
  rw [sat_guardL l hl] at hg
  interval_cases l
  · simp only [if_true] at hg
    obtain ⟨h1, h2, h3, h4⟩ := hg
    have hE := stay_given (Fq := Fw) (gq := wT) sat_Fw (boxle_wT 0 (by norm_num))
      (boxle_eT 0 (by norm_num))
    have hode' : Program.sem (Program.ode (DLCalTiming.clk tg (leftBlock (fL 0)))
        (Formula.and domL Fq)) σ₁ ν₀ := by
      refine sem_ode_and_of_stays _ _ _ hode ?_
      intro r Φ hr hΦ0 _ hder hmask hdom t ht
      refine (sat_Fq _).mpr (boxLe_trace (boxle_qT 0 (by norm_num) σ₁ ?_) hr hΦ0 hder hmask
        hdom t ht)
      rw [eval_qT, hσ₁L0, hσ₁L1]; linarith
    have := hE σ₁ (by rw [eval_wT, hσ₁L0, hσ₁L1]; linarith)
      (by rw [eval_eT, hσ₁L0]; linarith) ν₀ hode'
    simp only [eval_eT] at this
    exact le_trans (by linarith) (le_max_right _ _)
  · simp only [show (1:ℕ) ≠ 0 from by decide, if_false] at hg
    obtain ⟨h1, h2, h3⟩ := hg
    set k := σ (Lv 0) - 1/2 with hk
    have hE := stay_given (Fq := FqK k) (gq := qK k) (sat_FqK k)
      (boxle_qK 1 (by norm_num) k (by linarith)) (boxle_eK 1 (by norm_num) k)
    have := hE σ₁
      (by simp only [qK, linLe, eval_linQ, Term.eval, AOp.interp]; rw [hσ₁L0, hσ₁L1]; linarith)
      (by simp only [eK, thrLe, Term.eval, AOp.interp]; rw [hσ₁L0]; linarith) ν₀ hode
    simp only [eK, thrLe, Term.eval, AOp.interp] at this
    exact le_trans (by linarith) (le_max_left _ _)

/-! ## The guarded climb -/

/-- The right state with `θ_R` set to `b`. -/
noncomputable def setR (ρ : State (Var 2)) (b : ℝ) : State (Var 2) :=
  fun x => if x = Rv 0 then b else ρ x

@[simp] theorem setR_R0 (ρ : State (Var 2)) (b : ℝ) : setR ρ b (Rv 0) = b := by simp [setR]
theorem setR_ne (ρ : State (Var 2)) (b : ℝ) {x : Var 2} (hx : x ≠ Rv 0) :
    setR ρ b x = ρ x := by simp [setR, hx]
@[simp] theorem setR_L (ρ : State (Var 2)) (b : ℝ) (i : Fin 2) : setR ρ b (Lv i) = ρ (Lv i) :=
  setR_ne ρ b (by simp [Lv, Rv, Prod.ext_iff])
theorem setR_setR (ρ : State (Var 2)) (a b : ℝ) : setR (setR ρ a) b = setR ρ b := by
  funext x; by_cases hx : x = Rv 0 <;> simp [setR, hx]
theorem setR_self (ρ : State (Var 2)) : setR ρ (ρ (Rv 0)) = ρ := by
  funext x; by_cases hx : x = Rv 0 <;> simp [setR, hx]

theorem rate_pos (q : ℕ) (hq : q < 3) : 0 < rate q := by
  interval_cases q <;> norm_num [rate]

/-- One leg: a charging mode (`q < 3`) runs from `ρ` up to `θ_R = b`. -/
theorem leg (q : ℕ) (hq : q < 3) {ρ : State (Var 2)} (hdom : Formula.sat domR ρ) {b : ℝ}
    (hab : ρ (Rv 0) ≤ b) (hb : b ≤ 6/5) :
    Program.sem (Program.ode (modeW q).sys (modeW q).dom) ρ (setR ρ b) := by
  have hr := rate_pos q hq
  have h := sem_right_run q (by omega) ((b - ρ (Rv 0)) / rate q)
    (div_nonneg (by linarith) hr.le) hdom (by rw [mul_div_cancel₀ _ hr.ne']; linarith)
  have heq : (fun x => if x = Rv 0 then ρ (Rv 0) + rate q * ((b - ρ (Rv 0)) / rate q)
      else ρ x) = setR ρ b := by
    funext x
    by_cases hx : x = Rv 0
    · simp [setR, hx, mul_div_cancel₀ _ hr.ne']
    · simp [setR, hx]
  rw [heq] at h
  exact h

/-- The right guards, evaluated. -/
theorem sat_guardR (q : ℕ) (hq : q < 4) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 7/20
       else if q = 1 then 7/20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 1/2
       else if q = 2 then 1/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 3/5
       else 3/5 ≤ ν (Rv 0) ∧ ν (Rv 0) < 23/20) := by
  interval_cases q <;>
    simp [hostGuard, mR, arm_plateau_crit_IRv2, Run.lowerF, Run.lowerE, hp00, hp035, hp05, hp06, hp115, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

/-- **The guarded response.** After the left window the right either makes no step (it is
already within `0.255` of the left), or climbs from its start mode through the bands it
crosses — `ApproachA` up to `0.35`, the switch into `ApproachB` (legal: `0.35 ∈ [0.35, 0.5]`),
`ApproachB` up to the target `θ_L − 0.255` — and switches at the target into the mode whose
band contains it. The sharp end bound makes the target at most `0.5` whenever the right lags,
so `ApproachA` above `0.5` (no enabled successor) never has to move, and the climb never
needs `ApproachC`. Every switch is legal by the explicit end state of its leg. -/
theorem respondG (l : ℕ) (hl : l < 2) (q : ℕ) (hq : q < 4) (dt : ℝ) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ) (hreg : Formula.sat (region q) σ)
    (hguard : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ) :
    GResp Gr q (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro ν hleft
  have hθL : ν (Lv 0) ≤ max (σ (Lv 0)) (151/200) := window_end_sharp l hl dt hleft hguard
  have hRν : ν (Rv 0) = σ (Rv 0) := window_maskR l dt hleft 0
  have hdomLν : Formula.sat domL ν :=
    windowSeg_end_domL (leftBlock (fL l)) domL tg dt 1 (by norm_num) hleft
  have hdR : 0 ≤ σ (Rv 0) ∧ σ (Rv 0) ≤ 6/5 := (sat_domR σ).mp hσ.2.2
  have hdomRν : Formula.sat domR ν := by rw [sat_domR, hRν]; exact hdR
  have hlow := (sat_region q hq σ).mp hreg
  have hrow : σ (Lv 0) ≤ σ (Rv 0) + 51/200 := by
    have := (sat_FM_iff g gs σ).mp hσ.1 g List.mem_cons_self
    rw [eval_g] at this; linarith
  -- the loop postcondition at `setR ν b`
  have postAt : ∀ qf, qf < 4 → ∀ b : ℝ, ν (Lv 0) - 51/200 ≤ b → 0 ≤ b → b ≤ 6/5 →
      lowR qf ≤ b → (qf = 3 → b ≤ 23/20) →
      Formula.sat (Formula.and (Formula.and (FM g gs) env) (region qf)) (setR ν b) := by
    intro qf hqf b h1 h2 h3 h4 h5
    refine ⟨⟨?_, ?_, (sat_domR _).mpr (by simp; exact ⟨h2, h3⟩)⟩,
      (sat_region qf hqf _).mpr (by simp; exact ⟨h4, h5⟩)⟩
    · rw [sat_FM_iff]
      intro g' hg'
      simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg'
      subst hg'
      rw [eval_g]; simp; linarith
    · rw [sat_domL]; simp; exact (sat_domL ν).mp hdomLν
  have guardAt : ∀ t, t < 4 → ∀ b : ℝ,
      (if t = 0 then 0 ≤ b ∧ b ≤ 7/20
       else if t = 1 then 7/20 ≤ b ∧ b ≤ 1/2
       else if t = 2 then 1/2 ≤ b ∧ b ≤ 3/5 else 3/5 ≤ b ∧ b < 23/20) →
      ∀ s, SwitchLegal (edgeW s t) (setR ν b) := by
    intro t ht b hb s
    show Formula.sat (hostGuard vs 2 Side.R (mR t)) (setR ν b)
    rw [sat_guardR t ht]; simpa using hb
  by_cases hc : ν (Lv 0) - 51/200 ≤ ν (Rv 0)
  · -- no step
    refine ⟨[], by simp, by simp, by simp, ν, ?_, ?_⟩
    · show Program.sem (Program.test Formula.tt) ν ν
      exact ⟨rfl, trivial⟩
    · have := postAt q hq (ν (Rv 0)) hc (by rw [hRν]; exact hdR.1) (by rw [hRν]; exact hdR.2)
        (by rw [hRν]; exact hlow.1) (fun h3 => by rw [hRν]; exact hlow.2 h3)
      rw [setR_self] at this
      simpa [qfOf] using this
  -- the right lags: the target is at most 0.5
  replace hc := not_le.mp hc
  set T := ν (Lv 0) - 51/200 with hTdef
  have hT : T ≤ 1/2 := by
    rcases le_total (σ (Lv 0)) (151/200) with h | h
    · rw [max_eq_right h] at hθL; linarith
    · rw [max_eq_left h] at hθL; rw [hRν] at hc; linarith
  have hseg1 : ∀ (s : ℕ × RMode (Var 2) × REdge (Var 2)) (ρ κ : State (Var 2)),
      Program.sem (Program.ode s.2.1.sys s.2.1.dom) ρ κ → SwitchLegal s.2.2 κ →
      Program.sem (bigSeq ([s].map gseg)) ρ κ := by
    intro s ρ κ h1 h2
    exact ⟨κ, sem_gseg.mpr ⟨h1, h2⟩, rfl, trivial⟩
  interval_cases q
  · -- `ApproachA`
    by_cases hT35 : T ≤ 7/20
    · refine ⟨[(0, modeW 0, edgeW 0 0)], ?_, by simp, by simp, setR ν T, ?_, ?_⟩
      · intro s hs; rw [List.mem_singleton] at hs; subst hs
        exact ⟨Gr_modeAt 0 (by norm_num), edge_mem 0 0 (by decide)⟩
      · exact hseg1 _ _ _ (leg 0 (by norm_num) hdomRν (by linarith) (by linarith))
          (guardAt 0 (by norm_num) T (by simp; constructor <;> linarith [hlow.1]) 0)
      · simpa [qfOf, edgeW] using postAt 0 (by norm_num) T le_rfl (by linarith [hlow.1])
          (by linarith) (by simp [lowR]; linarith [hlow.1]) (by norm_num)
    · replace hT35 := not_le.mp hT35
      -- `ApproachA` up to `max(θ₀, 0.35)` (zero time if already above), the switch into
      -- `ApproachB`, `ApproachB` up to the target
      set a := max (ν (Rv 0)) (7/20) with ha
      have ha1 : ν (Rv 0) ≤ a := le_max_left _ _
      have ha2 : 7/20 ≤ a := le_max_right _ _
      have ha3 : a ≤ T := max_le (le_of_lt hc) (le_of_lt hT35)
      refine ⟨[(0, modeW 0, edgeW 0 1), (1, modeW 1, edgeW 1 1)], ?_, ?_, by simp,
        setR ν T, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨Gr_modeAt 0 (by norm_num), edge_mem 0 1 (by decide)⟩
        · exact ⟨Gr_modeAt 1 (by norm_num), edge_mem 1 1 (by decide)⟩
      · simp [edgeW]
      · refine ⟨setR ν a, sem_gseg.mpr ⟨leg 0 (by norm_num) hdomRν ha1 (by linarith),
          guardAt 1 (by norm_num) a (by simp; constructor <;> linarith) 0⟩, ?_⟩
        have hdoma : Formula.sat domR (setR ν a) := (sat_domR _).mpr (by simp; constructor <;> linarith)
        have h2 := leg 1 (by norm_num) hdoma (b := T) (by simp; exact ha3) (by linarith)
        rw [setR_setR] at h2
        exact hseg1 (1, modeW 1, edgeW 1 1) _ _ h2
          (guardAt 1 (by norm_num) T (by simp; constructor <;> linarith) 1)
      · simpa [qfOf, edgeW] using postAt 1 (by norm_num) T le_rfl (by linarith)
          (by linarith) (by simp [lowR]; linarith) (by norm_num)
  · -- `ApproachB`
    refine ⟨[(1, modeW 1, edgeW 1 1)], ?_, by simp, by simp, setR ν T, ?_, ?_⟩
    · intro s hs; rw [List.mem_singleton] at hs; subst hs
      exact ⟨Gr_modeAt 1 (by norm_num), edge_mem 1 1 (by decide)⟩
    · have hl1 : (7:ℝ)/20 ≤ σ (Rv 0) := by simpa [lowR] using hlow.1
      exact hseg1 _ _ _ (leg 1 (by norm_num) hdomRν (by linarith) (by linarith))
        (guardAt 1 (by norm_num) T (by simp; constructor <;> linarith) 1)
    · have hl1 : (7:ℝ)/20 ≤ σ (Rv 0) := by simpa [lowR] using hlow.1
      simpa [qfOf, edgeW] using postAt 1 (by norm_num) T le_rfl (by linarith)
        (by linarith) (by simp [lowR]; linarith) (by norm_num)
  · -- `ApproachC`: the right is at least at 0.5, the target at most there
    have : (1:ℝ)/2 ≤ σ (Rv 0) := by simpa [lowR] using hlow.1
    exfalso; rw [hRν] at hc; linarith
  · -- `Hold`
    have : (3:ℝ)/5 ≤ σ (Rv 0) := by simpa [lowR] using hlow.1
    exfalso; rw [hRν] at hc; linarith

theorem Hmulti (dt : ℝ) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ → Formula.sat (region q) σ →
      GResp Gr q P (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl
  · exact gresp_gate (fun hguard => respondG 0 (by norm_num) q hq dt hσ hreg hguard)
  · exact gresp_gate (fun hguard => respondG 1 (by norm_num) q hq dt hσ hreg hguard)

/-! ## Theorem 3 -/

/-- **`arm_plateau_crit` (suite_v2), modal Theorem 3 at the declared invariant**, by
CATCH-UP. Left: the two guard-gated PD windows (`Accelerate`, `Brake`; each entered inside
its guard); right: the four-mode reference automaton of the file (declared edges); the loop
invariant is the declared row `θ_L ≤ θ_R + 0.255`, the evolve envelope, and the right mode's
region (its kept cut atoms: `θ_R ≥ 0`, `≥ 0.35`, `≥ 0.5`, `∈ [0.6, 1.15]`). The response
lets the left window run first; the linear-form chain (`q = v + (θ − 0.5) ≤ 0.355`, then
`θ ≤ 0.855`, both entered from the guard and kept along the clocked left flow by DI) caps
`θ_L ≤ 0.855` at the window's end; the right then stays in its mode and catches up at its
constant rate to `θ_L − 0.255 ≤ 0.6` (never needed in `Hold`, whose region has
`θ_R ≥ 0.6`). No verdict hypotheses. -/
theorem arm_plateau_crit_modal (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g []) (envLR domL domR))
        (mvRegionR mv gregion Gr.modes.length))) := by
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
        (fun P hP q hq σ hmv hσ _ hreg => (Hmulti dt) P hP q hq σ hmv hσ hreg))
  · exact hddF_multiR_G Gr 0 1 dt leftData gregion (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2ArmPlateauCrit
end RelCertifier
