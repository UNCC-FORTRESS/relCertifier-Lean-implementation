/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_lag` (suite_v2) — modal Theorem 3

Adapted from `InstancesV2/Modal/Watertank.lean` (same generic layer, same structure). The
left `CRUISE` mode is the lagged second-order pair `v' = a`, `a' = −3 (v − 30) − 4 a`; its
kept cut atoms are the extended certificate's LINEAR-FORM CUT CHAIN (kinds `linearForm` and
`derivedBound`), lifted here by the generic O1/O2 lemmas of
`Proofs/Soundness/CutLiftX.lean`. Lowered at `n = 2` (`v` at coordinate 0, `a` at 1), so
`mv = (Aux, 0)` and `tg = (Aux, 1)` exist without padding.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.acc_tune_lag

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccTuneLag

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["v", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := acc_tune_lag_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := acc_tune_lag_IRv2.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (acc_tune_lag_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
abbrev gs : List (Term (Var 2)) := []

noncomputable def cL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.L (cutAtomsOfX acc_tune_lag_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX acc_tune_lag_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm100 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp160 : Run.parseRat "16.0" = some (16 : ℚ) := by
  have h : parseQ "16.0" = some (⟨160, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp3 : Run.parseRat "3" = some (3 : ℚ) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp30 : Run.parseRat "30" = some (30 : ℚ) := by
  have h : parseQ "30" = some (⟨30, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp2 : Run.parseRat "2" = some (2 : ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm7 : Run.parseRat "-7" = some (-7 : ℚ) := by
  have h : parseQ "-7" = some (⟨-7, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm17 : Run.parseRat "-17" = some (-17 : ℚ) := by
  have h : parseQ "-17" = some (⟨-17, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp32 : Run.parseRat "32" = some (32 : ℚ) := by
  have h : parseQ "32" = some (⟨32, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp23 : Run.parseRat "23" = some (23 : ℚ) := by
  have h : parseQ "23" = some (⟨23, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Evaluations -/

theorem fL0_eval (x : State (Var 2)) : Term.eval (fL 0 0) x = x (Lv 1) := by
  simp [fL, hostDyn, mL, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp40, hp075, hp300,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]

theorem fL1_eval (x : State (Var 2)) :
    Term.eval (fL 0 1) x = -3 * (x (Lv 0) - 30) - 4 * x (Lv 1) := by
  simp [fL, hostDyn, mL, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp40, hp075, hp300,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]
  ring

theorem fR0_eval (x : State (Var 2)) : Term.eval (fR 0 0) x = 1/2 * (30 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hp0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR1_eval (x : State (Var 2)) : Term.eval (fR 0 1) x = 0 := by
  simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hp0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 40) ∧ (-10 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 10) := by
  simp only [domR, hostEvolve, mR, acc_tune_lag_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp400, hpm100, hp100, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  tauto

theorem domR_univ (q : ℕ) (hq : q < 2) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem comps_eq : comps =
    [Term.binop .sub
      (Term.binop .add (Term.var (Lv 1)) (Term.binop .mul (Term.const 4) (Term.var (Lv 0))))
      (Term.binop .add (Term.binop .mul (Term.const 4) (Term.var (Rv 0))) (Term.const 16))] := by
  have hdLv : ("L_v".drop 2).copy = "v" := by decide
  have hdLa : ("L_a".drop 2).copy = "a" := by decide
  have hdRv : ("R_v".drop 2).copy = "v" := by decide
  simp [comps, hostComps, acc_tune_lag_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdLv, hdLa, hdRv, List.findIdx?_cons, hp40, hp160, ITerm.toHost,
    Lv, Rv]

theorem eval_g (x : State (Var 2)) :
    Term.eval g x = x (Lv 1) + 4 * x (Lv 0) - (4 * x (Rv 0) + 16) := by
  simp [g, comps_eq, Term.eval, AOp.interp]

/-! ## The cut families -/

theorem gL_q1le : hostAtomG vs 2 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1")
    (.bin "-" (.var "v") (.num "30")))) (.num "2")) = linLe (Lv 0) (Lv 1) 1 30 2 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp1, hp30, hp2, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linLe, linQ, Lv]
theorem gL_q1ge : hostAtomG vs 2 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1")
    (.bin "-" (.var "v") (.num "30")))) (.num "-7")) = linGe (Lv 0) (Lv 1) 1 30 (-7) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp1, hp30, hpm7, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linGe, linQ, Lv]
theorem gL_q3le : hostAtomG vs 2 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "3")
    (.bin "-" (.var "v") (.num "30")))) (.num "2")) = linLe (Lv 0) (Lv 1) 3 30 2 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp3, hp30, hp2, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linLe, linQ, Lv]
theorem gL_q3ge : hostAtomG vs 2 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "3")
    (.bin "-" (.var "v") (.num "30")))) (.num "-17")) = linGe (Lv 0) (Lv 1) 3 30 (-17) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp3, hp30, hpm17, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linGe, linQ, Lv]
theorem gL_vle : hostAtomG vs 2 Side.L (.cmp "<=" (.var "v") (.num "32")) = thrLe (Lv 0) 32 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp32, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_vge : hostAtomG vs 2 Side.L (.cmp ">=" (.var "v") (.num "23")) = thrGe (Lv 0) 23 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp23, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gR_ge20 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "v") (.num "20.0"))
    = thrGe (Rv 0) 20 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp200, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_le40 : hostAtomG vs 2 Side.R (.cmp "<=" (.var "v") (.num "40.0"))
    = thrLe (Rv 0) 40 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp400, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]


/-- The kept left atoms of `CRUISE`, as parsed (the extended certificate's payloads). -/
def A1le : PForm := .cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1")
  (.bin "-" (.var "v") (.num "30")))) (.num "2")
def A1ge : PForm := .cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1")
  (.bin "-" (.var "v") (.num "30")))) (.num "-7")
def A3le : PForm := .cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "3")
  (.bin "-" (.var "v") (.num "30")))) (.num "2")
def A3ge : PForm := .cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "3")
  (.bin "-" (.var "v") (.num "30")))) (.num "-17")
def Avle : PForm := .cmp "<=" (.var "v") (.num "32")
def Avge : PForm := .cmp ">=" (.var "v") (.num "23")

theorem cL_0 : cL 0 =
    [(hostAtomF vs 2 Side.L A1le, linLe (Lv 0) (Lv 1) 1 30 2),
     (hostAtomF vs 2 Side.L A1ge, linGe (Lv 0) (Lv 1) 1 30 (-7)),
     (hostAtomF vs 2 Side.L A3le, linLe (Lv 0) (Lv 1) 3 30 2),
     (hostAtomF vs 2 Side.L A3ge, linGe (Lv 0) (Lv 1) 3 30 (-17)),
     (hostAtomF vs 2 Side.L Avle, thrLe (Lv 0) 32),
     (hostAtomF vs 2 Side.L Avge, thrGe (Lv 0) 23)] := by
  rw [← gL_q1le, ← gL_q1ge, ← gL_q3le, ← gL_q3ge, ← gL_vle, ← gL_vge]; rfl
theorem cR_0 : cR 0 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "v") (.num "20.0")), thrGe (Rv 0) 20),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "v") (.num "40.0")), thrLe (Rv 0) 40)] := by
  rw [← gR_ge20, ← gR_le40]; rfl

theorem atomsNonstrictL :
    ∀ x ∈ cutAtomsOfX acc_tune_lag_cutsV2X.L (mL 0).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  simp [cutAtomsOfX, acc_tune_lag_cutsV2X, mL, acc_tune_lag_IRv2] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR :
    ∀ x ∈ cutAtomsOfX acc_tune_lag_cutsV2X.R (mR 0).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  simp [cutAtomsOfX, acc_tune_lag_cutsV2X, mR, acc_tune_lag_IRv2] at hx
  rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL : AtomsIff (cL 0) := atomsIff_cutPairsX atomsNonstrictL
theorem hiffR : AtomsIff (cR 0) := atomsIff_cutPairsX atomsNonstrictR

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked;
the linear-form atoms' rational entry is `CutLiftX.entry_linear`) -/

theorem hO1L : ∀ ν, Formula.sat (hostGuard vs 2 Side.L (mL 0)) ν → CutSat (cL 0) ν := by
  intro ν hν
  refine cutSatL_of_guard acc_tune_lag_cutsV2X_wf (mL 0) rfl ?_ ?_ ?_ ν hν
  · intro x hx
    simp [cutAtomsOfX, acc_tune_lag_cutsV2X, mL, acc_tune_lag_IRv2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x hx
    simp [cutAtomsOfX, acc_tune_lag_cutsV2X, mL, acc_tune_lag_IRv2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Run.lowerF, Run.lowerE, hp1, hp3, hp30, hp2, hpm7, hpm17, hp32, hp23, vs,
        Run.resolveVar, List.findIdx?_cons]
  · simp [mL, acc_tune_lag_IRv2, Run.lowerF, Run.lowerE, hp250, hp300, hpm20, hp20, vs,
      Run.resolveVar, List.findIdx?_cons]

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

theorem hfL : ∀ i, (fL 0 i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, acc_tune_lag_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe 0 i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 2) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, acc_tune_lag_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, acc_tune_lag_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, acc_tune_lag_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL : (hostGuard vs 2 Side.L (mL 0)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL 0).guard
    (by simp [mL, acc_tune_lag_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, comps_eq, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  subst hc
  intro x hx
  simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false, false_or] at hx
  rcases hx with (rfl | rfl) | rfl <;> simp

theorem lin_fv (r c K : ℝ) : (linLe (Lv (0 : Fin 2)) (Lv 1) r c K).fv ⊆ range Lv ∪ range Rv ∧
    (linGe (Lv (0 : Fin 2)) (Lv 1) r c K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [linLe, linGe, linQ, Term.fv] at hx <;>
    rcases hx with rfl | rfl <;> simp
theorem thr_fv_L (j : Fin 2) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 2) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv : ∀ c ∈ g :: gs ++ atomTerms (cL 0) (cR 0), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, cL_0, cR_0, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact (lin_fv _ _ _).1 | exact (lin_fv _ _ _).2 | exact (thr_fv_L _ _).1 |
      exact (thr_fv_L _ _).2 | exact (thr_fv_R _ _).1 | exact (thr_fv_R _ _).2

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CRUISE 0, DISENGAGE 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range acc_tune_lag_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (acc_tune_lag_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 2 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp [edgeW, Gr]

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

theorem hguardR (q : ℕ) (hq : q < 2) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R vs (mR q) (by
    interval_cases q <;> simp [mR, acc_tune_lag_IRv2, Parse.PForm.namesFree,
      Parse.PExpr.namesFree])

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 2 := by decide

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

/-- `CRUISE`'s guard, evaluated (`20 ≤ v < 40`). -/
theorem sat_guardR0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) < 40 := by
  simp [hostGuard, mR, acc_tune_lag_IRv2, Run.lowerF, Run.lowerE, hp200, hp400, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem rb_mem :
    (Rv 0, Term.binop .mul (Term.const 1) (fR 0 0)) ∈ rightBlock (fR 0) (Term.const 1) :=
  List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-! ## Regions: `CRUISE`'s kept cut atoms; the pruned sink `DISENGAGE` is excluded -/

noncomputable def region (q : ℕ) : Formula (Var 2) :=
  if q < 1 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region0 (ν : State (Var 2)) : Formula.sat (region 0) ν ↔ CutSat (cR 0) ν := by
  simp only [region, show (0:ℕ) < 1 from by norm_num, if_true, sat_cutF]

theorem not_sat_region1 (ν : State (Var 2)) : ¬ Formula.sat (region 1) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) (hq : q < 2) : (region q).fv ⊆ range Rv := by
  by_cases h1 : q < 1
  · have hq0 : q = 0 := by omega
    subst hq0
    simp only [region, h1, if_true]
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
    refine key (cR 0) Formula.tt (by simp [Formula.fv]) ?_ hx
    intro a ha y hy
    simp only [cR_0, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h1, if_false]
    simp [Formula.fv, Term.fv]

/-! ## The stretch of the left window (the emitted cover's λ) -/

noncomputable abbrev lam : ℝ := 5/4

theorem lam_pos : 0 < lam := by norm_num

/-! ## O2, left: the linear-form cut chain stays along the joint flow (`CutLiftX`)

`CRUISE`'s field is the second-order pair `v' = a`, `a' = −3 (v − 30) − 4 a`
(`a_coef = 3`, `b = 4`, `c = 30`; roots `r = 1, 3` of `r² − 4 r + 3 = 0`). Round 1: the
linear forms `q_r = a + r (v − 30)` (`super_linear_le_L` / `_ge_L`); round 2: the derived
bounds `v ≤ 32` given `q_1 ≤ 2` and `v ≥ 23` given `q_1 ≥ −7` (`super_derived_le_L` /
`_ge_L` over the domain narrowed by the given atom, composed by `stay_given`). -/

theorem hfxL (D : Formula (Var 2)) : ∀ z, Formula.sat D z → Term.eval (fL 0 0) z = z (Lv 1) :=
  fun z _ => fL0_eval z
theorem hfyL (D : Formula (Var 2)) : ∀ z, Formula.sat D z →
    Term.eval (fL 0 1) z = -3 * (z (Lv 0) - 30) - 4 * z (Lv 1) :=
  fun z _ => fL1_eval z

theorem stay_linLe (r K : ℝ) (hroot : r * r - 4 * r + 3 = 0) (hσ : 0 ≤ 4 - r) (hK : 0 ≤ K)
    (dom : Formula (Var 2)) (ν : State (Var 2))
    (hinit : Term.eval (linLe (Lv 0) (Lv 1) r 30 K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys (fL 0) (fR 0) (Term.const lam)) dom)
      (fun ω => Term.eval (linLe (Lv 0) (Lv 1) r 30 K) ω) ν :=
  boxle_L_of_super _ (fL 0) (fR 0) _ dom dom
    (fun i h => by simp [linLe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
    (super_linear_le_L (a := 3) (b := 4) hroot hσ hK (fL 0) dom (hfxL dom) (hfyL dom)) hinit

theorem stay_linGe (r K : ℝ) (hroot : r * r - 4 * r + 3 = 0) (hσ : 0 ≤ 4 - r) (hK : K ≤ 0)
    (dom : Formula (Var 2)) (ν : State (Var 2))
    (hinit : Term.eval (linGe (Lv 0) (Lv 1) r 30 K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys (fL 0) (fR 0) (Term.const lam)) dom)
      (fun ω => Term.eval (linGe (Lv 0) (Lv 1) r 30 K) ω) ν :=
  boxle_L_of_super _ (fL 0) (fR 0) _ dom dom
    (fun i h => by simp [linGe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
    (super_linear_ge_L (a := 3) (b := 4) hroot hσ hK (fL 0) dom (hfxL dom) (hfyL dom)) hinit

theorem hF1le (z : State (Var 2)) : Formula.sat (hostAtomF vs 2 Side.L A1le) z ↔
    Term.eval (linLe (Lv 0) (Lv 1) 1 30 2) z ≤ 0 := by
  rw [← gL_q1le]; exact hostAtom_iff (Or.inl rfl) z
theorem hF1ge (z : State (Var 2)) : Formula.sat (hostAtomF vs 2 Side.L A1ge) z ↔
    Term.eval (linGe (Lv 0) (Lv 1) 1 30 (-7)) z ≤ 0 := by
  rw [← gL_q1ge]; exact hostAtom_iff (Or.inr rfl) z

/-- `v ≤ 32` given `q_1 = a + (v − 30) ≤ 2` (stratified: round 2 inside round 1). -/
theorem stay_vle (dom : Formula (Var 2)) :
    ∀ ν, Term.eval (linLe (Lv 0) (Lv 1) 1 30 2) ν ≤ 0 → Term.eval (thrLe (Lv 0) 32) ν ≤ 0 →
      BoxLe (Program.ode (jointSys (fL 0) (fR 0) (Term.const lam)) dom)
        (fun ω => Term.eval (thrLe (Lv 0) 32) ω) ν :=
  stay_given (Fq := hostAtomF vs 2 Side.L A1le) hF1le
    (fun ν h => stay_linLe 1 2 (by norm_num) (by norm_num) (by norm_num) dom ν h)
    (fun ν h => boxle_L_of_super _ (fL 0) (fR 0) _
      (Formula.and dom (hostAtomF vs 2 Side.L A1le)) (Formula.and dom (hostAtomF vs 2 Side.L A1le))
      (fun i h => by simp [thrLe, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
      (super_derived_le_L (jx := 0) (jy := 1) (r := 1) (c := 30) (K := 2) (K' := 32)
        (by norm_num) (by norm_num) (fL 0) _ (hfxL _) (fun z hz => (hF1le z).mp hz.2)) h)

/-- `v ≥ 23` given `q_1 = a + (v − 30) ≥ −7`. -/
theorem stay_vge (dom : Formula (Var 2)) :
    ∀ ν, Term.eval (linGe (Lv 0) (Lv 1) 1 30 (-7)) ν ≤ 0 → Term.eval (thrGe (Lv 0) 23) ν ≤ 0 →
      BoxLe (Program.ode (jointSys (fL 0) (fR 0) (Term.const lam)) dom)
        (fun ω => Term.eval (thrGe (Lv 0) 23) ω) ν :=
  stay_given (Fq := hostAtomF vs 2 Side.L A1ge) hF1ge
    (fun ν h => stay_linGe 1 (-7) (by norm_num) (by norm_num) (by norm_num) dom ν h)
    (fun ν h => boxle_L_of_super _ (fL 0) (fR 0) _
      (Formula.and dom (hostAtomF vs 2 Side.L A1ge)) (Formula.and dom (hostAtomF vs 2 Side.L A1ge))
      (fun i h => by simp [thrGe, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
      (super_derived_ge_L (jx := 0) (jy := 1) (r := 1) (c := 30) (K := -7) (K' := 23)
        (by norm_num) (by norm_num) (fL 0) _ (hfxL _) (fun z hz => (hF1ge z).mp hz.2)) h)

theorem stayL :
    AtomsStayC (cL 0) (jointSys (fL 0) (fR 0) (Term.const lam)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL a ha ν).mp (hν a ha)
  have hm1 : (hostAtomF vs 2 Side.L A1le, linLe (Lv 0) (Lv 1) 1 30 2) ∈ cL 0 := by
    rw [cL_0]; exact List.mem_cons_self
  have hm2 : (hostAtomF vs 2 Side.L A1ge, linGe (Lv 0) (Lv 1) 1 30 (-7)) ∈ cL 0 := by
    rw [cL_0]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hq1le := (hiffL _ hm1 ν).mp (hν _ hm1)
  have hq1ge := (hiffL _ hm2 ν).mp (hν _ hm2)
  rw [cL_0] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact stay_linLe 1 2 (by norm_num) (by norm_num) (by norm_num) _ ν hinit
  · exact stay_linGe 1 (-7) (by norm_num) (by norm_num) (by norm_num) _ ν hinit
  · exact stay_linLe 3 2 (by norm_num) (by norm_num) (by norm_num) _ ν hinit
  · exact stay_linGe 3 (-17) (by norm_num) (by norm_num) (by norm_num) _ ν hinit
  · exact stay_vle _ ν hq1le hinit
  · exact stay_vge _ ν hq1ge hinit

/-! ## O2, right: `CRUISE` contracts toward 30, so `v_R ∈ [20, 40]` stays -/

theorem stayR :
    AtomsStayC (cR 0) (jointSys (fL 0) (fR 0) (Term.const lam)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR a ha ν).mp (hν a ha)
  have hc := le_of_lt lam_pos
  rw [cR_0] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 0 20 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fR0_eval]; linarith) hinit
  · exact boxle_thrLe_R 0 40 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fR0_eval]; linarith) hinit

/-! ## Existence: right `CRUISE` contracts `v` toward 30 inside `[0, 40]`, `a` frozen -/

/-- `WellFormedFlowB_contract` over a two-coordinate band: the contracted coordinate `j`
stays in its band (equilibrium interior), the frozen coordinate `j'` keeps its value
(`contractΦ_other`). -/
theorem wfB_contract_band2 (j j' : Fin 2) (hjj : j' ≠ j) (k c lo hi alo ahi dt : ℝ)
    (hk : 0 ≤ k) (hcl : lo ≤ c) (hch : c ≤ hi) :
    WellFormedFlowB (contractF j k c) (Term.const 1)
      (Formula.and (bandDom j lo hi) (bandDom j' alo ahi)) dt := by
  intro base hb s hs _
  have hne : (Rv j' : Var 2) ≠ Rv j := fun hc => hjj (by simpa [Rv, Prod.ext_iff] using hc)
  refine ⟨contractΦ j k c base, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases hx : x = Rv j
    · subst hx; simp [contractΦ]
    · exact contractΦ_other j k c base 0 hx
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = j
    · subst hij
      have hd := (contractΦ_hasDeriv i k c base t).hasDerivWithinAt (s := Icc 0 s)
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (contractF i k c i))
          (contractΦ i k c base t) = k * (c - contractΦ i k c base t (Rv i)) := by
        simp [contractF, Term.eval, AOp.interp]
      rw [heval]
      exact hd
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (contractF j k c i))
          (contractΦ j k c base t) = 0 := by
        simp [contractF, hij, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => contractΦ j k c base u (Rv i)) = fun _ => base (Rv i) := by
        funext u
        exact contractΦ_other j k c base u
          (fun hc => hij (by simpa [Rv, Prod.ext_iff] using hc))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have hxj : x ≠ Rv j := by
      intro hc; subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    exact contractΦ_other j k c base t hxj
  · intro t ht
    refine ⟨contract_stays j k c lo hi hk hcl hch base hb.1 t ht.1, ?_⟩
    have h2 := hb.2
    simp only [bandDom, Formula.sat, CompOp.interp, Term.eval] at h2 ⊢
    rw [contractΦ_other j k c base t hne]
    exact h2

theorem hwfB (dt : ℝ) : WellFormedFlowB (fR 0) (Term.const lam) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (lam * (1/2)) 30)
    (lam := Term.const 1) (domR := Formula.and (bandDom 0 0 40) (bandDom 1 (-10) 10))
    ?_ ?_ ?_
  · intro i x
    match i with
    | 0 =>
        simp only [Term.eval, AOp.interp, contractF, if_true]
        rw [fR0_eval]
        ring
    | 1 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR1_eval]
        simp [Term.eval]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · exact wfB_contract_band2 0 1 (by decide) (lam * (1/2)) 30 0 40 (-10) 10 dt
      (by norm_num) (by norm_num) (by norm_num)

theorem es (dt : ℝ) (A : Formula (Var 2)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL 0) (fR 0) (Term.const lam) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ
  refine hExistSegB_of_wellFormedFlowB (fL 0) (fR 0) _ domL domR dt _ (hwfB dt) ?_ ?_
  · intro x hx hb
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL 0) _ hb
    obtain ⟨j, hj⟩ := hdomR hx
    rw [← hj] at hi
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · have htgd : tg ∉ domR.fv := by
      intro h
      obtain ⟨i, hi⟩ := hdomR h
      exact absurd hi (by simp [Rv, Prod.ext_iff])
    rw [(Formula.coincidence domR (fun v hv =>
      Function.update_of_ne (fun hc => htgd (by rw [← hc]; exact hv)) _ _) :
        Formula.sat domR _ ↔ Formula.sat domR σ)]
    exact hσ.2.2

/-! ## The verdict pack (the tool's narrowed queries, read off the IR and certificate) -/

/-- The pack of right mode `q`: left window `CRUISE`, invariant row 0, strata order `[0]`,
the cover's λ = 5/4. -/
def Verd (q : ℕ) : Prop :=
  modalVerdX acc_tune_lag_IRv2 acc_tune_lag_cutsV2X 2 0 [0] (5/4) 0 q

theorem verd_core (h : Verd 0) :
    VerdXCore (g :: gs) (fL 0) (fR 0) lam
      (domCutX (Formula.and domL domR) (cL 0) (cR 0)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  exact h'

/-! ## The coupling, the window response -/

theorem couple (dt : ℝ) (hv : Verd 0) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL 0) (cR 0)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL 0))) domL)
        (Program.ode (rightBlock (fR 0) (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms (cL 0) (cR 0))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX g gs (g :: gs) (cL 0) (cR 0) (fL 0) (fR 0) lam lam_pos domL domR 1 dt
    hfL (hfR 0 (by norm_num)) hdomL hdomR anchor_fv (fun c hc => hc)
    (fun c hc => hc) hiffL hiffR stayL stayR (verd_core hv) (es dt _)

theorem sat_faModal_monoPost {P Q : Program (Var 2)} {A B : Formula (Var 2)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 2)}
    (h : Formula.sat (faModal (Equiv.refl (Var 2)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (dt : ℝ) (hv : Verd 0) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL 0) (cR 0)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fL 0)) domL tg dt 1)
      (bigSeq (([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
        ++ [Program.ode (rightBlock (fR 0) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM g gs) env) (region 0))) σ := by
  have htgF : tg ∉ (FM g (gs ++ atomTerms (cL 0) (cR 0))).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL 0) domL (FM g (gs ++ atomTerms (cL 0) (cR 0)))
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2)))
    (by intro h hh; simp at hh)
    (fun σ' hσ' => hσ'.2.1)
    (by intro h hh; simp at hh)
    hfL hdomL
    [Program.ode (rightBlock (fR 0) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR 0, Term.const 1, domR⟩ : RepoHop 2)
        (hfR 0 (by norm_num)) (by simp [Term.fv]) hdomR hfL hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple dt hv σ' hσ')
    hσ
  rw [show (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2))).map
      (fun h => h.progR)
      = ([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append g gs _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff hiffL hiffR ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region0 ν).mpr hRν⟩

/-! ## The step provider: stay in `CRUISE` -/

noncomputable def leftData : List (Formula (Var 2) × (Fin 2 → Term (Var 2))
    × Formula (Var 2) × ℕ) :=
  [(hostGuard vs 2 Side.L (mL 0), fL 0, domL, 1)]

noncomputable def leftProgs (dt : ℝ) : List (Program (Var 2)) :=
  leftData.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2)

theorem hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftData, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact ⟨hguardL, hfL, hdomL⟩

theorem hframes (dt : ℝ) : ∀ P ∈ leftProgs dt, FramesMv P mv := by
  intro P hP
  simp only [leftProgs, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg dt d.2.2.2 mv (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

theorem gate (dt : ℝ) (R : Program (Var 2)) (ψ : Formula (Var 2))
    {σ : State (Var 2)}
    (hbody : Formula.sat (hostGuard vs 2 Side.L (mL 0)) σ →
      Formula.sat (faModal (Equiv.refl (Var 2))
        (windowSeg (leftBlock (fL 0)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (gwindowSeg (hostGuard vs 2 Side.L (mL 0)) (leftBlock (fL 0)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

/-- **Nonblocking at the end of a response, or no step**, discharged from the explicit end
state. `CRUISE`'s region `20 ≤ v_R ≤ 40` and its guard `20 ≤ v_R < 40` differ only at
`v_R = 40`, where the field `(30 − v)/2` is negative: a flow of positive duration cannot END
there (`ode_coord_end_lt_or_eq`), so the stay is legal; a zero-duration response ended where
it started, and the right makes no step at all. -/
theorem nonblockI {F' : Formula (Var 2)} (q : ℕ) (hq : q < 1) :
    ∀ ν μ, Program.sem (Program.ode (modeW q).sys (modeW q).dom) ν μ →
      Formula.sat (Formula.and F' (region q)) μ →
      (μ = ν ∧ Formula.sat (Formula.and F' (region q)) μ) ∨
        ∃ e ∈ Gr.edgesFrom q, SwitchLegal e μ ∧
          Formula.sat (Formula.and F' (region e.tgt)) μ := by
  obtain rfl : q = 0 := by omega
  intro ν μ hrun hμ
  rcases ode_coord_end_lt_or_eq (c := 40) hrun rb_mem
      (fun s hs => ((sat_domR s).mp hs).1.2)
      (fun s _ hx => by
        simp only [Term.eval, AOp.interp]
        rw [fR0_eval, hx]; norm_num) with hlt | heq
  · right
    refine ⟨edgeW 0 0, edge_mem 0 0 (by decide), ?_, hμ⟩
    have h0 := (sat_region0 μ).mp hμ.2
    have h1 := (hiffR _ (by rw [cR_0]; exact List.mem_cons_self) μ).mp
      (h0 _ (by rw [cR_0]; exact List.mem_cons_self))
    simp only [thrGe, Term.eval, AOp.interp] at h1
    show Formula.sat (hostGuard vs 2 Side.R (mR 0)) μ
    rw [sat_guardR0]
    exact ⟨by linarith, hlt⟩
  · left; exact ⟨heq, hμ⟩

theorem stayCase (dt : ℝ) (hv : Verd 0)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hreg : Formula.sat (region 0) σ) :
    GResp Gr 0 (gwindowSeg (hostGuard vs 2 Side.L (mL 0)) (leftBlock (fL 0)) domL tg dt 1)
        (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL 0) (cR 0)))
      (Formula.and domL domR)) σ := by
    refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    exact (atomTerms_iff hiffL hiffR σ).mpr ⟨hO1L σ hguard, (sat_region0 σ).mp hreg⟩
  exact gresp_final_idle (Gr_modeAt 0 (by omega)) (respond dt hv hanchor)
    (nonblockI 0 (by omega))

theorem Hmulti (dt : ℝ) (h0 : Verd 0) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ → Formula.sat (region q) σ →
      GResp Gr q P
        (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  subst hP
  match q, hq, hreg with
  | 0, _, hreg => exact stayCase dt h0 hσ hreg
  | 1, _, hreg => exact absurd hreg (not_sat_region1 σ)

/-! ## Theorem 3 -/

/-- **`acc_tune_lag` (suite_v2), modal Theorem 3 at the declared invariant.** Left: the
guard-gated `CRUISE` window of the lagged vehicle (`v' = a`, `a' = 4 (0.75 (30 − v) − a)`,
entered inside its engagement guard `v ∈ [25, 30]`, `|a| ≤ 2`); right: the two-mode
automaton of the file (declared edges, the pruned `CRUISE → DISENGAGE` included); the loop
invariant is the declared row `a_L + 4 v_L ≤ 4 v_R + 16`, the evolve envelope, and the right
mode's region — `CRUISE`'s kept cut atoms (`v_R ∈ [20, 40]`), `DISENGAGE` excluded (the
pruned sink: the right is never in it). The response stays in `CRUISE` on the certified joint
segment at the cover's λ = 5/4. The left's kept atoms are the LINEAR-FORM CUT CHAIN of the
extended certificate, lifted by `CutLiftX`: O1 by `entry_linear` / `entry_rational` (through
`cutSatL_of_guard`), O2 by `super_linear_le_L` / `_ge_L` for the round-1 forms
`a + (v − 30) ∈ [−7, 2]`, `a + 3 (v − 30) ∈ [−17, 2]` and by `super_derived_le_L` / `_ge_L`
composed with `stay_given` for the round-2 bounds `v ≤ 32`, `v ≥ 23`. Residual: one
stratified verdict pack over the cut-narrowed domain (`modalVerdX`, the tool's own
queries). -/
theorem acc_tune_lag_modal (dt : ℝ) (h0 : Verd 0) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g []) (envLR domL domR))
        (mvRegionR mv region Gr.modes.length))) := by
  have hmvF : mv ∉ (FM g gs).fv := notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have hmvenv : mv ∉ env.fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 0 (hdomL h)
    · exact aux_notin_range_Rv 0 (hdomR h)
  have hmvreg : ∀ q, mv ∉ (region q).fv := by
    intro q h
    by_cases hq : q < 2
    · exact aux_notin_range_Rv 0 (region_fv q hq h)
    · simp only [region, show ¬ q < 1 from by omega, if_false] at h
      simp [Formula.fv, Term.fv] at h
  refine theorem3_faithful_multiR_LR Gr mv (FM g gs) domL domR region
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
  · exact hstep_assembled_GR Gr mv (FM g gs) env region (leftProgs dt) hmvF hmvenv hmvreg
      hfresh (guardsFresh_of_right Gr 0 hgR) hlt (hframes dt) (Hmulti dt h0)
  · exact hddF_multiR_G Gr 0 1 dt leftData region (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => region_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2AccTuneLag
end RelCertifier
