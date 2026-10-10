/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank` (suite_v2, the paper's running example) — modal Theorem 3

Stage 1: data, pins, evaluations.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.watertank

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Watertank

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["x"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := watertank_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := watertank_IRv2.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

/-- The declared invariant's components (`invComponents` of the row; all three rows equal). -/
noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (watertank_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 2)) := [comps.getD 1 (Term.const 0)]

/-- The kept cut atoms (extended certificate) of left mode `l` / right mode `q`. -/
noncomputable def cL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.L (cutAtomsOfX watertank_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX watertank_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp155 : Run.parseRat "15.5" = some ((31:ℚ)/2) := by
  have h : parseQ "15.5" = some (⟨155, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp125 : Run.parseRat "12.5" = some ((25:ℚ)/2) := by
  have h : parseQ "12.5" = some (⟨125, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp170 : Run.parseRat "17.0" = some (17 : ℚ) := by
  have h : parseQ "17.0" = some (⟨170, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp130 : Run.parseRat "13.0" = some (13 : ℚ) := by
  have h : parseQ "13.0" = some (⟨130, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp3 : Run.parseRat "3" = some (3 : ℚ) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Evaluations of the lowered data -/

/-- Left fields: `x' = k_l (c_l − x)`. -/
noncomputable def kL (l : ℕ) : ℝ := if l = 0 then 3/5 else 3/10
noncomputable def cLc (l : ℕ) : ℝ := if l = 0 then 31/2 else 20

theorem fL0_eval (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    Term.eval (fL l 0) x = kL l * (cLc l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, watertank_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp155, hp03,
      hp200, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv, kL, cLc]

theorem fL1_eval (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    Term.eval (fL l 1) x = 0 := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, watertank_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp155, hp03,
      hp200, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]

/-- Right fields: `x' = k_q (c_q − x)` (PumpOff: `0`). -/
noncomputable def kR (q : ℕ) : ℝ := if q = 1 then 3/20 else if q = 4 then 0 else 3/10
noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 25/2 else if q = 4 then 0 else 17

theorem fR0_eval (q : ℕ) (hq : q < 5) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_IRv2, vs, Run.dynOf, Run.lowerE, hp03, hp125, hp015,
      hp170, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 5) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_IRv2, vs, Run.dynOf, Run.lowerE, hp03, hp125, hp015,
      hp170, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domL (x : State (Var 2)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 25) := by
  simp only [domL, hostEvolve, mL, watertank_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp250, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 25) := by
  simp only [domR, hostEvolve, mR, watertank_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp250, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vs 2 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 5) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem comps_eq : comps =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0)) (Term.const 3)),
     Term.binop .sub (Term.var (Rv 0)) (Term.binop .add (Term.var (Lv 0)) (Term.const 3))] := by
  have hdL : ("L_x".drop 2).copy = "x" := by decide
  have hdR : ("R_x".drop 2).copy = "x" := by decide
  simp [comps, hostComps, watertank_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp3, ITerm.toHost, Lv, Rv]

theorem eval_g (x : State (Var 2)) : Term.eval g x = x (Lv 0) - (x (Rv 0) + 3) := by
  simp [g, comps_eq, Term.eval, AOp.interp]
theorem eval_gs0 (x : State (Var 2)) :
    Term.eval (gs.getD 0 (Term.const 0)) x = x (Rv 0) - (x (Lv 0) + 3) := by
  simp [gs, comps_eq, Term.eval, AOp.interp]



/-! ## The cut families, concretely -/

theorem gL_thr0 : hostAtomG vs 2 Side.L (.cmp ">=" (.var "x") (.num "5.0")) = thrGe (Lv 0) 5 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp50, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_thr1 : hostAtomG vs 2 Side.L (.cmp "<=" (.var "x") (.num "15.5"))
    = thrLe (Lv 0) (31/2) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp155, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_thr2 : hostAtomG vs 2 Side.L (.cmp ">=" (.var "x") (.num "13.0")) = thrGe (Lv 0) 13 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp130, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_thr3 : hostAtomG vs 2 Side.L (.cmp "<=" (.var "x") (.num "20.0")) = thrLe (Lv 0) 20 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp200, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_thr4 : hostAtomG vs 2 Side.L (.cmp ">=" (.var "x") (.num "20.0")) = thrGe (Lv 0) 20 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp200, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gR_thr0 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "x") (.num "2.0")) = thrGe (Rv 0) 2 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp20, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_thr1 : hostAtomG vs 2 Side.R (.cmp "<=" (.var "x") (.num "12.5"))
    = thrLe (Rv 0) (25/2) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp125, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]
theorem gR_thr2 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "x") (.num "10.0")) = thrGe (Rv 0) 10 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp100, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_thr3 : hostAtomG vs 2 Side.R (.cmp "<=" (.var "x") (.num "17.0")) = thrLe (Rv 0) 17 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp170, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]
theorem gR_thr4 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "x") (.num "17.0")) = thrGe (Rv 0) 17 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp170, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "x") (.num "5.0")), thrGe (Lv 0) 5),
     (hostAtomF vs 2 Side.L (.cmp "<=" (.var "x") (.num "15.5")), thrLe (Lv 0) (31/2))] := by
  rw [← gL_thr0, ← gL_thr1]; rfl
theorem cL_1 : cL 1 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "x") (.num "13.0")), thrGe (Lv 0) 13),
     (hostAtomF vs 2 Side.L (.cmp "<=" (.var "x") (.num "20.0")), thrLe (Lv 0) 20)] := by
  rw [← gL_thr2, ← gL_thr3]; rfl
theorem cL_2 : cL 2 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "x") (.num "20.0")), thrGe (Lv 0) 20)] := by
  rw [← gL_thr4]; rfl
theorem cR_0 : cR 0 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "x") (.num "2.0")), thrGe (Rv 0) 2),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "x") (.num "12.5")), thrLe (Rv 0) (25/2))] := by
  rw [← gR_thr0, ← gR_thr1]; rfl
theorem cR_1 : cR 1 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "x") (.num "10.0")), thrGe (Rv 0) 10),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "x") (.num "17.0")), thrLe (Rv 0) 17)] := by
  rw [← gR_thr2, ← gR_thr3]; rfl
theorem cR_2 : cR 2 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "x") (.num "10.0")), thrGe (Rv 0) 10),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "x") (.num "17.0")), thrLe (Rv 0) 17)] := by
  rw [← gR_thr2, ← gR_thr3]; rfl
theorem cR_3 : cR 3 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "x") (.num "17.0")), thrGe (Rv 0) 17)] := by
  rw [← gR_thr4]; rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 3) :
    ∀ x ∈ cutAtomsOfX watertank_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, watertank_cutsV2X, mL, watertank_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 4) :
    ∀ x ∈ cutAtomsOfX watertank_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, watertank_cutsV2X, mR, watertank_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 4) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

/-- The atom values, read through `hiff`. -/
theorem cutSat_iff (cs : List (CutAtomP 2)) (hiff : AtomsIff cs) (ν : State (Var 2)) :
    CutSat cs ν ↔ ∀ a ∈ cs, Term.eval a.2 ν ≤ 0 :=
  ⟨fun h a ha => (hiff a ha ν).mp (h a ha), fun h a ha => (hiff a ha ν).mpr (h a ha)⟩

theorem cutSatL_val (l : ℕ) (hl : l < 3) (ν : State (Var 2)) : CutSat (cL l) ν ↔
    (if l = 0 then 5 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ 31/2
     else if l = 1 then 13 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ 20 else 20 ≤ ν (Lv 0)) := by
  rw [cutSat_iff _ (hiffL l hl)]
  interval_cases l
  · rw [cL_0]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cL_1]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cL_2]; simp [thrGe, Term.eval, AOp.interp]

theorem cutSatR_val (q : ℕ) (hq : q < 4) (ν : State (Var 2)) : CutSat (cR q) ν ↔
    (if q = 0 then 2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 25/2
     else if q = 3 then 17 ≤ ν (Rv 0) else 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 17) := by
  rw [cutSat_iff _ (hiffR q hq)]
  interval_cases q
  · rw [cR_0]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_1]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_2]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_3]; simp [thrGe, Term.eval, AOp.interp]

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vs 2 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard watertank_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, watertank_cutsV2X, mL, watertank_IRv2] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, watertank_cutsV2X, mL, watertank_IRv2] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hp50, hp155, hp130, hp200, vs, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, watertank_IRv2, Run.lowerF, Run.lowerE, hp50, hp130, hp200, vs,
        Run.resolveVar, List.findIdx?_cons]

theorem sat_guardL (l : ℕ) (hl : l < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.L (mL l)) ν ↔
      (if l = 0 then 5 ≤ ν (Lv 0) ∧ ν (Lv 0) < 13
       else if l = 1 then 13 ≤ ν (Lv 0) ∧ ν (Lv 0) < 20 else 20 ≤ ν (Lv 0)) := by
  interval_cases l <;>
    simp [hostGuard, mL, watertank_IRv2, Run.lowerF, Run.lowerE, hp50, hp130, hp200, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Lv]

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

theorem hfL (l : ℕ) (hl : l < 3) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, watertank_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 5) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, watertank_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, watertank_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, watertank_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vs 2 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by interval_cases l <;>
      simp [mL, watertank_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, comps_eq, List.getD_cons_zero, List.getD_cons_succ, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
  · intro x hx
    simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp

theorem thr_fv_L (j : Fin 2) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 2) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 3) (hq : q < 4) :
    ∀ c ∈ g :: gs ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hc
  interval_cases l <;> interval_cases q <;>
    simp only [cL_0, cL_1, cL_2, cR_0, cR_1, cR_2, cR_3, List.mem_cons, List.not_mem_nil,
      or_false] at hc <;>
    rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
    rcases ha with rfl | rfl <;>
    first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2 | exact (thr_fv_R _ _).1 |
      exact (thr_fv_R _ _).2

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, exactly as the left windows' guards are lowered): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (Low 0, MidEco 1, MidBoost 2, High 3, PumpOff 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (2, 2), (2, 1), (2, 3),
   (3, 3), (3, 1), (3, 2), (4, 4)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range watertank_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (watertank_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 5 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 5) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The right guards, evaluated (Low `[2, 10)`, MidEco and MidBoost `[10, 17)`, High
`x ≥ 17`, PumpOff `x < 2`). -/
theorem sat_guardR (q : ℕ) (hq : q < 5) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 2 ≤ ν (Rv 0) ∧ ν (Rv 0) < 10
       else if q = 3 then 17 ≤ ν (Rv 0)
       else if q = 4 then ν (Rv 0) < 2 else 10 ≤ ν (Rv 0) ∧ ν (Rv 0) < 17) := by
  interval_cases q <;>
    simp [hostGuard, mR, watertank_IRv2, Run.lowerF, Run.lowerE, hp20, hp100, hp170, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem hguardR (q : ℕ) (hq : q < 5) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R vs (mR q) (by
    interval_cases q <;> simp [mR, watertank_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree])

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp [edgeW, Gr]

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

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 5 := by decide

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of
the mode it enters. -/
theorem Gr_guards : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = hostGuard vs 2 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem hgR : GuardsRight Gr := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact hguardR p.2 (edgeList_tgt p hp)

/-! ## Regions: the right mode's kept cut atoms; the pruned sink is excluded -/

noncomputable def region (q : ℕ) : Formula (Var 2) :=
  if q < 4 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 4) (ν : State (Var 2)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region4 (ν : State (Var 2)) : ¬ Formula.sat (region 4) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) (hq : q < 5) : (region q).fv ⊆ range Rv := by
  by_cases h4 : q < 4
  · simp only [region, h4, if_true]
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
      rcases ha with rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h4, if_false]
    simp [Formula.fv, Term.fv]


/-! ## The mode-consistent region: the right mode's guard and its kept cut atoms -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard (the state a guarded
jump into `q` leaves the right in) and its kept cut atoms (`region`; `PumpOff` excluded). -/
noncomputable def gregion (q : ℕ) : Formula (Var 2) :=
  regionG (fun q => hostGuard vs 2 Side.R (mR q)) region q

theorem hguardR_all (q : ℕ) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [watertank_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem gregion_fv (q : ℕ) (hq : q < 5) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

/-! ## The stretch of each left window (the emitted cover's λ) -/

noncomputable def lam (l : ℕ) : ℝ := if l = 2 then 1 else 2

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; split_ifs <;> norm_num

/-! ## O2: the kept atoms stay along the joint flows (contract shapes, rational) -/

theorem stayL (l q : ℕ) (hl : l < 3) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  have hf := fL0_eval l hl
  interval_cases l
  · rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 5 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
    · exact boxle_thrLe_L 0 (31/2) _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
  · rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 13 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
    · exact boxle_thrLe_L 0 20 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
  · rw [cL_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    exact boxle_thrGe_L 0 20 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit

theorem stayR (l q : ℕ) (hq : q < 4) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hf := fR0_eval q (by omega)
  have hc := le_of_lt (lam_pos l)
  interval_cases q
  · rw [cR_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 2 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 (25/2) _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
  · rw [cR_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 10 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 17 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
  · rw [cR_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 10 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 17 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
  · rw [cR_3] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    exact boxle_thrGe_R 0 17 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit

/-! ## Existence: every right mode is a contraction toward a set point inside `[0, 25]` -/

theorem hwfB (l q : ℕ) (hq : q < 5) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const (lam l)) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (lam l * kR q) (cRc q))
    (lam := Term.const 1) (domR := bandDom 0 0 25) ?_ ?_ ?_
  · intro i x
    match i with
    | 0 =>
        simp only [Term.eval, AOp.interp, contractF, if_true]
        rw [fR0_eval q hq]
        ring
    | 1 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR1_eval q hq]
        simp [Term.eval]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · refine WellFormedFlowB_contract 0 (lam l * kR q) (cRc q) 0 25 dt ?_ ?_ ?_
    · exact mul_nonneg (le_of_lt (lam_pos l)) (by unfold kR; split_ifs <;> norm_num)
    · unfold cRc; split_ifs <;> norm_num
    · unfold cRc; split_ifs <;> norm_num

theorem es (l q : ℕ) (hq : q < 5) (dt : ℝ) (A : Formula (Var 2)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR q) (Term.const (lam l)) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ
  refine hExistSegB_of_wellFormedFlowB (fL l) (fR q) _ domL domR dt _ (hwfB l q hq dt) ?_ ?_
  · intro x hx hb
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL l) _ hb
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

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `l`, right mode `q`, at the cover's λ and strata order `[0, 1]`. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX watertank_IRv2 watertank_cutsV2X 2 0 [0, 1] (lam l) l q

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 5) (h : Verd l q) :
    VerdXCore (g :: gs) (fL l) (fR q) (lam l)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

theorem couple (l q : ℕ) (hl : l < 3) (hq : q < 4) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX g gs (g :: gs) (cL l) (cR q) (fL l) (fR q) (lam l) (lam_pos l) domL domR 1 dt
    (hfL l hl) (hfR q (by omega)) hdomL hdomR (anchor_fv l q hl hq) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl) (stayR l q hq)
    (verd_core l q hl (by omega) hv) (es l q (by omega) dt _)

theorem sat_faModal_monoPost {P Q : Program (Var 2)} {A B : Formula (Var 2)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 2)}
    (h : Formula.sat (faModal (Equiv.refl (Var 2)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l qs : ℕ) (hl : l < 3) (hqs : qs < 4) (dt : ℝ) (hv : Verd l qs)
    (path : List ℕ) (hpath : ∀ p ∈ path, p < 5) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR qs)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR))
        ++ [Program.ode (rightBlock (fR qs) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM g gs) env) (region qs))) σ := by
  have htgF : tg ∉ (FM g (gs ++ atomTerms (cL l) (cR qs))).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv l qs hl hqs g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (FM g (gs ++ atomTerms (cL l) (cR qs)))
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (path.map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfR p (hpath p hp), by simp [Term.fv], hdomR⟩)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh σ' hσ' _
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      obtain ⟨ρ, hsem, hρσ⟩ := static_hop_existsR (fR := fR p)
        (lam := Term.const 1) (domR := domR) hσ'.2.2
      exact ⟨ρ, hsem, hρσ ▸ hσ'⟩)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fR qs) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR qs, Term.const 1, domR⟩ : RepoHop 2)
        (hfR qs (by omega)) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l qs hl hqs dt hv σ' hσ')
    hσ
  rw [show (path.map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2))).map
      (fun h => h.progR)
      = path.map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from by rw [List.map_map]; rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append g gs _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR qs hqs) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt qs hqs ν).mpr hRν⟩

/-! ## The step provider: stay in a certified start mode; `MidBoost` for a `Low` start of
the `Mid` window (the declared edge `Low → MidBoost`, entered inside its guard) -/

noncomputable def leftData : List (Formula (Var 2) × (Fin 2 → Term (Var 2))
    × Formula (Var 2) × ℕ) :=
  [(hostGuard vs 2 Side.L (mL 0), fL 0, domL, 1), (hostGuard vs 2 Side.L (mL 1), fL 1, domL, 1),
   (hostGuard vs 2 Side.L (mL 2), fL 2, domL, 1)]

noncomputable def leftProgs (dt : ℝ) : List (Program (Var 2)) :=
  leftData.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2)

theorem hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftData, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfL 0 (by norm_num), hdomL⟩
  · exact ⟨hguardL 1 (by norm_num), hfL 1 (by norm_num), hdomL⟩
  · exact ⟨hguardL 2 (by norm_num), hfL 2 (by norm_num), hdomL⟩

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

/-- **Nonblocking at the end of a response** (Assumption 1 at the states the response
reaches, discharged from the explicit end state): wherever the right ends inside a mode's
region, some declared successor of that mode is enabled there, and the loop postcondition
holds for it (its region is implied by its guard). Low `[2, 12.5]` is covered by Low
`[2, 10)` and MidEco `[10, 17)`; MidEco / MidBoost `[10, 17]` by themselves and High
`x ≥ 17`; High by itself. -/
theorem nonblock (q : ℕ) (hq : q < 4) :
    NonblockingAt Gr q (Formula.and (Formula.and (FM g gs) env) (region q))
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) := by
  intro μ ⟨hFe, hreg⟩
  have hr := (cutSatR_val q hq μ).mp ((sat_region_lt q hq μ).mp hreg)
  have pick : ∀ t, (q, t) ∈ edgeList → t < 4 → Formula.sat (hostGuard vs 2 Side.R (mR t)) μ →
      (CutSat (cR t) μ) →
      ∃ e ∈ Gr.edgesFrom q, SwitchLegal e μ ∧
        Formula.sat (Formula.and (Formula.and (FM g gs) env) (region e.tgt)) μ :=
    fun t ht ht4 hg hc => ⟨edgeW q t, edge_mem q t ht, hg, hFe, (sat_region_lt t ht4 μ).mpr hc⟩
  interval_cases q
  · simp only [if_true] at hr
    by_cases hx : μ (Rv 0) < 10
    · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) μ).mpr
        (by simp only [if_true]; exact ⟨hr.1, hx⟩))
        ((cutSatR_val 0 (by norm_num) μ).mpr (by simp only [if_true]; exact hr))
    · replace hx := not_lt.mp hx
      exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) μ).mpr
        (by norm_num; constructor <;> linarith))
        ((cutSatR_val 1 (by norm_num) μ).mpr (by norm_num; constructor <;> linarith))
  · simp only [show (1:ℕ) ≠ 0 from by decide, show (1:ℕ) ≠ 3 from by decide, if_false] at hr
    by_cases hx : μ (Rv 0) < 17
    · exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) μ).mpr
        (by norm_num; exact ⟨hr.1, hx⟩))
        ((cutSatR_val 1 (by norm_num) μ).mpr (by norm_num; exact hr))
    · replace hx := not_lt.mp hx
      exact pick 3 (by decide) (by norm_num) ((sat_guardR 3 (by norm_num) μ).mpr
        (by norm_num; exact hx))
        ((cutSatR_val 3 (by norm_num) μ).mpr (by norm_num; exact hx))
  · simp only [show (2:ℕ) ≠ 0 from by decide, show (2:ℕ) ≠ 3 from by decide, if_false] at hr
    by_cases hx : μ (Rv 0) < 17
    · exact pick 2 (by decide) (by norm_num) ((sat_guardR 2 (by norm_num) μ).mpr
        (by norm_num; exact ⟨hr.1, hx⟩))
        ((cutSatR_val 2 (by norm_num) μ).mpr (by norm_num; exact hr))
    · replace hx := not_lt.mp hx
      exact pick 3 (by decide) (by norm_num) ((sat_guardR 3 (by norm_num) μ).mpr
        (by norm_num; exact hx))
        ((cutSatR_val 3 (by norm_num) μ).mpr (by norm_num; exact hx))
  · simp only [show (3:ℕ) ≠ 0 from by decide, if_false, if_true] at hr
    exact pick 3 (by decide) (by norm_num) ((sat_guardR 3 (by norm_num) μ).mpr
      (by norm_num; exact hr))
      ((cutSatR_val 3 (by norm_num) μ).mpr (by norm_num; exact hr))

/-- The response from the anchor of `(l, q)`: the certified joint segment in `q`, then a
legal switch into an enabled successor of `q`. -/
theorem flowCase (l q : ℕ) (hl : l < 3) (hq : q < 4) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 2)}
    (hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ) :
    GResp Gr q (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ :=
  gresp_final (Gr_modeAt q (by omega)) (respond l q hl hq dt hv [] (by simp) hanchor)
    (nonblock q hq)

/-- The left window touches only its clock and left coordinates, so right-only facts of
the start state hold at the window's end. -/
theorem right_framed (l : ℕ) (hl : l < 3) (dt : ℝ) {φ : Formula (Var 2)}
    (hφ : φ.fv ⊆ range Rv) {σ ν : State (Var 2)}
    (hrun : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν) :
    Formula.sat φ σ ↔ Formula.sat φ ν :=
  sat_framed (notMem_bv_of_vars (vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL) hφ)
    hrun

theorem stayCase (l q : ℕ) (hl : l < 3) (hq : q < 4) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hreg : Formula.sat (region q) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
      (Formula.and domL domR)) σ := by
    refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
      ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
  exact flowCase l q hl hq dt hv hanchor

/-- A `Low` start of the `Mid` window: a zero-duration switch `Low → MidBoost`, LEGAL
because `MidBoost`'s guard `10 ≤ x_R < 17` holds there (`x_R ≥ x_L − 3 ≥ 10` by the
invariant and the `Mid` guard, `x_R ≤ 12.5` by `Low`'s region), then the certified joint
segment in `MidBoost` and a legal switch at its end. -/
theorem hopCase (dt : ℝ) (hv : Verd 1 2) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ) (hreg : Formula.sat (region 0) σ) :
    GResp Gr 0 (gwindowSeg (hostGuard vs 2 Side.L (mL 1)) (leftBlock (fL 1)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hx := (sat_guardL 1 (by norm_num) σ).mp hguard
  simp only [show (1:ℕ) ≠ 0 from by decide, if_false, if_true] at hx
  have hr0 := (cutSatR_val 0 (by norm_num) σ).mp ((sat_region_lt 0 (by norm_num) σ).mp hreg)
  simp only [if_true] at hr0
  have hg0 := (sat_FM_iff g gs σ).mp hσ.1 g List.mem_cons_self
  rw [eval_g] at hg0
  have hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL 1) (cR 2)))
      (Formula.and domL domR)) σ := by
    refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    refine (atomTerms_iff (hiffL 1 (by norm_num)) (hiffR 2 (by norm_num)) σ).mpr
      ⟨hO1L 1 (by norm_num) σ hguard, ?_⟩
    rw [cutSatR_val 2 (by norm_num)]
    simp only [show (2:ℕ) ≠ 0 from by decide, show (2:ℕ) ≠ 3 from by decide, if_false]
    constructor <;> linarith
  -- the switch `Low → MidBoost`: legal at the start, hence (right-only) at the window's end
  have hg2σ : Formula.sat (hostGuard vs 2 Side.R (mR 2)) σ := by
    rw [sat_guardR 2 (by norm_num)]
    norm_num
    constructor <;> linarith
  refine gresp_hop (e := edgeW 0 2) (Gr_modeAt 0 (by norm_num)) (edge_mem 0 2 (by decide))
    (fun ν hν => ⟨(right_framed 1 (by norm_num) dt hdomR hν).mp hσ.2.2,
      (right_framed 1 (by norm_num) dt (hguardR 2 (by norm_num)) hν).mp hg2σ⟩) ?_
  exact flowCase 1 2 (by norm_num) (by norm_num) dt hv hanchor

theorem Hmulti (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) (h23 : Verd 2 3) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ → Formula.sat (region q) σ →
      GResp Gr q P (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · match q, hq, hreg with
    | 0, _, hreg => exact stayCase 0 0 (by norm_num) (by norm_num) dt h00 hσ hreg
    | 1, _, hreg => exact stayCase 0 1 (by norm_num) (by norm_num) dt h01 hσ hreg
    | 2, _, hreg => exact stayCase 0 2 (by norm_num) (by norm_num) dt h02 hσ hreg
    | 3, _, hreg => exact stayCase 0 3 (by norm_num) (by norm_num) dt h03 hσ hreg
    | 4, _, hreg => exact absurd hreg (not_sat_region4 σ)
  · match q, hq, hreg with
    | 0, _, hreg => exact hopCase dt h12 hσ hreg
    | 1, _, hreg => exact stayCase 1 1 (by norm_num) (by norm_num) dt h11 hσ hreg
    | 2, _, hreg => exact stayCase 1 2 (by norm_num) (by norm_num) dt h12 hσ hreg
    | 3, _, hreg => exact stayCase 1 3 (by norm_num) (by norm_num) dt h13 hσ hreg
    | 4, _, hreg => exact absurd hreg (not_sat_region4 σ)
  · match q, hq, hreg with
    | 0, _, hreg => exact stayCase 2 0 (by norm_num) (by norm_num) dt h20 hσ hreg
    | 1, _, hreg => exact stayCase 2 1 (by norm_num) (by norm_num) dt h21 hσ hreg
    | 2, _, hreg => exact stayCase 2 2 (by norm_num) (by norm_num) dt h22 hσ hreg
    | 3, _, hreg => exact stayCase 2 3 (by norm_num) (by norm_num) dt h23 hσ hreg
    | 4, _, hreg => exact absurd hreg (not_sat_region4 σ)

/-! ## Theorem 3 -/

/-- **`watertank` (suite_v2), modal Theorem 3 at the declared invariant.** Left: the three
guard-gated pump windows (each window's left mode entered inside its guard); right: the
five-mode automaton of the file (declared edges, the pruned `Low → PumpOff` included); the
loop invariant is the declared row `|x_L − x_R| ≤ 3`, the evolve envelope, and the right
mode's region — its kept cut atoms (`x_R ∈ [2, 12.5]` in `Low`, `[10, 17]` in `MidEco` and
`MidBoost`, `x_R ≥ 17` in `High`), `PumpOff` excluded (the pruned sink: the right is never
in it). The right automaton is the GUARDED one: every edge carries the entered mode's
lowered guard (`Gr_guards`), so every switch of the response is kernel-checked legal. The
response runs the certified joint segment in the start mode at the cover's λ (2 for `Low`
and `Mid`, 1 for `High`) and then switches into a successor enabled at its end state
(`nonblock`: the region of every non-sink mode is covered by its successors' guards), except
a `Low` start of a `Mid` window, which first switches along `Low → MidBoost` in zero time,
inside `MidBoost`'s guard (`10 ≤ x_R ≤ 12.5`, forced by the invariant, the `Mid` guard and
`Low`'s region). Residuals: eleven stratified verdict packs over the cut-narrowed domains
(`modalVerdX`, the tool's own queries). -/
theorem watertank_modal (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) (h23 : Verd 2 3) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv gregion Gr.modes.length))) := by
  have hmvF : mv ∉ (FM g gs).fv := notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have hmvenv : mv ∉ env.fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 0 (hdomL h)
    · exact aux_notin_range_Rv 0 (hdomR h)
  have hmvreg : ∀ q, mv ∉ (gregion q).fv := by
    intro q
    refine notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) ?_
    intro h
    by_cases hq : q < 5
    · exact aux_notin_range_Rv 0 (region_fv q hq h)
    · simp only [region, show ¬ q < 4 from by omega, if_false] at h
      simp [Formula.fv, Term.fv] at h
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
        (fun P hP q hq σ ν hrun => by
          simp only [leftProgs, List.mem_map] at hP
          obtain ⟨d, hd, rfl⟩ := hP
          exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL d hd).1
            (hL d hd).2.1 (hL d hd).2.2) (hguardR_all q) hrun)
        (fun P hP q hq σ hmv hσ _ hreg =>
          Hmulti dt h00 h01 h02 h03 h11 h12 h13 h20 h21 h22 h23 P hP q hq σ hmv hσ hreg))
  · exact hddF_multiR_G Gr 0 1 dt leftData gregion (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2Watertank
end RelCertifier
