/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints` (suite_v2) — modal Theorem 3

Adapted from `InstancesV2/Modal/Watertank.lean` (same generic layer, same structure). The
two non-jointOK pairs (a `BULK` right start of the `BULK` and `ABSORB` windows) respond with a
DYNAMIC right-only reposition in `BULK` (the explicit contraction solution, run until
`x_R = 80`), the declared edge `BULK → ABSORB`, and the certified joint piece in `ABSORB`.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.Proofs.Soundness.UniformEvol
import RelCertifier.InstancesV2.Cuts.charger_fast_setpoints

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ChargerFastSetpoints

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["x"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := charger_fast_setpoints_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := charger_fast_setpoints_IRv2.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

/-- The declared invariant's components (`invComponents` of row 0; all three rows equal). -/
noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (charger_fast_setpoints_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
/-- The invariant has ONE component (`x_L ≤ x_R + 5`): the tail is empty. -/
noncomputable def gs : List (Term (Var 2)) := []

/-- The three declared invariant rows (`BULK`, `ABSORB`, `FULL`) are syntactically identical. -/
theorem row_eq (l : ℕ) (hl : l < 3) :
    (charger_fast_setpoints_IRv2.invariants.getD l ("", PForm.tt)).2
      = (charger_fast_setpoints_IRv2.invariants.getD 0 ("", PForm.tt)).2 := by
  interval_cases l <;> rfl

/-- The kept cut atoms (extended certificate) of left mode `l` / right mode `q`. -/
noncomputable def cL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.L (cutAtomsOfX charger_fast_setpoints_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX charger_fast_setpoints_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp0125 : Run.parseRat "0.125" = some ((1:ℚ)/8) := by
  have h : parseQ "0.125" = some (⟨125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00625 : Run.parseRat "0.0625" = some ((1:ℚ)/16) := by
  have h : parseQ "0.0625" = some (⟨625, 10000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp150 : Run.parseRat "15.0" = some (15 : ℚ) := by
  have h : parseQ "15.0" = some (⟨150, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp800 : Run.parseRat "80.0" = some (80 : ℚ) := by
  have h : parseQ "80.0" = some (⟨800, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp900 : Run.parseRat "90.0" = some (90 : ℚ) := by
  have h : parseQ "90.0" = some (⟨900, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp990 : Run.parseRat "99.0" = some (99 : ℚ) := by
  have h : parseQ "99.0" = some (⟨990, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp1000 : Run.parseRat "100.0" = some (100 : ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp5 : Run.parseRat "5" = some (5 : ℚ) := by
  have h : parseQ "5" = some (⟨5, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Evaluations of the lowered data -/

/-- Left fields: `x' = k_l (c_l − x)` (`BULK` 1/8 toward 90, `ABSORB` 1/16 toward 100,
`FULL` 0). -/
noncomputable def kL (l : ℕ) : ℝ := if l = 0 then 1/8 else if l = 1 then 1/16 else 0
noncomputable def cLc (l : ℕ) : ℝ := if l = 0 then 90 else 100

theorem fL0_eval (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    Term.eval (fL l 0) x = kL l * (cLc l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, charger_fast_setpoints_IRv2, vs, Run.dynOf, Run.lowerE, hp0125,
      hp00625, hp900, hp1000, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Lv, kL, cLc]

theorem fL1_eval (l : ℕ) (hl : l < 3) (x : State (Var 2)) :
    Term.eval (fL l 1) x = 0 := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, charger_fast_setpoints_IRv2, vs, Run.dynOf, Run.lowerE, hp0125,
      hp00625, hp900, hp1000, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Lv]

/-- Right fields of the non-sink modes: `x' = k_q (c_q − x)` (`BULK` 1/10 toward 90,
`ABSORB` 1/20 toward 100, `FULL` 0). -/
noncomputable def kR (q : ℕ) : ℝ := if q = 0 then 1/10 else if q = 1 then 1/20 else 0
noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 90 else 100

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, charger_fast_setpoints_IRv2, vs, Run.dynOf, Run.lowerE, hp01,
      hp005, hp900, hp1000, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, charger_fast_setpoints_IRv2, vs, Run.dynOf, Run.lowerE, hp01,
      hp005, hp900, hp1000, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domL (x : State (Var 2)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 100) := by
  simp only [domL, hostEvolve, mL, charger_fast_setpoints_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp1000, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 100) := by
  simp only [domR, hostEvolve, mR, charger_fast_setpoints_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp1000, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vs 2 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem comps_eq : comps =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0)) (Term.const 5))] := by
  have hdL : ("L_x".drop 2).copy = "x" := by decide
  have hdR : ("R_x".drop 2).copy = "x" := by decide
  simp [comps, hostComps, charger_fast_setpoints_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp5, ITerm.toHost, Lv, Rv]

theorem eval_g (x : State (Var 2)) : Term.eval g x = x (Lv 0) - (x (Rv 0) + 5) := by
  simp [g, comps_eq, Term.eval, AOp.interp]

/-! ## The cut families, concretely -/

theorem gL_ge (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 2 Side.L (.cmp ">=" (.var "x") (.num s)) = thrGe (Lv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_le (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 2 Side.L (.cmp "<=" (.var "x") (.num s)) = thrLe (Lv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gR_ge (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 2 Side.R (.cmp ">=" (.var "x") (.num s)) = thrGe (Rv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_le (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 2 Side.R (.cmp "<=" (.var "x") (.num s)) = thrLe (Rv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "x") (.num "15.0")), thrGe (Lv 0) 15),
     (hostAtomF vs 2 Side.L (.cmp "<=" (.var "x") (.num "90.0")), thrLe (Lv 0) 90)] := by
  have h1 := gL_ge "15.0" 15 hp150
  have h2 := gL_le "90.0" 90 hp900
  push_cast at h1 h2
  rw [← h1, ← h2]; rfl
theorem cL_1 : cL 1 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "x") (.num "80.0")), thrGe (Lv 0) 80),
     (hostAtomF vs 2 Side.L (.cmp "<=" (.var "x") (.num "100.0")), thrLe (Lv 0) 100)] := by
  have h1 := gL_ge "80.0" 80 hp800
  have h2 := gL_le "100.0" 100 hp1000
  push_cast at h1 h2
  rw [← h1, ← h2]; rfl
theorem cL_2 : cL 2 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "x") (.num "99.0")), thrGe (Lv 0) 99)] := by
  have h1 := gL_ge "99.0" 99 hp990
  push_cast at h1
  rw [← h1]; rfl
theorem cR_0 : cR 0 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "x") (.num "15.0")), thrGe (Rv 0) 15),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "x") (.num "90.0")), thrLe (Rv 0) 90)] := by
  have h1 := gR_ge "15.0" 15 hp150
  have h2 := gR_le "90.0" 90 hp900
  push_cast at h1 h2
  rw [← h1, ← h2]; rfl
theorem cR_1 : cR 1 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "x") (.num "80.0")), thrGe (Rv 0) 80),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "x") (.num "100.0")), thrLe (Rv 0) 100)] := by
  have h1 := gR_ge "80.0" 80 hp800
  have h2 := gR_le "100.0" 100 hp1000
  push_cast at h1 h2
  rw [← h1, ← h2]; rfl
theorem cR_2 : cR 2 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "x") (.num "99.0")), thrGe (Rv 0) 99)] := by
  have h1 := gR_ge "99.0" 99 hp990
  push_cast at h1
  rw [← h1]; rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 3) :
    ∀ x ∈ cutAtomsOfX charger_fast_setpoints_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, charger_fast_setpoints_cutsV2X, mL, charger_fast_setpoints_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX charger_fast_setpoints_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, charger_fast_setpoints_cutsV2X, mR, charger_fast_setpoints_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

theorem cutSat_iff (cs : List (CutAtomP 2)) (hiff : AtomsIff cs) (ν : State (Var 2)) :
    CutSat cs ν ↔ ∀ a ∈ cs, Term.eval a.2 ν ≤ 0 :=
  ⟨fun h a ha => (hiff a ha ν).mp (h a ha), fun h a ha => (hiff a ha ν).mpr (h a ha)⟩

theorem cutSatL_val (l : ℕ) (hl : l < 3) (ν : State (Var 2)) : CutSat (cL l) ν ↔
    (if l = 0 then 15 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ 90
     else if l = 1 then 80 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ 100 else 99 ≤ ν (Lv 0)) := by
  rw [cutSat_iff _ (hiffL l hl)]
  interval_cases l
  · rw [cL_0]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cL_1]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cL_2]; simp [thrGe, Term.eval, AOp.interp]

theorem cutSatR_val (q : ℕ) (hq : q < 3) (ν : State (Var 2)) : CutSat (cR q) ν ↔
    (if q = 0 then 15 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 90
     else if q = 1 then 80 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 100 else 99 ≤ ν (Rv 0)) := by
  rw [cutSat_iff _ (hiffR q hq)]
  interval_cases q
  · rw [cR_0]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_1]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_2]; simp [thrGe, Term.eval, AOp.interp]

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vs 2 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard charger_fast_setpoints_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, charger_fast_setpoints_cutsV2X, mL, charger_fast_setpoints_IRv2] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, charger_fast_setpoints_cutsV2X, mL, charger_fast_setpoints_IRv2] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hp150, hp900, hp800, hp1000, hp990, vs, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, charger_fast_setpoints_IRv2, Run.lowerF, Run.lowerE, hp150, hp800, hp990, vs,
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

theorem hfL (l : ℕ) (hl : l < 3) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, charger_fast_setpoints_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, charger_fast_setpoints_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, charger_fast_setpoints_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, charger_fast_setpoints_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vs 2 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by interval_cases l <;>
      simp [mL, charger_fast_setpoints_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, comps_eq, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  subst hc
  intro x hx
  simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false] at hx
  rcases hx with rfl | rfl <;> simp

theorem thr_fv_L (j : Fin 2) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 2) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ c ∈ g :: gs ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hc
  interval_cases l <;> interval_cases q <;>
    simp only [cL_0, cL_1, cL_2, cR_0, cR_1, cR_2, List.mem_cons, List.not_mem_nil,
      or_false] at hc <;>
    rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
    rcases ha with rfl | rfl <;>
    first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2 | exact (thr_fv_R _ _).1 |
      exact (thr_fv_R _ _).2

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (BULK 0, ABSORB 1, FULL 2, FAULT 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 0), (0, 3), (1, 2), (1, 1), (2, 2), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range charger_fast_setpoints_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (charger_fast_setpoints_IRv2.R.modes.findIdx (·.name == nm))))) := by
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
    interval_cases q <;> simp [mR, charger_fast_setpoints_IRv2, Parse.PForm.namesFree,
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

/-- The non-sink right guards, evaluated (`BULK`: `[15, 80)`; `ABSORB`: `[80, 99)`;
`FULL`: `x ≥ 99`). -/
theorem sat_guardR (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 15 ≤ ν (Rv 0) ∧ ν (Rv 0) < 80
       else if q = 1 then 80 ≤ ν (Rv 0) ∧ ν (Rv 0) < 99 else 99 ≤ ν (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mR, charger_fast_setpoints_IRv2, Run.lowerF, Run.lowerE, hp150, hp800,
      hp990, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

/-! ## Regions: the right mode's kept cut atoms; the pruned sink `FAULT` is excluded -/

noncomputable def region (q : ℕ) : Formula (Var 2) :=
  if q < 3 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region3 (ν : State (Var 2)) : ¬ Formula.sat (region 3) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) (hq : q < 4) : (region q).fv ⊆ range Rv := by
  by_cases h3 : q < 3
  · simp only [region, h3, if_true]
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
      simp only [cR_0, cR_1, cR_2, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h3, if_false]
    simp [Formula.fv, Term.fv]

/-! ## The stretch of each left window (the emitted cover's λ = 1 for all three windows) -/

noncomputable def lam (_l : ℕ) : ℝ := 1

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; norm_num

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
    · exact boxle_thrGe_L 0 15 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
    · exact boxle_thrLe_L 0 90 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
  · rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 80 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
    · exact boxle_thrLe_L 0 100 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
  · rw [cL_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    exact boxle_thrGe_L 0 99 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; simp [kL, cLc]) hinit

theorem stayR (l q : ℕ) (hq : q < 3) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hf := fR0_eval q hq
  have hc := le_of_lt (lam_pos l)
  interval_cases q
  · rw [cR_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 15 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 90 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
  · rw [cR_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 80 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 100 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
  · rw [cR_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    exact boxle_thrGe_R 0 99 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; simp [kR, cRc]) hinit

/-! ## Existence: every non-sink right mode is a contraction inside `[0, 100]` -/

theorem domR_band (x : State (Var 2)) :
    Formula.sat domR x ↔ Formula.sat (bandDom 0 0 100) x := by
  rw [sat_domR]
  simp [bandDom, Formula.sat, CompOp.interp, Term.eval]

theorem hwfB (l q : ℕ) (hq : q < 3) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const (lam l)) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (lam l * kR q) (cRc q))
    (lam := Term.const 1) (domR := bandDom 0 0 100) ?_ domR_band ?_
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
  · refine WellFormedFlowB_contract 0 (lam l * kR q) (cRc q) 0 100 dt ?_ ?_ ?_
    · exact mul_nonneg (le_of_lt (lam_pos l)) (by unfold kR; split_ifs <;> norm_num)
    · unfold cRc; split_ifs <;> norm_num
    · unfold cRc; split_ifs <;> norm_num

theorem es (l q : ℕ) (hq : q < 3) (dt : ℝ) (A : Formula (Var 2)) :
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

/-- One pack: left window `l` (invariant row `l`, the window's own), right mode `q`, at the
cover's λ = 1 and strata order `[0]`. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX charger_fast_setpoints_IRv2 charger_fast_setpoints_cutsV2X 2 l [0] (lam l) l q

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 4) (h : Verd l q) :
    VerdXCore (g :: gs) (fL l) (fR q) (lam l)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [row_eq l hl] at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

/-- The joint-piece anchor of the pair `(l, q)`: invariant, both modes' atoms, envelope. -/
noncomputable def anchor (l q : ℕ) : Formula (Var 2) :=
  Formula.and (FM g (gs ++ atomTerms (cL l) (cR q))) (Formula.and domL domR)

theorem couple (l q : ℕ) (hl : l < 3) (hq : q < 3) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (anchor l q) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (anchor l q) tg dt (Function.update σ tg 0) :=
  couple_cutX g gs (g :: gs) (cL l) (cR q) (fL l) (fR q) (lam l) (lam_pos l) domL domR 1 dt
    (hfL l hl) (hfR q (by omega)) hdomL hdomR (anchor_fv l q hl hq) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl) (stayR l q hq)
    (verd_core l q hl (by omega) hv) (es l q hq dt _)

theorem sat_faModal_monoPost {P Q : Program (Var 2)} {A B : Formula (Var 2)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 2)}
    (h : Formula.sat (faModal (Equiv.refl (Var 2)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem htg_anchor (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    tg ∉ (FM g (gs ++ atomTerms (cL l) (cR q))).fv :=
  notMem_FM_fv (fun g' hg' hx => by
    rcases anchor_fv l q hl hq g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))

theorem htg_env : tg ∉ (Formula.and domL domR).fv := by
  rintro (h | h)
  · exact aux_notin_range_Lv 1 (hdomL h)
  · exact aux_notin_range_Rv 1 (hdomR h)

theorem anchor_post (l q : ℕ) (hl : l < 3) (hq : q < 3) (ν : State (Var 2))
    (hν : Formula.sat (anchor l q) ν) :
    Formula.sat (Formula.and (Formula.and (FM g gs) env) (region q)) ν := by
  obtain ⟨hFν, hatν⟩ := (sat_FM_append g gs _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR q hq) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt q hq ν).mpr hRν⟩

theorem respond (l qs : ℕ) (hl : l < 3) (hqs : qs < 3) (dt : ℝ) (hv : Verd l qs)
    {σ : State (Var 2)} (hσ : Formula.sat (anchor l qs) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq (([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
        ++ [Program.ode (rightBlock (fR qs) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM g gs) env) (region qs))) σ := by
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (FM g (gs ++ atomTerms (cL l) (cR qs)))
    (Formula.and domL domR) 1 dt 1 (htg_anchor l qs hl hqs) htg_env
    ([] : List (RepoHop 2)) (by simp) (fun σ' hσ' => hσ'.2.1) (by simp)
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
  exact sat_faModal_monoPost (anchor_post l qs hl hqs) hfa

/-! ## The dynamic right-only reposition in `BULK` (the explicit contraction solution) -/

/-- The right `BULK` flow `x' = (90 − x)/10` from `ω`, run for any duration `τ ≥ 0`: the
explicit solution `contractΦ 0 (1/10) 90 ω` is a run of the automaton's `BULK` mode program
(it stays in the envelope `[0, 100]`: a convex combination of `x₀` and the set point 90). -/
theorem bulk_run (ω : State (Var 2)) (τ : ℝ) (hτ : 0 ≤ τ) (hb : Formula.sat domR ω) :
    Program.sem (Program.ode (rightBlock (fR 0) (Term.const 1)) domR) ω
      (contractΦ 0 (1/10) 90 ω τ) := by
  refine ⟨τ, contractΦ 0 (1/10) 90 ω, hτ, ?_, rfl, ?_, ?_, ?_⟩
  · funext x
    by_cases hx : x = Rv 0
    · subst hx; simp [contractΦ]
    · exact contractΦ_other 0 (1/10) 90 ω 0 hx
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    match i with
    | 0 =>
        have hd := (contractΦ_hasDeriv 0 (1/10) 90 ω t).hasDerivWithinAt (s := Icc 0 τ)
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fR 0 0))
            (contractΦ 0 (1/10) 90 ω t) = 1/10 * (90 - contractΦ 0 (1/10) 90 ω t (Rv 0)) := by
          simp only [Term.eval, AOp.interp]
          rw [fR0_eval 0 (by norm_num)]
          simp [kR, cRc]
        rw [heval]
        exact hd
    | 1 =>
        have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fR 0 1))
            (contractΦ 0 (1/10) 90 ω t) = 0 := by
          simp only [Term.eval, AOp.interp]
          rw [fR1_eval 0 (by norm_num)]
          ring
        rw [heval]
        have hcurve : (fun u => contractΦ 0 (1/10) 90 ω u (Rv 1)) = fun _ => ω (Rv 1) := by
          funext u
          exact contractΦ_other 0 (1/10) 90 ω u (by simp [Rv, Prod.ext_iff])
        rw [hcurve]
        exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have hxj : x ≠ Rv 0 := by
      intro hc; subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
    exact contractΦ_other 0 (1/10) 90 ω t hxj
  · intro t ht
    exact (domR_band _).mpr (contract_stays 0 (1/10) 90 0 100 (by norm_num) (by norm_num)
      (by norm_num) ω ((domR_band ω).mp hb) t ht.1)

/-- The contraction reaches `x_R = 80` at `τ = 10·log((90 − x₀)/10)`. -/
theorem bulk_end (ω : State (Var 2)) (h80 : ω (Rv 0) < 80) :
    contractΦ 0 (1/10) 90 ω (10 * Real.log ((90 - ω (Rv 0)) / 10)) (Rv 0) = 80 := by
  have hy : 0 < (90 - ω (Rv 0)) / 10 := by linarith
  rw [contractΦ_Rvj]
  have he : Real.exp (-(1 / 10 * (10 * Real.log ((90 - ω (Rv 0)) / 10))))
      = ((90 - ω (Rv 0)) / 10)⁻¹ := by
    rw [show -(1 / 10 * (10 * Real.log ((90 - ω (Rv 0)) / 10)))
        = -Real.log ((90 - ω (Rv 0)) / 10) from by ring, Real.exp_neg, Real.exp_log hy]
  rw [he]
  have hne : (90 - ω (Rv 0)) ≠ 0 := by linarith
  field_simp
  ring

/-! ## The k = 1 window with a right-only prefix and DIFFERENT pre/post anchors

`Hmulti_windowRF_prefixed` holds one anchor across the hop. Here the window starts at a
state that need NOT satisfy the joint piece's anchor `φ` (the right is still in `BULK`,
below `ABSORB`'s floor); only the hop's END satisfies `φ`. `faModalB_repoPrefix` needs `φ`
only at the hop's end, the hop run converts to the frozen-left joint form from `domL` at
the start (`hop_run_toJoint`), and the k = 1 window plumbing of `Hmulti_window1_prefixedF`
closes the assembly. -/
theorem window1_hop (fL' : Fin 2 → Term (Var 2)) (domL' : Formula (Var 2))
    (fRh : Fin 2 → Term (Var 2)) (lamh : Term (Var 2)) (domRh : Formula (Var 2))
    (Q : Program (Var 2)) (φ : Formula (Var 2)) (dt : ℝ)
    (hfL' : ∀ i, (fL' i).fv ⊆ range Lv) (hdomL' : domL'.fv ⊆ range Lv)
    (hfRh : ∀ i, (fRh i).fv ⊆ range Rv) (hlamh : lamh.fv ⊆ range Rv)
    (hdomRh : domRh.fv ⊆ range Rv)
    {σ : State (Var 2)} (hdomLσ : Formula.sat domL' σ)
    (hR : ∃ ρ₁, Program.sem (Program.ode (rightBlock fRh lamh) domRh)
        (Function.update σ tg 0) ρ₁ ∧ Formula.sat φ ρ₁)
    (hQ : ∀ τ, Formula.sat φ τ → τ tg = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') Q φ tg dt τ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock fL') domL' tg dt 1)
      (bigSeq [Program.ode (rightBlock fRh lamh) domRh, Q]) φ) σ := by
  have htgL : tg ∉ domL'.fv := fun h => aux_notin_range_Lv 1 (hdomL' h)
  have hdomL0 : Formula.sat domL' (Function.update σ tg 0) := by
    rwa [(Formula.coincidence domL' (fun v hv =>
      Function.update_of_ne (fun hc => htgL (by rw [← hc]; exact hv)) _ _) :
        Formula.sat domL' _ ↔ Formula.sat domL' σ)]
  obtain ⟨ρ₁, hrun, hρ₁⟩ := hR
  have hj := faModalB_repoPrefix (fL := fL') (fR := fRh) (lam := lamh) (domL := domL')
    (domR := domRh) (φ := φ) (Q := Q) (a := 1) (dt := dt) hfL' hdomL' hfRh hlamh hdomRh
    (Function.update_self _ _ _)
    ⟨ρ₁, hop_run_toJoint hfRh hlamh hdomL' hdomL0 hrun, hρ₁⟩ hQ
  have hb : faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL')
      (Program.seq (Program.ode (rightBlock fRh lamh) domRh) Q) φ tg dt
      (Function.update σ tg 0) := by
    refine faModalB_monoQ ?_ hj
    rintro ν μ ⟨κ, hhop, hQrun⟩
    exact ⟨κ, joint_run_toR hfRh hlamh hhop, hQrun⟩
  have hseg := (faModalB_clockedSeg_iff (leftBlock fL') domL' _ φ tg dt σ).mpr hb
  have hcong := sat_faModal_congrR
    (Q' := bigSeq [Program.ode (rightBlock fRh lamh) domRh, Q])
    (fun ν μ => sem_foldr_seq_bigSeq [Program.ode (rightBlock fRh lamh) domRh] Q ν μ) hseg
  exact sat_faModal_monoL
    (fun ν μ h => (sem_windowSeg_one (leftBlock fL') domL' tg dt).mp h) hcong

/-- `window1_hop` with the switch test after the hop (the entered mode's guard `γ`, which
the hop's end state satisfies). -/
theorem window1_hopG (fL' : Fin 2 → Term (Var 2)) (domL' : Formula (Var 2))
    (fRh : Fin 2 → Term (Var 2)) (lamh : Term (Var 2)) (domRh : Formula (Var 2))
    (γ : Formula (Var 2)) (Q : Program (Var 2)) (φ : Formula (Var 2)) (dt : ℝ)
    (hfL' : ∀ i, (fL' i).fv ⊆ range Lv) (hdomL' : domL'.fv ⊆ range Lv)
    (hfRh : ∀ i, (fRh i).fv ⊆ range Rv) (hlamh : lamh.fv ⊆ range Rv)
    (hdomRh : domRh.fv ⊆ range Rv) (hγ : γ.fv ⊆ range Rv)
    {σ : State (Var 2)} (hdomLσ : Formula.sat domL' σ)
    (hR : ∃ ρ₁, Program.sem (Program.ode (rightBlock fRh lamh) domRh)
        (Function.update σ tg 0) ρ₁ ∧ Formula.sat φ ρ₁ ∧ Formula.sat γ ρ₁)
    (hQ : ∀ τ, Formula.sat φ τ → τ tg = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') Q φ tg dt τ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock fL') domL' tg dt 1)
      (bigSeq [Program.seq (Program.ode (rightBlock fRh lamh) domRh) (Program.test γ), Q])
      φ) σ := by
  have htgL : tg ∉ domL'.fv := fun h => aux_notin_range_Lv 1 (hdomL' h)
  have hdomL0 : Formula.sat domL' (Function.update σ tg 0) := by
    rwa [(Formula.coincidence domL' (fun v hv =>
      Function.update_of_ne (fun hc => htgL (by rw [← hc]; exact hv)) _ _) :
        Formula.sat domL' _ ↔ Formula.sat domL' σ)]
  obtain ⟨ρ₁, hrun, hρ₁, hγρ⟩ := hR
  have hj := faModalB_repoPrefixG (fL := fL') (fR := fRh) (lam := lamh) (domL := domL')
    (domR := domRh) (γ := γ) (φ := φ) (Q := Q) (a := 1) (dt := dt) hfL' hdomL' hfRh hlamh
    hdomRh hγ (Function.update_self _ _ _)
    ⟨ρ₁, hop_run_toJoint hfRh hlamh hdomL' hdomL0 hrun, hρ₁, hγρ⟩ hQ
  have hb : faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL')
      (Program.seq (Program.seq (Program.ode (rightBlock fRh lamh) domRh) (Program.test γ)) Q)
      φ tg dt (Function.update σ tg 0) := by
    refine faModalB_monoQ ?_ hj
    rintro ν μ ⟨κ, ⟨κ', hhop, htest⟩, hQrun⟩
    exact ⟨κ, ⟨κ', joint_run_toR hfRh hlamh hhop, htest⟩, hQrun⟩
  have hseg := (faModalB_clockedSeg_iff (leftBlock fL') domL' _ φ tg dt σ).mpr hb
  have hcong := sat_faModal_congrR
    (Q' := bigSeq [Program.seq (Program.ode (rightBlock fRh lamh) domRh) (Program.test γ), Q])
    (fun ν μ => sem_foldr_seq_bigSeq
      [Program.seq (Program.ode (rightBlock fRh lamh) domRh) (Program.test γ)] Q ν μ) hseg
  exact sat_faModal_monoL
    (fun ν μ h => (sem_windowSeg_one (leftBlock fL') domL' tg dt).mp h) hcong

/-- **The reposition's existence.** From a `BULK` right start (`x_R ∈ [15, 90]`) with the
loop invariant, the envelope and window `l`'s left atoms: the right-only `BULK` run (zero
duration if `x_R ≥ 80`, else the contraction up to exactly `x_R = 80`) ends in `ABSORB`'s
joint anchor — `x_R` only grew (the invariant `x_L ≤ x_R + 5` survives), lefts are frozen. -/
theorem bulk_hop_exists (l : ℕ) (hl : l < 3) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ) (hreg : Formula.sat (region 0) σ)
    (hLat : CutSat (cL l) σ) :
    ∃ ρ₁, Program.sem (Program.ode (rightBlock (fR 0) (Term.const 1)) domR)
      (Function.update σ tg 0) ρ₁ ∧ Formula.sat (anchor l 1) ρ₁ ∧
        Formula.sat (hostGuard vs 2 Side.R (mR 1)) ρ₁ := by
  set ω₀ := Function.update σ tg 0 with hω₀
  have hωL : ω₀ (Lv 0) = σ (Lv 0) :=
    Function.update_of_ne (by simp [Lv, Prod.ext_iff]) _ _
  have hωR : ω₀ (Rv 0) = σ (Rv 0) :=
    Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hx0 := (cutSatR_val 0 (by norm_num) σ).mp ((sat_region_lt 0 (by norm_num) σ).mp hreg)
  simp only [if_true] at hx0
  have hinv : σ (Lv 0) ≤ σ (Rv 0) + 5 := by
    have := (sat_FM_iff g gs σ).mp hσ.1 g List.mem_cons_self
    rw [eval_g] at this; linarith
  have hdL := (sat_domL σ).mp hσ.2.1
  have hLv := (cutSatL_val l hl σ).mp hLat
  have key : ∀ ρ : State (Var 2), ρ (Lv 0) = σ (Lv 0) → σ (Rv 0) ≤ ρ (Rv 0) →
      80 ≤ ρ (Rv 0) → ρ (Rv 0) ≤ 100 → Formula.sat (anchor l 1) ρ := by
    intro ρ hρL hρR h1 h2
    refine ⟨(sat_FM_append g gs _ ρ).mpr ⟨(sat_FM_iff g gs ρ).mpr ?_,
      (atomTerms_iff (hiffL l hl) (hiffR 1 (by norm_num)) ρ).mpr ⟨?_, ?_⟩⟩,
      (sat_domL ρ).mpr ?_, (sat_domR ρ).mpr ⟨by linarith, h2⟩⟩
    · intro g' hg'
      simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg'
      subst hg'
      rw [eval_g]; linarith
    · rw [cutSatL_val l hl ρ, hρL]; exact hLv
    · rw [cutSatR_val 1 (by norm_num) ρ]
      simp only [show (1:ℕ) ≠ 0 from by decide, if_false, if_true]
      exact ⟨h1, h2⟩
    · rw [hρL]; exact hdL
  have hdomRω : Formula.sat domR ω₀ := by
    rw [sat_domR, hωR]; exact (sat_domR σ).mp hσ.2.2
  by_cases h80 : 80 ≤ σ (Rv 0)
  · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fR 0) (lam := Term.const 1)
      (domR := domR) hdomRω
    subst hρ
    refine ⟨ω₀, hsem, key ω₀ hωL (by rw [hωR]) (by rw [hωR]; exact h80)
      (by rw [hωR]; linarith), ?_⟩
    rw [sat_guardR 1 (by norm_num), hωR]
    norm_num
    exact ⟨h80, by linarith⟩
  · replace h80 : σ (Rv 0) < 80 := not_le.mp h80
    have hy1 : 1 ≤ (90 - ω₀ (Rv 0)) / 10 := by rw [hωR]; linarith
    have hτ : 0 ≤ 10 * Real.log ((90 - ω₀ (Rv 0)) / 10) :=
      mul_nonneg (by norm_num) (Real.log_nonneg hy1)
    have hend := bulk_end ω₀ (by rw [hωR]; exact h80)
    refine ⟨_, bulk_run ω₀ _ hτ hdomRω, key _ ?_ ?_ ?_ ?_, ?_⟩
    · rw [contractΦ_other 0 (1/10) 90 ω₀ _ (by simp [Lv, Rv, Prod.ext_iff]), hωL]
    · rw [hend]; exact le_of_lt h80
    · rw [hend]
    · rw [hend]; norm_num
    · rw [sat_guardR 1 (by norm_num), hend]; norm_num

/-! ## The step provider: stay in a certified start mode; for a `BULK` right start of the
`BULK` / `ABSORB` window, reposition dynamically in `BULK` and switch along the declared edge
`BULK → ABSORB` -/

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

/-- **Nonblocking at the end of a response**, discharged from the explicit end state:
`BULK`'s region `[15, 90]` is covered by `BULK` `[15, 80)` and `ABSORB` `[80, 99)`;
`ABSORB`'s `[80, 100]` by `ABSORB` and `FULL` `x ≥ 99`; `FULL`'s region is its guard. -/
theorem nonblock {F' : Formula (Var 2)} (q : ℕ) (hq : q < 3) :
    NonblockingAt Gr q (Formula.and F' (region q)) (fun qf => Formula.and F' (region qf)) := by
  intro μ ⟨hF, hreg⟩
  have hr := (cutSatR_val q hq μ).mp ((sat_region_lt q hq μ).mp hreg)
  have pick : ∀ t, (q, t) ∈ edgeList → t < 3 → Formula.sat (hostGuard vs 2 Side.R (mR t)) μ →
      CutSat (cR t) μ →
      ∃ e ∈ Gr.edgesFrom q, SwitchLegal e μ ∧ Formula.sat (Formula.and F' (region e.tgt)) μ :=
    fun t ht ht3 hg hc => ⟨edgeW q t, edge_mem q t ht, hg, hF, (sat_region_lt t ht3 μ).mpr hc⟩
  interval_cases q
  · simp only [if_true] at hr
    by_cases hx : μ (Rv 0) < 80
    · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) μ).mpr
        (by simp only [if_true]; exact ⟨hr.1, hx⟩))
        ((cutSatR_val 0 (by norm_num) μ).mpr (by simp only [if_true]; exact hr))
    · replace hx := not_lt.mp hx
      exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) μ).mpr
        (by norm_num; constructor <;> linarith))
        ((cutSatR_val 1 (by norm_num) μ).mpr (by norm_num; constructor <;> linarith))
  · simp only [show (1:ℕ) ≠ 0 from by decide, if_false, if_true] at hr
    by_cases hx : μ (Rv 0) < 99
    · exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) μ).mpr
        (by norm_num; exact ⟨hr.1, hx⟩))
        ((cutSatR_val 1 (by norm_num) μ).mpr (by norm_num; exact hr))
    · replace hx := not_lt.mp hx
      exact pick 2 (by decide) (by norm_num) ((sat_guardR 2 (by norm_num) μ).mpr
        (by norm_num; exact hx))
        ((cutSatR_val 2 (by norm_num) μ).mpr (by norm_num; exact hx))
  · simp only [show (2:ℕ) ≠ 0 from by decide, show (2:ℕ) ≠ 1 from by decide, if_false] at hr
    exact pick 2 (by decide) (by norm_num) ((sat_guardR 2 (by norm_num) μ).mpr
      (by norm_num; exact hr))
      ((cutSatR_val 2 (by norm_num) μ).mpr (by norm_num; exact hr))

theorem stayCase (l q : ℕ) (hl : l < 3) (hq : q < 3) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hreg : Formula.sat (region q) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hanchor : Formula.sat (anchor l q) σ := by
    refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
      ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
  exact gresp_final (Gr_modeAt q (by omega)) (respond l q hl hq dt hv hanchor) (nonblock q hq)

/-- **The dynamic-reposition case.** A `BULK` right start of window `l ∈ {BULK, ABSORB}`:
segments `BULK →(edge BULK→ABSORB) ABSORB →(self) ABSORB`; the right first runs `BULK`
alone (the left frozen in the coupling, `faModalB_repoPrefix`) up to `x_R = 80`, then the
certified joint piece `(l, ABSORB)` tracks the window. -/
theorem hopCase (l : ℕ) (hl : l < 2) (dt : ℝ) (hv : Verd l 1) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ) (hreg : Formula.sat (region 0) σ) :
    GResp Gr 0 (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hl3 : l < 3 := by omega
  have hw := window1_hopG (fL l) domL (fR 0) (Term.const 1) domR
    (hostGuard vs 2 Side.R (mR 1))
    (Program.ode (rightBlock (fR 1) (Term.const 1)) domR) (anchor l 1) dt
    (hfL l hl3) hdomL (hfR 0 (by norm_num)) (by simp [Term.fv]) hdomR
    (hguardR 1 (by norm_num)) hσ.2.1
    (bulk_hop_exists l hl3 hσ hreg (hO1L l hl3 σ hguard))
    (by
      intro τ hτ hτtg
      have hupd : Function.update τ tg 0 = τ := by
        funext x
        by_cases hx : x = tg
        · subst hx; rw [Function.update_self, hτtg]
        · rw [Function.update_of_ne hx]
      have := couple l 1 hl3 (by norm_num) dt hv τ hτ
      rwa [hupd] at this)
  exact gresp_final_pre (Gr_modeAt 1 (by norm_num)) [(0, modeW 0, edgeW 0 1)]
    (by
      intro s hs
      rw [List.mem_singleton] at hs
      subst hs
      exact ⟨Gr_modeAt 0 (by norm_num), edge_mem 0 1 (by decide)⟩)
    (by simp) (by simp) (by simp [qfOf, edgeW])
    (sat_faModal_monoPost (anchor_post l 1 hl3 (by norm_num)) hw) (nonblock 1 (by norm_num))

theorem Hmulti (dt : ℝ)
    (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ → Formula.sat (region q) σ →
      GResp Gr q P
        (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · match q, hq, hreg with
    | 0, _, hreg => exact hopCase 0 (by norm_num) dt h01 hσ hreg
    | 1, _, hreg => exact stayCase 0 1 (by norm_num) (by norm_num) dt h01 hσ hreg
    | 2, _, hreg => exact stayCase 0 2 (by norm_num) (by norm_num) dt h02 hσ hreg
    | 3, _, hreg => exact absurd hreg (not_sat_region3 σ)
  · match q, hq, hreg with
    | 0, _, hreg => exact hopCase 1 (by norm_num) dt h11 hσ hreg
    | 1, _, hreg => exact stayCase 1 1 (by norm_num) (by norm_num) dt h11 hσ hreg
    | 2, _, hreg => exact stayCase 1 2 (by norm_num) (by norm_num) dt h12 hσ hreg
    | 3, _, hreg => exact absurd hreg (not_sat_region3 σ)
  · match q, hq, hreg with
    | 0, _, hreg => exact stayCase 2 0 (by norm_num) (by norm_num) dt h20 hσ hreg
    | 1, _, hreg => exact stayCase 2 1 (by norm_num) (by norm_num) dt h21 hσ hreg
    | 2, _, hreg => exact stayCase 2 2 (by norm_num) (by norm_num) dt h22 hσ hreg
    | 3, _, hreg => exact absurd hreg (not_sat_region3 σ)

/-! ## Theorem 3 -/

/-- **`charger_fast_setpoints` (suite_v2), modal Theorem 3 at the declared invariant.**
Left: the three guard-gated charger windows `BULK`, `ABSORB`, `FULL` (each window's left mode
entered inside its guard); right: the four-mode certified profile of the file (declared
edges, the pruned `BULK → FAULT` included); the loop invariant is the declared row
`x_L ≤ x_R + 5` (all three rows equal), the evolve envelope `[0, 100]` on both sides, and
the right mode's region — its kept cut atoms (`x_R ∈ [15, 90]` in `BULK`, the guard-implied
cap 90 included; `[80, 100]` in `ABSORB`; `x_R ≥ 99` in `FULL`), `FAULT` excluded (the
pruned sink: the right is never in it). The response stays in the start mode on the
certified joint segment at the cover's λ = 1, except a `BULK` right start of the `BULK` or
`ABSORB` window (not jointOK): there the right repositions ALONE in `BULK` (the explicit
contraction `x(t) = 90 + (x₀ − 90)e^{−t/10}`, run until `x_R = 80`, zero duration if
already `x_R ≥ 80`), takes the declared edge `BULK → ABSORB`, and the certified joint piece
`(window, ABSORB)` tracks the window. Residuals: seven stratified verdict packs over the
cut-narrowed domains (`modalVerdX`, the tool's own queries, each window's own invariant
row). -/
theorem charger_fast_setpoints_modal (dt : ℝ)
    (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
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
    by_cases hq : q < 4
    · exact aux_notin_range_Rv 0 (region_fv q hq h)
    · simp only [region, show ¬ q < 3 from by omega, if_false] at h
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
      hfresh (guardsFresh_of_right Gr 0 hgR) hlt (hframes dt)
      (Hmulti dt h01 h02 h11 h12 h20 h21 h22)
  · exact hddF_multiR_G Gr 0 1 dt leftData region (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => region_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2ChargerFastSetpoints
end RelCertifier
