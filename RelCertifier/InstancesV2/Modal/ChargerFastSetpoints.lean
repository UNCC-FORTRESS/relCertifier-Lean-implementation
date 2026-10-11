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
import RelCertifier.Proofs.Encoding.ReplayOne
import RelCertifier.Proofs.Encoding.ContractRun
import RelCertifier.Proofs.Encoding.WindowGrowth

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

/-! ## The reposition packs (the cover's `dynPre` nodes: `BULK` for the `BULK` and `ABSORB`
windows) -/

/-- The reposition pack of window `l` at right mode `q` (the left held at the window's start,
inside its guard; strata `[0]`). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX charger_fast_setpoints_IRv2 charger_fast_setpoints_cutsV2X 2 l [0] true l q

theorem verdD_core (l q : ℕ) (hl : l < 3) (hq : q < 4) (h : VerdD l q) :
    VerdDynCore true (g :: gs) (fR q)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) (hostGuard vs 2 Side.L (mL l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [row_eq l hl] at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## O2 for the right atoms along every flow of the right mode (joint at any stretch, or
with the left frozen) -/

theorem stayR_gen (q : ℕ) (hq : q < 3) (fL' : Fin 2 → Term (Var 2)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 2)) :
    AtomsStayC (cR q) (jointSys fL' (fR q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hf := fR0_eval q hq
  interval_cases q
  · rw [cR_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 15 _ _ _ hc _ D (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 90 _ _ _ hc _ D (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
  · rw [cR_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 80 _ _ _ hc _ D (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 100 _ _ _ hc _ D (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR, cRc]; norm_num; linarith) hinit
  · rw [cR_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl
    exact boxle_thrGe_R 0 99 _ _ _ hc _ D (fun x h => h)
      (fun z _ hz => by rw [hf]; simp [kR, cRc]) hinit

/-! ## The anchors of the cover's pairs -/

/-- The right atoms of the cover's nodes (the non-sink modes; `FAULT` is never visited). -/
noncomputable def cR' (q : ℕ) : List (CutAtomP 2) := if q < 3 then cR q else []

noncomputable def anc (l q : ℕ) : Formula (Var 2) := FM g (gs ++ atomTerms (cL l) (cR' q))

theorem anc_eq (l q : ℕ) (hq : q < 3) : anc l q = FM g (gs ++ atomTerms (cL l) (cR q)) := by
  unfold anc cR'; rw [if_pos hq]

theorem anc_fv (l q : ℕ) (hl : l < 3) : (anc l q).fv ⊆ range Lv ∪ range Rv := by
  intro x hx
  by_cases hq : q < 3
  · rw [anc_eq l q hq] at hx
    by_contra hS
    exact notMem_FM_fv (fun g' hg' hxg => hS (anchor_fv l q hl hq g' (by simpa using hg') hxg)) hx
  · unfold anc cR' at hx
    rw [if_neg hq] at hx
    by_contra hS
    refine notMem_FM_fv (fun g' hg' hxg => hS ?_) hx
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact comps_fv _ List.mem_cons_self hxg
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact comps_fv _ (List.mem_cons_of_mem _ hg') hxg
    simp only [atomTerms, List.map_append, List.mem_append, List.mem_map, List.not_mem_nil,
      false_and, exists_false, or_false] at hg'
    obtain ⟨a, ha, rfl⟩ := hg'
    exact anchor_fv l 0 hl (by norm_num) a.2 (by
      simp only [List.cons_append, List.mem_cons, List.mem_append, atomTerms, List.map_append,
        List.mem_map]
      exact Or.inr (Or.inr (Or.inl ⟨a, ha, rfl⟩))) hxg

theorem anc_box (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : Verd l q) :
    ∀ σ ω, Formula.sat (anc l q) σ →
      Program.sem (Program.ode (jointSys (fL l) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (anc l q) ω := by
  rw [anc_eq l q hq]
  exact couple_box_cutX g gs (g :: gs) (cL l) (cR q) (fL l) (fR q) 1 domL domR
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl)
    (stayR_gen q hq (fL l) 1 (by norm_num) _) (verd_core l q hl (by omega) hv)

theorem cL_fvL (l : ℕ) (hl : l < 3) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv := by
  intro a ha
  interval_cases l
  · rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;>
      subst hx <;> simp
  · rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;>
      subst hx <;> simp
  · rw [cL_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; intro x hx; simp [thrGe, Term.fv] at hx; subst hx; simp

theorem anc_boxD (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vs 2 Side.L (mL l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (anc l q) ω := by
  rw [anc_eq l q hq]
  intro σ ω h1 h2 h3
  exact couple_box_dyn true g gs (g :: gs) (cL l) (cR q) (fR q) domL domR
    (hostGuard vs 2 Side.L (mL l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fvL l hl) (hguardL l hl) (stayR_gen q hq _ 1 (by norm_num) _)
    (verdD_core l q hl (by omega) hv) σ ω h1 (fun _ => h2) h3

/-- O1 for the right: a non-sink mode's guard implies its kept atoms (`BULK` `[15, 80)` ⊆
`[15, 90]`; `ABSORB` `[80, 99)` ⊆ `[80, 100]`; `FULL`). -/
theorem hO1R (q : ℕ) (hq : q < 3) (ν : State (Var 2))
    (hg : Formula.sat (hostGuard vs 2 Side.R (mR q)) ν) : CutSat (cR q) ν := by
  have h := (sat_guardR q hq ν).mp hg
  rw [cutSatR_val q hq ν]
  interval_cases q
  · simp only [if_true] at h ⊢; exact ⟨h.1, by linarith [h.2]⟩
  · simp only [show (1:ℕ) ≠ 0 from by decide, if_false, if_true] at h ⊢
    exact ⟨h.1, by linarith [h.2]⟩
  · simp only [show (2:ℕ) ≠ 0 from by decide, show (2:ℕ) ≠ 1 from by decide, if_false] at h ⊢
    exact h

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ Gr.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have hg : Formula.sat (hostGuard vs 2 Side.R (mR e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [Gr_guards q e he] at this
  rw [anc_eq l q hq] at hA
  by_cases ht : e.tgt < 3
  · rw [anc_eq l e.tgt ht]
    exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)
  · unfold anc cR'
    rw [if_neg ht]
    exact anchor_hand (cR' := []) (hiffL l hl) (hiffR q hq) (fun a ha => by simp at ha) hA
      (fun a ha => by simp at ha)

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 2)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM g gs) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  rw [anc_eq l q hq, sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem FM_fv : (FM g gs).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => hn (comps_fv c hc hvc)) hv

/-! ## The right's moves: `BULK → ABSORB` at `80`, `ABSORB → FULL` at `99` (the explicit
contractions give only the runs' existence and the switch instants) -/

/-- A right state of a non-sink mode: in its guard and the envelope. -/
def Pre (q : ℕ) (x : State (Var 2)) : Prop :=
  q < 3 ∧ Formula.sat (hostGuard vs 2 Side.R (mR q)) x ∧ Formula.sat domR x

theorem pre_R (q : ℕ) (x y : State (Var 2)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : Pre q x) : Pre q y := by
  obtain ⟨hq, hg, hd⟩ := h
  refine ⟨hq, ?_, ?_⟩
  · refine (Formula.coincidence _ (fun v hv => ?_)).mp hg
    obtain ⟨i, rfl⟩ := hguardR q (by omega) hv
    exact hxy i
  · refine (Formula.coincidence domR (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomR hv
    exact hxy i

theorem g0 (y : State (Var 2)) : Formula.sat (hostGuard vs 2 Side.R (mR 0)) y ↔
    15 ≤ y (Rv 0) ∧ y (Rv 0) < 80 := by rw [sat_guardR 0 (by norm_num)]; simp
theorem g1 (y : State (Var 2)) : Formula.sat (hostGuard vs 2 Side.R (mR 1)) y ↔
    80 ≤ y (Rv 0) ∧ y (Rv 0) < 99 := by rw [sat_guardR 1 (by norm_num)]; simp
theorem g2 (y : State (Var 2)) : Formula.sat (hostGuard vs 2 Side.R (mR 2)) y ↔
    99 ≤ y (Rv 0) := by rw [sat_guardR 2 (by norm_num)]; simp

/-- The explicit run of right mode `q < 3` (its contraction). -/
noncomputable def runΦ (q : ℕ) (ρ : State (Var 2)) : ℝ → State (Var 2) :=
  cΦ ρ 0 (kR q) (cRc q)

theorem run_sol (q : ℕ) (hq : q < 3) (ρ : State (Var 2)) (hd : Formula.sat domR ρ)
    (ε : ℝ) (hε : 0 ≤ ε) : ODESol (modeW q).sys (modeW q).dom ρ ε (runΦ q ρ) := by
  have hD := (sat_domR ρ).mp hd
  have hc : cRc q ≤ 100 ∧ 0 ≤ cRc q := by unfold cRc; split_ifs <;> norm_num
  exact contract_sol (fR := fR q) (domR := domR) ρ 0 (kR q) (cRc q)
    (by unfold kR; split_ifs <;> norm_num) (fR0_eval q hq)
    (fun i hi s => by
      match i, hi with
      | 1, _ => exact fR1_eval q hq s)
    (fun v h1 h2 => by
      rw [sat_domR, trajJ_j]
      constructor
      · exact le_trans (le_min hD.1 hc.2) h1
      · exact le_trans h2 (max_le hD.2 hc.1)) ε hε

theorem run_val (q : ℕ) (ρ : State (Var 2)) (t : ℝ) :
    runΦ q ρ t (Rv 0) = cRc q + (ρ (Rv 0) - cRc q) * Real.exp (-(kR q * t)) := by
  simp [runΦ, cΦ_j]

theorem run_dom (q : ℕ) (hq : q < 3) (ρ : State (Var 2)) (hd : Formula.sat domR ρ)
    (ε : ℝ) (hε : 0 ≤ ε) : Formula.sat domR (runΦ q ρ ε) := by
  simpa [modeW] using (run_sol q hq ρ hd ε hε).hdom ε ⟨hε, le_rfl⟩

theorem run_ge (q : ℕ) (ρ : State (Var 2)) (t : ℝ) (ht : 0 ≤ t) (hρ : ρ (Rv 0) ≤ cRc q) :
    ρ (Rv 0) ≤ runΦ q ρ t (Rv 0) := by
  rw [run_val]
  have := (exp_approach_between (kR q) (cRc q) (ρ (Rv 0)) t
    (by unfold kR; split_ifs <;> norm_num) ht).1
  rwa [min_eq_left hρ] at this

/-- The cover's joint nodes (every window: `ABSORB`, `FULL`) and reposition node (`BULK`, for
the `BULK` and `ABSORB` windows; a `BULK` start of the `FULL` window is inadmissible). -/
def J (q : ℕ) : Prop := 1 ≤ q ∧ q < 3
def D (l q : ℕ) : Prop := l < 2 ∧ q = 0

theorem hmove (E : ℕ → State (Var 2) → Prop) (hE : ∀ q x, Pre q x → E q x) :
    HMove Gr modeW J (fun q => q) Pre E := by
  intro q hJ ρ hpre T hT
  obtain ⟨hq1, hq3⟩ := hJ
  obtain ⟨-, hg, hd⟩ := hpre
  interval_cases q
  · -- `ABSORB` climbs toward 100; it switches into `FULL` at 99
    have hg' := (g1 ρ).mp hg
    have hk : (0:ℝ) < kR 1 := by simp [kR]
    have hc : cRc 1 = 100 := by simp [cRc]
    by_cases hlo : runΦ 1 ρ T (Rv 0) < 99
    · have hge := run_ge 1 ρ T hT (by rw [hc]; linarith [hg'.2])
      have hgT : Formula.sat (hostGuard vs 2 Side.R (mR 1)) (runΦ 1 ρ T) :=
        (g1 _).mpr ⟨by linarith [hg'.1], hlo⟩
      exact Or.inl ⟨runΦ 1 ρ, run_sol 1 (by norm_num) ρ hd T hT, edgeW 1 1,
        edge_mem 1 1 (by decide), hgT, hE 1 _ ⟨by norm_num, hgT, run_dom 1 (by norm_num) ρ hd T hT⟩⟩
    · push Not at hlo
      rw [run_val, hc] at hlo
      have hhit := contract_hit_up (kR 1) 100 (ρ (Rv 0)) 99 hk hg'.2.le (by norm_num)
      have hτT := contract_hit_le_up (kR 1) 100 (ρ (Rv 0)) 99 T hk hg'.2.le (by norm_num) hlo
      set τ := hitTime (kR 1) 100 (ρ (Rv 0)) 99
      have hend : runΦ 1 ρ τ (Rv 0) = 99 := by rw [run_val, hc]; exact hhit.2
      have hgF : Formula.sat (hostGuard vs 2 Side.R (mR 2)) (runΦ 1 ρ τ) := by
        rw [g2, hend]
      exact Or.inr ⟨τ, hhit.1, hτT, runΦ 1 ρ, run_sol 1 (by norm_num) ρ hd τ hhit.1, edgeW 1 2,
        edge_mem 1 2 (by decide), hgF, ⟨by simp [edgeW], by simp [edgeW]⟩,
        (by show (1:ℕ) < 2; norm_num),
        ⟨by simp [edgeW], hgF, run_dom 1 (by norm_num) ρ hd τ hhit.1⟩⟩
  · -- `FULL` is frozen
    have hg' := (g2 ρ).mp hg
    have hk : kR 2 = 0 := by simp [kR]
    have hend : runΦ 2 ρ T (Rv 0) = ρ (Rv 0) := by rw [run_val, hk]; simp
    have hgT : Formula.sat (hostGuard vs 2 Side.R (mR 2)) (runΦ 2 ρ T) := by
      rw [g2, hend]; exact hg'
    exact Or.inl ⟨runΦ 2 ρ, run_sol 2 (by norm_num) ρ hd T hT, edgeW 2 2,
      edge_mem 2 2 (by decide), hgT, hE 2 _ ⟨by norm_num, hgT, run_dom 2 (by norm_num) ρ hd T hT⟩⟩

/-- The reposition exit of `BULK`: the right alone climbs toward 90 and switches into
`ABSORB` at 80, a joint node. -/
theorem hexit (l : ℕ) : HExit Gr modeW J (D l) (fun q => 2 - q) Pre Pre := by
  intro q hD hnJ ρ hpre
  obtain ⟨-, rfl⟩ := hD
  obtain ⟨-, hg, hd⟩ := hpre
  have hg' := (g0 ρ).mp hg
  have hk : (0:ℝ) < kR 0 := by simp [kR]
  have hc : cRc 0 = 90 := by simp [cRc]
  have hhit := contract_hit_up (kR 0) 90 (ρ (Rv 0)) 80 hk hg'.2.le (by norm_num)
  set τ := hitTime (kR 0) 90 (ρ (Rv 0)) 80
  have hend : runΦ 0 ρ τ (Rv 0) = 80 := by rw [run_val, hc]; exact hhit.2
  have hgA : Formula.sat (hostGuard vs 2 Side.R (mR 1)) (runΦ 0 ρ τ) := by
    rw [g1, hend]; norm_num
  exact ⟨τ, runΦ 0 ρ, run_sol 0 (by norm_num) ρ hd τ hhit.1, edgeW 0 1, edge_mem 0 1 (by decide),
    hgA, by simp [edgeW], by simp [edgeW],
    Or.inl ⟨⟨by simp [edgeW], by simp [edgeW]⟩,
      ⟨by simp [edgeW], hgA, run_dom 0 (by norm_num) ρ hd τ hhit.1⟩⟩⟩

/-! ## The mode-consistent region: the right mode's guard and its kept cut atoms -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard (the state a guarded
jump into `q` leaves the right in) and its checked cuts (`region`). -/
noncomputable def gregion (q : ℕ) : Formula (Var 2) :=
  regionG (fun q => hostGuard vs 2 Side.R (mR q)) region q

theorem hguardR_all (q : ℕ) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [charger_fast_setpoints_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem gregion_fv (q : ℕ) (hq : q < 4) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

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

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 3) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hg : Formula.sat (hostGuard vs 2 Side.R (mR q)) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt (0 + 1))
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  have hJD : ∀ q, J q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · rw [h.2]; norm_num
  refine replay_gresp_k Gr modeW fR domR (fL l) domL (hostGuard vs 2 Side.L (mL l)) 1
    hgR (hfL l hl) hdomL hdomR (hguardL l hl) 1 one_pos J (D l)
    (fun q h => hfR q (by have := hJD q h; omega)) (fun q => q) (fun q => 2 - q) 3
    (fun q h => h.2)
    (fun q h => Gr_modeAt q (by have := hJD q h; omega)) (fun _ _ => rfl) (fun _ _ => rfl)
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => by
      have hb := anc_box l q hl h.2 (hJv q h)
      simpa [lam] using hb)
    (fun q h => anc_boxD l q hl (hJD q (Or.inr h)) (hDv q h))
    (fun q h => anc_hand l q hl (hJD q h))
    Pre Pre Pre pre_R pre_R
    (hmove _ (fun _ _ h => h)) (hexit l) dt 0 (fun h => absurd h (lt_irrefl 0)) q σ ?_
    hσ.2.1 _ ?_
  · intro hgL
    have hpre : Pre q σ := ⟨hq, hg, hσ.2.2⟩
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    by_cases hq0 : q = 0
    · subst hq0
      by_cases hl2 : l < 2
      · exact Or.inr ⟨⟨hl2, rfl⟩, fun h => absurd h.1 (by norm_num), hpre⟩
      · -- the `FULL` window from `BULK` is inadmissible: `x_L ≥ 99`, `x_R < 80`,
        -- `x_L ≤ x_R + 5`
        exfalso
        have hl2' : l = 2 := by omega
        subst hl2'
        have hL := (cutSatL_val 2 (by norm_num) σ).mp (hO1L 2 (by norm_num) σ hgL)
        simp only [show (2:ℕ) ≠ 0 from by decide, show (2:ℕ) ≠ 1 from by decide,
          if_false] at hL
        have hR := (g0 σ).mp hg
        have hrow := (sat_FM_iff g gs σ).mp hσ.1 g List.mem_cons_self
        rw [eval_g] at hrow
        linarith [hR.2]
    · exact Or.inl ⟨⟨by omega, hq⟩, hpre⟩
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domL ν :=
      windowSeg_end_domL (leftBlock (fL l)) domL tg dt (0 + 1) (by norm_num) hwin
    obtain ⟨hq', hgq, hdR⟩ := hpre
    have hA' := (anc_iff l q' hl hq' _).mp hA
    have hF : Formula.sat (FM g gs) μ := by
      refine (sat_of_agree FM_fv (fun i => ?_) (fun i => ?_)).mp hA'.1
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hdR⟩, (sat_region_lt q' hq' μ).mpr (hO1R q' hq' μ hgq)⟩
    refine (Formula.coincidence domL (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomL hv
    exact hμL i

theorem Hmulti (dt : ℝ) (hJv : ∀ l < 3, ∀ q, J q → Verd l q)
    (hDv : ∀ l < 3, ∀ q, D l q → VerdD l q) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ →
      Formula.sat (hostGuard vs 2 Side.R (mR q)) σ → Formula.sat (region q) σ →
      GResp Gr q P (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hg hreg
  rw [Gr_len] at hq
  by_cases hq3 : q = 3
  · subst hq3; exact absurd hreg (not_sat_region3 σ)
  have hq3' : q < 3 := by omega
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact respondR 0 (by norm_num) dt (hJv 0 (by norm_num)) (hDv 0 (by norm_num)) q hq3' hσ hg
  · exact respondR 1 (by norm_num) dt (hJv 1 (by norm_num)) (hDv 1 (by norm_num)) q hq3' hσ hg
  · exact respondR 2 (by norm_num) dt (hJv 2 (by norm_num)) (hDv 2 (by norm_num)) q hq3' hσ hg

/-! ## Theorem 3 -/

/-- **`charger_fast_setpoints` (suite_v2), modal Theorem 3 at the declared invariant, by
replaying the emitted cover** (`InstancesV2/BenchCovers/charger_fast_setpoints.lean`, λ = 1).
Left: the three guard-gated charger windows `BULK`, `ABSORB`, `FULL`; right: the four-mode
certified profile of the file (declared edges, the pruned `BULK → FAULT` included); loop
invariant: the declared row `x_L ≤ x_R + 5`, the evolve envelope `[0, 100]` on both sides,
and the right mode's guard and region (its kept cut atoms; `FAULT` excluded). Response: the
right keeps time with the window in the joint nodes `ABSORB` and `FULL`, switching
`ABSORB → FULL` at 99, every stretch preserved by its joint pack `Verd l q`; a `BULK` start
of the `BULK` or `ABSORB` window (a reposition node only) first repositions the right alone
to 80 under the reposition pack `VerdD l 0` and switches into `ABSORB`; a `BULK` start of
the `FULL` window is contradictory (inadmissible). Every switch is legal against the
entered mode's guard; the explicit contractions give only the runs' existence and the switch
instants. -/
theorem charger_fast_setpoints_modal (dt : ℝ)
    (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h21 : Verd 2 1) (h22 : Verd 2 2) (d00 : VerdD 0 0) (d10 : VerdD 1 0) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv gregion Gr.modes.length))) := by
  have hJv : ∀ l < 3, ∀ q, J q → Verd l q := by
    intro l hl q hJ
    obtain ⟨h1, h3⟩ := hJ
    match l, q, hl, h1, h3 with
    | 0, 1, _, _, _ => exact h01
    | 0, 2, _, _, _ => exact h02
    | 1, 1, _, _, _ => exact h11
    | 1, 2, _, _, _ => exact h12
    | 2, 1, _, _, _ => exact h21
    | 2, 2, _, _, _ => exact h22
    | _, 0, _, h1, _ => exact absurd h1 (by norm_num)
    | _ + 3, _, hl, _, _ => exact absurd hl (by omega)
    | _, _ + 3, _, _, h3 => exact absurd h3 (by omega)
  have hDv : ∀ l < 3, ∀ q, D l q → VerdD l q := by
    intro l _ q hD
    obtain ⟨hl2, rfl⟩ := hD
    match l, hl2 with
    | 0, _ => exact d00
    | 1, _ => exact d10
  have hmvF : mv ∉ (FM g gs).fv := notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have hmvenv : mv ∉ env.fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 0 (hdomL h)
    · exact aux_notin_range_Rv 0 (hdomR h)
  have hmvreg0 : ∀ q, mv ∉ (region q).fv := by
    intro q h
    by_cases hq : q < 4
    · exact aux_notin_range_Rv 0 (region_fv q hq h)
    · simp only [region, show ¬ q < 3 from by omega, if_false] at h
      simp [Formula.fv, Term.fv] at h
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
        (fun P hP q hq σ hmv hσ hg hreg => Hmulti dt hJv hDv P hP q hq σ hmv hσ hg hreg))
  · exact hddF_multiR_G Gr 0 1 dt leftData gregion (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2ChargerFastSetpoints
end RelCertifier
