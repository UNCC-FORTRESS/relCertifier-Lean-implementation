/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_linkloss` (suite_v2) — mode-keyed Theorem 3 at the declared rows

The file declares one row per LEFT mode (FOLLOW = CATCH: `g_L ≤ g_R + 1 ∧ g_R ≤ g_L + 3`;
LOST: `0.55 g_L ≤ g_R − 8.45 ∧ g_R ≤ g_L + 3`). This leaf composes the per-left-mode modal
statements over the file's left automaton (`ModeHandoff.theorem3_modeKeyed`), with
`mv = (Aux, 0)`, the window clock `tg = (Aux, 1)` and the left mode variable `u_L = (Aux, 2)`
(lowered at `n = 3`: `vars = ["g"]`, pads 1 and 2). Ingredients: the suite_v2 cut layer
(`CutRespond`: `couple_cutX`, `modalVerdX`, threshold staying, O1 from the extended
certificate), the region-carrying R-chain (`hstepMode_multiR`, `mvRegionR`), and the
in-kernel handoffs.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.platoon_delay_linkloss

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2PlatoonDelayLinkloss

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["g"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := platoon_delay_linkloss_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := platoon_delay_linkloss_IRv2.R.modes.getD q dm

abbrev mv : Var 3 := (Side.Aux, 0)
abbrev tg : Var 3 := (Side.Aux, 1)
abbrev uL : Var 3 := (Side.Aux, 2)

noncomputable def fL (l : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domL : Formula (Var 3) := hostEvolve vs 3 Side.L (mL 0)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
noncomputable def env : Formula (Var 3) := Formula.and domL domR

noncomputable def comps (l : ℕ) : List (Term (Var 3)) :=
  hostComps vs 3 (platoon_delay_linkloss_IRv2.invariants.getD l ("", PForm.tt)).2
noncomputable def g (l : ℕ) : Term (Var 3) := (comps l).getD 0 (Term.const 0)
noncomputable def gs (l : ℕ) : List (Term (Var 3)) := [(comps l).getD 1 (Term.const 0)]

theorem hp05m : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp06m : Run.parseRat "-0.6" = some (-(3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp290 : Run.parseRat "29.0" = some (29 : ℚ) := by
  have h : parseQ "29.0" = some (⟨290, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp350 : Run.parseRat "35.0" = some (35 : ℚ) := by
  have h : parseQ "35.0" = some (⟨350, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp15 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp600 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp210 : Run.parseRat "21.0" = some (21 : ℚ) := by
  have h : parseQ "21.0" = some (⟨210, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp30 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp055 : Run.parseRat "0.55" = some ((11:ℚ)/20) := by
  have h : parseQ "0.55" = some (⟨55, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp845 : Run.parseRat "8.45" = some ((169:ℚ)/20) := by
  have h : parseQ "8.45" = some (⟨845, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Evaluations -/

/-- Left fields: `g' = k_l (c_l − g)`. -/
noncomputable def kL (l : ℕ) : ℝ := if l = 1 then 3/5 else 1/2
noncomputable def cLc (l : ℕ) : ℝ := if l = 2 then 35 else 29

theorem fL0_eval (l : ℕ) (hl : l < 3) (x : State (Var 3)) :
    Term.eval (fL l 0) x = kL l * (cLc l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp05m,
      hp06m, hp290, hp350, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv, kL, cLc] <;> ring

theorem fL_pad (l : ℕ) (hl : l < 3) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fL l i) x = 0 := by
  fin_cases i
  · exact absurd rfl hi
  all_goals interval_cases l <;>
    simp [fL, hostDyn, mL, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp05m,
      hp06m, hp290, hp350, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv]

/-- Right fields (FOLLOW, CATCH): `g' = k_q (30 − g)`. -/
noncomputable def kR (q : ℕ) : ℝ := if q = 1 then 3/5 else 1/2

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (30 - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp05m,
      hp06m, hp300, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR] <;> ring

theorem fR_pad (q : ℕ) (hq : q < 3) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  fin_cases i
  · exact absurd rfl hi
  all_goals interval_cases q <;>
    simp [fR, hostDyn, mR, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp05m,
      hp06m, hp300, hp15, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domL (x : State (Var 3)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 60) := by
  simp only [domL, hostEvolve, mL, platoon_delay_linkloss_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60) := by
  simp only [domR, hostEvolve, mR, platoon_delay_linkloss_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vs 3 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vs 3 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-- The declared rows, evaluated: FOLLOW = CATCH: `g_L − (g_R + 1) ≤ 0 ∧ g_R − (g_L + 3) ≤ 0`;
LOST: `0.55 g_L − (g_R − 8.45) ≤ 0 ∧ g_R − (g_L + 3) ≤ 0`. -/
theorem eval_g (l : ℕ) (hl : l < 3) (x : State (Var 3)) : Term.eval (g l) x =
    (if l = 2 then 11/20 * x (Lv 0) - (x (Rv 0) - 169/20) else x (Lv 0) - (x (Rv 0) + 1)) := by
  have hdL : ("L_g".drop 2).copy = "g" := by decide
  have hdR : ("R_g".drop 2).copy = "g" := by decide
  interval_cases l <;>
    simp [g, comps, hostComps, platoon_delay_linkloss_IRv2, Oracle.invComponents, Run.lowerE,
      vs, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp10, hp30, hp055, hp845,
      ITerm.toHost, Lv, Rv, Term.eval, AOp.interp]

theorem eval_gs0 (l : ℕ) (hl : l < 3) (x : State (Var 3)) :
    Term.eval ((gs l).getD 0 (Term.const 0)) x = x (Rv 0) - (x (Lv 0) + 3) := by
  have hdL : ("L_g".drop 2).copy = "g" := by decide
  have hdR : ("R_g".drop 2).copy = "g" := by decide
  interval_cases l <;>
    simp [gs, comps, hostComps, platoon_delay_linkloss_IRv2, Oracle.invComponents, Run.lowerE,
      vs, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp10, hp30, hp055, hp845,
      ITerm.toHost, Lv, Rv, Term.eval, AOp.interp]


theorem comps_eq01 (l : ℕ) (hl : l < 2) : comps l =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0)) (Term.const 1)),
     Term.binop .sub (Term.var (Rv 0)) (Term.binop .add (Term.var (Lv 0)) (Term.const 3))] := by
  have hdL : ("L_g".drop 2).copy = "g" := by decide
  have hdR : ("R_g".drop 2).copy = "g" := by decide
  interval_cases l <;>
  simp [comps, hostComps, platoon_delay_linkloss_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp10, hp30, ITerm.toHost, Lv, Rv]

theorem comps_eq2 : comps 2 =
    [Term.binop .sub (Term.binop .mul (Term.const (11/20)) (Term.var (Lv 0)))
       (Term.binop .sub (Term.var (Rv 0)) (Term.const (169/20))),
     Term.binop .sub (Term.var (Rv 0)) (Term.binop .add (Term.var (Lv 0)) (Term.const 3))] := by
  have hdL : ("L_g".drop 2).copy = "g" := by decide
  have hdR : ("R_g".drop 2).copy = "g" := by decide
  simp [comps, hostComps, platoon_delay_linkloss_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp10, hp30, hp055, hp845,
    ITerm.toHost, Lv, Rv]

theorem comps_fv (l : ℕ) (hl : l < 3) : ∀ c ∈ g l :: gs l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  have hc' : c ∈ comps l := by
    simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rcases (show l < 2 ∨ l = 2 by omega) with h | rfl
      · rw [comps_eq01 l h]; simp
      · rw [comps_eq2]; simp
    · rcases (show l < 2 ∨ l = 2 by omega) with h | rfl
      · rw [comps_eq01 l h]; simp
      · rw [comps_eq2]; simp
  rcases (show l < 2 ∨ l = 2 by omega) with h | rfl
  · rw [comps_eq01 l h] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl <;>
    · intro x hx
      simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp
  · rw [comps_eq2] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl <;>
    · intro x hx
      simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        or_false, false_or] at hx
      rcases hx with rfl | rfl | rfl <;> simp

/-- The window's row is the left mode's own declared row (by name, as the tool reads it). -/
theorem invRow_faithful (l : ℕ) (hl : l < 3) :
    Handoff.invRowOf platoon_delay_linkloss_IRv2 (mL l)
      = some (platoon_delay_linkloss_IRv2.invariants.getD l ("", PForm.tt)).2 := by
  interval_cases l <;> decide

/-! ## The cut families -/

noncomputable def cL (l : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.L (cutAtomsOfX platoon_delay_linkloss_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.R (cutAtomsOfX platoon_delay_linkloss_cutsV2X.R (mR q).name)

theorem gL_ge21 : hostAtomG vs 3 Side.L (.cmp ">=" (.var "g") (.num "21.0")) = thrGe (Lv 0) 21 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp210, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_le40 : hostAtomG vs 3 Side.L (.cmp "<=" (.var "g") (.num "40.0")) = thrLe (Lv 0) 40 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp400, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_ge29 : hostAtomG vs 3 Side.L (.cmp ">=" (.var "g") (.num "29.0")) = thrGe (Lv 0) 29 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp290, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_le60 : hostAtomG vs 3 Side.L (.cmp "<=" (.var "g") (.num "60.0")) = thrLe (Lv 0) 60 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp600, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gR_ge20 : hostAtomG vs 3 Side.R (.cmp ">=" (.var "g") (.num "20.0")) = thrGe (Rv 0) 20 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp200, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_le40 : hostAtomG vs 3 Side.R (.cmp "<=" (.var "g") (.num "40.0")) = thrLe (Rv 0) 40 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp400, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]
theorem gR_ge30 : hostAtomG vs 3 Side.R (.cmp ">=" (.var "g") (.num "30.0")) = thrGe (Rv 0) 30 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp300, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "g") (.num "21.0")), thrGe (Lv 0) 21),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "g") (.num "40.0")), thrLe (Lv 0) 40)] := by
  rw [← gL_ge21, ← gL_le40]; rfl
theorem cL_1 : cL 1 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "g") (.num "29.0")), thrGe (Lv 0) 29)] := by
  rw [← gL_ge29]; rfl
theorem cL_2 : cL 2 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "g") (.num "21.0")), thrGe (Lv 0) 21),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "g") (.num "60.0")), thrLe (Lv 0) 60)] := by
  rw [← gL_ge21, ← gL_le60]; rfl
theorem cR_0 : cR 0 =
    [(hostAtomF vs 3 Side.R (.cmp ">=" (.var "g") (.num "20.0")), thrGe (Rv 0) 20),
     (hostAtomF vs 3 Side.R (.cmp "<=" (.var "g") (.num "40.0")), thrLe (Rv 0) 40)] := by
  rw [← gR_ge20, ← gR_le40]; rfl
theorem cR_1 : cR 1 =
    [(hostAtomF vs 3 Side.R (.cmp ">=" (.var "g") (.num "30.0")), thrGe (Rv 0) 30)] := by
  rw [← gR_ge30]; rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 3) :
    ∀ x ∈ cutAtomsOfX platoon_delay_linkloss_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, platoon_delay_linkloss_cutsV2X, mL, platoon_delay_linkloss_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 2) :
    ∀ x ∈ cutAtomsOfX platoon_delay_linkloss_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, platoon_delay_linkloss_cutsV2X, mR, platoon_delay_linkloss_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 2) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vs 3 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard platoon_delay_linkloss_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, platoon_delay_linkloss_cutsV2X, mL, platoon_delay_linkloss_IRv2] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, platoon_delay_linkloss_cutsV2X, mL, platoon_delay_linkloss_IRv2] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hp210, hp400, hp290, hp600, vs, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, platoon_delay_linkloss_IRv2, Run.lowerF, Run.lowerE, hp210, hp400, hp300,
        hp600, vs, Run.resolveVar, List.findIdx?_cons]

theorem sat_guardL2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.L (mL 2)) ν ↔ (21 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ 60) := by
  simp [hostGuard, mL, platoon_delay_linkloss_IRv2, Run.lowerF, Run.lowerE, hp210, hp600, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv]


/-! ## Side splits -/

theorem fL_pipe (l : ℕ) (i : Fin 3) : fL l i =
    (((some (mL l)).bind (Run.dynOf vs 3 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fR_pipe (q : ℕ) (i : Fin 3) : fR q i =
    (((some (mR q)).bind (Run.dynOf vs 3 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL_pipe : domL =
    (((some (mL 0)).bind (fun m => Run.lowerF vs 3 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domR_pipe : domR =
    (((some (mR 0)).bind (fun m => Run.lowerF vs 3 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL (l : ℕ) (hl : l < 3) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, platoon_delay_linkloss_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 3) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, platoon_delay_linkloss_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, platoon_delay_linkloss_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, platoon_delay_linkloss_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vs 3 Side.L (mL l)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vs (mL l) ?_
  interval_cases l <;>
    simp [mL, platoon_delay_linkloss_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]

/-- Every row's components (out-of-range rows are the empty row: `0 ≤ 0`) live on `Lv ∪ Rv`. -/
theorem comps_fv_all (l : ℕ) : ∀ c ∈ g l :: gs l, c.fv ⊆ range Lv ∪ range Rv := by
  by_cases hl : l < 3
  · exact comps_fv l hl
  · have hnil : comps l = [] := by
      have : platoon_delay_linkloss_IRv2.invariants.getD l ("", PForm.tt) = ("", PForm.tt) :=
        List.getD_eq_default _ _ (by simp [platoon_delay_linkloss_IRv2]; omega)
      rw [comps, this]; simp [hostComps, Oracle.invComponents]
    intro c hc
    simp only [g, gs, hnil, List.getD_nil, List.mem_cons, List.not_mem_nil, or_false,
      or_self] at hc
    subst hc
    simp [Term.fv]

theorem thr_fv_L (j : Fin 3) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 3) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 3) (hq : q < 2) :
    ∀ c ∈ g l :: gs l ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv_all l _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv_all l _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hc
  interval_cases l <;> interval_cases q <;>
    simp only [cL_0, cL_1, cL_2, cR_0, cR_1, List.mem_cons, List.not_mem_nil,
      or_false] at hc <;>
    rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
    rcases ha with rfl | rfl <;>
    first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2 | exact (thr_fv_R _ _).1 |
      exact (thr_fv_R _ _).2

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (FOLLOW 0, CATCH 1, BRAKE 2). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 0), (0, 2), (1, 0), (1, 1), (2, 2), (2, 0)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range platoon_delay_linkloss_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (platoon_delay_linkloss_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 3 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

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

theorem hguardR (q : ℕ) (hq : q < 3) : (hostGuard vs 3 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R vs (mR q) (by
    interval_cases q <;> simp [mR, platoon_delay_linkloss_IRv2, Parse.PForm.namesFree,
      Parse.PExpr.namesFree])

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 3 := by decide

theorem hgR : GuardsRight Gr := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact hguardR p.2 (edgeList_tgt p hp)

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of
the mode it enters. -/
theorem Gr_guards : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = hostGuard vs 3 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

/-- The non-sink right guards, evaluated (`FOLLOW`: `20 ≤ g < 40`; `CATCH`: `g ≥ 30`). -/
theorem sat_guardR (q : ℕ) (hq : q < 2) (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) ν ↔
      (if q = 0 then 20 ≤ ν (Rv 0) ∧ ν (Rv 0) < 40 else 30 ≤ ν (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mR, platoon_delay_linkloss_IRv2, Run.lowerF, Run.lowerE, hp200, hp400,
      hp300, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

/-- The non-sink regions, evaluated (`FOLLOW`: `20 ≤ g ≤ 40`; `CATCH`: `g ≥ 30`). -/
theorem cutSatR_val (q : ℕ) (hq : q < 2) (ν : State (Var 3)) :
    CutSat (cR q) ν ↔ (if q = 0 then 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 40 else 30 ≤ ν (Rv 0)) := by
  have hiff : CutSat (cR q) ν ↔ ∀ a ∈ cR q, Term.eval a.2 ν ≤ 0 :=
    ⟨fun h a ha => (hiffR q hq a ha ν).mp (h a ha),
     fun h a ha => (hiffR q hq a ha ν).mpr (h a ha)⟩
  rw [hiff]
  interval_cases q
  · rw [cR_0]; simp [thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_1]; simp [thrGe, Term.eval, AOp.interp]

/-! ## Regions: the right mode's kept cut atoms; the pruned sink `BRAKE` is excluded -/

noncomputable def region (q : ℕ) : Formula (Var 3) :=
  if q < 2 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 2) (ν : State (Var 3)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region2 (ν : State (Var 3)) : ¬ Formula.sat (region 2) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) (hq : q < 3) : (region q).fv ⊆ range Rv := by
  by_cases h2 : q < 2
  · simp only [region, h2, if_true]
    intro x hx
    unfold cutF at hx
    have key : ∀ (L : List (CutAtomP 3)) (acc : Formula (Var 3)),
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
      simp only [cR_0, cR_1, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h2, if_false]
    simp [Formula.fv, Term.fv]

/-! ## O2: the kept atoms stay along the joint flows (rational, from the own field's sign) -/

theorem stayL (l q : ℕ) (hl : l < 3) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  have hf := fL0_eval l hl
  interval_cases l
  · rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 21 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
    · exact boxle_thrLe_L 0 40 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
  · rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_L 0 29 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
  · rw [cL_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 21 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit
    · exact boxle_thrLe_L 0 60 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kL, cLc]; norm_num; linarith) hinit

theorem stayR (l q : ℕ) (hq : q < 2) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hf := fR0_eval q hq
  have hc : (0:ℝ) ≤ 1 := zero_le_one
  interval_cases q
  · rw [cR_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 20 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR]; norm_num; linarith) hinit
    · exact boxle_thrLe_R 0 40 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [hf]; simp only [kR]; norm_num; linarith) hinit
  · rw [cR_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 0 30 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; simp only [kR]; norm_num; linarith) hinit

/-! ## Existence: FOLLOW and CATCH contract toward 30 inside `[0, 60]` -/

theorem hwfB (q : ℕ) (hq : q < 2) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const 1) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (kR q) 30)
    (lam := Term.const 1) (domR := bandDom 0 0 60) ?_ ?_ ?_
  · intro i x
    match i with
    | 0 =>
        simp only [Term.eval, AOp.interp, contractF, if_true]
        rw [fR0_eval q hq]
    | 1 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR_pad q (by omega) 1 (by decide)]
        simp [Term.eval]
    | 2 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR_pad q (by omega) 2 (by decide)]
        simp [Term.eval]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · refine WellFormedFlowB_contract 0 (kR q) 30 0 60 dt ?_ (by norm_num) (by norm_num)
    unfold kR; split_ifs <;> norm_num

theorem es (l q : ℕ) (hq : q < 2) (dt : ℝ) (A : Formula (Var 3)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR q) (Term.const 1) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ
  refine hExistSegB_of_wellFormedFlowB (fL l) (fR q) _ domL domR dt _ (hwfB q hq dt) ?_ ?_
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

/-- One pack: left window `l` at its OWN declared row (`invRow = l`), right mode `q`, at the
cover's λ = 1 and strata order `[0, 1]`. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX platoon_delay_linkloss_IRv2 platoon_delay_linkloss_cutsV2X 3 l [0, 1] 1 l q

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (g l :: gs l) (fL l) (fR q) 1
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

theorem couple (l q : ℕ) (hl : l < 3) (hq : q < 2) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX (g l) (gs l) (g l :: gs l) (cL l) (cR q) (fL l) (fR q) 1 one_pos domL domR 1 dt
    (hfL l hl) (hfR q (by omega)) hdomL hdomR (anchor_fv l q hl hq) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl) (stayR l q hq)
    (verd_core l q hl (by omega) hv) (es l q hq dt _)

theorem sat_faModal_monoPost {P Q : Program (Var 3)} {A B : Formula (Var 3)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 3)}
    (h : Formula.sat (faModal (Equiv.refl (Var 3)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l qs : ℕ) (hl : l < 3) (hqs : qs < 2) (dt : ℝ) (hv : Verd l qs)
    {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq ([] ++ [Program.ode (rightBlock (fR qs) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM (g l) (gs l)) env) (region qs))) σ := by
  have htgF : tg ∉ (FM (g l) (gs l ++ atomTerms (cL l) (cR qs))).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv l qs hl hqs g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
    (Formula.and domL domR) 1 dt 1 htgF htgenv [] (by simp)
    (fun σ' hσ' => hσ'.2.1) (by simp)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fR qs) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR qs, Term.const 1, domR⟩ : RepoHop 3)
        (hfR qs (by omega)) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l qs hl hqs dt hv σ' hσ')
    hσ
  refine sat_faModal_monoPost ?_ (by simpa using hfa)
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append (g l) (gs l) _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR qs hqs) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt qs hqs ν).mpr hRν⟩

/-! ## The per-left-mode step provider: STAY in the certified start mode -/

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 3)) (ψ : Formula (Var 3))
    {σ : State (Var 3)}
    (hbody : Formula.sat (hostGuard vs 3 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 3))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3))
      (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

/-- **Nonblocking at the end of a response**, discharged from the explicit end state:
`FOLLOW`'s region `[20, 40]` is covered by `FOLLOW`'s guard `[20, 40)` and `CATCH`'s
`g ≥ 30` (the declared edge `FOLLOW → CATCH`); `CATCH`'s region is its guard. -/
theorem nonblock {F' : Formula (Var 3)} (q : ℕ) (hq : q < 2) :
    NonblockingAt Gr q (Formula.and F' (region q)) (fun qf => Formula.and F' (region qf)) := by
  intro μ ⟨hF, hreg⟩
  have hr := (cutSatR_val q hq μ).mp ((sat_region_lt q hq μ).mp hreg)
  have pick : ∀ t, (q, t) ∈ edgeList → t < 2 → Formula.sat (hostGuard vs 3 Side.R (mR t)) μ →
      CutSat (cR t) μ →
      ∃ e ∈ Gr.edgesFrom q, SwitchLegal e μ ∧ Formula.sat (Formula.and F' (region e.tgt)) μ :=
    fun t ht ht2 hg hc => ⟨edgeW q t, edge_mem q t ht, hg, hF, (sat_region_lt t ht2 μ).mpr hc⟩
  interval_cases q
  · simp only [if_true] at hr
    by_cases hx : μ (Rv 0) < 40
    · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) μ).mpr
        (by simp only [if_true]; exact ⟨hr.1, hx⟩))
        ((cutSatR_val 0 (by norm_num) μ).mpr (by simp only [if_true]; exact hr))
    · replace hx := not_lt.mp hx
      exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) μ).mpr
        (by norm_num; linarith))
        ((cutSatR_val 1 (by norm_num) μ).mpr (by norm_num; linarith))
  · simp only [show (1:ℕ) ≠ 0 from by decide, if_false] at hr
    exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) μ).mpr
      (by norm_num; exact hr))
      ((cutSatR_val 1 (by norm_num) μ).mpr (by norm_num; exact hr))

theorem stayCase (l q : ℕ) (hl : l < 3) (hq : q < 2) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 3)} (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hreg : Formula.sat (region q) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (fun qf => Formula.and (Formula.and (FM (g l) (gs l)) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hanchor : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q)))
      (Formula.and domL domR)) σ := by
    refine ⟨(sat_FM_append (g l) (gs l) _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
      ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
  exact gresp_final (Gr_modeAt q (by omega)) (respond l q hl hq dt hv hanchor) (nonblock q hq)

/-- Left mode `l`'s window, every admissible right start: FOLLOW and CATCH stay (the
cover's response), BRAKE is excluded by its (false) region. -/
theorem HmultiL (l : ℕ) (hl : l < 3) (dt : ℝ) (h0 : Verd l 0) (h1 : Verd l 1) :
    ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region q)) σ →
      GResp Gr q (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (fun qf => Formula.and (Formula.and (FM (g l) (gs l)) env) (region qf)) σ := by
  intro q hq σ _ hσ
  rw [Gr_len] at hq
  match q, hq, hσ with
  | 0, _, hσ => exact stayCase l 0 hl (by norm_num) dt h0 hσ.1 hσ.2
  | 1, _, hσ => exact stayCase l 1 hl (by norm_num) dt h1 hσ.1 hσ.2
  | 2, _, hσ => exact absurd hσ.2 (not_sat_region2 σ)


/-! ## The declared rows, per left mode -/

noncomputable def FRow (l : ℕ) : Formula (Var 3) := FM (g l) (gs l)
noncomputable def ϕRow (l : ℕ) : RFormula (Var 3) := canonInvM (g l) (gs l)

theorem encode_ϕRow (l : ℕ) : encode (Equiv.refl (Var 3)) (ϕRow l) = FRow l :=
  encode_canonInvM _ _

theorem aux_notin_FRow (a : Fin 3) (l : ℕ) : ((Side.Aux, a) : Var 3) ∉ (FRow l).fv :=
  notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv_all l g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-- The rows, evaluated. -/
theorem sat_FRow (l : ℕ) (hl : l < 3) (ω : State (Var 3)) :
    Formula.sat (FRow l) ω ↔
      (if l = 2 then 11/20 * ω (Lv 0) - (ω (Rv 0) - 169/20) else ω (Lv 0) - (ω (Rv 0) + 1)) ≤ 0
      ∧ ω (Rv 0) - (ω (Lv 0) + 3) ≤ 0 := by
  rw [FRow, sat_FM_iff]
  rw [← eval_g l hl, ← eval_gs0 l hl]
  simp only [gs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.getD_cons_zero]

/-! ## The left automaton, from the file -/

def nextL : List (List ℕ) :=
  (List.range 3).map (fun l =>
    (mL l).next.filterMap (Handoff.leftModeIndex platoon_delay_linkloss_IRv2))

/-- `FOLLOW → [CATCH, FOLLOW, LOST]`, `CATCH → [FOLLOW, CATCH, LOST]`, `LOST → [LOST]`. -/
theorem nextL_eq : nextL = [[1, 0, 2], [0, 1, 2], [2]] := by decide

theorem nextL_transitions :
    ((List.range 3).flatMap (fun m' => (nextL.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions platoon_delay_linkloss_IRv2 := by decide

noncomputable def guardsL : List (Formula (Var 3)) :=
  (List.range 3).map (fun l => hostGuard vs 3 Side.L (mL l))

/-- The left automaton: mode `l`'s window re-tests `l`'s guard and flows `l`'s field
(clock-capped at `dt`, one piece). -/
noncomputable def A (dt : ℝ) : LeftAut 3 :=
  { windows := (List.range 3).map (fun l =>
      gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1),
    guards := guardsL,
    next := nextL }

theorem A_numModes (dt : ℝ) : (A dt).numModes = 3 := rfl

theorem A_window (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (A dt).window t = gwindowSeg (hostGuard vs 3 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1 := by
  interval_cases t <;> rfl

theorem A_guard (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (A dt).guard t = hostGuard vs 3 Side.L (mL t) := by
  interval_cases t <;> rfl

theorem A_succ (dt : ℝ) (m' : ℕ) : (A dt).succ m' = nextL.getD m' [] := rfl

theorem hnext (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', t < (A dt).numModes := by
  intro m' hm' t ht
  rw [A_numModes] at hm' ⊢
  rw [A_succ, nextL_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hgrd (dt : ℝ) : ∀ t < (A dt).numModes, ((A dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_guard dt t ht]
  exact hguardL t ht

theorem hwin (dt : ℝ) : ∀ t < (A dt).numModes,
    Program.vars ((A dt).window t) ⊆ {((Side.Aux, 1) : Var 3)} ∪ range Lv := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  exact vars_gwindowSegL_sub _ (fL t) domL 1 dt 1 (hguardL t ht) (hfL t ht) hdomL

/-! ## Freshness of `u_L` and `mv` -/

theorem hulenv : uL ∉ env.fv := fun h => by
  rcases h with h | h
  · exact aux_notin_range_Lv 2 (hdomL h)
  · exact aux_notin_range_Rv 2 (hdomR h)

theorem hmvenv : mv ∉ env.fv := fun h => by
  rcases h with h | h
  · exact aux_notin_range_Lv 0 (hdomL h)
  · exact aux_notin_range_Rv 0 (hdomR h)

/-! ## The mode-consistent region: the right mode's guard and its kept cut atoms -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard (the state a guarded
jump into `q` leaves the right in) and its checked cuts (`region`). -/
noncomputable def gregion (q : ℕ) : Formula (Var 3) :=
  regionG (fun q => hostGuard vs 3 Side.R (mR q)) region q

theorem hguardR_all (q : ℕ) : (hostGuard vs 3 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [platoon_delay_linkloss_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem gregion_fv (q : ℕ) (hq : q < 3) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

/-- The left windows leave the right guards' truth values unchanged. -/
theorem frameG (dt : ℝ) (t : ℕ) (ht : t < 3) (q : ℕ) {σ ν : State (Var 3)}
    (h : Program.sem ((A dt).window t) σ ν) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) σ → Formula.sat (hostGuard vs 3 Side.R (mR q)) ν :=
  frames_right (hwin dt t (by rw [A_numModes]; exact ht)) (hguardR_all q) h

theorem hmvreg : ∀ q, mv ∉ (region q).fv := by
  intro q h
  by_cases hq : q < 3
  · exact aux_notin_range_Rv 0 (region_fv q hq h)
  · simp only [region, show ¬ q < 2 from by omega, if_false] at h
    simp [Formula.fv, Term.fv] at h

theorem hulBk : uL ∉ (mvRegion mv region Gr.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv region Gr.modes.length (fun q hq => region_fv q hq) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hmvregG : ∀ q, mv ∉ (gregion q).fv := fun q =>
  notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) (hmvreg q)

theorem hulBkG : uL ∉ (mvRegion mv gregion Gr.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv gregion Gr.modes.length (fun q hq => gregion_fv q hq) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hulG (dt : ℝ) : ∀ t, uL ∉ ((A dt).guard t).fv := by
  intro t h
  by_cases ht : t < 3
  · exact aux_notin_range_Lv 2 (hgrd dt t ht h)
  · have : (A dt).guard t = Formula.tt := by
      unfold LeftAut.guard A guardsL
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem framesGw (t : ℕ) (dt : ℝ) (a : Fin 3) (ha : a ≠ 1) :
    FramesMv (gwindowSeg (hostGuard vs 3 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1)
      ((Side.Aux, a) : Var 3) := by
  refine framesMv_gwindow _ (fL t) domL tg dt 1 _ (by simpa [Prod.ext_iff] using ha) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
  exact aux_ne_Lv a i hi

theorem hframesUl (dt : ℝ) : ∀ t, FramesMv ((A dt).window t) uL := by
  intro t
  by_cases ht : t < 3
  · rw [A_window dt t ht]
    exact framesGw t dt 2 (by decide)
  · have : (A dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window A
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulR : uL ∉ (rightAutomatonBody Gr mv).bv :=
  notMem_bv_rightAutomatonBody_G Gr mv uL (by decide) (aux_notin_range_Rv 2) hgR hRv

/-! ## The handoffs, in-kernel (domain-conditioned at `→ LOST`) -/

/-- FOLLOW ↔ CATCH: identical rows. FOLLOW/CATCH → LOST: from `g_R ≥ g_L − 1` and LOST's guard
`g_L ≥ 21`, `g_R − 8.45 ≥ g_L − 9.45 ≥ 0.55 g_L`; the upper conjunct is common. -/
theorem handoff (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat env ω → Formula.sat ((A dt).guard t) ω →
      Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ hG
  rw [A_numModes] at hm'
  rw [A_succ, nextL_eq] at ht
  have ht3 : t < 3 := by interval_cases m' <;> simp at ht <;> omega
  rw [A_guard dt t ht3] at hG
  rw [sat_FRow m' hm'] at hF
  rw [sat_FRow t ht3]
  interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl | rfl <;>
    simp only [show (0:ℕ) ≠ 2 from by decide, show (1:ℕ) ≠ 2 from by decide, if_true,
      if_false] at hF ⊢ <;>
    first
    | exact hF
    | (have hg := (sat_guardL2 ω).mp hG
       exact ⟨by linarith [hF.1, hg.1], hF.2⟩)

/-! ## The per-mode steps -/

theorem hstepM (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h10 : Verd 1 0) (h11 : Verd 1 1)
    (h20 : Verd 2 0) (h21 : Verd 2 1) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv gregion Gr.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((A dt).window t)
      (Program.star (rightAutomatonBody Gr mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv gregion Gr.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  have hv0 : Verd t 0 := by interval_cases t <;> assumption
  have hv1 : Verd t 1 := by interval_cases t <;> assumption
  exact hstepMode_GR Gr mv (FRow t) env gregion _ (aux_notin_FRow 0 t) hmvenv hmvregG
    hfresh (guardsFresh_of_right Gr 0 hgR) hlt (framesGw t dt 0 (by decide)) (HMode_regionG Gr mv _ region Gr_guards (FRow t) env _
      (fun q _ σ ν hrun => frameG dt t ht q (by rw [A_window dt t ht]; exact hrun))
      (fun q hq σ hmv hσ _ hreg => (HmultiL t ht dt hv0 hv1) q hq σ hmv ⟨hσ, hreg⟩))

/-! ## Theorem 3, mode-keyed -/

/-- **`platoon_delay_linkloss` (suite_v2), Theorem 3 at the DECLARED mode-dependent invariant.**
Left: the automaton of the file (`FOLLOW → [CATCH, FOLLOW, LOST]`, `CATCH → [FOLLOW, CATCH,
LOST]`, `LOST → [LOST]`), each step `?guard_t ; u_L := t ; ?guard_t ; window_t` with `u_L =
(Aux, 2)` the left mode variable; right: the three-mode automaton of the file (declared edges,
the pruned `FOLLOW → BRAKE` included). The loop invariant keys the declared rows by `u_L`
(FOLLOW = CATCH: `g_L ≤ g_R + 1 ∧ g_R ≤ g_L + 3`; LOST: `0.55 g_L ≤ g_R − 8.45 ∧ g_R ≤ g_L + 3`),
plus the evolve envelope `0 ≤ g ≤ 60` on both sides and the right mode's region — its kept cut
atoms (`20 ≤ g_R ≤ 40` in FOLLOW, `g_R ≥ 30` in CATCH), BRAKE excluded (the pruned sink: the
right is never in it). Response: in every left window, STAY in the start mode (FOLLOW or CATCH)
on the certified joint segment at the cover's λ = 1. Handoffs (in-kernel, no Z3): FOLLOW ↔ CATCH
identical rows; FOLLOW/CATCH → LOST domain-conditioned on LOST's guard `g_L ≥ 21`. Staying of
every kept atom is proved rationally from the own field's sign. Residuals: six stratified
verdict packs `Verd l q` (left window `l` at its own row, right mode `q ∈ {FOLLOW, CATCH}`;
`modalVerdX`, the tool's own narrowed queries). -/
theorem platoon_delay_linkloss_modeKeyed (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h10 : Verd 1 0) (h11 : Verd 1 1)
    (h20 : Verd 2 0) (h21 : Verd 2 1) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody Gr mv)
      (psiK uL ϕRow (A dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL Gr mv FRow ϕRow domL domR
    (mvRegion mv gregion Gr.modes.length) (mvRegionR mv gregion Gr.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (A dt) Gr 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) hgR hRv
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody Gr mv) FRow env
      (mvRegion mv gregion Gr.modes.length) (aux_notin_FRow 2) hulenv hulBkG (hulG dt)
      (hframesUl dt) hulR (hnext dt) (hstepM dt h00 h01 h10 h11 h20 h21) (handoff dt)
  · exact hddF_modeKeyed_G (A dt) Gr 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv gregion Gr.modes.length) (hwin dt) (hgrd dt) (hnext dt) hgR hRv
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv gregion Gr.modes.length (fun q hq => gregion_fv q hq) hv)

end V2PlatoonDelayLinkloss
end RelCertifier
