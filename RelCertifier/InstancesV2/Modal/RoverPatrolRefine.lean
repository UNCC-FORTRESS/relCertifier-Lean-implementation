/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_refine` (suite_v2) — mode-keyed Theorem 3 at the declared rows

The refinement rung of `rover_patrol_zones`: the deployed rover (left) carries its motor
lag, `v' = a`, `s' = v`, `a' = 5 (1.25 (0.8 c − v) − a)` (critically damped, double root
2.5); the reference (right) is the first-order nominal rover of `rover_patrol_zones`
(`v' = c − v`, `s' = v`, `a' = 0`, `c = 0.6/0.9/1.1/1.5`). The file declares one row per
LEFT zone (`a_L + 5 v_L ≤ 5 v_R + 0.35 ∧ s_L ≤ s_R + m`, `m = 0.5, 1, 1, 2`). Lowered at
`n = 3` (`v, s, a` at 0, 1, 2), `mv = (Aux, 0)`, `tg = (Aux, 1)`, `u_L = (Aux, 2)`. Every
window is certified at the cover's λ = 9/4.

Adapted from `InstancesV2/Modal/RoverPatrolZones.lean` (the mode-keyed composition, the
explicit zone runs, the right-only reposition prefixes) and `InstancesV2/Modal/AccTuneLag.lean`
(the left LINEAR-FORM CUT CHAIN — `q = a + 2.5 (v − c)` in a box, then the derived speed
bounds — lifted by the `CutLiftX` shape lemmas). The odometer has no upper wall
(`docs/SUITE-REDESIGN.md` §19).
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.rover_patrol_refine

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolRefine

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["v", "s", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := rover_patrol_refine_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := rover_patrol_refine_IRv2.R.modes.getD q dm

abbrev mv : Var 3 := (Side.Aux, 0)
abbrev tg : Var 3 := (Side.Aux, 1)
abbrev uL : Var 3 := (Side.Aux, 2)

noncomputable def fL (l : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domL : Formula (Var 3) := hostEvolve vs 3 Side.L (mL 0)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
noncomputable def env : Formula (Var 3) := Formula.and domL domR

noncomputable def comps (l : ℕ) : List (Term (Var 3)) :=
  hostComps vs 3 (rover_patrol_refine_IRv2.invariants.getD l ("", PForm.tt)).2
noncomputable def g (l : ℕ) : Term (Var 3) := (comps l).getD 0 (Term.const 0)
noncomputable def gs (l : ℕ) : List (Term (Var 3)) := [(comps l).getD 1 (Term.const 0)]

/-- The cover's stretch (every window). -/
noncomputable abbrev lam : ℝ := 9/4
theorem lam_pos : 0 < lam := by norm_num

/-! ## Parse pins -/

theorem hp0_48 : Run.parseRat "0.48" = some ((12/25 : ℚ)) := by
  have h : parseQ "0.48" = some (⟨48, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_72 : Run.parseRat "0.72" = some ((18/25 : ℚ)) := by
  have h : parseQ "0.72" = some (⟨72, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_88 : Run.parseRat "0.88" = some ((22/25 : ℚ)) := by
  have h : parseQ "0.88" = some (⟨88, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_2 : Run.parseRat "1.2" = some ((6/5 : ℚ)) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_8 : Run.parseRat "0.8" = some ((4/5 : ℚ)) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_95 : Run.parseRat "0.95" = some ((19/20 : ℚ)) := by
  have h : parseQ "0.95" = some (⟨95, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_05 : Run.parseRat "1.05" = some ((21/20 : ℚ)) := by
  have h : parseQ "1.05" = some (⟨105, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_25 : Run.parseRat "1.25" = some ((5/4 : ℚ)) := by
  have h : parseQ "1.25" = some (⟨125, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm0_95 : Run.parseRat "-0.95" = some ((-19/20 : ℚ)) := by
  have h : parseQ "-0.95" = some (⟨-95, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm1_55 : Run.parseRat "-1.55" = some ((-31/20 : ℚ)) := by
  have h : parseQ "-1.55" = some (⟨-155, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm1_95 : Run.parseRat "-1.95" = some ((-39/20 : ℚ)) := by
  have h : parseQ "-1.95" = some (⟨-195, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm2_75 : Run.parseRat "-2.75" = some ((-11/4 : ℚ)) := by
  have h : parseQ "-2.75" = some (⟨-275, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_1 : Run.parseRat "1.1" = some ((11/10 : ℚ)) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_3 : Run.parseRat "1.3" = some ((13/10 : ℚ)) := by
  have h : parseQ "1.3" = some (⟨13, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_1 : Run.parseRat "0.1" = some ((1/10 : ℚ)) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp2_5 : Run.parseRat "2.5" = some ((5/2 : ℚ)) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp5_0 : Run.parseRat "5.0" = some ((5 : ℚ)) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_35 : Run.parseRat "0.35" = some ((7/20 : ℚ)) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_6 : Run.parseRat "0.6" = some ((3/5 : ℚ)) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_9 : Run.parseRat "0.9" = some ((9/10 : ℚ)) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_5 : Run.parseRat "1.5" = some ((3/2 : ℚ)) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm2_0 : Run.parseRat "-2.0" = some ((-2 : ℚ)) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp2_0 : Run.parseRat "2.0" = some ((2 : ℚ)) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_0 : Run.parseRat "0.0" = some ((0 : ℚ)) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_6 : Run.parseRat "1.6" = some ((8/5 : ℚ)) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp20_0 : Run.parseRat "20.0" = some ((20 : ℚ)) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp50_0 : Run.parseRat "50.0" = some ((50 : ℚ)) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_3 : Run.parseRat "0.3" = some ((3/10 : ℚ)) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_5 : Run.parseRat "0.5" = some ((1/2 : ℚ)) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm0_5 : Run.parseRat "-0.5" = some ((-1/2 : ℚ)) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_0 : Run.parseRat "1.0" = some ((1 : ℚ)) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0 : Run.parseRat "0" = some ((0 : ℚ)) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## Per-zone constants (the right zones' floors and caps, the left set points) -/

def loS : ℕ → String
  | 0 => "0.0" | 1 => "20.0" | 2 => "20.0" | _ => "50.0"
def loQ : ℕ → ℚ
  | 0 => 0 | 1 => 20 | 2 => 20 | _ => 50
def capS : ℕ → String
  | 0 => "0.6" | 1 => "0.9" | 2 => "1.1" | _ => "1.5"
def capQ : ℕ → ℚ
  | 0 => 3/5 | 1 => 9/10 | 2 => 11/10 | _ => 3/2
def cLQ : ℕ → ℚ
  | 0 => 12/25 | 1 => 18/25 | 2 => 22/25 | _ => 6/5
def mQ : ℕ → ℚ
  | 0 => 1/2 | 1 => 1 | 2 => 1 | _ => 2

noncomputable def loL (l : ℕ) : ℝ := (loQ l : ℝ)
noncomputable def capL (l : ℕ) : ℝ := (capQ l : ℝ)
noncomputable def cLv (l : ℕ) : ℝ := (cLQ l : ℝ)
noncomputable def mL' (l : ℕ) : ℝ := (mQ l : ℝ)

theorem hlo (l : ℕ) (hl : l < 4) : Run.parseRat (loS l) = some (loQ l) := by
  interval_cases l <;> simp only [loS, loQ] <;> first | exact hp0_0 | exact hp20_0 | exact hp50_0
theorem hcap (l : ℕ) (hl : l < 4) : Run.parseRat (capS l) = some (capQ l) := by
  interval_cases l <;> simp only [capS, capQ] <;>
    first | exact hp0_6 | exact hp0_9 | exact hp1_1 | exact hp1_5

theorem lo_nonneg (l : ℕ) (hl : l < 4) : 0 ≤ loL l := by
  interval_cases l <;> norm_num [loL, loQ]
theorem cap_bounds (l : ℕ) (hl : l < 4) : 3/5 ≤ capL l ∧ capL l ≤ 3/2 := by
  interval_cases l <;> norm_num [capL, capQ]

/-! ## Evaluations of the lowered data -/

theorem fL0_eval (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval (fL l 0) x = x (Lv 2) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem fL1_eval (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval (fL l 1) x = x (Lv 0) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

/-- The lag: `a' = 5 (1.25 (c − v) − a) = −6.25 (v − c) − 5 a`. -/
theorem fL2_eval (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval (fL l 2) x = -(25/4) * (x (Lv 0) - cLv l) - 5 * x (Lv 2) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv,
      cLv, cLQ] <;> ring

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = capL q - x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv,
      capL, capQ]

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domL (x : State (Var 3)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 8/5 ∧ 0 ≤ x (Lv 1) ∧ -2 ≤ x (Lv 2) ∧
      x (Lv 2) ≤ 2) := by
  simp only [domL, hostEvolve, mL, rover_patrol_refine_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv, and_assoc]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8/5 ∧ 0 ≤ x (Rv 1) ∧ -2 ≤ x (Rv 2) ∧
      x (Rv 2) ≤ 2) := by
  simp only [domR, hostEvolve, mR, rover_patrol_refine_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem domL_univ (l : ℕ) (hl : l < 4) : hostEvolve vs 3 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 3 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-- The declared rows, lowered: `(a_L + 5 v_L) − (5 v_R + 0.35) ≤ 0`, `s_L − (s_R + m) ≤ 0`. -/
theorem comps_eq (l : ℕ) (hl : l < 4) : comps l =
    [Term.binop .sub (Term.binop .add (Term.var (Lv 2)) (Term.binop .mul (Term.const 5)
        (Term.var (Lv 0))))
      (Term.binop .add (Term.binop .mul (Term.const 5) (Term.var (Rv 0))) (Term.const (7/20))),
     Term.binop .sub (Term.var (Lv 1)) (Term.binop .add (Term.var (Rv 1))
       (Term.const (mL' l)))] := by
  have h1 : ("L_v".drop 2).copy = "v" := by decide
  have h2 : ("R_v".drop 2).copy = "v" := by decide
  have h3 : ("L_s".drop 2).copy = "s" := by decide
  have h4 : ("R_s".drop 2).copy = "s" := by decide
  have h5 : ("L_a".drop 2).copy = "a" := by decide
  interval_cases l <;>
    simp [comps, hostComps, rover_patrol_refine_IRv2, Oracle.invComponents, Run.lowerE, vs,
      Run.resolveVar, Parse.dr, h1, h2, h3, h4, h5, List.findIdx?_cons, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      ITerm.toHost, Lv, Rv, mL', mQ]

theorem comps_nil (l : ℕ) (hl : ¬ l < 4) : comps l = [] := by
  have : rover_patrol_refine_IRv2.invariants.getD l ("", PForm.tt) = ("", PForm.tt) :=
    List.getD_eq_default _ _ (by simp [rover_patrol_refine_IRv2]; omega)
  rw [comps, this]; simp [hostComps, Oracle.invComponents]

theorem eval_g (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval (g l) x = (x (Lv 2) + 5 * x (Lv 0)) - (5 * x (Rv 0) + 7/20) := by
  simp [g, comps_eq l hl, Term.eval, AOp.interp]
theorem eval_gs0 (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval ((gs l).getD 0 (Term.const 0)) x = x (Lv 1) - (x (Rv 1) + mL' l) := by
  simp [gs, comps_eq l hl, Term.eval, AOp.interp]

theorem comps_fv_all (l : ℕ) : ∀ c ∈ g l :: gs l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  by_cases hl : l < 4
  · simp only [g, gs, comps_eq l hl, List.getD_cons_zero, List.getD_cons_succ, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · intro x hx
      simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        or_false, false_or] at hx
      rcases hx with ((rfl | rfl) | (rfl | rfl)) | rfl | rfl <;> simp
  · simp only [g, gs, comps_nil l hl, List.getD_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_self] at hc
    subst hc
    simp [Term.fv]

theorem invRow_faithful (l : ℕ) (hl : l < 4) :
    Handoff.invRowOf rover_patrol_refine_IRv2 (mL l)
      = some (rover_patrol_refine_IRv2.invariants.getD l ("", PForm.tt)).2 := by
  interval_cases l <;> decide

/-! ## The cut families -/

noncomputable def cL (l : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.L (cutAtomsOfX rover_patrol_refine_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.R (cutAtomsOfX rover_patrol_refine_cutsV2X.R (mR q).name)

theorem gL_thrGe1 (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 Side.L (.cmp ">=" (.var "s") (.num s)) = thrGe (Lv 1) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_thrGe0 (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 Side.L (.cmp ">=" (.var "v") (.num s)) = thrGe (Lv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_thrLe0 (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 Side.L (.cmp "<=" (.var "v") (.num s)) = thrLe (Lv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_linLe (cs Ks : String) (c K : ℚ) (hc : Run.parseRat cs = some c)
    (hK : Run.parseRat Ks = some K) :
    hostAtomG vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5")
      (.bin "-" (.var "v") (.num cs)))) (.num Ks)) = linLe (Lv 0) (Lv 2) (5/2) (c : ℝ) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hc, hK, hp2_5, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, linLe, linQ, Lv]
theorem gL_linGe (cs Ks : String) (c K : ℚ) (hc : Run.parseRat cs = some c)
    (hK : Run.parseRat Ks = some K) :
    hostAtomG vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5")
      (.bin "-" (.var "v") (.num cs)))) (.num Ks)) = linGe (Lv 0) (Lv 2) (5/2) (c : ℝ) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hc, hK, hp2_5, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, linGe, linQ, Lv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "0.0")), thrGe (Lv 1) 0),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "0.8")), linLe (Lv 0) (Lv 2) (5/2) (12/25) (4/5)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "-0.95")), linGe (Lv 0) (Lv 2) (5/2) (12/25) (-19/20)),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "0.8")), thrLe (Lv 0) (4/5)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), thrGe (Lv 0) (1/10))] := by
  have h : cL 0 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "s") (.num "0.0"))),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "0.8")), hostAtomG vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "0.8"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "-0.95")), hostAtomG vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "-0.95"))),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "0.8")), hostAtomG vs 3 Side.L (.cmp "<=" (.var "v") (.num "0.8"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")))] := rfl
  rw [h, gL_thrGe1 "0.0" (0) hp0_0, gL_linLe "0.48" "0.8" (12/25) (4/5) hp0_48 hp0_8, gL_linGe "0.48" "-0.95" (12/25) (-19/20) hp0_48 hpm0_95, gL_thrLe0 "0.8" (4/5) hp0_8, gL_thrGe0 "0.1" (1/10) hp0_1]
  norm_num
theorem cL_1 : cL 1 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "20.0")), thrGe (Lv 1) 20),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "0.95")), linLe (Lv 0) (Lv 2) (5/2) (18/25) (19/20)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "-1.55")), linGe (Lv 0) (Lv 2) (5/2) (18/25) (-31/20)),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "1.1")), thrLe (Lv 0) (11/10)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), thrGe (Lv 0) (1/10))] := by
  have h : cL 1 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "20.0")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "s") (.num "20.0"))),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "0.95")), hostAtomG vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "0.95"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "-1.55")), hostAtomG vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "-1.55"))),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "1.1")), hostAtomG vs 3 Side.L (.cmp "<=" (.var "v") (.num "1.1"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")))] := rfl
  rw [h, gL_thrGe1 "20.0" (20) hp20_0, gL_linLe "0.72" "0.95" (18/25) (19/20) hp0_72 hp0_95, gL_linGe "0.72" "-1.55" (18/25) (-31/20) hp0_72 hpm1_55, gL_thrLe0 "1.1" (11/10) hp1_1, gL_thrGe0 "0.1" (1/10) hp0_1]
  norm_num
theorem cL_2 : cL 2 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "20.0")), thrGe (Lv 1) 20),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "1.05")), linLe (Lv 0) (Lv 2) (5/2) (22/25) (21/20)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "-1.95")), linGe (Lv 0) (Lv 2) (5/2) (22/25) (-39/20)),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "1.3")), thrLe (Lv 0) (13/10)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), thrGe (Lv 0) (1/10))] := by
  have h : cL 2 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "20.0")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "s") (.num "20.0"))),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "1.05")), hostAtomG vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "1.05"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "-1.95")), hostAtomG vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "-1.95"))),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "1.3")), hostAtomG vs 3 Side.L (.cmp "<=" (.var "v") (.num "1.3"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")))] := rfl
  rw [h, gL_thrGe1 "20.0" (20) hp20_0, gL_linLe "0.88" "1.05" (22/25) (21/20) hp0_88 hp1_05, gL_linGe "0.88" "-1.95" (22/25) (-39/20) hp0_88 hpm1_95, gL_thrLe0 "1.3" (13/10) hp1_3, gL_thrGe0 "0.1" (1/10) hp0_1]
  norm_num
theorem cL_3 : cL 3 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "50.0")), thrGe (Lv 1) 50),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "1.25")), linLe (Lv 0) (Lv 2) (5/2) (6/5) (5/4)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "-2.75")), linGe (Lv 0) (Lv 2) (5/2) (6/5) (-11/4)),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), thrGe (Lv 0) (1/10))] := by
  have h : cL 3 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "s") (.num "50.0")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "s") (.num "50.0"))),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "1.25")), hostAtomG vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "1.25"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "-2.75")), hostAtomG vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "-2.75"))),
     (hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")), hostAtomG vs 3 Side.L (.cmp ">=" (.var "v") (.num "0.1")))] := rfl
  rw [h, gL_thrGe1 "50.0" (50) hp50_0, gL_linLe "1.2" "1.25" (6/5) (5/4) hp1_2 hp1_25, gL_linGe "1.2" "-2.75" (6/5) (-11/4) hp1_2 hpm2_75, gL_thrGe0 "0.1" (1/10) hp0_1]
  norm_num

theorem gR_s_ge (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 Side.R (.cmp ">=" (.var "s") (.num s)) = thrGe (Rv 1) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_v_ge (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 Side.R (.cmp ">=" (.var "v") (.num s)) = thrGe (Rv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_v_le (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 Side.R (.cmp "<=" (.var "v") (.num s)) = thrLe (Rv 0) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]

/-- A right zone's three kept atoms (floor on `s`, the 0.3 m/s floor, the cap). -/
noncomputable def zoneAtoms (q : ℕ) : List (CutAtomP 3) :=
  [(hostAtomF vs 3 Side.R (.cmp ">=" (.var "s") (.num (loS q))), thrGe (Rv 1) (loL q)),
   (hostAtomF vs 3 Side.R (.cmp ">=" (.var "v") (.num "0.3")), thrGe (Rv 0) (3/10)),
   (hostAtomF vs 3 Side.R (.cmp "<=" (.var "v") (.num (capS q))), thrLe (Rv 0) (capL q))]

theorem zoneAtoms_eq (q : ℕ) (hq : q < 4) : zoneAtoms q =
    [(hostAtomF vs 3 Side.R (.cmp ">=" (.var "s") (.num (loS q))),
        hostAtomG vs 3 Side.R (.cmp ">=" (.var "s") (.num (loS q)))),
     (hostAtomF vs 3 Side.R (.cmp ">=" (.var "v") (.num "0.3")),
        hostAtomG vs 3 Side.R (.cmp ">=" (.var "v") (.num "0.3"))),
     (hostAtomF vs 3 Side.R (.cmp "<=" (.var "v") (.num (capS q))),
        hostAtomG vs 3 Side.R (.cmp "<=" (.var "v") (.num (capS q))))] := by
  rw [gR_s_ge _ _ (hlo q hq), gR_v_ge _ _ hp0_3, gR_v_le _ _ (hcap q hq)]
  simp [zoneAtoms, loL, capL]

theorem cR_eq (q : ℕ) (hq : q < 4) : cR q = zoneAtoms q := by
  rw [zoneAtoms_eq q hq]
  interval_cases q <;> rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 4) :
    ∀ x ∈ cutAtomsOfX rover_patrol_refine_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, rover_patrol_refine_cutsV2X, mL, rover_patrol_refine_IRv2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 4) :
    ∀ x ∈ cutAtomsOfX rover_patrol_refine_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, rover_patrol_refine_cutsV2X, mR, rover_patrol_refine_IRv2] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 4) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 4) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

theorem cutSat_iff (cs : List (CutAtomP 3)) (hiff : AtomsIff cs) (ν : State (Var 3)) :
    CutSat cs ν ↔ ∀ a ∈ cs, Term.eval a.2 ν ≤ 0 :=
  ⟨fun h a ha => (hiff a ha ν).mp (h a ha), fun h a ha => (hiff a ha ν).mpr (h a ha)⟩

theorem cutSatR_val (q : ℕ) (hq : q < 4) (ν : State (Var 3)) : CutSat (cR q) ν ↔
    (loL q ≤ ν (Rv 1) ∧ 3/10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ capL q) := by
  rw [cutSat_iff _ (hiffR q hq), cR_eq q hq]
  simp [zoneAtoms, thrGe, thrLe, Term.eval, AOp.interp, Rv]

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked;
the linear-form and derived atoms' rational entries are `CutLiftX.entry_linear`/`_rational`) -/

theorem hO1L (l : ℕ) (hl : l < 4) :
    ∀ ν, Formula.sat (hostGuard vs 3 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard rover_patrol_refine_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, rover_patrol_refine_cutsV2X, mL, rover_patrol_refine_IRv2] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, rover_patrol_refine_cutsV2X, mL, rover_patrol_refine_IRv2] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0, vs, Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0, vs,
        Run.resolveVar, List.findIdx?_cons]

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

theorem hfL (l : ℕ) (hl : l < 4) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, rover_patrol_refine_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, rover_patrol_refine_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, rover_patrol_refine_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, rover_patrol_refine_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 4) : (hostGuard vs 3 Side.L (mL l)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vs (mL l) ?_
  interval_cases l <;>
    simp [mL, rover_patrol_refine_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]

/-- The left atoms read only left variables (so they are frozen by a right-only hop). -/
theorem atomsFreeL (l : ℕ) (hl : l < 4) :
    ∀ x ∈ cutAtomsOfX rover_patrol_refine_cutsV2X.L (mL l).name,
      Parse.PForm.namesFree "R_" x.atom = true := by
  interval_cases l <;>
  · intro x hx
    simp only [cutAtomsOfX, rover_patrol_refine_cutsV2X, mL, rover_patrol_refine_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem cutFL_fv (l : ℕ) (hl : l < 4) : (cutF (cL l)).fv ⊆ range Lv := by
  intro x hx
  unfold cutF at hx
  have key : ∀ (L : List (CutAtomP 3)) (acc : Formula (Var 3)),
      acc.fv ⊆ range Lv → (∀ a ∈ L, a.1.fv ⊆ range Lv) →
      (L.foldl (fun d a => Formula.and d a.1) acc).fv ⊆ range Lv := by
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
  refine key (cL l) Formula.tt (by simp [Formula.fv]) ?_ hx
  intro a ha y hy
  obtain ⟨xa, hxa, rfl⟩ := List.mem_map.mp ha
  exact side_eq_L_mem (by
    simp only at hy
    unfold hostAtomF at hy
    exact hostForm_side (resolvesTo_L vs) _ (atomsFreeL l hl xa hxa) y hy)

/-- Frozen lefts keep the left atoms. -/
theorem cutSatL_congr (l : ℕ) (hl : l < 4) {σ ρ : State (Var 3)}
    (hρL : ∀ i, ρ (Lv i) = σ (Lv i)) (h : CutSat (cL l) σ) : CutSat (cL l) ρ := by
  rw [← sat_cutF] at h ⊢
  refine (Formula.coincidence (cutF (cL l)) (fun x hx => ?_)).mp h
  obtain ⟨i, rfl⟩ := cutFL_fv l hl hx
  exact (hρL i).symm

theorem lin_fv (r c K : ℝ) : (linLe (Lv (0 : Fin 3)) (Lv 2) r c K).fv ⊆ range Lv ∪ range Rv ∧
    (linGe (Lv (0 : Fin 3)) (Lv 2) r c K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [linLe, linGe, linQ, Term.fv] at hx <;>
    rcases hx with rfl | rfl <;> simp
theorem thr_fv_L (j : Fin 3) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 3) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 4) (hq : q < 4) :
    ∀ c ∈ g l :: gs l ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv_all l _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv_all l _ (List.mem_cons_of_mem _ hc)
  interval_cases l <;>
  · simp only [atomTerms, cL_0, cL_1, cL_2, cL_3, cR_eq q hq, zoneAtoms, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact (lin_fv _ _ _).1 | exact (lin_fv _ _ _).2 | exact (thr_fv_L _ _).1 |
        exact (thr_fv_L _ _).2 | exact (thr_fv_R _ _).1 | exact (thr_fv_R _ _).2

/-! ## O2, left: the linear-form cut chain stays along the joint flow (`CutLiftX`)

Each zone's lag field is `v' = a`, `a' = −6.25 (v − c) − 5 a` (`a_coef = 6.25`, `b = 5`, the
double root `r = 2.5` of `r² − 5 r + 6.25 = 0`). Round 1: the linear forms
`q = a + 2.5 (v − c)` (`super_linear_le_L` / `_ge_L`); round 2: the derived speed bounds
(`super_derived_le_L` / `_ge_L` inside the given round-1 atom, `stay_given`); the odometer
floor `s ≥ lo` from `s' = v ≥ 0`. -/

theorem hfxL (l : ℕ) (hl : l < 4) (D : Formula (Var 3)) :
    ∀ z, Formula.sat D z → Term.eval (fL l 0) z = z (Lv 2) :=
  fun z _ => fL0_eval l hl z
theorem hfyL (l : ℕ) (hl : l < 4) (c : ℝ) (hc : cLv l = c) (D : Formula (Var 3)) :
    ∀ z, Formula.sat D z → Term.eval (fL l 2) z = -(25/4) * (z (Lv 0) - c) - 5 * z (Lv 2) :=
  fun z _ => by rw [fL2_eval l hl, hc]

theorem stay_linLe (l : ℕ) (hl : l < 4) (q : ℕ) (c K : ℝ) (hc : cLv l = c) (hK : 0 ≤ K)
    (dom : Formula (Var 3)) (ν : State (Var 3))
    (hinit : Term.eval (linLe (Lv 0) (Lv 2) (5/2) c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys (fL l) (fR q) (Term.const lam)) dom)
      (fun ω => Term.eval (linLe (Lv 0) (Lv 2) (5/2) c K) ω) ν :=
  boxle_L_of_super _ (fL l) (fR q) _ dom dom
    (fun i h => by simp [linLe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
    (super_linear_le_L (a := 25/4) (b := 5) (by norm_num) (by norm_num) hK (fL l) dom
      (hfxL l hl dom) (hfyL l hl c hc dom)) hinit

theorem stay_linGe (l : ℕ) (hl : l < 4) (q : ℕ) (c K : ℝ) (hc : cLv l = c) (hK : K ≤ 0)
    (dom : Formula (Var 3)) (ν : State (Var 3))
    (hinit : Term.eval (linGe (Lv 0) (Lv 2) (5/2) c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys (fL l) (fR q) (Term.const lam)) dom)
      (fun ω => Term.eval (linGe (Lv 0) (Lv 2) (5/2) c K) ω) ν :=
  boxle_L_of_super _ (fL l) (fR q) _ dom dom
    (fun i h => by simp [linGe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
    (super_linear_ge_L (a := 25/4) (b := 5) (by norm_num) (by norm_num) hK (fL l) dom
      (hfxL l hl dom) (hfyL l hl c hc dom)) hinit

/-- `v ≤ D` given `q ≤ K` (stratified: round 2 inside round 1). -/
theorem stay_vle (l : ℕ) (hl : l < 4) (q : ℕ) (c K D : ℝ) (hc : cLv l = c) (hK : 0 ≤ K)
    (hKK : K ≤ 5/2 * (D - c)) (Fq : Formula (Var 3))
    (hFq : ∀ z, Formula.sat Fq z ↔ Term.eval (linLe (Lv 0) (Lv 2) (5/2) c K) z ≤ 0)
    (dom : Formula (Var 3)) :
    ∀ ν, Term.eval (linLe (Lv 0) (Lv 2) (5/2) c K) ν ≤ 0 → Term.eval (thrLe (Lv 0) D) ν ≤ 0 →
      BoxLe (Program.ode (jointSys (fL l) (fR q) (Term.const lam)) dom)
        (fun ω => Term.eval (thrLe (Lv 0) D) ω) ν :=
  stay_given (Fq := Fq) hFq
    (fun ν h => stay_linLe l hl q c K hc hK dom ν h)
    (fun ν h => boxle_L_of_super _ (fL l) (fR q) _ (Formula.and dom Fq) (Formula.and dom Fq)
      (fun i h => by simp [thrLe, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
      (super_derived_le_L (jx := 0) (jy := 2) (r := 5/2) (c := c) (K := K) (K' := D)
        (by norm_num) hKK (fL l) _ (hfxL l hl _) (fun z hz => (hFq z).mp hz.2)) h)

/-- `v ≥ D` given `q ≥ K`. -/
theorem stay_vge (l : ℕ) (hl : l < 4) (q : ℕ) (c K D : ℝ) (hc : cLv l = c) (hK : K ≤ 0)
    (hKK : 5/2 * (D - c) ≤ K) (Fq : Formula (Var 3))
    (hFq : ∀ z, Formula.sat Fq z ↔ Term.eval (linGe (Lv 0) (Lv 2) (5/2) c K) z ≤ 0)
    (dom : Formula (Var 3)) :
    ∀ ν, Term.eval (linGe (Lv 0) (Lv 2) (5/2) c K) ν ≤ 0 → Term.eval (thrGe (Lv 0) D) ν ≤ 0 →
      BoxLe (Program.ode (jointSys (fL l) (fR q) (Term.const lam)) dom)
        (fun ω => Term.eval (thrGe (Lv 0) D) ω) ν :=
  stay_given (Fq := Fq) hFq
    (fun ν h => stay_linGe l hl q c K hc hK dom ν h)
    (fun ν h => boxle_L_of_super _ (fL l) (fR q) _ (Formula.and dom Fq) (Formula.and dom Fq)
      (fun i h => by simp [thrGe, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h)
      (super_derived_ge_L (jx := 0) (jy := 2) (r := 5/2) (c := c) (K := K) (K' := D)
        (by norm_num) hKK (fL l) _ (hfxL l hl _) (fun z hz => (hFq z).mp hz.2)) h)

theorem stayL (l q : ℕ) (hl : l < 4) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const lam)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  interval_cases l
  · have hm2 : (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "0.8")), linLe (Lv 0) (Lv 2) (5/2) (12/25) (4/5)) ∈ cL 0 := by
      rw [cL_0]; simp
    have hm3 : (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "-0.95")), linGe (Lv 0) (Lv 2) (5/2) (12/25) (-19/20)) ∈ cL 0 := by
      rw [cL_0]; simp
    have hq2 := (hiffL 0 (by norm_num) _ hm2 ν).mp (hν _ hm2)
    have hq3 := (hiffL 0 (by norm_num) _ hm3 ν).mp (hν _ hm3)
    have hc : cLv 0 = 12/25 := by norm_num [cLv, cLQ]
    rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact boxle_thrGe_L 1 _ _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z hz _ => by rw [fL1_eval 0 (by norm_num)]; exact ((sat_domL z).mp hz.1).1) hinit
    · exact stay_linLe 0 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_linGe 0 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_vle 0 (by norm_num) q _ _ (4/5) hc (by norm_num) (by norm_num) _
        (fun z => hiffL 0 (by norm_num) _ hm2 z) _ ν hq2 hinit
    · exact stay_vge 0 (by norm_num) q _ _ (1/10) hc (by norm_num) (by norm_num) _
        (fun z => hiffL 0 (by norm_num) _ hm3 z) _ ν hq3 hinit
  · have hm2 : (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "0.95")), linLe (Lv 0) (Lv 2) (5/2) (18/25) (19/20)) ∈ cL 1 := by
      rw [cL_1]; simp
    have hm3 : (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "-1.55")), linGe (Lv 0) (Lv 2) (5/2) (18/25) (-31/20)) ∈ cL 1 := by
      rw [cL_1]; simp
    have hq2 := (hiffL 1 (by norm_num) _ hm2 ν).mp (hν _ hm2)
    have hq3 := (hiffL 1 (by norm_num) _ hm3 ν).mp (hν _ hm3)
    have hc : cLv 1 = 18/25 := by norm_num [cLv, cLQ]
    rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact boxle_thrGe_L 1 _ _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z hz _ => by rw [fL1_eval 1 (by norm_num)]; exact ((sat_domL z).mp hz.1).1) hinit
    · exact stay_linLe 1 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_linGe 1 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_vle 1 (by norm_num) q _ _ (11/10) hc (by norm_num) (by norm_num) _
        (fun z => hiffL 1 (by norm_num) _ hm2 z) _ ν hq2 hinit
    · exact stay_vge 1 (by norm_num) q _ _ (1/10) hc (by norm_num) (by norm_num) _
        (fun z => hiffL 1 (by norm_num) _ hm3 z) _ ν hq3 hinit
  · have hm2 : (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "1.05")), linLe (Lv 0) (Lv 2) (5/2) (22/25) (21/20)) ∈ cL 2 := by
      rw [cL_2]; simp
    have hm3 : (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "-1.95")), linGe (Lv 0) (Lv 2) (5/2) (22/25) (-39/20)) ∈ cL 2 := by
      rw [cL_2]; simp
    have hq2 := (hiffL 2 (by norm_num) _ hm2 ν).mp (hν _ hm2)
    have hq3 := (hiffL 2 (by norm_num) _ hm3 ν).mp (hν _ hm3)
    have hc : cLv 2 = 22/25 := by norm_num [cLv, cLQ]
    rw [cL_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact boxle_thrGe_L 1 _ _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z hz _ => by rw [fL1_eval 2 (by norm_num)]; exact ((sat_domL z).mp hz.1).1) hinit
    · exact stay_linLe 2 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_linGe 2 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_vle 2 (by norm_num) q _ _ (13/10) hc (by norm_num) (by norm_num) _
        (fun z => hiffL 2 (by norm_num) _ hm2 z) _ ν hq2 hinit
    · exact stay_vge 2 (by norm_num) q _ _ (1/10) hc (by norm_num) (by norm_num) _
        (fun z => hiffL 2 (by norm_num) _ hm3 z) _ ν hq3 hinit
  · have hm2 : (hostAtomF vs 3 Side.L (.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "1.25")), linLe (Lv 0) (Lv 2) (5/2) (6/5) (5/4)) ∈ cL 3 := by
      rw [cL_3]; simp
    have hm3 : (hostAtomF vs 3 Side.L (.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "-2.75")), linGe (Lv 0) (Lv 2) (5/2) (6/5) (-11/4)) ∈ cL 3 := by
      rw [cL_3]; simp
    have hq2 := (hiffL 3 (by norm_num) _ hm2 ν).mp (hν _ hm2)
    have hq3 := (hiffL 3 (by norm_num) _ hm3 ν).mp (hν _ hm3)
    have hc : cLv 3 = 6/5 := by norm_num [cLv, cLQ]
    rw [cL_3] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact boxle_thrGe_L 1 _ _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z hz _ => by rw [fL1_eval 3 (by norm_num)]; exact ((sat_domL z).mp hz.1).1) hinit
    · exact stay_linLe 3 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_linGe 3 (by norm_num) q _ _ hc (by norm_num) _ ν hinit
    · exact stay_vge 3 (by norm_num) q _ _ (1/10) hc (by norm_num) (by norm_num) _
        (fun z => hiffL 3 (by norm_num) _ hm3 z) _ ν hq3 hinit

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

/-- The declared transitions, as indices (`SLOW` 0, `MEDIUM_ECO` 1, `MEDIUM_BRISK` 2,
`FAST` 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 0), (1, 3), (1, 1), (2, 3), (2, 2), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range rover_patrol_refine_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (rover_patrol_refine_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 4 := rfl

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

theorem htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [edgeW, Gr]

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

/-! ## Regions: the right zone's kept cut atoms (no sink in this rung) -/

noncomputable def region (q : ℕ) : Formula (Var 3) :=
  if q < 4 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 4) (ν : State (Var 3)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region_sink (q : ℕ) (hq : ¬ q < 4) (ν : State (Var 3)) :
    ¬ Formula.sat (region q) ν := by
  simp [region, hq, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) (_hq : q < 4) : (region q).fv ⊆ range Rv := by
  by_cases h4 : q < 4
  · simp only [region, h4, if_true]
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
    rw [cR_eq q h4] at ha
    simp only [zoneAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h4, if_false]
    simp [Formula.fv, Term.fv]

/-! ## O2, right: each zone contracts toward its command, so its atoms stay -/

theorem stayR (l q : ℕ) (hq : q < 4) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const lam)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hc := cap_bounds q hq
  have h1 : (0:ℝ) ≤ lam := le_of_lt lam_pos
  rw [cR_eq q hq] at ha
  simp only [zoneAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact boxle_thrGe_R 1 _ _ _ _ h1 _ (Formula.and domL domR) (fun x h => h)
      (fun z hz _ => by rw [fR1_eval q hq]; exact ((sat_domR z).mp hz.2).1) hinit
  · exact boxle_thrGe_R 0 _ _ _ _ h1 _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fR0_eval q hq]; linarith) hinit
  · exact boxle_thrLe_R 0 _ _ _ _ h1 _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fR0_eval q hq]; linarith) hinit

/-! ## Existence: each zone's flow, explicitly, at any rate `k ≥ 0`

`v(t) = c + (v₀ − c) e^{−k t}` (a convex combination of `v₀` and the command `c`, inside
`[0, 1.6]`), `s(t) = s₀ + k c t + (v₀ − c)(1 − e^{−k t}) = s₀ + v₀ (1 − e^{−kt}) +
c (k t − 1 + e^{−k t}) ≥ s₀` (no odometer wall), `a` frozen (the reference has no lag). The
joint pieces run at the cover's λ = 9/4, the right-only repositions at rate 1. -/

noncomputable def ex (k t : ℝ) : ℝ := Real.exp (-(k * t))

noncomputable def solR (c k : ℝ) (b : State (Var 3)) (t : ℝ) : State (Var 3) := fun x =>
  if x = Rv 0 then c + (b (Rv 0) - c) * ex k t
  else if x = Rv 1 then b (Rv 1) + k * c * t + (b (Rv 0) - c) * (1 - ex k t)
  else b x

theorem solR_0 (c k : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c k b t (Rv 0) = c + (b (Rv 0) - c) * ex k t := by simp [solR]
theorem solR_1 (c k : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c k b t (Rv 1) = b (Rv 1) + k * c * t + (b (Rv 0) - c) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (c k : ℝ) (b : State (Var 3)) (t : ℝ) {x : Var 3} (h0 : x ≠ Rv 0)
    (h1 : x ≠ Rv 1) : solR c k b t x = b x := by
  simp [solR, h0, h1]

theorem ex_hasDeriv (k t : ℝ) : HasDerivAt (ex k) (-k * ex k t) t := by
  have h := ((hasDerivAt_id t).const_mul k).neg.exp
  have h' : HasDerivAt (ex k) (Real.exp (-(k * id t)) * (-(k * 1))) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring
theorem ex_zero (k : ℝ) : ex k 0 = 1 := by simp [ex]
theorem ex_pos (k t : ℝ) : 0 < ex k t := Real.exp_pos _
theorem ex_le_one {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) : ex k t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; nlinarith
theorem ex_ge (k t : ℝ) : 1 - k * t ≤ ex k t := by
  unfold ex; have := Real.add_one_le_exp (-(k * t)); linarith

theorem solR_stays (q : ℕ) (hq : q < 4) (k : ℝ) (hk : 0 ≤ k) (b : State (Var 3))
    (hb : Formula.sat domR b) {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR (capL q) k b t) := by
  rw [sat_domR] at hb ⊢
  obtain ⟨h0, h1, h2, h3, h4⟩ := hb
  have hc := cap_bounds q hq
  have he0 := ex_pos k t
  have he1 := ex_le_one hk ht
  have he2 := ex_ge k t
  have hkt : 0 ≤ k * t := mul_nonneg hk ht
  rw [solR_0, solR_1, solR_other _ _ _ _ (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, h3, h4⟩

theorem rightBlock_bound_mem (q : ℕ) (k : ℝ) (i : Fin 3) :
    Rv i ∈ (rightBlock (fR q) (Term.const k)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- **The explicit run of a zone at rate `k`** (any duration `s`, from any envelope state). -/
theorem flowR_run (q : ℕ) (hq : q < 4) (k : ℝ) (hk : 0 ≤ k) (b : State (Var 3))
    (hb : Formula.sat domR b) (s : ℝ) :
    solR (capL q) k b 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const k),
          HasDerivWithinAt (fun u => solR (capL q) k b u p.1) (p.2.eval (solR (capL q) k b t))
            (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const k)).bound →
        solR (capL q) k b t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (solR (capL q) k b t)) := by
  set c := capL q with hcdef
  refine ⟨?_, ?_, ?_, fun t ht => solR_stays q hq k hk b hb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero]; ring
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero]; ring
    exact solR_other c k b 0 h0 h1
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hd := ex_hasDeriv k t
    fin_cases i
    · have h := (((hd.const_mul (b (Rv 0) - c)).const_add c)).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c k b u (Rv 0)) = fun u => c + (b (Rv 0) - c) * ex k u := by
        funext u; exact solR_0 c k b u
      show HasDerivWithinAt (fun u => solR c k b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const k) (fR q 0)) (solR c k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR0_eval q hq, solR_0]
      exact h.congr_deriv (by rw [← hcdef]; ring)
    · have h := ((((hasDerivAt_id t).const_mul (k * c)).const_add (b (Rv 1))).add
        ((hd.const_sub 1).const_mul (b (Rv 0) - c))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c k b u (Rv 1)) =
          fun u => (b (Rv 1) + k * c * id u) + (b (Rv 0) - c) * (1 - ex k u) := by
        funext u; rw [solR_1]; rfl
      show HasDerivWithinAt (fun u => solR c k b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const k) (fR q 1)) (solR c k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR1_eval q hq, solR_0]
      exact h.congr_deriv (by ring)
    · have hcurve : (fun u => solR c k b u (Rv 2)) = fun _ => b (Rv 2) := by
        funext u
        exact solR_other c k b u (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])
      show HasDerivWithinAt (fun u => solR c k b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const k) (fR q 2)) (solR c k b t)) (Icc 0 s) t
      rw [hcurve]
      simp only [Term.eval, AOp.interp]
      rw [fR2_eval q hq, mul_zero]
      exact hasDerivWithinAt_const t _ _
  · intro t _ x hx
    refine solR_other c k b t (fun h => hx ?_) (fun h => hx ?_)
    · rw [h]; exact rightBlock_bound_mem q k 0
    · rw [h]; exact rightBlock_bound_mem q k 1

/-- A zone's program (rate 1) runs from `ω` to `solR c 1 ω τ` for any `τ ≥ 0`. -/
theorem mode_run (q : ℕ) (hq : q < 4) (ω : State (Var 3)) (τ : ℝ) (hτ : 0 ≤ τ)
    (hb : Formula.sat domR ω) :
    Program.sem (Program.ode (rightBlock (fR q) (Term.const 1)) domR) ω
      (solR (capL q) 1 ω τ) := by
  obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q hq 1 zero_le_one ω hb τ
  exact ⟨τ, solR (capL q) 1 ω, hτ, h0, rfl, hder, hmask, hdom⟩

/-- **Reaching an odometer level** (as in `rover_patrol_zones`): from `0.3 ≤ v₀ ≤ c_q`, zone
`q`'s program reaches `s_R = max(s₀, T)`; `v` only grows and stays `≤ c_q`; every other
coordinate (the right `a`, all lefts, Aux) is unchanged. -/
theorem mode_reach (q : ℕ) (hq : q < 4) (T : ℝ) (ω : State (Var 3))
    (hb : Formula.sat domR ω) (hv0 : 3/10 ≤ ω (Rv 0)) (hv1 : ω (Rv 0) ≤ capL q) :
    ∃ ρ, Program.sem (Program.ode (rightBlock (fR q) (Term.const 1)) domR) ω ρ ∧
      ρ (Rv 1) = max (ω (Rv 1)) T ∧ ω (Rv 0) ≤ ρ (Rv 0) ∧ ρ (Rv 0) ≤ capL q ∧
      ∀ x, (x ≠ Rv 0 ∧ x ≠ Rv 1) → ρ x = ω x := by
  by_cases hT : T ≤ ω (Rv 1)
  · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fR q) (lam := Term.const 1)
      (domR := domR) hb
    rw [hρ] at hsem
    exact ⟨ω, hsem, (max_eq_left hT).symm, le_refl _, hv1, fun _ _ => rfl⟩
  · replace hT : ω (Rv 1) < T := not_le.mp hT
    set c := capL q with hcdef
    set f : ℝ → ℝ := fun t => ω (Rv 1) + 1 * c * t + (ω (Rv 0) - c) * (1 - Real.exp (-(1 * t)))
      with hfdef
    have hcont : ContinuousOn f (Icc 0 ((T - ω (Rv 1)) / (3/10))) := by
      apply Continuous.continuousOn
      simp only [hfdef]
      fun_prop
    have hTm : 0 ≤ (T - ω (Rv 1)) / (3/10) := div_nonneg (by linarith) (by norm_num)
    have hf0 : f 0 = ω (Rv 1) := by simp [hfdef]
    have hlow : ∀ t, 0 ≤ t → ω (Rv 1) + ω (Rv 0) * t ≤ f t := by
      intro t ht
      have he := ex_ge 1 t
      have : f t - (ω (Rv 1) + ω (Rv 0) * t) = (c - ω (Rv 0)) * (t - 1 + Real.exp (-(1 * t))) := by
        simp only [hfdef]; ring
      have h2 : 0 ≤ (c - ω (Rv 0)) * (t - 1 + Real.exp (-(1 * t))) := by
        apply mul_nonneg (by linarith)
        unfold ex at he; linarith
      linarith
    have hfT : T ≤ f ((T - ω (Rv 1)) / (3/10)) := by
      have := hlow _ hTm
      have h3 : (3/10) * ((T - ω (Rv 1)) / (3/10)) ≤ ω (Rv 0) * ((T - ω (Rv 1)) / (3/10)) :=
        mul_le_mul_of_nonneg_right hv0 hTm
      have h4 : (3/10) * ((T - ω (Rv 1)) / (3/10)) = T - ω (Rv 1) := by field_simp
      linarith
    obtain ⟨τ, hτI, hτf⟩ := intermediate_value_Icc hTm hcont ⟨by rw [hf0]; exact le_of_lt hT, hfT⟩
    refine ⟨_, mode_run q hq ω τ hτI.1 hb, ?_, ?_, ?_, ?_⟩
    · rw [solR_1, max_eq_right (le_of_lt hT), ← hτf]
      simp only [hfdef, ex, hcdef]
    · rw [solR_0]
      have := ex_le_one zero_le_one hτI.1
      have := ex_pos 1 τ
      nlinarith
    · rw [solR_0]
      have := ex_pos 1 τ
      nlinarith
    · intro x hx
      exact solR_other c 1 ω τ hx.1 hx.2

/-- **Within-segment existence** at the cover's λ = 9/4. -/
theorem es (l q : ℕ) (hq : q < 4) (dt : ℝ) (A : Formula (Var 3)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR q) (Term.const lam) domL domR dt (Function.update σ tg 0) := by
  intro σ hσ s ΦL hs0 _ _ _ hmaskL _
  have hagree : ∀ i, ΦL s (Rv i) = σ (Rv i) := by
    intro i
    rw [hmaskL s (right_mem_Icc.mpr hs0) (Rv i) (fun hb => by
      obtain ⟨j, hj⟩ := leftBlock_bound_sub (fL l) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))]
    exact Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hdom' : Formula.sat domR (ΦL s) := by
    refine (Formula.coincidence domR (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomR hx
    exact (hagree i).symm
  obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q hq lam (le_of_lt lam_pos) (ΦL s) hdom' s
  exact ⟨solR (capL q) lam (ΦL s), h0, hder, hmask, hdom⟩

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `l` at its OWN declared row (`invRow = l`), right zone `q`, at the
cover's λ = 9/4 and strata order `[0, 1]`. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX rover_patrol_refine_IRv2 rover_patrol_refine_cutsV2X 3 l [0, 1] (9/4) l q

theorem verd_core (l q : ℕ) (hl : l < 4) (hq : q < 4) (h : Verd l q) :
    VerdXCore (g l :: gs l) (fL l) (fR q) lam
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

/-- The joint-piece anchor of the pair `(l, q)`: row `l`, both zones' atoms, the envelope. -/
noncomputable def anchor (l q : ℕ) : Formula (Var 3) :=
  Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q))) (Formula.and domL domR)

theorem couple (l q : ℕ) (hl : l < 4) (hq : q < 4) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (anchor l q) σ →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (anchor l q) tg dt (Function.update σ tg 0) :=
  couple_cutX (g l) (gs l) (g l :: gs l) (cL l) (cR q) (fL l) (fR q) lam lam_pos domL domR 1 dt
    (hfL l hl) (hfR q hq) hdomL hdomR (anchor_fv l q hl hq) (fun _c hc => hc)
    (fun _c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl) (stayR l q hq)
    (verd_core l q hl hq hv) (es l q hq dt _)

theorem sat_faModal_monoPost {P Q : Program (Var 3)} {A B : Formula (Var 3)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 3)}
    (h : Formula.sat (faModal (Equiv.refl (Var 3)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem anchor_post (l q : ℕ) (hl : l < 4) (hq : q < 4) (ν : State (Var 3))
    (hν : Formula.sat (anchor l q) ν) :
    Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region q)) ν := by
  obtain ⟨hFν, hatν⟩ := (sat_FM_append (g l) (gs l) _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR q hq) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt q hq ν).mpr hRν⟩

theorem respond (l qs : ℕ) (hl : l < 4) (hqs : qs < 4) (dt : ℝ) (hv : Verd l qs)
    {σ : State (Var 3)} (hσ : Formula.sat (anchor l qs) σ) :
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
        (hfR qs hqs) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l qs hl hqs dt hv σ' hσ')
    hσ
  refine sat_faModal_monoPost (A := anchor l qs) (anchor_post l qs hl hqs) ?_
  simpa [anchor] using hfa

/-! ## A right-only prefix hop whose landing predicate is arbitrary (from
`ChargerFastTapers.repoPrefixA` / `hopA` / `window1_of_B`, re-stated at `n = 3`) -/

theorem repoPrefixA {fL' fRh : Fin 3 → Term (Var 3)} {lamh : Term (Var 3)}
    {domL' domRh : Formula (Var 3)} {φ : Formula (Var 3)} {Q : Program (Var 3)}
    {dt : ℝ} {ω₀ : State (Var 3)}
    (hfL : ∀ i, (fL' i).fv ⊆ range Lv) (hdomL : domL'.fv ⊆ range Lv)
    (hfR : ∀ i, (fRh i).fv ⊆ range Rv) (hlam : lamh.fv ⊆ range Rv)
    (hdomR : domRh.fv ⊆ range Rv)
    (hω₀tg : ω₀ tg = 0) (A : State (Var 3) → Prop)
    (hR : ∃ ρ₁, Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fRh lamh)
        (Formula.and domL' domRh)) ω₀ ρ₁ ∧ A ρ₁)
    (hQ : ∀ σ, A σ → σ tg = 0 →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') Q φ tg dt σ) :
    faModalB (Equiv.refl (Var 3))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL')
      (Program.seq
        (Program.ode (jointSys (fun _ => Term.const 0) fRh lamh) (Formula.and domL' domRh))
        Q)
      φ tg dt ω₀ := by
  intro ν hplant
  obtain ⟨ρ₁, hhop, hρ₁A⟩ := hR
  have hrights : ∀ i : Fin 3, ν (Rv i) = ω₀ (Rv i) := by
    intro i
    refine sem_ode_mask hplant.1 ?_
    intro hb
    rcases clk_boundSet_sub _ _ (by simpa [ODESystem.boundSet] using hb) with hx | hx
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub fL' hx
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at hx
      exact absurd hx (by simp [Rv, Prod.ext_iff])
  have hνdomL : Formula.sat domL' ν := by
    obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hplant.1
    rw [← hΦr]
    exact hdom r (Set.right_mem_Icc.mpr hr)
  have hreplay := sem_frozen_replay hfR hlam hdomL hdomR hhop hrights hνdomL
  have hρ₁eq : rpatch ω₀ ρ₁ = ρ₁ := by
    funext v
    obtain ⟨s, i⟩ := v
    cases s with
    | R => rfl
    | L =>
        show ω₀ (Lv i) = ρ₁ (Lv i)
        exact (frozen_left_constant hhop i).symm
    | Aux =>
        show ω₀ ((Side.Aux, i) : Var 3) = ρ₁ ((Side.Aux, i) : Var 3)
        exact (sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ i)).symm
  have hplant' := plantT_rpatch hfL hdomL (ρ := ρ₁) hplant
  rw [hρ₁eq] at hplant'
  have hρ₁tg : ρ₁ tg = 0 := by
    rw [sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ 1)]
    exact hω₀tg
  obtain ⟨μ, hQμSem, hQμφ⟩ := hQ ρ₁ hρ₁A hρ₁tg (rpatch ν ρ₁) hplant'
  refine ⟨μ, ?_, hQμφ⟩
  rw [Program.rename_refl] at hQμSem ⊢
  exact ⟨rpatch ν ρ₁, hreplay, hQμSem⟩

theorem hopA {fL' fRh : Fin 3 → Term (Var 3)} {lamh : Term (Var 3)}
    {domL' domRh : Formula (Var 3)} {φ : Formula (Var 3)} {Q : Program (Var 3)}
    {dt : ℝ} {ω₀ : State (Var 3)}
    (hfL : ∀ i, (fL' i).fv ⊆ range Lv) (hdomL : domL'.fv ⊆ range Lv)
    (hfR : ∀ i, (fRh i).fv ⊆ range Rv) (hlam : lamh.fv ⊆ range Rv)
    (hdomR : domRh.fv ⊆ range Rv)
    (hω₀tg : ω₀ tg = 0) (hdomLω : Formula.sat domL' ω₀) (A : State (Var 3) → Prop)
    (hR : ∃ ρ₁, Program.sem (Program.ode (rightBlock fRh lamh) domRh) ω₀ ρ₁ ∧ A ρ₁)
    (hQ : ∀ σ, A σ → σ tg = 0 →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') Q φ tg dt σ) :
    faModalB (Equiv.refl (Var 3))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL')
      (Program.seq (Program.ode (rightBlock fRh lamh) domRh) Q) φ tg dt ω₀ := by
  obtain ⟨ρ₁, hrun, hρ₁⟩ := hR
  have hj := repoPrefixA (φ := φ) (Q := Q) (dt := dt) hfL hdomL hfR hlam hdomR hω₀tg A
    ⟨ρ₁, hop_run_toJoint hfR hlam hdomL hdomLω hrun, hρ₁⟩ hQ
  refine faModalB_monoQ ?_ hj
  rintro ν μ ⟨κ, hhop, hQrun⟩
  exact ⟨κ, joint_run_toR hfR hlam hhop, hQrun⟩

theorem window1_of_B (fL' : Fin 3 → Term (Var 3)) (domL' : Formula (Var 3))
    (R R' : Program (Var 3)) (φ : Formula (Var 3)) (dt : ℝ) {σ : State (Var 3)}
    (heq : ∀ ν μ, Program.sem R ν μ ↔ Program.sem R' ν μ)
    (hb : faModalB (Equiv.refl (Var 3))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') R φ tg dt
      (Function.update σ tg 0)) :
    Formula.sat (faModal (Equiv.refl (Var 3))
      (windowSeg (leftBlock fL') domL' tg dt 1) R' φ) σ := by
  have hseg := (faModalB_clockedSeg_iff (leftBlock fL') domL' R φ tg dt σ).mpr hb
  exact sat_faModal_monoL
    (fun ν μ h => (sem_windowSeg_one (leftBlock fL') domL' tg dt).mp h)
    (sat_faModal_congrR heq hseg)

/-! ## The step provider -/

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

theorem stayCase (l q : ℕ) (hl : l < 4) (hq : q < 4) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 3)} (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 3))
        (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    refine ⟨Gr_modeAt q (by omega), edge_mem q q ?_⟩
    interval_cases q <;> simp [edgeList]
  · refine gate l dt _ _ (fun hguard => ?_)
    have hanchor : Formula.sat (anchor l q) σ := by
      refine ⟨(sat_FM_append (g l) (gs l) _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
      exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
        ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
    have := respond l q hl hq dt hv hanchor
    simpa [modeW, qfOf, edgeW] using this

/-! ## The dynamic right-only reposition to the deployed's zone -/

/-- The rows, evaluated. -/
theorem sat_FRow (l : ℕ) (hl : l < 4) (ω : State (Var 3)) :
    Formula.sat (FM (g l) (gs l)) ω ↔
      (ω (Lv 2) + 5 * ω (Lv 0)) - (5 * ω (Rv 0) + 7/20) ≤ 0 ∧
        ω (Lv 1) - (ω (Rv 1) + mL' l) ≤ 0 := by
  rw [sat_FM_iff]
  rw [← eval_g l hl, ← eval_gs0 l hl]
  simp only [gs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.getD_cons_zero]

theorem upd_L (σ : State (Var 3)) (i : Fin 3) : Function.update σ tg 0 (Lv i) = σ (Lv i) :=
  Function.update_of_ne (by simp [Lv, Prod.ext_iff]) _ _
theorem upd_R (σ : State (Var 3)) (i : Fin 3) : Function.update σ tg 0 (Rv i) = σ (Rv i) :=
  Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _

/-- **The landing.** A state whose lefts are the window start's, whose right speed and
odometer only grew (the right `a` unchanged), and which lies in the target zone `q'`'s atoms,
satisfies the joint anchor `(l, q')`: the row survives (`v_R`, `s_R` only increased), the
left atoms are the start's (frozen), the envelope holds. -/
theorem land (l q' : ℕ) (hl : l < 4) (hq' : q' < 4) {σ ρ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ) (hLat : CutSat (cL l) σ)
    (hρL : ∀ i, ρ (Lv i) = σ (Lv i)) (hρa : ρ (Rv 2) = σ (Rv 2)) (hv : σ (Rv 0) ≤ ρ (Rv 0))
    (hv2 : ρ (Rv 0) ≤ capL q') (hv3 : 3/10 ≤ ρ (Rv 0)) (hs : σ (Rv 1) ≤ ρ (Rv 1))
    (hs2 : loL q' ≤ ρ (Rv 1)) :
    Formula.sat (anchor l q') ρ := by
  have hrow := (sat_FRow l hl σ).mp hσ.1
  have hdL := (sat_domL σ).mp hσ.2.1
  have hdR := (sat_domR σ).mp hσ.2.2
  have hc := cap_bounds q' hq'
  have hlo := lo_nonneg q' hq'
  refine ⟨(sat_FM_append (g l) (gs l) _ ρ).mpr ⟨(sat_FRow l hl ρ).mpr ?_,
    (atomTerms_iff (hiffL l hl) (hiffR q' hq') ρ).mpr ⟨cutSatL_congr l hl hρL hLat, ?_⟩⟩,
    (sat_domL ρ).mpr ?_, (sat_domR ρ).mpr ?_⟩
  · rw [hρL 0, hρL 1, hρL 2]; constructor <;> linarith [hrow.1, hrow.2]
  · rw [cutSatR_val q' hq' ρ]; exact ⟨hs2, hv3, hv2⟩
  · rw [hρL 0, hρL 1, hρL 2]; exact hdL
  · rw [hρa]; exact ⟨by linarith, by linarith, by linarith, hdR.2.2.2.1, hdR.2.2.2.2⟩

/-- The joint piece `(l, q')`, anchored wherever its anchor holds with the clock at 0. -/
theorem piece (l q' : ℕ) (hl : l < 4) (hq' : q' < 4) (dt : ℝ) (hv : Verd l q') :
    ∀ τ, Formula.sat (anchor l q') τ → τ tg = 0 →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q') (Term.const 1)) domR) (anchor l q') tg dt τ := by
  intro τ hτ hτtg
  have hupd : Function.update τ tg 0 = τ := by
    funext x
    by_cases hx : x = tg
    · subst hx; rw [Function.update_self, hτtg]
    · rw [Function.update_of_ne hx]
  have := couple l q' hl hq' dt hv τ hτ
  rwa [hupd] at this

/-- **One-hop reposition**: from a right start in zone `q` (an earlier zone than the window's
certified target `q'`, edge `q → q'` declared, `c_q ≤ cap_{q'}`), run zone `q` alone until the
odometer reaches `q'`'s floor (`s_R = max(s₀, lo_{q'})`), take the edge, then the certified
joint piece `(l, q')`. -/
theorem hopCase (l q q' : ℕ) (hl : l < 4) (hq : q < 4) (hq' : q' < 4)
    (hedge : (q, q') ∈ edgeList) (hself : (q', q') ∈ edgeList) (hcap : capL q ≤ capL q')
    (dt : ℝ) (hv : Verd l q') {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 3))
        (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q'), (q', modeW q', edgeW q' q')], ?_, ?_, by simp, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨Gr_modeAt q (by omega), edge_mem q q' hedge⟩
    · exact ⟨Gr_modeAt q' (by omega), edge_mem q' q' hself⟩
  · exact (show List.IsChain (fun a b : ℕ × RMode (Var 3) × REdge (Var 3) => a.2.2.tgt = b.1)
        [(q', modeW q', edgeW q' q')] from by simp).cons (by
      intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      rfl)
  · refine gate l dt _ _ (fun hguard => ?_)
    have hLat := hO1L l hl σ hguard
    have hx0 := (cutSatR_val q hq σ).mp ((sat_region_lt q hq σ).mp hreg)
    have hdomL0 : Formula.sat domL (Function.update σ tg 0) := by
      rw [sat_domL]; simp only [upd_L]; exact (sat_domL σ).mp hσ.2.1
    have hdomR0 : Formula.sat domR (Function.update σ tg 0) := by
      rw [sat_domR]; simp only [upd_R]; exact (sat_domR σ).mp hσ.2.2
    have hb := hopA (fL' := fL l) (fRh := fR q) (lamh := Term.const 1) (domL' := domL)
      (domRh := domR) (φ := anchor l q')
      (Q := Program.ode (rightBlock (fR q') (Term.const 1)) domR) (dt := dt)
      (hfL l hl) hdomL (hfR q hq) (by simp [Term.fv]) hdomR
      (Function.update_self _ _ _) hdomL0 (fun ρ => Formula.sat (anchor l q') ρ)
      (by
        obtain ⟨ρ, hrun, hρs, hρv1, hρv2, hρo⟩ := mode_reach q hq (loL q') _ hdomR0
          (by rw [upd_R]; exact hx0.2.1) (by rw [upd_R]; exact hx0.2.2)
        rw [upd_R] at hρs hρv1
        refine ⟨ρ, hrun, land l q' hl hq' hσ hLat ?_ ?_ hρv1 (le_trans hρv2 hcap)
          (le_trans hx0.2.1 hρv1) ?_ ?_⟩
        · intro i
          rw [hρo (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩,
            upd_L]
        · rw [hρo (Rv 2) ⟨by simp [Rv, Prod.ext_iff], by simp [Rv, Prod.ext_iff]⟩, upd_R]
        · rw [hρs]; exact le_max_left _ _
        · rw [hρs]; exact le_max_right _ _)
      (piece l q' hl hq' dt hv)
    have hw := window1_of_B (fL l) domL _
      (bigSeq [Program.ode (rightBlock (fR q) (Term.const 1)) domR,
        Program.ode (rightBlock (fR q') (Term.const 1)) domR]) (anchor l q') dt
      (fun ν μ => sem_foldr_seq_bigSeq [Program.ode (rightBlock (fR q) (Term.const 1)) domR]
        (Program.ode (rightBlock (fR q') (Term.const 1)) domR) ν μ) hb
    have := sat_faModal_monoPost (anchor_post l q' hl hq') hw
    simpa [modeW, qfOf, edgeW] using this

/-- **Two-hop reposition** (a `SLOW` right start of the `FAST` window; `SLOW` has no edge to
`FAST`): run `SLOW` alone up to `s_R = max(s₀, 50)`, the edge `SLOW → MEDIUM_ECO`, run
`MEDIUM_ECO` (zero duration: the odometer is already past 50), the edge
`MEDIUM_ECO → FAST`, the certified joint piece `(FAST, FAST)`. -/
theorem twoHopCase (dt : ℝ) (hv : Verd 3 3) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g 3) (gs 3)) env) σ)
    (hreg : Formula.sat (region 0) σ) :
    ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = 0) ∧
      Formula.sat (faModal (Equiv.refl (Var 3))
        (gwindowSeg (hostGuard vs 3 Side.L (mL 3)) (leftBlock (fL 3)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM (g 3) (gs 3)) env) (region (qfOf segs 0)))) σ := by
  refine ⟨[(0, modeW 0, edgeW 0 1), (1, modeW 1, edgeW 1 3), (3, modeW 3, edgeW 3 3)],
    ?_, ?_, by simp, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨Gr_modeAt 0 (by norm_num), edge_mem 0 1 (by simp [edgeList])⟩
    · exact ⟨Gr_modeAt 1 (by norm_num), edge_mem 1 3 (by simp [edgeList])⟩
    · exact ⟨Gr_modeAt 3 (by norm_num), edge_mem 3 3 (by simp [edgeList])⟩
  · refine List.IsChain.cons (List.IsChain.cons (by simp) ?_) ?_ <;>
    · intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      rfl
  · refine gate 3 dt _ _ (fun hguard => ?_)
    have hLat := hO1L 3 (by norm_num) σ hguard
    have hx0 := (cutSatR_val 0 (by norm_num) σ).mp ((sat_region_lt 0 (by norm_num) σ).mp hreg)
    have hdomL0 : Formula.sat domL (Function.update σ tg 0) := by
      rw [sat_domL]; simp only [upd_L]; exact (sat_domL σ).mp hσ.2.1
    have hdomR0 : Formula.sat domR (Function.update σ tg 0) := by
      rw [sat_domR]; simp only [upd_R]; exact (sat_domR σ).mp hσ.2.2
    have hc0 : capL 0 = 3/5 := by norm_num [capL, capQ]
    have hc1 : capL 1 = 9/10 := by norm_num [capL, capQ]
    have hc3 : capL 3 = 3/2 := by norm_num [capL, capQ]
    have hlo3 : loL 3 = 50 := by norm_num [loL, loQ]
    let EC := Program.ode (rightBlock (fR 1) (Term.const 1)) domR
    let FA := Program.ode (rightBlock (fR 3) (Term.const 1)) domR
    have hb := hopA (fL' := fL 3) (fRh := fR 0) (lamh := Term.const 1) (domL' := domL)
      (domRh := domR) (φ := anchor 3 3) (Q := Program.seq EC FA) (dt := dt)
      (hfL 3 (by norm_num)) hdomL (hfR 0 (by norm_num)) (by simp [Term.fv]) hdomR
      (Function.update_self _ _ _) hdomL0
      (fun ρ => Formula.sat domL ρ ∧ ∃ ρ₂, Program.sem EC ρ ρ₂ ∧ Formula.sat (anchor 3 3) ρ₂)
      (by
        obtain ⟨ρ₁, hrun₁, hρ₁s, hρ₁v1, hρ₁v2, hρ₁o⟩ := mode_reach 0 (by norm_num) 50 _ hdomR0
          (by rw [upd_R]; exact hx0.2.1) (by rw [upd_R]; exact hx0.2.2)
        rw [upd_R] at hρ₁s hρ₁v1
        have hρ₁L : ∀ i, ρ₁ (Lv i) = σ (Lv i) := by
          intro i
          rw [hρ₁o (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩,
            upd_L]
        have hv1 : 3/10 ≤ ρ₁ (Rv 0) := le_trans hx0.2.1 hρ₁v1
        have hs1 : 50 ≤ ρ₁ (Rv 1) := by rw [hρ₁s]; exact le_max_right _ _
        have hρ₁a : ρ₁ (Rv 2) = σ (Rv 2) := by
          rw [hρ₁o (Rv 2) ⟨by simp [Rv, Prod.ext_iff], by simp [Rv, Prod.ext_iff]⟩, upd_R]
        have hdR := (sat_domR σ).mp hσ.2.2
        have hρ₁dom : Formula.sat domR ρ₁ := by
          rw [sat_domR, hρ₁a]
          refine ⟨by linarith, by rw [hc0] at hρ₁v2; linarith, by linarith, hdR.2.2.2.1,
            hdR.2.2.2.2⟩
        obtain ⟨ρ₂, hrun₂, hρ₂s, hρ₂v1, hρ₂v2, hρ₂o⟩ := mode_reach 1 (by norm_num) 50 _ hρ₁dom
          hv1 (by rw [hc1]; rw [hc0] at hρ₁v2; linarith)
        refine ⟨ρ₁, hrun₁, ?_, ρ₂, hrun₂, land 3 3 (by norm_num) (by norm_num) hσ hLat ?_ ?_ ?_
          ?_ ?_ ?_ ?_⟩
        · rw [sat_domL, hρ₁L 0, hρ₁L 1, hρ₁L 2]; exact (sat_domL σ).mp hσ.2.1
        · intro i
          rw [hρ₂o (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩,
            hρ₁L i]
        · rw [hρ₂o (Rv 2) ⟨by simp [Rv, Prod.ext_iff], by simp [Rv, Prod.ext_iff]⟩, hρ₁a]
        · exact le_trans hρ₁v1 hρ₂v1
        · rw [hc3]; rw [hc1] at hρ₂v2; linarith
        · exact le_trans hv1 hρ₂v1
        · rw [hρ₂s, hρ₁s]; exact le_trans (le_max_left _ _) (le_max_left _ _)
        · rw [hρ₂s, hlo3]; exact le_trans hs1 (le_max_left _ _))
      (by
        rintro τ ⟨hτL, hτex⟩ hτtg
        exact hopA (hfL 3 (by norm_num)) hdomL (hfR 1 (by norm_num)) (by simp [Term.fv])
          hdomR hτtg hτL (fun ρ => Formula.sat (anchor 3 3) ρ) hτex
          (piece 3 3 (by norm_num) (by norm_num) dt hv))
    have hw := window1_of_B (fL 3) domL _
      (bigSeq [Program.ode (rightBlock (fR 0) (Term.const 1)) domR, EC, FA]) (anchor 3 3) dt
      (fun ν μ => sem_foldr_seq_bigSeq
        [Program.ode (rightBlock (fR 0) (Term.const 1)) domR, EC] FA ν μ) hb
    have := sat_faModal_monoPost (anchor_post 3 3 (by norm_num) (by norm_num)) hw
    simpa [modeW, qfOf, edgeW, EC, FA] using this

/-- Left zone `l`'s window, every right start (the emitted cover): stay in a jointOK start;
reposition from an earlier zone. -/
theorem HmultiL (l : ℕ) (hl : l < 4) (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (h33 : Verd 3 3) :
    ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region q)) σ →
      ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 3))
          (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  intro q hq σ _ hσ
  rw [Gr_len] at hq
  have hc : ∀ a b : ℕ, a < 4 → b < 4 → capQ a ≤ capQ b → capL a ≤ capL b := by
    intro a b _ _ h; unfold capL; exact_mod_cast h
  interval_cases l
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact stayCase 0 0 (by norm_num) (by norm_num) dt h00 hσ.1 hσ.2
    | 1, _, hσ =>
      exact stayCase 0 1 (by norm_num) (by norm_num) dt h01 hσ.1 hσ.2
    | 2, _, hσ =>
      exact stayCase 0 2 (by norm_num) (by norm_num) dt h02 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 0 3 (by norm_num) (by norm_num) dt h03 hσ.1 hσ.2
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact hopCase 1 0 1 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 0 1 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h11 hσ.1 hσ.2
    | 1, _, hσ =>
      exact stayCase 1 1 (by norm_num) (by norm_num) dt h11 hσ.1 hσ.2
    | 2, _, hσ =>
      exact stayCase 1 2 (by norm_num) (by norm_num) dt h12 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 1 3 (by norm_num) (by norm_num) dt h13 hσ.1 hσ.2
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact hopCase 2 0 2 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 0 2 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h22 hσ.1 hσ.2
    | 1, _, hσ =>
      exact hopCase 2 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 1 3 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h23 hσ.1 hσ.2
    | 2, _, hσ =>
      exact stayCase 2 2 (by norm_num) (by norm_num) dt h22 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 2 3 (by norm_num) (by norm_num) dt h23 hσ.1 hσ.2
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact twoHopCase dt h33 hσ.1 hσ.2
    | 1, _, hσ =>
      exact hopCase 3 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 1 3 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h33 hσ.1 hσ.2
    | 2, _, hσ =>
      exact hopCase 3 2 3 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 2 3 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h33 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 3 3 (by norm_num) (by norm_num) dt h33 hσ.1 hσ.2

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

/-! ## The left automaton, from the file -/

def nextL : List (List ℕ) :=
  (List.range 4).map (fun l =>
    (mL l).next.filterMap (Handoff.leftModeIndex rover_patrol_refine_IRv2))

/-- `SLOW → [MEDIUM_ECO, MEDIUM_BRISK, SLOW]`, `MEDIUM_ECO → [FAST, MEDIUM_BRISK, MEDIUM_ECO]`,
`MEDIUM_BRISK → [FAST, MEDIUM_ECO, MEDIUM_BRISK]`, `FAST → [FAST]`. -/
theorem nextL_eq : nextL = [[1, 2, 0], [3, 2, 1], [3, 1, 2], [3]] := by decide

theorem nextL_transitions :
    ((List.range 4).flatMap (fun m' => (nextL.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions rover_patrol_refine_IRv2 := by decide

noncomputable def guardsL : List (Formula (Var 3)) :=
  (List.range 4).map (fun l => hostGuard vs 3 Side.L (mL l))

noncomputable def A (dt : ℝ) : LeftAut 3 :=
  { windows := (List.range 4).map (fun l =>
      gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1),
    guards := guardsL,
    next := nextL }

theorem A_numModes (dt : ℝ) : (A dt).numModes = 4 := rfl

theorem A_window (dt : ℝ) (t : ℕ) (ht : t < 4) :
    (A dt).window t = gwindowSeg (hostGuard vs 3 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1 := by
  interval_cases t <;> rfl

theorem A_guard (dt : ℝ) (t : ℕ) (ht : t < 4) :
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

theorem hmvreg : ∀ q, mv ∉ (region q).fv := by
  intro q h
  by_cases hq : q < 4
  · exact aux_notin_range_Rv 0 (region_fv q hq h)
  · simp only [region, show ¬ q < 4 from by omega, if_false] at h
    simp [Formula.fv, Term.fv] at h

theorem hulBk : uL ∉ (mvRegion mv region Gr.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv region Gr.modes.length (fun q hq => region_fv q hq) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hulG (dt : ℝ) : ∀ t, uL ∉ ((A dt).guard t).fv := by
  intro t h
  by_cases ht : t < 4
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
  by_cases ht : t < 4
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
  notMem_bv_rightAutomatonBody Gr mv uL (by decide) (aux_notin_range_Rv 2) htt hRv

/-! ## The handoffs, in-kernel: the odometer margin only loosens along the route -/

theorem handoff (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat env ω → Formula.sat ((A dt).guard t) ω →
      Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [A_numModes] at hm'
  rw [A_succ, nextL_eq] at ht
  have ht4 : t < 4 := by interval_cases m' <;> simp at ht <;> omega
  have hm : mL' m' ≤ mL' t := by
    interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl | rfl <;>
      norm_num [mL', mQ]
  rw [FRow, sat_FRow m' hm'] at hF
  rw [FRow, sat_FRow t ht4]
  exact ⟨hF.1, by linarith [hF.2]⟩

/-! ## The per-mode steps -/

theorem hstepM (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (h33 : Verd 3 3) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv region Gr.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((A dt).window t)
      (Program.star (rightAutomatonBody Gr mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv region Gr.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  exact hstepMode_multiR Gr mv (FRow t) env region _ (aux_notin_FRow 0 t) hmvenv hmvreg
    hfresh htt hlt (framesGw t dt 0 (by decide))
    (HmultiL t ht dt h00 h01 h02 h03 h11 h12 h13 h22 h23 h33)

/-! ## Theorem 3, mode-keyed -/

/-- **`rover_patrol_refine` (suite_v2), Theorem 3 at the DECLARED mode-dependent invariant.**
Left: the automaton of the file (`SLOW → [MEDIUM_ECO, MEDIUM_BRISK, SLOW]`,
`MEDIUM_ECO → [FAST, MEDIUM_BRISK, MEDIUM_ECO]`, `MEDIUM_BRISK → [FAST, MEDIUM_ECO,
MEDIUM_BRISK]`, `FAST → [FAST]`; the worn deployed rover with its motor lag, `v' = a`,
`s' = v`, `a' = 5 (1.25 (0.8 c − v) − a)`), each step `?guard_t ; u_L := t ; ?guard_t ;
window_t` with `u_L = (Aux, 2)`; right: the four-zone reference automaton of the file
(`v' = c − v`, `s' = v`, `a' = 0`, `c = 0.6/0.9/1.1/1.5`; declared edges; nothing pruned). The
loop invariant keys the declared rows by `u_L` (`a_L + 5 v_L ≤ 5 v_R + 0.35 ∧ s_L ≤ s_R + m`,
`m = 0.5, 1, 1, 2`), plus the evolve envelope (`v ∈ [0, 1.6]`, `s ≥ 0`, `a ∈ [−2, 2]`; no
odometer wall, §19 of `docs/SUITE-REDESIGN.md`) on both sides and the right zone's region —
its kept cut atoms (`s ≥ floor`, `0.3 ≤ v ≤ cap`). Response (the emitted cover): in every
left window, STAY in a jointOK start zone on the certified joint segment at the cover's
λ = 9/4; from an earlier zone, reposition right-only (the explicit zone run at rate 1, until
the odometer reaches the target zone's floor; from `SLOW` in the `FAST` window via
`MEDIUM_ECO`) and then the certified joint piece. The left atoms are the extended
certificate's linear-form chain (`q = a + 2.5 (v − c)` in its box, then the derived speed
bounds), lifted by the `CutLiftX` shape lemmas; handoffs in-kernel (the margin only grows
along the route); existence is the explicit zone solution. Residuals: ten stratified verdict
packs `Verd l q` (left window `l` at its own row, `modalVerdX` at λ = 9/4, the tool's own
narrowed queries). -/
theorem rover_patrol_refine_modeKeyed (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (h33 : Verd 3 3) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody Gr mv)
      (psiK uL ϕRow (A dt).numModes domL domR
        (mvRegionR mv region Gr.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL Gr mv FRow ϕRow domL domR
    (mvRegion mv region Gr.modes.length) (mvRegionR mv region Gr.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) htt hRv
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody Gr mv) FRow env
      (mvRegion mv region Gr.modes.length) (aux_notin_FRow 2) hulenv hulBk (hulG dt)
      (hframesUl dt) hulR (hnext dt)
      (hstepM dt h00 h01 h02 h03 h11 h12 h13 h22 h23 h33) (handoff dt)
  · exact hddF_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv region Gr.modes.length) (hwin dt) (hgrd dt) (hnext dt) htt hRv
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv region Gr.modes.length (fun q hq => region_fv q hq) hv)

end V2RoverPatrolRefine
end RelCertifier
