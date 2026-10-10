/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_linkloss` (suite_v2) — mode-keyed Theorem 3 over the GUARDED automata

Three-follower CACC string (`n = 6`: `g1, r1, g2, r2, g3, r3`), linear damped links on both
sides (roots `ρ = 1/4, 1/2`). The file declares one row per LEFT mode (FOLLOW: 12
components, the exact refinement up to the 1 m offset; LOST: 14 components, link 1
loosened after the latch to the radar stand-off 35). The guards are the OPERATING RANGE
(`docs/SUITE-REDESIGN.md` §20; the engagement band of the earlier model made the nominal
controller block after a full cycle, violating Assumption 1). This leaf composes the
per-left-mode modal statements over the file's left automaton
(`ModeHandoff.theorem3_modeKeyed`), with `mv = (Aux, 0)`, the window clock `tg = (Aux, 1)`
and the left mode variable `u_L = (Aux, 2)`, against the GUARDED right automaton (every edge
tests the entered mode's lowered guard) at the mode-consistent region (guard ∧ kept cuts).
Ingredients: the suite_v2 cut layer (`CutRespond`), O2 for every kept atom through
`Platoon3Link` (guard atoms, linear forms, LOST's derived floor), existence Z3-free by the
explicit closed-form solution of the linear right `FOLLOW` mode (`link_bounds`), the gap
floor along the reference's own run (`gap_floor_Ronly`), and the in-kernel handoff
FOLLOW → LOST.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.platoon3_linkloss
import RelCertifier.InstancesV2.Modal.Platoon3Link

set_option linter.unusedSimpArgs false
namespace RelCertifier
namespace V2Platoon3Linkloss

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle Platoon3Link

def vs : List String := ["g1", "r1", "g2", "r2", "g3", "r3"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := platoon3_linkloss_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := platoon3_linkloss_IRv2.R.modes.getD q dm

abbrev mv : Var 6 := (Side.Aux, 0)
abbrev tg : Var 6 := (Side.Aux, 1)
abbrev uL : Var 6 := (Side.Aux, 2)

noncomputable def fL (l : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.R (mR q)
noncomputable def domL : Formula (Var 6) := hostEvolve vs 6 Side.L (mL 0)
noncomputable def domR : Formula (Var 6) := hostEvolve vs 6 Side.R (mR 0)
noncomputable def env : Formula (Var 6) := Formula.and domL domR

/-! ## Parse pins -/

theorem hq0_25 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq29 : Run.parseRat "29" = some (29 : ℚ) := by
  have h : parseQ "29" = some (⟨29, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq30 : Run.parseRat "30" = some (30 : ℚ) := by
  have h : parseQ "30" = some (⟨30, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq35 : Run.parseRat "35" = some (35 : ℚ) := by
  have h : parseQ "35" = some (⟨35, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq2 : Run.parseRat "2" = some (2 : ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm2 : Run.parseRat "-2" = some (-2 : ℚ) := by
  have h : parseQ "-2" = some (⟨-2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq3 : Run.parseRat "3" = some (3 : ℚ) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm3 : Run.parseRat "-3" = some (-3 : ℚ) := by
  have h : parseQ "-3" = some (⟨-3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm3_5 : Run.parseRat "-3.5" = some ((-7:ℚ)/2) := by
  have h : parseQ "-3.5" = some (⟨-35, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm6 : Run.parseRat "-6" = some (-6 : ℚ) := by
  have h : parseQ "-6" = some (⟨-6, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq37 : Run.parseRat "37" = some (37 : ℚ) := by
  have h : parseQ "37" = some (⟨37, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq21 : Run.parseRat "21" = some (21 : ℚ) := by
  have h : parseQ "21" = some (⟨21, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq38 : Run.parseRat "38" = some (38 : ℚ) := by
  have h : parseQ "38" = some (⟨38, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq22 : Run.parseRat "22" = some (22 : ℚ) := by
  have h : parseQ "22" = some (⟨22, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq36 : Run.parseRat "36" = some (36 : ℚ) := by
  have h : parseQ "36" = some (⟨36, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq24 : Run.parseRat "24" = some (24 : ℚ) := by
  have h : parseQ "24" = some (⟨24, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq23 : Run.parseRat "23" = some (23 : ℚ) := by
  have h : parseQ "23" = some (⟨23, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm0_125 : Run.parseRat "-0.125" = some ((-1:ℚ)/8) := by
  have h : parseQ "-0.125" = some (⟨-125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq0_75 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq29_0 : Run.parseRat "29.0" = some (29 : ℚ) := by
  have h : parseQ "29.0" = some (⟨290, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq30_0 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq35_0 : Run.parseRat "35.0" = some (35 : ℚ) := by
  have h : parseQ "35.0" = some (⟨350, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq60_0 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm10_0 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq10_0 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq25_0 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq33_0 : Run.parseRat "33.0" = some (33 : ℚ) := by
  have h : parseQ "33.0" = some (⟨330, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm1_0 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq5_0 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq1_5 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq3_0 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq6_0 : Run.parseRat "6.0" = some (6 : ℚ) := by
  have h : parseQ "6.0" = some (⟨60, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq17_5 : Run.parseRat "17.5" = some ((35:ℚ)/2) := by
  have h : parseQ "17.5" = some (⟨175, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm12_5 : Run.parseRat "-12.5" = some ((-25:ℚ)/2) := by
  have h : parseQ "-12.5" = some (⟨-125, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq25 : Run.parseRat "25" = some (25 : ℚ) := by
  have h : parseQ "25" = some (⟨25, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm15 : Run.parseRat "-15" = some (-15 : ℚ) := by
  have h : parseQ "-15" = some (⟨-15, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq16 : Run.parseRat "16" = some (16 : ℚ) := by
  have h : parseQ "16" = some (⟨16, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq5 : Run.parseRat "5" = some (5 : ℚ) := by
  have h : parseQ "5" = some (⟨5, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq2_0 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq20_0 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq58_0 : Run.parseRat "58.0" = some (58 : ℚ) := by
  have h : parseQ "58.0" = some (⟨580, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq21_0 : Run.parseRat "21.0" = some (21 : ℚ) := by
  have h : parseQ "21.0" = some (⟨210, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq59_0 : Run.parseRat "59.0" = some (59 : ℚ) := by
  have h : parseQ "59.0" = some (⟨590, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq19_0 : Run.parseRat "19.0" = some (19 : ℚ) := by
  have h : parseQ "19.0" = some (⟨190, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num


/-! ## Evaluations of the lowered data -/

/-- Three damped links on side `W`, set points `c₁, c₂, c₃`. -/
def PairField3 (W : Fin 6 → Var 6) (f : Fin 6 → Term (Var 6)) (c1 c2 c3 : ℝ) : Prop :=
  ∀ z : State (Var 6),
    Term.eval (f 0) z = z (W 1) ∧
    Term.eval (f 1) z = -(1/8) * (z (W 0) - c1) - 3/4 * z (W 1) ∧
    Term.eval (f 2) z = z (W 3) ∧
    Term.eval (f 3) z = -(1/8) * (z (W 2) - c2) - 3/4 * z (W 3) ∧
    Term.eval (f 4) z = z (W 5) ∧
    Term.eval (f 5) z = -(1/8) * (z (W 4) - c3) - 3/4 * z (W 5)

/-- `FOLLOW` (all links at 29) and `LOST` (link 1 latched at the radar stand-off 35). -/
theorem fL_field0 : PairField3 Lv (fL 0) 29 29 29 := by
  intro z
  simp [fL, hostDyn, mL, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq29_0, hq35_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]
  refine ⟨by ring, by ring, by ring⟩

theorem fL_field1 : PairField3 Lv (fL 1) 35 29 29 := by
  intro z
  simp [fL, hostDyn, mL, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq29_0, hq35_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]
  refine ⟨by ring, by ring, by ring⟩

theorem fR_field : PairField3 Rv (fR 0) 30 30 30 := by
  intro z
  simp [fR, hostDyn, mR, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq30_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
  refine ⟨by ring, by ring, by ring⟩

/-- The evolve box (both sides): `g_i ∈ [0, 60]`, `r_i ∈ [−10, 10]`. -/
def Box (W : Fin 6 → Var 6) (x : State (Var 6)) : Prop :=
  (0 ≤ x (W 0) ∧ x (W 0) ≤ 60 ∧ -10 ≤ x (W 1) ∧ x (W 1) ≤ 10) ∧
  (0 ≤ x (W 2) ∧ x (W 2) ≤ 60 ∧ -10 ≤ x (W 3) ∧ x (W 3) ≤ 10) ∧
  (0 ≤ x (W 4) ∧ x (W 4) ≤ 60 ∧ -10 ≤ x (W 5) ∧ x (W 5) ≤ 10)

theorem sat_domR (x : State (Var 6)) : Formula.sat domR x ↔ Box Rv x := by
  simp only [domR, hostEvolve, mR, platoon3_linkloss_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hq0_0, hq60_0, hqm10_0, hq10_0, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    Box, and_assoc]

theorem sat_domL (x : State (Var 6)) : Formula.sat domL x ↔ Box Lv x := by
  simp only [domL, hostEvolve, mL, platoon3_linkloss_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hq0_0, hq60_0, hqm10_0, hq10_0, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv,
    Box, and_assoc]

theorem domL_univ (l : ℕ) (hl : l < 2) : hostEvolve vs 6 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 6 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-! ## The cut families, concretely -/

noncomputable def cL (l : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.L (cutAtomsOfX platoon3_linkloss_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.R (cutAtomsOfX platoon3_linkloss_cutsV2X.R (mR q).name)

/-- Left `FOLLOW` links (set point 29; projected gap `[20, 58]`), left `LOST` link 1 (the
radar stand-off 35), right `FOLLOW` links (set point 30; projected gap `[21, 59]`). The
linear-form boxes are the tool's, read off the operating-range guard box. -/
noncomputable def pF : LinkC := ⟨29, 35/2, -25/2, 25, -15, 20, 58⟩
noncomputable def pLost : LinkC := ⟨35, 16, -25/2, 22, -15, 20, 58⟩
noncomputable def pR : LinkC := ⟨30, 35/2, -25/2, 25, -15, 21, 59⟩

theorem pF_ok : LinkOK pF := by simp only [LinkOK, pF]; norm_num
theorem pLost_ok : LinkOK pLost := by simp only [LinkOK, pLost]; norm_num
theorem pR_ok : LinkOK pR := by simp only [LinkOK, pR]; norm_num

/-- LOST's derived floor on link 1, `g₁ ≥ 5` (from the ρ = 1/2 form's lower bound). -/
noncomputable def lostExtra : List (Term (Var 6)) := [thrGe (Lv 0) 5]

theorem cL_terms0 : (cL 0).map Prod.snd = termsW Lv pF pF pF [] := by
  simp [cL, cutPairsX, cutAtomsOfX, platoon3_linkloss_cutsV2X, mL, platoon3_linkloss_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons, hq0_25, hq0_5, hq29, hq30, hq35, hq17_5, hqm12_5, hq25, hqm15, hq16, hq22, hq5, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq21_0, hq59_0,
    ITerm.toHost, termsW, guardT, linT, pgGe, pgLe, linLe, linGe, linQ, thrLe, thrGe, Lv, pF]

theorem cL_terms1 : (cL 1).map Prod.snd = termsW Lv pLost pF pF lostExtra := by
  simp [cL, cutPairsX, cutAtomsOfX, platoon3_linkloss_cutsV2X, mL, platoon3_linkloss_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons, hq0_25, hq0_5, hq29, hq30, hq35, hq17_5, hqm12_5, hq25, hqm15, hq16, hq22, hq5, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq21_0, hq59_0,
    ITerm.toHost, termsW, guardT, linT, pgGe, pgLe, linLe, linGe, linQ, thrLe, thrGe, Lv, pF,
    pLost, lostExtra]

theorem cR_terms0 : (cR 0).map Prod.snd = termsW Rv pR pR pR [] := by
  simp [cR, cutPairsX, cutAtomsOfX, platoon3_linkloss_cutsV2X, mR, platoon3_linkloss_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons, hq0_25, hq0_5, hq29, hq30, hq35, hq17_5, hqm12_5, hq25, hqm15, hq16, hq22, hq5, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq21_0, hq59_0,
    ITerm.toHost, termsW, guardT, linT, pgGe, pgLe, linLe, linGe, linQ, thrLe, thrGe, Rv, pR]

theorem atomsNonstrictL (l : ℕ) (hl : l < 2) :
    ∀ x ∈ cutAtomsOfX platoon3_linkloss_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp only [cutAtomsOfX, platoon3_linkloss_cutsV2X, mL, platoon3_linkloss_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 1) :
    ∀ x ∈ cutAtomsOfX platoon3_linkloss_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  obtain rfl : q = 0 := by omega
  intro x hx
  simp only [cutAtomsOfX, platoon3_linkloss_cutsV2X, mR, platoon3_linkloss_IRv2] at hx
  simp at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 2) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 1) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 2) :
    ∀ ν, Formula.sat (hostGuard vs 6 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard platoon3_linkloss_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp only [cutAtomsOfX, platoon3_linkloss_cutsV2X, mL, platoon3_linkloss_IRv2] at hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp only [cutAtomsOfX, platoon3_linkloss_cutsV2X, mL, platoon3_linkloss_IRv2] at hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hq0_25, hq0_5, hq29, hq30, hq35, hq17_5, hqm12_5, hq25, hqm15, hq16, hq22, hq5, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq21_0, hq59_0, vs, Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq19_0, hq59_0, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq25_0, hq21_0, hq60_0,
        vs, Run.resolveVar, List.findIdx?_cons]

/-! ## O2: the kept atoms stay along the joint flows (`Platoon3Link` shape lemmas) -/

theorem linkFields {W : Fin 6 → Var 6} {f : Fin 6 → Term (Var 6)} {c1 c2 c3 : ℝ}
    (h : PairField3 W f c1 c2 c3) :
    LinkField W f 0 1 c1 ∧ LinkField W f 2 3 c2 ∧ LinkField W f 4 5 c3 :=
  ⟨⟨fun z => (h z).1, fun z => (h z).2.1⟩, ⟨fun z => (h z).2.2.1, fun z => (h z).2.2.2.1⟩,
    ⟨fun z => (h z).2.2.2.2.1, fun z => (h z).2.2.2.2.2⟩⟩

/-- **The right family stays** (each atom from a base where the whole family holds). -/
theorem stayR_terms (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv)
    (dom : Formula (Var 6)) (hbox : ∀ z, Formula.sat dom z → Box Rv z)
    (p1 p2 p3 : LinkC) (ok1 : LinkOK p1) (ok2 : LinkOK p2) (ok3 : LinkOK p3)
    (hF : PairField3 Rv fR p1.c p2.c p3.c) :
    ∀ t ∈ termsW Rv p1 p2 p3 [], ∀ ν, (∀ t' ∈ termsW Rv p1 p2 p3 [], Term.eval t' ν ≤ 0) →
      BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
        (fun ω => Term.eval t ω) ν := by
  obtain ⟨F1, F2, F3⟩ := linkFields hF
  intro t ht ν hall
  have own := hall t ht
  simp only [termsW, List.append_nil, List.mem_append] at ht
  rcases ht with (((((ht | ht) | ht) | ht) | ht) | ht)
  · exact stayR_link fL fR lamv hlam dom 0 1 p1 ok1 F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 2 3 p2 ok2 F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 4 5 p3 ok3 F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 0 1 p1 ok1 F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 2 3 p2 ok2 F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 4 5 p3 ok3 F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_right _ ht) ν own

/-- **The left family stays**; the extra derived floor `g ≥ K'` on link 1 is stratified on
the link's `ρ = 1/2` lower form (`hder`). -/
theorem stayL_terms (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6))
    (dom : Formula (Var 6)) (hbox : ∀ z, Formula.sat dom z → Box Lv z)
    (p1 p2 p3 : LinkC) (ok1 : LinkOK p1) (ok2 : LinkOK p2) (ok3 : LinkOK p3)
    (hF : PairField3 Lv fL p1.c p2.c p3.c) (extra : List (Term (Var 6)))
    (hder : ∀ t ∈ extra, ∃ K', t = thrGe (Lv 0) K' ∧ 1/2 * (K' - p1.c) ≤ p1.e) :
    ∀ t ∈ termsW Lv p1 p2 p3 extra, ∀ ν, (∀ t' ∈ termsW Lv p1 p2 p3 extra, Term.eval t' ν ≤ 0) →
      BoxLe (Program.ode (jointSys fL fR lam) dom)
        (fun ω => Term.eval t ω) ν := by
  obtain ⟨F1, F2, F3⟩ := linkFields hF
  intro t ht ν hall
  have own := hall t ht
  simp only [termsW, List.mem_append] at ht
  rcases ht with ((((((ht | ht) | ht) | ht) | ht) | ht) | ht)
  · exact stayL_link fL fR lam dom 0 1 p1 ok1 F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayL_link fL fR lam dom 2 3 p2 ok2 F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayL_link fL fR lam dom 4 5 p3 ok3 F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayL_link fL fR lam dom 0 1 p1 ok1 F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayL_link fL fR lam dom 2 3 p2 ok2 F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayL_link fL fR lam dom 4 5 p3 ok3 F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_right _ ht) ν own
  · obtain ⟨K', rfl, hK'⟩ := hder t ht
    have hq : Term.eval (linGe (Lv 0) (Lv 1) (1/2) p1.c p1.e) ν ≤ 0 :=
      hall _ (by simp [termsW, linT])
    exact stayL_derGe fL fR lam dom 0 1 (1/2) p1.c p1.e K' hroot2 (by norm_num) ok1.2.2.2.1
      (by norm_num) hK' F1 ν hq own

/-! ## The declared rows (one per left mode) -/

noncomputable def comps (l : ℕ) : List (Term (Var 6)) :=
  hostComps vs 6 (platoon3_linkloss_IRv2.invariants.getD l ("", PForm.tt)).2
noncomputable def c0 : Term (Var 6) := Term.const 0
noncomputable def g (l : ℕ) : Term (Var 6) := (comps l).getD 0 c0
/-- Components `1 …` of row `l` (FOLLOW 12 components, LOST 14; the cover's strata orders are
the identities). -/
noncomputable def gs : ℕ → List (Term (Var 6))
  | 0 => [(comps 0).getD 1 c0, (comps 0).getD 2 c0, (comps 0).getD 3 c0, (comps 0).getD 4 c0, (comps 0).getD 5 c0, (comps 0).getD 6 c0, (comps 0).getD 7 c0, (comps 0).getD 8 c0, (comps 0).getD 9 c0, (comps 0).getD 10 c0, (comps 0).getD 11 c0]
  | _ => [(comps 1).getD 1 c0, (comps 1).getD 2 c0, (comps 1).getD 3 c0, (comps 1).getD 4 c0, (comps 1).getD 5 c0, (comps 1).getD 6 c0, (comps 1).getD 7 c0, (comps 1).getD 8 c0, (comps 1).getD 9 c0, (comps 1).getD 10 c0, (comps 1).getD 11 c0, (comps 1).getD 12 c0, (comps 1).getD 13 c0]

/-- The cover's strata order of window `l` (the identity on the row's components). -/
def order : ℕ → List ℕ
  | 0 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  | _ => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- Lowered invariant components mention no Aux coordinate. -/
theorem invComponents_no_aux {vars : List String} {n : ℕ} :
    ∀ (f : PForm) (l : List (ITerm n)), Oracle.invComponents vars n f = some l →
      ∀ t ∈ l, ∀ v ∈ (ITerm.toHost t).fv, v.1 ≠ Side.Aux := by
  intro f
  induction f with
  | tt =>
      intro l h t ht
      simp [Oracle.invComponents] at h
      subst h
      simp at ht
  | cmp op a b =>
      intro l h t ht v hv
      simp only [Oracle.invComponents] at h
      split at h
      · rcases hea : Run.lowerE vars n Side.L a with _ | ea <;> rw [hea] at h
        · simp at h
        rcases heb : Run.lowerE vars n Side.L b with _ | eb <;> rw [heb] at h
        · simp at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [List.mem_singleton] at ht
        subst ht
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact Run.lowerE_no_aux (by simp) hea v hv
        · exact Run.lowerE_no_aux (by simp) heb v hv
      · split at h
        · rcases hea : Run.lowerE vars n Side.L a with _ | ea <;> rw [hea] at h
          · simp at h
          rcases heb : Run.lowerE vars n Side.L b with _ | eb <;> rw [heb] at h
          · simp at h
          simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          simp only [List.mem_singleton] at ht
          subst ht
          simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
          rcases hv with hv | hv
          · exact Run.lowerE_no_aux (by simp) heb v hv
          · exact Run.lowerE_no_aux (by simp) hea v hv
        · exact absurd h (by simp)
  | and x y ihx ihy =>
      intro l h t ht v hv
      simp only [Oracle.invComponents] at h
      rcases hx : Oracle.invComponents vars n x with _ | lx <;> rw [hx] at h
      · simp at h
      rcases hy : Oracle.invComponents vars n y with _ | ly <;> rw [hy] at h
      · simp at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
      subst h
      rcases List.mem_append.mp ht with ht | ht
      · exact ihx lx hx t ht v hv
      · exact ihy ly hy t ht v hv
  | or x y _ _ => intro l h; simp [Oracle.invComponents] at h
  | not x _ => intro l h; simp [Oracle.invComponents] at h


theorem comps_mem_fv (l : ℕ) : ∀ c ∈ comps l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc v hv
  unfold comps hostComps at hc
  rcases h : Oracle.invComponents vs 6 (platoon3_linkloss_IRv2.invariants.getD l
      ("", PForm.tt)).2 with _ | L
  · rw [h] at hc; simp at hc
  · rw [h] at hc
    simp only [Option.map_some, Option.getD_some, List.mem_map] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact notAux_mem_LR (invComponents_no_aux _ L h t ht v hv)

theorem getD_fv (l i : ℕ) : ((comps l).getD i c0).fv ⊆ range Lv ∪ range Rv := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (comps l)[i]? with _ | c
  · simp [c0, Term.fv]
  · simp only [Option.getD_some]
    exact comps_mem_fv l c (List.mem_of_getElem? h)

theorem comps_fv_all (l : ℕ) : ∀ c ∈ g l :: gs l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  match l with
  | 0 =>
      simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact getD_fv _ _
  | l + 1 =>
      simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> exact getD_fv _ _

/-- Row FOLLOW lowers to exactly 12 components, row LOST to 14 (so `g l :: gs l` is the whole
row). -/
theorem comps_length0 : (comps 0).length = 12 := by
  have e1 : ("L_g1".drop 2).copy = "g1" := by decide
  have e2 : ("R_g1".drop 2).copy = "g1" := by decide
  have e3 : ("L_r1".drop 2).copy = "r1" := by decide
  have e4 : ("R_r1".drop 2).copy = "r1" := by decide
  have e5 : ("L_g2".drop 2).copy = "g2" := by decide
  have e6 : ("R_g2".drop 2).copy = "g2" := by decide
  have e7 : ("L_r2".drop 2).copy = "r2" := by decide
  have e8 : ("R_r2".drop 2).copy = "r2" := by decide
  have e9 : ("L_g3".drop 2).copy = "g3" := by decide
  have e10 : ("R_g3".drop 2).copy = "g3" := by decide
  have e11 : ("L_r3".drop 2).copy = "r3" := by decide
  have e12 : ("R_r3".drop 2).copy = "r3" := by decide
  simp [comps, hostComps, platoon3_linkloss_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    List.findIdx?_cons, hq0_0, hq1_0, hq0_25, hq0_5, hq5_0, hq1_5, hq3_0, hq6_0]

theorem comps_length1 : (comps 1).length = 14 := by
  have e1 : ("L_g1".drop 2).copy = "g1" := by decide
  have e2 : ("R_g1".drop 2).copy = "g1" := by decide
  have e3 : ("L_r1".drop 2).copy = "r1" := by decide
  have e4 : ("R_r1".drop 2).copy = "r1" := by decide
  have e5 : ("L_g2".drop 2).copy = "g2" := by decide
  have e6 : ("R_g2".drop 2).copy = "g2" := by decide
  have e7 : ("L_r2".drop 2).copy = "r2" := by decide
  have e8 : ("R_r2".drop 2).copy = "r2" := by decide
  have e9 : ("L_g3".drop 2).copy = "g3" := by decide
  have e10 : ("R_g3".drop 2).copy = "g3" := by decide
  have e11 : ("L_r3".drop 2).copy = "r3" := by decide
  have e12 : ("R_r3".drop 2).copy = "r3" := by decide
  simp [comps, hostComps, platoon3_linkloss_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    List.findIdx?_cons, hq0_0, hq1_0, hq0_25, hq0_5, hq5_0, hq1_5, hq3_0, hq6_0]

/-- The window's row is the left mode's own declared row (by name, as the tool reads it). -/
theorem invRow_faithful (l : ℕ) (hl : l < 2) :
    Handoff.invRowOf platoon3_linkloss_IRv2 (mL l)
      = some (platoon3_linkloss_IRv2.invariants.getD l ("", PForm.tt)).2 := by
  interval_cases l <;> decide

/-! ## Existence: the explicit solution of the (linear) right `FOLLOW` mode -/

noncomputable def solC (c : ℝ) (b : State (Var 6)) (t : ℝ) : Fin 6 → ℝ
  | ⟨0, _⟩ => gS c (b (Rv 0)) (b (Rv 1)) t
  | ⟨1, _⟩ => rS c (b (Rv 0)) (b (Rv 1)) t
  | ⟨2, _⟩ => gS c (b (Rv 2)) (b (Rv 3)) t
  | ⟨3, _⟩ => rS c (b (Rv 2)) (b (Rv 3)) t
  | ⟨4, _⟩ => gS c (b (Rv 4)) (b (Rv 5)) t
  | ⟨5, _⟩ => rS c (b (Rv 4)) (b (Rv 5)) t

noncomputable def solΦ (c : ℝ) (b : State (Var 6)) (t : ℝ) : State (Var 6) :=
  fun x => if x.1 = Side.R then solC c b t x.2 else b x

theorem solΦ_R (c : ℝ) (b : State (Var 6)) (t : ℝ) (j : Fin 6) :
    solΦ c b t (Rv j) = solC c b t j := by simp [solΦ, Rv]

theorem solΦ_zero (c : ℝ) (b : State (Var 6)) : solΦ c b 0 = b := by
  funext x
  obtain ⟨s, j⟩ := x
  by_cases hs : s = Side.R
  · subst hs
    rw [show ((Side.R, j) : Var 6) = Rv j from rfl, solΦ_R]
    fin_cases j <;> simp [solC, gS_zero, rS_zero, Rv]
  · simp [solΦ, hs]

theorem solΦ_frozen (c : ℝ) (b : State (Var 6)) (t : ℝ) (x : Var 6) (hx : x.1 ≠ Side.R) :
    solΦ c b t x = b x := by simp [solΦ, hx]

/-- The link's own box and slow form at the anchor (the evolve box, the projected-gap
guard). -/
def LinkStart (c : ℝ) (x y : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 60 ∧ -10 ≤ y ∧ y ≤ 10 ∧ -(9/2) ≤ Q2 c x y ∧ 2 * Q2 c x y ≤ 60 - c

def QBounds (c : ℝ) (b : State (Var 6)) : Prop :=
  LinkStart c (b (Rv 0)) (b (Rv 1)) ∧ LinkStart c (b (Rv 2)) (b (Rv 3)) ∧
    LinkStart c (b (Rv 4)) (b (Rv 5))

theorem solΦ_box (c : ℝ) (hc1 : 20 ≤ c) (hc2 : c ≤ 60) (b : State (Var 6)) (hb : QBounds c b)
    (t : ℝ) (ht : 0 ≤ t) : Box Rv (solΦ c b t) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := hb
  have k0 := link_bounds c (9/2) _ _ t ht hc1 hc2 (by linarith) (by norm_num) a1 a2 a3 a4 a5 a6
  have k1 := link_bounds c (9/2) _ _ t ht hc1 hc2 (by linarith) (by norm_num) b1 b2 b3 b4 b5 b6
  have k2 := link_bounds c (9/2) _ _ t ht hc1 hc2 (by linarith) (by norm_num) d1 d2 d3 d4 d5 d6
  simp only [Box, solΦ_R]
  exact ⟨⟨k0.1.1, k0.1.2, k0.2.1, k0.2.2⟩, ⟨k1.1.1, k1.1.2, k1.2.1, k1.2.2⟩,
    ⟨k2.1.1, k2.1.2, k2.2.1, k2.2.2⟩⟩

/-- The explicit solution solves the stretched right block (`λ = 1`). -/
theorem solΦ_deriv (c : ℝ) (fR : Fin 6 → Term (Var 6)) (hF : PairField3 Rv fR c c c)
    (b : State (Var 6)) (s t : ℝ) :
    ∀ p ∈ rightBlock fR (Term.const 1),
      HasDerivWithinAt (fun u => solΦ c b u p.1) (p.2.eval (solΦ c b t)) (Icc 0 s) t := by
  intro p hp
  simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
  obtain ⟨i, rfl⟩ := hp
  have hfun : (fun u => solΦ c b u (Rv i)) = fun u => solC c b u i := by
    funext u; exact solΦ_R c b u i
  simp only [hfun, Term.eval, AOp.interp, one_mul]
  refine HasDerivAt.hasDerivWithinAt ?_
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := hF (solΦ c b t)
  fin_cases i
  · rw [show ((⟨0, by norm_num⟩ : Fin 6)) = (0 : Fin 6) from rfl, f0, solΦ_R]
    exact gS_hasDeriv c _ _ t
  · rw [show ((⟨1, by norm_num⟩ : Fin 6)) = (1 : Fin 6) from rfl, f1, solΦ_R, solΦ_R]
    exact rS_hasDeriv c _ _ t
  · rw [show ((⟨2, by norm_num⟩ : Fin 6)) = (2 : Fin 6) from rfl, f2, solΦ_R]
    exact gS_hasDeriv c _ _ t
  · rw [show ((⟨3, by norm_num⟩ : Fin 6)) = (3 : Fin 6) from rfl, f3, solΦ_R, solΦ_R]
    exact rS_hasDeriv c _ _ t
  · rw [show ((⟨4, by norm_num⟩ : Fin 6)) = (4 : Fin 6) from rfl, f4, solΦ_R]
    exact gS_hasDeriv c _ _ t
  · rw [show ((⟨5, by norm_num⟩ : Fin 6)) = (5 : Fin 6) from rfl, f5, solΦ_R, solΦ_R]
    exact rS_hasDeriv c _ _ t



/-- **The existence residual, discharged Z3-free by the explicit solution.** From any anchor
satisfying the right `FOLLOW` mode's kept atoms (the rated closing rate and the projected
gap) and the evolve box, the closed-form solution of the three damped links (set point 30)
solves the right block, freezes every other coordinate, and stays in the evolve box. -/
theorem es (l : ℕ) (dt : ℝ) :
    ∀ σ, Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR 0)))
        (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR 0) (Term.const 1) domL domR dt (Function.update σ tg 0) := by
  intro σ hσ s ΦL hs0 _ _ _ hmaskL _
  have hatoms := ((sat_FM_append (g l) (gs l) _ σ).mp hσ.1).2
  have hR : ∀ t ∈ termsW Rv pR pR pR [], Term.eval t σ ≤ 0 := by
    intro t ht
    apply hatoms
    unfold atomTerms
    rw [List.map_append, cR_terms0]
    exact List.mem_append_right _ ht
  have hbox : Box Rv σ := (sat_domR σ).mp hσ.2.2
  have hbR : ∀ j : Fin 6, ΦL s (Rv j) = σ (Rv j) := by
    intro j
    rw [hmaskL s ⟨hs0, le_rfl⟩ (Rv j) (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub _ _ h
      simp [Lv, Rv, Prod.ext_iff] at hi)]
    exact Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hQ : QBounds 30 (ΦL s) := by
    have m : ∀ t, t ∈ termsW Rv pR pR pR [] → Term.eval t σ ≤ 0 := hR
    simp only [termsW, guardT, linT, pR, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at m
    have a1 := m (thrGe (Rv 1) (-10)) (by simp)
    have a2 := m (thrLe (Rv 1) 10) (by simp)
    have a3 := m (pgGe (Rv 0) (Rv 1) 21) (by simp)
    have a4 := m (pgLe (Rv 0) (Rv 1) 59) (by simp)
    have b1 := m (thrGe (Rv 3) (-10)) (by simp)
    have b2 := m (thrLe (Rv 3) 10) (by simp)
    have b3 := m (pgGe (Rv 2) (Rv 3) 21) (by simp)
    have b4 := m (pgLe (Rv 2) (Rv 3) 59) (by simp)
    have d1 := m (thrGe (Rv 5) (-10)) (by simp)
    have d2 := m (thrLe (Rv 5) 10) (by simp)
    have d3 := m (pgGe (Rv 4) (Rv 5) 21) (by simp)
    have d4 := m (pgLe (Rv 4) (Rv 5) 59) (by simp)
    simp only [thrGe, thrLe, pgGe, pgLe, Term.eval, AOp.interp] at a1 a2 a3 a4 b1 b2 b3 b4
    simp only [thrGe, thrLe, pgGe, pgLe, Term.eval, AOp.interp] at d1 d2 d3 d4
    obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hbox
    simp only [QBounds, LinkStart, Q2, hbR]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      linarith
  refine ⟨solΦ 30 (ΦL s), solΦ_zero _ _, ?_, ?_, ?_⟩
  · intro t _
    exact solΦ_deriv 30 (fR 0) fR_field (ΦL s) s t
  · intro t _ x hx
    refine solΦ_frozen _ _ _ x (fun hxR => hx ?_)
    obtain ⟨sx, j⟩ := x
    simp only at hxR
    subst hxR
    simp only [rightBlock, ODESystem.bound, List.map_map]
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  · intro t ht
    rw [sat_domR]
    exact solΦ_box 30 (by norm_num) (by norm_num) _ hQ t ht.1

/-! ## O2 for the instance: both families stay along every joint flow -/

theorem stayL (l q : ℕ) (hl : l < 2) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hmem : ∀ t' ∈ (cL l).map Prod.snd, Term.eval t' ν ≤ 0 := by
    intro t' ht'
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ht'
    exact (hiffL l hl a' ha' ν).mp (hν a' ha')
  have ha2 : a.2 ∈ (cL l).map Prod.snd := List.mem_map_of_mem ha
  have hbox : ∀ z, Formula.sat (Formula.and domL domR) z → Box Lv z :=
    fun z hz => (sat_domL z).mp hz.1
  interval_cases l
  · rw [cL_terms0] at hmem ha2
    exact stayL_terms (fL 0) (fR q) _ _ hbox pF pF pF pF_ok pF_ok pF_ok fL_field0 []
      (by simp) a.2 ha2 ν hmem
  · rw [cL_terms1] at hmem ha2
    exact stayL_terms (fL 1) (fR q) _ _ hbox pLost pF pF pLost_ok pF_ok pF_ok fL_field1
      lostExtra (by
        intro t ht
        simp only [lostExtra, List.mem_singleton] at ht
        exact ⟨5, ht, by simp only [pLost]; norm_num⟩) a.2 ha2 ν hmem

theorem stayR (l q : ℕ) (hq : q < 1) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR) := by
  obtain rfl : q = 0 := by omega
  intro a ha ν hν
  have hmem : ∀ t' ∈ (cR 0).map Prod.snd, Term.eval t' ν ≤ 0 := by
    intro t' ht'
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ht'
    exact (hiffR 0 hq a' ha' ν).mp (hν a' ha')
  have ha2 : a.2 ∈ (cR 0).map Prod.snd := List.mem_map_of_mem ha
  rw [cR_terms0] at hmem ha2
  exact stayR_terms (fL l) (fR 0) 1 zero_le_one (Formula.and domL domR) (fun z hz => (sat_domR z).mp hz.2)
    pR pR pR pR_ok pR_ok pR_ok fR_field a.2 ha2 ν hmem

/-! ## Side splits -/

theorem fL_pipe (l : ℕ) (i : Fin 6) : fL l i =
    (((some (mL l)).bind (Run.dynOf vs 6 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fR_pipe (q : ℕ) (i : Fin 6) : fR q i =
    (((some (mR q)).bind (Run.dynOf vs 6 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL_pipe : domL =
    (((some (mL 0)).bind (fun m => Run.lowerF vs 6 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domR_pipe : domR =
    (((some (mR 0)).bind (fun m => Run.lowerF vs 6 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL (l : ℕ) (hl : l < 2) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, platoon3_linkloss_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, platoon3_linkloss_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, platoon3_linkloss_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, platoon3_linkloss_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 2) : (hostGuard vs 6 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by interval_cases l <;>
      simp [mL, platoon3_linkloss_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem termsW_fv (W : Fin 6 → Var 6) (p1 p2 p3 : LinkC) (extra : List (Term (Var 6)))
    (hex : ∀ t ∈ extra, ∀ x ∈ t.fv, ∃ j, x = W j) :
    ∀ t ∈ termsW W p1 p2 p3 extra, ∀ x ∈ t.fv, ∃ j, x = W j := by
  intro t ht x hx
  simp only [termsW, guardT, linT, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with ((((((h | h | h | h) | (h | h | h | h)) | (h | h | h | h)) | (h | h | h | h)) |
    (h | h | h | h)) | (h | h | h | h)) | h
  all_goals first
    | exact hex t h x hx
    | (subst h
       simp only [linLe, linGe, linQ, thrLe, thrGe, pgGe, pgLe, Term.fv, Set.mem_union,
         Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false, false_or] at hx
       first | exact ⟨_, hx⟩ | (rcases hx with hx | hx <;> exact ⟨_, hx⟩))

theorem cL_terms (l : ℕ) (hl : l < 2) : ∃ p1 p2 p3 extra,
    (cL l).map Prod.snd = termsW Lv p1 p2 p3 extra ∧
      ∀ t ∈ extra, ∀ x ∈ t.fv, ∃ j, x = Lv j := by
  interval_cases l
  · exact ⟨_, _, _, _, cL_terms0, by simp⟩
  · refine ⟨_, _, _, _, cL_terms1, ?_⟩
    intro t ht x hx
    simp only [lostExtra, List.mem_singleton] at ht
    subst ht
    simp only [thrGe, Term.fv, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, false_or] at hx
    exact ⟨_, hx⟩

theorem anchor_fv (l q : ℕ) (hl : l < 2) (hq : q < 1) :
    ∀ c ∈ g l :: gs l ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  obtain rfl : q = 0 := by omega
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv_all l _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv_all l _ (List.mem_cons_of_mem _ hc)
  unfold atomTerms at hc
  obtain ⟨p1, p2, p3, ex, hLt, hex⟩ := cL_terms l hl
  rw [List.map_append, hLt, cR_terms0] at hc
  intro x hx
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨j, rfl⟩ := termsW_fv Lv _ _ _ ex hex c hc x hx
    exact Or.inl ⟨j, rfl⟩
  · obtain ⟨j, rfl⟩ := termsW_fv Rv _ _ _ [] (by simp) c hc x hx
    exact Or.inr ⟨j, rfl⟩

/-! ## The GUARDED right automaton (the file's modes, declared `next` lists, entered guards) -/

noncomputable def modeW (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- An edge tests the lowered guard of the mode it ENTERS (the paper's `?guard_m(x)`). -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := hostGuard vs 6 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (FOLLOW 0, BRAKE1 1, BRAKE2 2, BRAKE3 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (2, 2), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range platoon3_linkloss_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (platoon3_linkloss_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 4 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 6)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem Gr_guards : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = hostGuard vs 6 Side.R (mR e.tgt) := by
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

theorem hguardR_all (q : ℕ) : (hostGuard vs 6 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [platoon3_linkloss_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem hgR : GuardsRight Gr := by
  intro q e he
  rw [Gr_guards q e he]
  exact hguardR_all e.tgt

/-- The reference's `FOLLOW` guard (the operating range), from its parts. -/
theorem guardR0_of (x : State (Var 6))
    (h1 : 20 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60 ∧ -10 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 10 ∧
      21 ≤ x (Rv 0) + 2 * x (Rv 1) ∧ x (Rv 0) + 2 * x (Rv 1) ≤ 59)
    (h2 : 20 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 60 ∧ -10 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 10 ∧
      21 ≤ x (Rv 2) + 2 * x (Rv 3) ∧ x (Rv 2) + 2 * x (Rv 3) ≤ 59)
    (h3 : 20 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 60 ∧ -10 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 10 ∧
      21 ≤ x (Rv 4) + 2 * x (Rv 5) ∧ x (Rv 4) + 2 * x (Rv 5) ≤ 59) :
    Formula.sat (hostGuard vs 6 Side.R (mR 0)) x := by
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq19_0, hq59_0, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq25_0, hq21_0, hq60_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]
  simp only [Rv] at h1 h2 h3
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h3
  repeat' apply And.intro
  all_goals linarith

/-- The reference's `FOLLOW` guard gives the gap floor. -/
theorem guardR0_floor (x : State (Var 6)) (h : Formula.sat (hostGuard vs 6 Side.R (mR 0)) x) :
    20 ≤ x (Rv 0) ∧ 20 ≤ x (Rv 2) ∧ 20 ≤ x (Rv 4) := by
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq19_0, hq59_0, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq25_0, hq21_0, hq60_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv] at h
  simp only [Rv]
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.2⟩

/-! ## Regions: the right `FOLLOW` mode's kept cut atoms; the pruned sinks are excluded -/

noncomputable def region (q : ℕ) : Formula (Var 6) :=
  if q < 1 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 1) (ν : State (Var 6)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region_sink (q : ℕ) (hq : ¬ q < 1) (ν : State (Var 6)) :
    ¬ Formula.sat (region q) ν := by
  simp [region, hq, Formula.sat, CompOp.interp, Term.eval]

theorem atomsFreeR (q : ℕ) (hq : q < 1) :
    ∀ x ∈ cutAtomsOfX platoon3_linkloss_cutsV2X.R (mR q).name,
      Parse.PForm.namesFree "L_" x.atom = true := by
  obtain rfl : q = 0 := by omega
  intro x hx
  simp only [cutAtomsOfX, platoon3_linkloss_cutsV2X, mR, platoon3_linkloss_IRv2] at hx
  simp at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem region_fv (q : ℕ) (_hq : q < 4) : (region q).fv ⊆ range Rv := by
  by_cases h1 : q < 1
  · simp only [region, h1, if_true]
    intro x hx
    unfold cutF at hx
    have key : ∀ (L : List (CutAtomP 6)) (acc : Formula (Var 6)),
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
    obtain ⟨xa, hxa, rfl⟩ := List.mem_map.mp ha
    exact side_eq_R_mem (by
      simp only at hy
      unfold hostAtomF at hy
      exact hostForm_side (resolvesTo_R vs) _ (atomsFreeR q h1 xa hxa) y hy)
  · simp only [region, h1, if_false]
    simp [Formula.fv, Term.fv]

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `l` at its OWN declared row (`invRow = l`), right mode `q`, at the
cover's λ = 1 and the window's strata order (`[0, …, 11]` for FOLLOW, `[0, …, 13]` for LOST). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX platoon3_linkloss_IRv2 platoon3_linkloss_cutsV2X 6 l (order l) 1 l q

theorem verd_core (l q : ℕ) (hl : l < 2) (hq : q < 4) (h : Verd l q) :
    VerdXCore (g l :: gs l) (fL l) (fR q) 1
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  interval_cases l
  · exact h'
  · exact h'

/-! ## The coupling, the window response -/

theorem couple (l q : ℕ) (hl : l < 2) (hq : q < 1) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 6))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) := by
  obtain rfl : q = 0 := by omega
  exact couple_cutX (g l) (gs l) (g l :: gs l) (cL l) (cR 0) (fL l) (fR 0) 1 one_pos domL domR
    1 dt (hfL l hl) (hfR 0 (by norm_num)) hdomL hdomR (anchor_fv l 0 hl hq) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR 0 hq) (stayL l 0 hl) (stayR l 0 hq)
    (verd_core l 0 hl (by norm_num) hv) (es l dt)

theorem sat_faModal_monoPost {P Q : Program (Var 6)} {A B : Formula (Var 6)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 6)}
    (h : Formula.sat (faModal (Equiv.refl (Var 6)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l qs : ℕ) (hl : l < 2) (hqs : qs < 1) (dt : ℝ) (hv : Verd l qs)
    {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq (([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
        ++ [Program.ode (rightBlock (fR qs) (Term.const 1)) domR]))
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
  have hfa := Hmulti_windowRF_prefixed (fL l) domL
    (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 6)))
    (by intro h hh; simp at hh)
    (fun σ' hσ' => hσ'.2.1)
    (by intro h hh; simp at hh)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fR qs) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR qs, Term.const 1, domR⟩ : RepoHop 6)
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

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 6)) (ψ : Formula (Var 6))
    {σ : State (Var 6)}
    (hbody : Formula.sat (hostGuard vs 6 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 6))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
      (gwindowSeg (hostGuard vs 6 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

/-- `FOLLOW`'s window, the GUARDED response: stay in `FOLLOW` on the certified joint segment,
then take the self-loop, legal at the end state: the kept cuts give the rated closing rate
and the projected gap, the envelope gives `g_i ≤ 60`, and the gap floor `g_i ≥ 20` holds
along the reference's own run (`gap_floor_Ronly`: the projected-gap conjunct makes the flow
repel at the AEB floor). -/
theorem stayCaseG (l : ℕ) (hl : l < 2) (dt : ℝ) (hv : Verd l 0)
    {σ : State (Var 6)} (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hgd : Formula.sat (hostGuard vs 6 Side.R (mR 0)) σ) (hreg : Formula.sat (region 0) σ) :
    GResp Gr 0 (gwindowSeg (hostGuard vs 6 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM (g l) (gs l)) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hanchor : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR 0)))
      (Formula.and domL domR)) σ := by
    refine ⟨(sat_FM_append (g l) (gs l) _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    exact (atomTerms_iff (hiffL l hl) (hiffR 0 (by norm_num)) σ).mpr
      ⟨hO1L l hl σ hguard, (sat_region_lt 0 (by norm_num) σ).mp hreg⟩
  have hresp := respond l 0 hl (by norm_num) dt hv hanchor
  simp only [List.map_nil, List.nil_append] at hresp
  refine gresp_final_run (ms := modeW 0) (Gr_modeAt 0 (by norm_num)) hresp ?_
  intro ν hν μ hflow hpost
  -- the window leaves the right untouched
  have hRν : ∀ i, ν (Rv i) = σ (Rv i) := by
    intro i
    have hP := vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL
    refine (Program.bound_effect _ hν (Rv i) ?_).symm
    intro hb
    rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
    · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
  -- the right's kept atoms at the start (σ) and at the end (μ)
  have hRσ : ∀ t ∈ termsW Rv pR pR pR [], Term.eval t σ ≤ 0 := by
    have h := (sat_region_lt 0 (by norm_num) σ).mp hreg
    intro t ht
    rw [← cR_terms0] at ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact (hiffR 0 (by norm_num) a ha σ).mp (h a ha)
  have hRμ : ∀ t ∈ termsW Rv pR pR pR [], Term.eval t μ ≤ 0 := by
    have h := (sat_region_lt 0 (by norm_num) μ).mp hpost.2
    intro t ht
    rw [← cR_terms0] at ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact (hiffR 0 (by norm_num) a ha μ).mp (h a ha)
  have hfl := guardR0_floor σ hgd
  obtain ⟨F1, F2, F3⟩ := linkFields fR_field
  have hflow' : Program.sem (Program.ode (rightBlock (fR 0) (Term.const 1)) domR) ν μ := hflow
  have tr : ∀ t ∈ termsW Rv pR pR pR [], Term.eval t ν ≤ 0 := by
    intro t ht
    have hfv := termsW_fv Rv pR pR pR [] (by simp) t ht
    rw [Term.coincidence t (ν := ν) (w := σ) (fun x hx => by
      obtain ⟨j, rfl⟩ := hfv x hx
      exact hRν j)]
    exact hRσ t ht
  have floor : ∀ (jx jy : Fin 6), LinkField Rv (fR 0) jx jy 30 →
      pgGe (Rv jx) (Rv jy) 21 ∈ termsW Rv pR pR pR [] → 20 ≤ σ (Rv jx) → 20 ≤ μ (Rv jx) :=
    fun jx jy hF hmem h0 => gap_floor_Ronly (fR 0) domR jx jy 30 20 21 (by norm_num)
      (by norm_num) hF hflow' (tr _ hmem) (by rw [hRν]; exact h0)
  have g1 := floor 0 1 F1 (by simp [termsW, guardT, pR]) hfl.1
  have g2 := floor 2 3 F2 (by simp [termsW, guardT, pR]) hfl.2.1
  have g3 := floor 4 5 F3 (by simp [termsW, guardT, pR]) hfl.2.2
  have hboxμ : Box Rv μ := (sat_domR μ).mp hpost.1.2.2
  have m := hRμ
  simp only [termsW, guardT, linT, pR, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at m
  have a3 := m (pgGe (Rv 0) (Rv 1) 21) (by simp)
  have a4 := m (pgLe (Rv 0) (Rv 1) 59) (by simp)
  have b3 := m (pgGe (Rv 2) (Rv 3) 21) (by simp)
  have b4 := m (pgLe (Rv 2) (Rv 3) 59) (by simp)
  have d3 := m (pgGe (Rv 4) (Rv 5) 21) (by simp)
  have d4 := m (pgLe (Rv 4) (Rv 5) 59) (by simp)
  simp only [pgGe, pgLe, Term.eval, AOp.interp] at a3 a4 b3 b4 d3 d4
  obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hboxμ
  refine ⟨edgeW 0 0, edge_mem 0 0 (by simp [edgeList]), ?_, hpost⟩
  show Formula.sat (hostGuard vs 6 Side.R (mR 0)) μ
  exact guardR0_of μ ⟨g1, x1, y0, y1, by linarith, by linarith⟩
    ⟨g2, x3, y2, y3, by linarith, by linarith⟩ ⟨g3, x5, y4, y5, by linarith, by linarith⟩

/-- Left mode `l`'s window, every admissible right start (in its guard and cuts): FOLLOW
stays and takes its legal self-loop; the BRAKE sinks are excluded by their (false) regions. -/
theorem HmultiG (l : ℕ) (hl : l < 2) (dt : ℝ) (h0 : Verd l 0) :
    ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM (g l) (gs l)) env) σ →
      Formula.sat (hostGuard vs 6 Side.R (mR q)) σ → Formula.sat (region q) σ →
      GResp Gr q (gwindowSeg (hostGuard vs 6 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (fun qf => Formula.and (Formula.and (FM (g l) (gs l)) env) (region qf)) σ := by
  intro q hq σ _ hσ hg hreg
  rw [Gr_len] at hq
  match q, hq, hg, hreg with
  | 0, _, hg, hreg => exact stayCaseG l hl dt h0 hσ hg hreg
  | 1, _, _, hreg => exact absurd hreg (not_sat_region_sink 1 (by norm_num) σ)
  | 2, _, _, hreg => exact absurd hreg (not_sat_region_sink 2 (by norm_num) σ)
  | 3, _, _, hreg => exact absurd hreg (not_sat_region_sink 3 (by norm_num) σ)

/-! ## The declared rows, per left mode -/

noncomputable def FRow (l : ℕ) : Formula (Var 6) := FM (g l) (gs l)
noncomputable def ϕRow (l : ℕ) : RFormula (Var 6) := canonInvM (g l) (gs l)

theorem encode_ϕRow (l : ℕ) : encode (Equiv.refl (Var 6)) (ϕRow l) = FRow l :=
  encode_canonInvM _ _

theorem aux_notin_FRow (a : Fin 6) (l : ℕ) : ((Side.Aux, a) : Var 6) ∉ (FRow l).fv :=
  notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv_all l g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-- **The handoff FOLLOW → LOST, in-kernel.** The FOLLOW row pins every link to the exact
refinement (`Δr_i + ρ_j (Δg_i + 1) = 0`, so `e₁ = Δg₁ + 1 = 0`, `Δr₁ = 0`); there the LOST
row's link-1 forms take the values `−6 ρ_j` (inside `[−6 ρ_j, 0]`) and `e₁ = 0 ∈ [0, 6]`;
links 2, 3 are common. -/
theorem handoff01 (ω : State (Var 6)) (h : Formula.sat (FRow 0) ω) :
    Formula.sat (FRow 1) ω := by
  have e1 : ("L_g1".drop 2).copy = "g1" := by decide
  have e2 : ("R_g1".drop 2).copy = "g1" := by decide
  have e3 : ("L_r1".drop 2).copy = "r1" := by decide
  have e4 : ("R_r1".drop 2).copy = "r1" := by decide
  have e5 : ("L_g2".drop 2).copy = "g2" := by decide
  have e6 : ("R_g2".drop 2).copy = "g2" := by decide
  have e7 : ("L_r2".drop 2).copy = "r2" := by decide
  have e8 : ("R_r2".drop 2).copy = "r2" := by decide
  have e9 : ("L_g3".drop 2).copy = "g3" := by decide
  have e10 : ("R_g3".drop 2).copy = "g3" := by decide
  have e11 : ("L_r3".drop 2).copy = "r3" := by decide
  have e12 : ("R_r3".drop 2).copy = "r3" := by decide
  rw [FRow, sat_FM_iff] at h ⊢
  simp [g, gs, comps, hostComps, platoon3_linkloss_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    List.findIdx?_cons, hq0_0, hq1_0, hq0_25, hq0_5, hq5_0, hq1_5, hq3_0, hq6_0, c0,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The left automaton, from the file -/

def nextL : List (List ℕ) :=
  (List.range 2).map (fun l =>
    (mL l).next.filterMap (Handoff.leftModeIndex platoon3_linkloss_IRv2))

/-- `FOLLOW → [FOLLOW, LOST]`, `LOST → [LOST]`. -/
theorem nextL_eq : nextL = [[0, 1], [1]] := by decide

theorem nextL_transitions :
    ((List.range 2).flatMap (fun m' => (nextL.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions platoon3_linkloss_IRv2 := by decide

noncomputable def guardsL : List (Formula (Var 6)) :=
  (List.range 2).map (fun l => hostGuard vs 6 Side.L (mL l))

/-- The left automaton: mode `l`'s window re-tests `l`'s guard and flows `l`'s field
(clock-capped at `dt`, one piece). -/
noncomputable def A (dt : ℝ) : LeftAut 6 :=
  { windows := (List.range 2).map (fun l =>
      gwindowSeg (hostGuard vs 6 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1),
    guards := guardsL,
    next := nextL }

theorem A_numModes (dt : ℝ) : (A dt).numModes = 2 := rfl

theorem A_window (dt : ℝ) (t : ℕ) (ht : t < 2) :
    (A dt).window t = gwindowSeg (hostGuard vs 6 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1 := by
  interval_cases t <;> rfl

theorem A_guard (dt : ℝ) (t : ℕ) (ht : t < 2) :
    (A dt).guard t = hostGuard vs 6 Side.L (mL t) := by
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
    Program.vars ((A dt).window t) ⊆ {((Side.Aux, 1) : Var 6)} ∪ range Lv := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  exact vars_gwindowSegL_sub _ (fL t) domL 1 dt 1 (hguardL t ht) (hfL t ht) hdomL

/-! ## Freshness of `u_L` and `mv`; the mode-consistent region -/

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
  · simp only [region, show ¬ q < 1 from by omega, if_false] at h
    simp [Formula.fv, Term.fv] at h

/-- **The mode-consistent region** of right mode `q`: its lowered guard (the operating range
for `FOLLOW`) and its kept cut atoms. -/
noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vs 6 Side.R (mR q)) region q

theorem gregion_fv (q : ℕ) (hq : q < 4) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

theorem hmvregG : ∀ q, mv ∉ (gregion q).fv := fun q =>
  notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) (hmvreg q)

theorem hulBkG : uL ∉ (mvRegion mv gregion Gr.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv gregion Gr.modes.length (fun q hq => gregion_fv q hq) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

/-- The left windows leave the right guards' truth values unchanged. -/
theorem frameG (dt : ℝ) (t : ℕ) (ht : t < 2) (q : ℕ) {σ ν : State (Var 6)}
    (h : Program.sem ((A dt).window t) σ ν) :
    Formula.sat (hostGuard vs 6 Side.R (mR q)) σ → Formula.sat (hostGuard vs 6 Side.R (mR q)) ν :=
  frames_right (hwin dt t (by rw [A_numModes]; exact ht)) (hguardR_all q) h

theorem hulG (dt : ℝ) : ∀ t, uL ∉ ((A dt).guard t).fv := by
  intro t h
  by_cases ht : t < 2
  · exact aux_notin_range_Lv 2 (hgrd dt t ht h)
  · have : (A dt).guard t = Formula.tt := by
      unfold LeftAut.guard A guardsL
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem framesGw (t : ℕ) (dt : ℝ) (a : Fin 6) (ha : a ≠ 1) :
    FramesMv (gwindowSeg (hostGuard vs 6 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1)
      ((Side.Aux, a) : Var 6) := by
  refine framesMv_gwindow _ (fL t) domL tg dt 1 _ (by simpa [Prod.ext_iff] using ha) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
  exact aux_ne_Lv a i hi

theorem hframesUl (dt : ℝ) : ∀ t, FramesMv ((A dt).window t) uL := by
  intro t
  by_cases ht : t < 2
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

/-! ## The handoffs, in-kernel -/

/-- FOLLOW → FOLLOW and LOST → LOST: the same row. FOLLOW → LOST: `handoff01`. -/
theorem handoff (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat env ω → Formula.sat ((A dt).guard t) ω →
      Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [A_numModes] at hm'
  rw [A_succ, nextL_eq] at ht
  interval_cases m' <;> simp at ht
  · rcases ht with rfl | rfl
    · exact hF
    · exact handoff01 ω hF
  · subst ht
    exact hF


/-! ## The per-mode steps -/

theorem hstepM (dt : ℝ) (h00 : Verd 0 0) (h10 : Verd 1 0) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv gregion Gr.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 6)) ((A dt).window t)
      (Program.star (rightAutomatonBody Gr mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv gregion Gr.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  have hv0 : Verd t 0 := by interval_cases t <;> assumption
  have hframe := frameG dt t ht
  rw [A_window dt t ht] at hframe ⊢
  exact hstepMode_GR Gr mv (FRow t) env gregion _ (aux_notin_FRow 0 t) hmvenv hmvregG
    hfresh (guardsFresh_of_right Gr 0 hgR) hlt (framesGw t dt 0 (by decide))
    (HMode_regionG Gr mv _ region Gr_guards (FRow t) env _
      (fun q _ σ ν hrun => hframe q hrun)
      (fun q hq σ hmv hσ hg hreg => HmultiG t ht dt hv0 q hq σ hmv hσ hg hreg))

/-! ## Theorem 3, mode-keyed, over the guarded right automaton -/

/-- **`platoon3_linkloss` (suite_v2), Theorem 3 at the declared mode-dependent invariant, over
the GUARDED automata, at the mode-consistent region.** Left: the automaton of the file
(`FOLLOW → [FOLLOW, LOST]`, `LOST → [LOST]`), each step `?guard_t ; u_L := t ; ?guard_t ;
window_t` (`u_L = (Aux, 2)`); the left guards are the deployed's operating range (links
`19 ≤ g_i ≤ 59`, `|r_i| ≤ 10`, `20 ≤ g_i + 2 r_i ≤ 58`; LOST link 1 `g₁ ≥ 25`). Right: the
four-mode automaton of the file with every edge testing the lowered guard of the mode it
enters (`Gr_guards`): `FOLLOW` (the reference's operating range `20 ≤ g_i ≤ 60`,
`|r_i| ≤ 10`, `21 ≤ g_i + 2 r_i ≤ 59`) and the AEB sinks `BRAKE1..3` (`g_k < 20`; the three
`FOLLOW → BRAKE` edges pruned: the sinks have the empty region). Loop invariant: the
declared rows keyed by `u_L`, the evolve envelope on both sides, and the right in the guard
and the kept cuts of its current mode (`gregion`). Response: in every left window, the
certified joint segment in `FOLLOW` at the cover's λ = 1, then the self-loop, legal at its
end state (the kept cuts and the gap floor `g_i ≥ 20` along the reference's own run,
`gap_floor_Ronly`). Handoff FOLLOW → LOST in-kernel. Existence Z3-free (`link_bounds`).
Residuals: two stratified verdict packs `Verd l 0`. -/
theorem platoon3_linkloss_modeKeyed (dt : ℝ) (h00 : Verd 0 0) (h10 : Verd 1 0) :
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
      (hframesUl dt) hulR (hnext dt) (hstepM dt h00 h10) (handoff dt)
  · exact hddF_modeKeyed_G (A dt) Gr 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv gregion Gr.modes.length) (hwin dt) (hgrd dt) (hnext dt) hgR hRv
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv gregion Gr.modes.length (fun q hq => gregion_fv q hq) hv)

end V2Platoon3Linkloss
end RelCertifier
