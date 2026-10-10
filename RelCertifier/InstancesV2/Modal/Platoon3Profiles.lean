/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_profiles` (suite_v2) — Theorem 3 over the GUARDED automata

Three-follower CACC string (`n = 6`), linear damped links on both sides (roots
`ρ = 1/4, 1/2`); the reference selects a gap profile (`NORMAL`/`CLOSE`/`FAR`, set points
30/28/32) under the same guard, the OPERATING RANGE (`docs/SUITE-REDESIGN.md` §20: the
engagement bands of the earlier model made the nominal controller block after a full cycle,
violating Assumption 1). Theorem 3 at the declared 18-component row over the guarded right
automaton (every edge tests the entered mode's lowered guard) at the mode-consistent region
(guard ∧ kept cuts): first with the left program the guard-gated `FOLLOW` window
(`platoon3_profiles_modal`), then with the paper's left automaton
(`platoon3_profiles_leftAut`, the generic bridge). Response: the certified joint segment
in the start profile, then its self-loop, legal at the end state (the kept cuts, the
envelope, and the gap floor along the reference's own run, `gap_floor_Ronly`). Existence
Z3-free (`link_bounds`).
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.platoon3_profiles
import RelCertifier.InstancesV2.Modal.Platoon3Link
import RelCertifier.Proofs.Encoding.LeftAutUniform

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Platoon3Profiles

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle Platoon3Link

def vs : List String := ["g1", "r1", "g2", "r2", "g3", "r3"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := platoon3_profiles_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := platoon3_profiles_IRv2.R.modes.getD q dm

abbrev mv : Var 6 := (Side.Aux, 0)
abbrev tg : Var 6 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.R (mR q)
noncomputable def domL : Formula (Var 6) := hostEvolve vs 6 Side.L (mL 0)
noncomputable def domR : Formula (Var 6) := hostEvolve vs 6 Side.R (mR 0)
noncomputable def env : Formula (Var 6) := Formula.and domL domR

theorem hpm0125 : Run.parseRat "-0.125" = some (-(1:ℚ)/8) := by
  have h : parseQ "-0.125" = some (⟨-125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp290 : Run.parseRat "29.0" = some (29 : ℚ) := by
  have h : parseQ "29.0" = some (⟨290, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp280 : Run.parseRat "28.0" = some (28 : ℚ) := by
  have h : parseQ "28.0" = some (⟨280, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp320 : Run.parseRat "32.0" = some (32 : ℚ) := by
  have h : parseQ "32.0" = some (⟨320, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp600 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm100 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

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
theorem hq28 : Run.parseRat "28" = some (28 : ℚ) := by
  have h : parseQ "28" = some (⟨28, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq32 : Run.parseRat "32" = some (32 : ℚ) := by
  have h : parseQ "32" = some (⟨32, 1⟩ : QF) := by decide
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
theorem hq37 : Run.parseRat "37" = some (37 : ℚ) := by
  have h : parseQ "37" = some (⟨37, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq21 : Run.parseRat "21" = some (21 : ℚ) := by
  have h : parseQ "21" = some (⟨21, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq35 : Run.parseRat "35" = some (35 : ℚ) := by
  have h : parseQ "35" = some (⟨35, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq23 : Run.parseRat "23" = some (23 : ℚ) := by
  have h : parseQ "23" = some (⟨23, 1⟩ : QF) := by decide
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
theorem hq34 : Run.parseRat "34" = some (34 : ℚ) := by
  have h : parseQ "34" = some (⟨34, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq20 : Run.parseRat "20" = some (20 : ℚ) := by
  have h : parseQ "20" = some (⟨20, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq40 : Run.parseRat "40" = some (40 : ℚ) := by
  have h : parseQ "40" = some (⟨40, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq26 : Run.parseRat "26" = some (26 : ℚ) := by
  have h : parseQ "26" = some (⟨26, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num

theorem hpm10 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hn17_5 : Run.parseRat "17.5" = some ((35:ℚ)/2) := by
  have h : parseQ "17.5" = some (⟨175, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hnm12_5 : Run.parseRat "-12.5" = some ((-25:ℚ)/2) := by
  have h : parseQ "-12.5" = some (⟨-125, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn25 : Run.parseRat "25" = some (25 : ℚ) := by
  have h : parseQ "25" = some (⟨25, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hnm15 : Run.parseRat "-15" = some (-15 : ℚ) := by
  have h : parseQ "-15" = some (⟨-15, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hnm12 : Run.parseRat "-12" = some (-12 : ℚ) := by
  have h : parseQ "-12" = some (⟨-12, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hnm14 : Run.parseRat "-14" = some (-14 : ℚ) := by
  have h : parseQ "-14" = some (⟨-14, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn18 : Run.parseRat "18" = some (18 : ℚ) := by
  have h : parseQ "18" = some (⟨18, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn26 : Run.parseRat "26" = some (26 : ℚ) := by
  have h : parseQ "26" = some (⟨26, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn17 : Run.parseRat "17" = some (17 : ℚ) := by
  have h : parseQ "17" = some (⟨17, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hnm13 : Run.parseRat "-13" = some (-13 : ℚ) := by
  have h : parseQ "-13" = some (⟨-13, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn24 : Run.parseRat "24" = some (24 : ℚ) := by
  have h : parseQ "24" = some (⟨24, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hnm16 : Run.parseRat "-16" = some (-16 : ℚ) := by
  have h : parseQ "-16" = some (⟨-16, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn2_0 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn20_0 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn58_0 : Run.parseRat "58.0" = some (58 : ℚ) := by
  have h : parseQ "58.0" = some (⟨580, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn21_0 : Run.parseRat "21.0" = some (21 : ℚ) := by
  have h : parseQ "21.0" = some (⟨210, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hn59_0 : Run.parseRat "59.0" = some (59 : ℚ) := by
  have h : parseQ "59.0" = some (⟨590, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num


/-! ## Evaluations of the lowered data -/

/-- The damped-pair field on side `W` with set point `c` (the three links). -/
def PairField (W : Fin 6 → Var 6) (f : Fin 6 → Term (Var 6)) (c : ℝ) : Prop :=
  ∀ z : State (Var 6),
    Term.eval (f 0) z = z (W 1) ∧
    Term.eval (f 1) z = -(1/8) * (z (W 0) - c) - 3/4 * z (W 1) ∧
    Term.eval (f 2) z = z (W 3) ∧
    Term.eval (f 3) z = -(1/8) * (z (W 2) - c) - 3/4 * z (W 3) ∧
    Term.eval (f 4) z = z (W 5) ∧
    Term.eval (f 5) z = -(1/8) * (z (W 4) - c) - 3/4 * z (W 5)

theorem fL_field : PairField Lv (fL 0) 29 := by
  intro z
  simp [fL, hostDyn, mL, platoon3_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm0125, hp075,
    hp290, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]
  refine ⟨by ring, by ring, by ring⟩

noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 30 else if q = 1 then 28 else 32

theorem fR_field (q : ℕ) (hq : q < 3) : PairField Rv (fR q) (cRc q) := by
  intro z
  interval_cases q <;>
  · simp [fR, hostDyn, mR, platoon3_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm0125, hp075,
      hp300, hp280, hp320, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, cRc]
    refine ⟨by ring, by ring, by ring⟩

/-- The evolve box (both sides): `g_i ∈ [0, 60]`, `r_i ∈ [−10, 10]`. -/
def Box (W : Fin 6 → Var 6) (x : State (Var 6)) : Prop :=
  (0 ≤ x (W 0) ∧ x (W 0) ≤ 60 ∧ -10 ≤ x (W 1) ∧ x (W 1) ≤ 10) ∧
  (0 ≤ x (W 2) ∧ x (W 2) ≤ 60 ∧ -10 ≤ x (W 3) ∧ x (W 3) ≤ 10) ∧
  (0 ≤ x (W 4) ∧ x (W 4) ≤ 60 ∧ -10 ≤ x (W 5) ∧ x (W 5) ≤ 10)

theorem sat_domL (x : State (Var 6)) : Formula.sat domL x ↔ Box Lv x := by
  simp only [domL, hostEvolve, mL, platoon3_profiles_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, hpm100, hp100, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv, Box, and_assoc]

theorem sat_domR (x : State (Var 6)) : Formula.sat domR x ↔ Box Rv x := by
  simp only [domR, hostEvolve, mR, platoon3_profiles_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, hpm100, hp100, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, Box, and_assoc]

theorem domL_univ (l : ℕ) (hl : l < 1) : hostEvolve vs 6 Side.L (mL l) = domL := by
  obtain rfl : l = 0 := by omega
  rfl
theorem domR_univ (q : ℕ) (hq : q < 6) : hostEvolve vs 6 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-! ## The cut families, concretely -/

noncomputable def cL (l : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.L (cutAtomsOfX platoon3_profiles_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.R (cutAtomsOfX platoon3_profiles_cutsV2X.R (mR q).name)

/-- Left `FOLLOW` links (set point 29, projected gap `[20, 58]`); the reference's profiles
(`NORMAL` 30, `CLOSE` 28, `FAR` 32; projected gap `[21, 59]`). The linear-form boxes are the
tool's, read off the operating-range guard box. -/
noncomputable def pF : LinkC := ⟨29, 35/2, -12, 25, -14, 20, 58⟩
noncomputable def pN : LinkC := ⟨30, 35/2, -25/2, 25, -15, 21, 59⟩
noncomputable def pC : LinkC := ⟨28, 18, -12, 26, -14, 21, 59⟩
noncomputable def pFar : LinkC := ⟨32, 17, -13, 24, -16, 21, 59⟩

noncomputable def pR (q : ℕ) : LinkC := if q = 0 then pN else if q = 1 then pC else pFar

theorem pF_ok : LinkOK pF := by simp only [LinkOK, pF]; norm_num
theorem pR_ok (q : ℕ) : LinkOK (pR q) := by
  unfold pR; split_ifs <;> simp only [LinkOK, pN, pC, pFar] <;> norm_num

theorem pR_c (q : ℕ) : (pR q).c = cRc q := by unfold pR cRc; split_ifs <;> rfl

/-- The left derived floors `g_i ≥ 1` (one per link, from its `ρ = 1/2` lower form). -/
noncomputable def leftExtra : List (Term (Var 6)) := [thrGe (Lv 0) 1, thrGe (Lv 2) 1, thrGe (Lv 4) 1]

theorem cL_terms : (cL 0).map Prod.snd = termsW Lv pF pF pF leftExtra := by
  simp [cL, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons, hq0_25, hq0_5, hq29, hq30, hq28, hq32, hn17_5, hnm12_5, hn25, hnm15, hnm12, hnm14, hn18, hn26, hn17, hnm13, hn24, hnm16, hn1, hpm100, hp100, hn2_0, hn20_0, hn58_0, hn21_0, hn59_0,
    ITerm.toHost, termsW, guardT, linT, pgGe, pgLe, linLe, linGe, linQ, thrLe, thrGe, Lv, pF,
    leftExtra]

theorem cR_terms0 : (cR 0).map Prod.snd = termsW Rv pN pN pN [] := by
  simp [cR, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons, hq0_25, hq0_5, hq29, hq30, hq28, hq32, hn17_5, hnm12_5, hn25, hnm15, hnm12, hnm14, hn18, hn26, hn17, hnm13, hn24, hnm16, hn1, hpm100, hp100, hn2_0, hn20_0, hn58_0, hn21_0, hn59_0,
    ITerm.toHost, termsW, guardT, linT, pgGe, pgLe, linLe, linGe, linQ, thrLe, thrGe, Rv, pN]
theorem cR_terms1 : (cR 1).map Prod.snd = termsW Rv pC pC pC [] := by
  simp [cR, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons, hq0_25, hq0_5, hq29, hq30, hq28, hq32, hn17_5, hnm12_5, hn25, hnm15, hnm12, hnm14, hn18, hn26, hn17, hnm13, hn24, hnm16, hn1, hpm100, hp100, hn2_0, hn20_0, hn58_0, hn21_0, hn59_0,
    ITerm.toHost, termsW, guardT, linT, pgGe, pgLe, linLe, linGe, linQ, thrLe, thrGe, Rv, pC]
theorem cR_terms2 : (cR 2).map Prod.snd = termsW Rv pFar pFar pFar [] := by
  simp [cR, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons, hq0_25, hq0_5, hq29, hq30, hq28, hq32, hn17_5, hnm12_5, hn25, hnm15, hnm12, hnm14, hn18, hn26, hn17, hnm13, hn24, hnm16, hn1, hpm100, hp100, hn2_0, hn20_0, hn58_0, hn21_0, hn59_0,
    ITerm.toHost, termsW, guardT, linT, pgGe, pgLe, linLe, linGe, linQ, thrLe, thrGe, Rv, pFar]

theorem cR_terms (q : ℕ) (hq : q < 3) :
    (cR q).map Prod.snd = termsW Rv (pR q) (pR q) (pR q) [] := by
  interval_cases q
  · rw [cR_terms0]; rfl
  · rw [cR_terms1]; rfl
  · rw [cR_terms2]; rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 1) :
    ∀ x ∈ cutAtomsOfX platoon3_profiles_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  obtain rfl : l = 0 := by omega
  intro x hx
  simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2] at hx
  simp at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX platoon3_profiles_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 1) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 1) :
    ∀ ν, Formula.sat (hostGuard vs 6 Side.L (mL l)) ν → CutSat (cL l) ν := by
  obtain rfl : l = 0 := by omega
  intro ν hν
  refine cutSatL_of_guard platoon3_profiles_cutsV2X_wf (mL 0) ?_ ?_ ?_ ?_ ν hν
  · rfl
  · intro x hx
    simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x hx
    simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Run.lowerF, Run.lowerE, hq0_25, hq0_5, hq29, hq30, hq28, hq32, hn17_5, hnm12_5, hn25, hnm15, hnm12, hnm14, hn18, hn26, hn17, hnm13, hn24, hnm16, hn1, hpm100, hp100, hn2_0, hn20_0, hn58_0, hn21_0, hn59_0, vs, Run.resolveVar, List.findIdx?_cons]
  · simp [mL, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hn21_0, hn59_0, hpm100, hp100, hn2_0, hn20_0, hn58_0, hp600, vs,
      Run.resolveVar, List.findIdx?_cons]

/-! ## O2: the kept atoms stay along the joint flows (`Platoon3Link` shape lemmas) -/

theorem linkFields {W : Fin 6 → Var 6} {f : Fin 6 → Term (Var 6)} {c : ℝ}
    (h : PairField W f c) :
    LinkField W f 0 1 c ∧ LinkField W f 2 3 c ∧ LinkField W f 4 5 c :=
  ⟨⟨fun z => (h z).1, fun z => (h z).2.1⟩, ⟨fun z => (h z).2.2.1, fun z => (h z).2.2.2.1⟩,
    ⟨fun z => (h z).2.2.2.2.1, fun z => (h z).2.2.2.2.2⟩⟩

theorem stayR_terms (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv)
    (dom : Formula (Var 6)) (hbox : ∀ z, Formula.sat dom z → Box Rv z)
    (p : LinkC) (ok : LinkOK p) (hF : PairField Rv fR p.c) :
    ∀ t ∈ termsW Rv p p p [], ∀ ν, (∀ t' ∈ termsW Rv p p p [], Term.eval t' ν ≤ 0) →
      BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
        (fun ω => Term.eval t ω) ν := by
  obtain ⟨F1, F2, F3⟩ := linkFields hF
  intro t ht ν hall
  have own := hall t ht
  simp only [termsW, List.append_nil, List.mem_append] at ht
  rcases ht with (((((ht | ht) | ht) | ht) | ht) | ht)
  · exact stayR_link fL fR lamv hlam dom 0 1 p ok F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 2 3 p ok F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 4 5 p ok F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 0 1 p ok F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 2 3 p ok F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayR_link fL fR lamv hlam dom 4 5 p ok F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_right _ ht) ν own

theorem stayL_terms (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6))
    (dom : Formula (Var 6)) (hbox : ∀ z, Formula.sat dom z → Box Lv z)
    (hF : PairField Lv fL 29) :
    ∀ t ∈ termsW Lv pF pF pF leftExtra, ∀ ν,
      (∀ t' ∈ termsW Lv pF pF pF leftExtra, Term.eval t' ν ≤ 0) →
      BoxLe (Program.ode (jointSys fL fR lam) dom)
        (fun ω => Term.eval t ω) ν := by
  obtain ⟨F1, F2, F3⟩ := linkFields hF
  intro t ht ν hall
  have own := hall t ht
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  simp only [termsW, List.mem_append] at ht
  rcases ht with ((((((ht | ht) | ht) | ht) | ht) | ht) | ht)
  · exact stayL_link fL fR lam dom 0 1 pF pF_ok F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayL_link fL fR lam dom 2 3 pF pF_ok F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayL_link fL fR lam dom 4 5 pF pF_ok F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_left _ ht) ν own
  · exact stayL_link fL fR lam dom 0 1 pF pF_ok F1
      (fun z hz => ⟨(hbox z hz).1.1, (hbox z hz).1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayL_link fL fR lam dom 2 3 pF pF_ok F2
      (fun z hz => ⟨(hbox z hz).2.1.1, (hbox z hz).2.1.2.1⟩) t (List.mem_append_right _ ht) ν own
  · exact stayL_link fL fR lam dom 4 5 pF pF_ok F3
      (fun z hz => ⟨(hbox z hz).2.2.1, (hbox z hz).2.2.2.1⟩) t (List.mem_append_right _ ht) ν own
  · simp only [leftExtra, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact stayL_derGe fL fR lam dom 0 1 (1/2) 29 (-14) 1 hroot2 hs2 (by norm_num) (by norm_num)
        (by norm_num) F1 ν (hall _ (by simp [termsW, linT, pF])) own
    · exact stayL_derGe fL fR lam dom 2 3 (1/2) 29 (-14) 1 hroot2 hs2 (by norm_num) (by norm_num)
        (by norm_num) F2 ν (hall _ (by simp [termsW, linT, pF])) own
    · exact stayL_derGe fL fR lam dom 4 5 (1/2) 29 (-14) 1 hroot2 hs2 (by norm_num) (by norm_num)
        (by norm_num) F3 ν (hall _ (by simp [termsW, linT, pF])) own

/-! ## The declared invariant's components -/

noncomputable def comps : List (Term (Var 6)) :=
  hostComps vs 6 (platoon3_profiles_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def c0 : Term (Var 6) := Term.const 0
noncomputable def g : Term (Var 6) := comps.getD 0 c0
/-- Components 1–17 of the row (the cover's strata order is the identity `[0, …, 17]`). -/
noncomputable def gs : List (Term (Var 6)) :=
  [comps.getD 1 c0, comps.getD 2 c0, comps.getD 3 c0, comps.getD 4 c0, comps.getD 5 c0,
   comps.getD 6 c0, comps.getD 7 c0, comps.getD 8 c0, comps.getD 9 c0, comps.getD 10 c0,
   comps.getD 11 c0, comps.getD 12 c0, comps.getD 13 c0, comps.getD 14 c0, comps.getD 15 c0,
   comps.getD 16 c0, comps.getD 17 c0]

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

theorem comps_mem_fv : ∀ c ∈ comps, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc v hv
  unfold comps hostComps at hc
  rcases h : Oracle.invComponents vs 6 (platoon3_profiles_IRv2.invariants.getD 0
      ("", PForm.tt)).2 with _ | l
  · rw [h] at hc; simp at hc
  · rw [h] at hc
    simp only [Option.map_some, Option.getD_some, List.mem_map] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact notAux_mem_LR (invComponents_no_aux _ l h t ht v hv)

theorem getD_fv (i : ℕ) : (comps.getD i c0).fv ⊆ range Lv ∪ range Rv := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : comps[i]? with _ | c
  · simp [c0, Term.fv]
  · simp only [Option.getD_some]
    exact comps_mem_fv c (List.mem_of_getElem? h)

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> exact getD_fv _

/-! ## Existence: the explicit solution of the (linear) right modes -/

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

/-- The link's own box and slow form at the anchor (the evolve box, the projected-gap guard). -/
def LinkStart (c K : ℝ) (x y : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 60 ∧ -10 ≤ y ∧ y ≤ 10 ∧ -K ≤ Q2 c x y ∧ 2 * Q2 c x y ≤ 60 - c

def QBounds (c K : ℝ) (b : State (Var 6)) : Prop :=
  LinkStart c K (b (Rv 0)) (b (Rv 1)) ∧ LinkStart c K (b (Rv 2)) (b (Rv 3)) ∧
    LinkStart c K (b (Rv 4)) (b (Rv 5))

theorem solΦ_box (c K : ℝ) (hc1 : 20 ≤ c) (hc2 : c ≤ 60) (hK1 : 4 * K ≤ c) (hK2 : K ≤ 10)
    (b : State (Var 6)) (hb : QBounds c K b) (t : ℝ) (ht : 0 ≤ t) : Box Rv (solΦ c b t) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := hb
  have k0 := link_bounds c K _ _ t ht hc1 hc2 hK1 hK2 a1 a2 a3 a4 a5 a6
  have k1 := link_bounds c K _ _ t ht hc1 hc2 hK1 hK2 b1 b2 b3 b4 b5 b6
  have k2 := link_bounds c K _ _ t ht hc1 hc2 hK1 hK2 d1 d2 d3 d4 d5 d6
  simp only [Box, solΦ_R]
  exact ⟨⟨k0.1.1, k0.1.2, k0.2.1, k0.2.2⟩, ⟨k1.1.1, k1.1.2, k1.2.1, k1.2.2⟩,
    ⟨k2.1.1, k2.1.2, k2.2.1, k2.2.2⟩⟩

/-- The explicit solution solves the stretched right block (`λ = 1`). -/
theorem solΦ_deriv (c : ℝ) (fR : Fin 6 → Term (Var 6)) (hF : PairField Rv fR c)
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

theorem cRc_lo (q : ℕ) : 28 ≤ cRc q := by unfold cRc; split_ifs <;> norm_num
theorem cRc_hi (q : ℕ) : cRc q ≤ 32 := by unfold cRc; split_ifs <;> norm_num

/-- The stretch of the (single) left window: the emitted cover's λ = 1. -/
noncomputable def lam (_l : ℕ) : ℝ := 1

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; norm_num

/-- **The existence residual, discharged Z3-free by the explicit solution.** From any anchor
satisfying the right profile's kept atoms (the rated closing rate, the projected gap) and the
evolve box, the closed-form solution of the three damped links solves the (λ = 1) right
block, freezes every other coordinate, and stays in the evolve box. -/
theorem es (q : ℕ) (hq : q < 3) (dt : ℝ) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL 0) (cR q)))
        (Formula.and domL domR)) σ →
      HExistSegB (fL 0) (fR q) (Term.const (lam 0)) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ s ΦL hs0 _ _ _ hmaskL _
  have hatoms := ((sat_FM_append g gs _ σ).mp hσ.1).2
  have hR : ∀ t ∈ termsW Rv (pR q) (pR q) (pR q) [], Term.eval t σ ≤ 0 := by
    intro t ht
    apply hatoms
    unfold atomTerms
    rw [List.map_append, cR_terms q hq]
    exact List.mem_append_right _ ht
  have hbox : Box Rv σ := (sat_domR σ).mp hσ.2.2
  have hbR : ∀ j : Fin 6, ΦL s (Rv j) = σ (Rv j) := by
    intro j
    rw [hmaskL s ⟨hs0, le_rfl⟩ (Rv j) (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub _ _ h
      simp [Lv, Rv, Prod.ext_iff] at hi)]
    exact Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hPc : (pR q).P = 21 ∧ (pR q).U = 59 := by unfold pR; split_ifs <;> simp [pN, pC, pFar]
  have hQ : QBounds (cRc q) ((cRc q - 21) / 2) (ΦL s) := by
    have m : ∀ t, t ∈ termsW Rv (pR q) (pR q) (pR q) [] → Term.eval t σ ≤ 0 := hR
    simp only [termsW, guardT, linT, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at m
    have a3 := m (pgGe (Rv 0) (Rv 1) (pR q).P) (by simp)
    have a4 := m (pgLe (Rv 0) (Rv 1) (pR q).U) (by simp)
    have b3 := m (pgGe (Rv 2) (Rv 3) (pR q).P) (by simp)
    have b4 := m (pgLe (Rv 2) (Rv 3) (pR q).U) (by simp)
    have d3 := m (pgGe (Rv 4) (Rv 5) (pR q).P) (by simp)
    have d4 := m (pgLe (Rv 4) (Rv 5) (pR q).U) (by simp)
    rw [hPc.1] at a3 b3 d3
    rw [hPc.2] at a4 b4 d4
    simp only [pgGe, pgLe, Term.eval, AOp.interp] at a3 a4 b3 b4 d3 d4
    obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hbox
    have hc := cRc_lo q
    have hc' := cRc_hi q
    simp only [QBounds, LinkStart, Q2, hbR]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      linarith
  refine ⟨solΦ (cRc q) (ΦL s), solΦ_zero _ _, ?_, ?_, ?_⟩
  · intro t _
    exact solΦ_deriv (cRc q) (fR q) (fR_field q hq) (ΦL s) s t
  · intro t _ x hx
    refine solΦ_frozen _ _ _ x (fun hxR => hx ?_)
    obtain ⟨sx, j⟩ := x
    simp only at hxR
    subst hxR
    simp only [rightBlock, ODESystem.bound, List.map_map]
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  · intro t ht
    rw [sat_domR]
    have hc := cRc_lo q
    have hc' := cRc_hi q
    exact solΦ_box (cRc q) ((cRc q - 21) / 2) (by linarith) (by linarith) (by linarith)
      (by linarith) _ hQ t ht.1

/-! ## O2 for the instance: both families stay along every joint flow -/

theorem stayL (l q : ℕ) (hl : l < 1) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  obtain rfl : l = 0 := by omega
  intro a ha ν hν
  have hmem : ∀ t' ∈ (cL 0).map Prod.snd, Term.eval t' ν ≤ 0 := by
    intro t' ht'
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ht'
    exact (hiffL 0 hl a' ha' ν).mp (hν a' ha')
  have ha2 : a.2 ∈ (cL 0).map Prod.snd := List.mem_map_of_mem ha
  rw [cL_terms] at hmem ha2
  exact stayL_terms (fL 0) (fR q) _ (Formula.and domL domR) (fun z hz => (sat_domL z).mp hz.1)
    fL_field a.2 ha2 ν hmem

theorem stayR (l q : ℕ) (hq : q < 3) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hmem : ∀ t' ∈ (cR q).map Prod.snd, Term.eval t' ν ≤ 0 := by
    intro t' ht'
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ht'
    exact (hiffR q hq a' ha' ν).mp (hν a' ha')
  have ha2 : a.2 ∈ (cR q).map Prod.snd := List.mem_map_of_mem ha
  rw [cR_terms q hq] at hmem ha2
  have hF : PairField Rv (fR q) (pR q).c := by rw [pR_c]; exact fR_field q hq
  exact stayR_terms (fL l) (fR q) (lam l) (lam_pos l).le (Formula.and domL domR)
    (fun z hz => (sat_domR z).mp hz.2) (pR q) (pR_ok q) hF a.2 ha2 ν hmem

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

theorem hfL (l : ℕ) (hl : l < 1) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by
      obtain rfl : l = 0 := by omega
      simp [mL, platoon3_profiles_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 6) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, platoon3_profiles_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, platoon3_profiles_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, platoon3_profiles_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 1) : (hostGuard vs 6 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by
      obtain rfl : l = 0 := by omega
      simp [mL, platoon3_profiles_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

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

theorem leftExtra_fv : ∀ t ∈ leftExtra, ∀ x ∈ t.fv, ∃ j, x = Lv j := by
  intro t ht x hx
  simp only [leftExtra, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;>
    simp only [thrGe, Term.fv, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, false_or] at hx <;> exact ⟨_, hx⟩

theorem anchor_fv (l q : ℕ) (hl : l < 1) (hq : q < 3) :
    ∀ c ∈ g :: gs ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  obtain rfl : l = 0 := by omega
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv _ (List.mem_cons_of_mem _ hc)
  unfold atomTerms at hc
  rw [List.map_append, cL_terms, cR_terms q hq] at hc
  intro x hx
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨j, rfl⟩ := termsW_fv Lv _ _ _ _ leftExtra_fv c hc x hx
    exact Or.inl ⟨j, rfl⟩
  · obtain ⟨j, rfl⟩ := termsW_fv Rv _ _ _ [] (by simp) c hc x hx
    exact Or.inr ⟨j, rfl⟩

/-! ## The GUARDED right automaton (the file's modes, declared `next` lists, entered guards) -/

noncomputable def modeW (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- An edge tests the lowered guard of the mode it ENTERS (the paper's `?guard_m(x)`). -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := hostGuard vs 6 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, CLOSE 1, FAR 2, BRAKE1 3, BRAKE2 4,
BRAKE3 5). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 0), (1, 3), (1, 4), (1, 5),
   (2, 2), (2, 0), (2, 3), (2, 4), (2, 5), (3, 3), (4, 4), (5, 5)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range platoon3_profiles_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (platoon3_profiles_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4, modeW 5]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 6 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 6) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 6)} (hm : Gr.modeAt q = some m) :
    q < 6 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 5 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 6 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])


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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [edgeW, Gr]

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
  hostGuard_fv_R_getD vs _ dm rfl (by simp [platoon3_profiles_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem hgR : GuardsRight Gr := by
  intro q e he
  rw [Gr_guards q e he]
  exact hguardR_all e.tgt

/-- Every profile's guard (the operating range), from its parts. -/
theorem guardR_of (q : ℕ) (hq : q < 3) (x : State (Var 6))
    (h1 : 20 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60 ∧ -10 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 10 ∧
      21 ≤ x (Rv 0) + 2 * x (Rv 1) ∧ x (Rv 0) + 2 * x (Rv 1) ≤ 59)
    (h2 : 20 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 60 ∧ -10 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 10 ∧
      21 ≤ x (Rv 2) + 2 * x (Rv 3) ∧ x (Rv 2) + 2 * x (Rv 3) ≤ 59)
    (h3 : 20 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 60 ∧ -10 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 10 ∧
      21 ≤ x (Rv 4) + 2 * x (Rv 5) ∧ x (Rv 4) + 2 * x (Rv 5) ≤ 59) :
    Formula.sat (hostGuard vs 6 Side.R (mR q)) x := by
  simp only [Rv] at h1 h2 h3
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h3
  interval_cases q <;>
  · simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hn21_0, hn59_0, hpm100, hp100, hn2_0, hn20_0, hn58_0, hp600, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, AOp.interp, Rv]
    repeat' apply And.intro
    all_goals linarith

/-- Every profile's guard gives the gap floor. -/
theorem guardR_floor (q : ℕ) (hq : q < 3) (x : State (Var 6))
    (h : Formula.sat (hostGuard vs 6 Side.R (mR q)) x) :
    20 ≤ x (Rv 0) ∧ 20 ≤ x (Rv 2) ∧ 20 ≤ x (Rv 4) := by
  interval_cases q <;>
  · simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hn21_0, hn59_0, hpm100, hp100, hn2_0, hn20_0, hn58_0, hp600, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, AOp.interp, Rv] at h
    simp only [Rv]
    exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.2⟩

/-! ## Regions: the right mode's kept cut atoms; the pruned sinks are excluded -/

noncomputable def region (q : ℕ) : Formula (Var 6) :=
  if q < 3 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 3) (ν : State (Var 6)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region_sink (q : ℕ) (hq : ¬ q < 3) (ν : State (Var 6)) :
    ¬ Formula.sat (region q) ν := by
  simp [region, hq, Formula.sat, CompOp.interp, Term.eval]

theorem atomsFreeR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX platoon3_profiles_cutsV2X.R (mR q).name,
      Parse.PForm.namesFree "L_" x.atom = true := by
  interval_cases q <;>
  · intro x hx
    simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem region_fv (q : ℕ) (_hq : q < 6) : (region q).fv ⊆ range Rv := by
  by_cases h1 : q < 3
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

/-- One pack: the left window (`FOLLOW`, invariant row 0), right mode `q`, at the cover's
λ = 1 and strata order `[0, 1, …, 17]` (the identity). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX platoon3_profiles_IRv2 platoon3_profiles_cutsV2X 6 0
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] 1 l q

theorem verd_core (l q : ℕ) (hl : l < 1) (hq : q < 6) (h : Verd l q) :
    VerdXCore (g :: gs) (fL l) (fR q) (lam l)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

theorem couple (l q : ℕ) (hl : l < 1) (hq : q < 3) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 6))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) := by
  obtain rfl : l = 0 := by omega
  exact couple_cutX g gs (g :: gs) (cL 0) (cR q) (fL 0) (fR q) (lam 0) (lam_pos 0) domL domR 1 dt
    (hfL 0 hl) (hfR q (by omega)) hdomL hdomR (anchor_fv 0 q hl hq) (fun c hc => hc)
    (fun c hc => hc) (hiffL 0 hl) (hiffR q hq) (stayL 0 q hl) (stayR 0 q hq)
    (verd_core 0 q hl (by omega) hv) (es q hq dt)

theorem sat_faModal_monoPost {P Q : Program (Var 6)} {A B : Formula (Var 6)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 6)}
    (h : Formula.sat (faModal (Equiv.refl (Var 6)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l qs : ℕ) (hl : l < 1) (hqs : qs < 3) (dt : ℝ) (hv : Verd l qs)
    (path : List ℕ) (hpath : ∀ p ∈ path, p < 6) {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR qs)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
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
    (path.map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 6)))
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
      exact hdisH_progR (⟨fR qs, Term.const 1, domR⟩ : RepoHop 6)
        (hfR qs (by omega)) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l qs hl hqs dt hv σ' hσ')
    hσ
  rw [show (path.map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 6))).map
      (fun h => h.progR)
      = path.map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from by rw [List.map_map]; rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append g gs _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR qs hqs) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt qs hqs ν).mpr hRν⟩

/-! ## The step provider: stay in the certified start mode -/

noncomputable def leftData : List (Formula (Var 6) × (Fin 6 → Term (Var 6))
    × Formula (Var 6) × ℕ) :=
  [(hostGuard vs 6 Side.L (mL 0), fL 0, domL, 1)]

noncomputable def leftProgs (dt : ℝ) : List (Program (Var 6)) :=
  leftData.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2)

theorem hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftData, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact ⟨hguardL 0 (by norm_num), hfL 0 (by norm_num), hdomL⟩

theorem hframes (dt : ℝ) : ∀ P ∈ leftProgs dt, FramesMv P mv := by
  intro P hP
  simp only [leftProgs, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg dt d.2.2.2 mv (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

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


/-- A profile's window, the GUARDED response: stay in the start profile on the certified joint
segment, then take its self-loop, legal at the end state (the kept cuts give the rated
closing rate and the projected gap, the envelope `g_i ≤ 60`, and `gap_floor_Ronly` the gap
floor along the reference's own run). -/
theorem stayCaseG (l q : ℕ) (hl : l < 1) (hq : q < 3) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 6)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hgd : Formula.sat (hostGuard vs 6 Side.R (mR q)) σ) (hreg : Formula.sat (region q) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 6 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
      (Formula.and domL domR)) σ := by
    refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
      ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
  have hresp := respond l q hl hq dt hv [] (by simp) hanchor
  simp only [List.map_nil, List.nil_append] at hresp
  refine gresp_final_run (ms := modeW q) (Gr_modeAt q (by omega)) hresp ?_
  intro ν hν μ hflow hpost
  have hRν : ∀ i, ν (Rv i) = σ (Rv i) := by
    intro i
    have hP := vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL
    refine (Program.bound_effect _ hν (Rv i) ?_).symm
    intro hb
    rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
    · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
  have hRσ : ∀ t ∈ termsW Rv (pR q) (pR q) (pR q) [], Term.eval t σ ≤ 0 := by
    have h := (sat_region_lt q hq σ).mp hreg
    intro t ht
    rw [← cR_terms q hq] at ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact (hiffR q hq a ha σ).mp (h a ha)
  have hRμ : ∀ t ∈ termsW Rv (pR q) (pR q) (pR q) [], Term.eval t μ ≤ 0 := by
    have h := (sat_region_lt q hq μ).mp hpost.2
    intro t ht
    rw [← cR_terms q hq] at ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact (hiffR q hq a ha μ).mp (h a ha)
  have hfl := guardR_floor q hq σ hgd
  have hF : PairField Rv (fR q) (pR q).c := by rw [pR_c]; exact fR_field q hq
  obtain ⟨F1, F2, F3⟩ := linkFields hF
  have hPc : (pR q).P = 21 ∧ (pR q).U = 59 := by unfold pR; split_ifs <;> simp [pN, pC, pFar]
  have hc21 : 21 ≤ (pR q).c := by rw [pR_c]; have := cRc_lo q; linarith
  have hflow' : Program.sem (Program.ode (rightBlock (fR q) (Term.const 1)) domR) ν μ := hflow
  have tr : ∀ t ∈ termsW Rv (pR q) (pR q) (pR q) [], Term.eval t ν ≤ 0 := by
    intro t ht
    have hfv := termsW_fv Rv _ _ _ [] (by simp) t ht
    rw [Term.coincidence t (ν := ν) (w := σ) (fun x hx => by
      obtain ⟨j, rfl⟩ := hfv x hx
      exact hRν j)]
    exact hRσ t ht
  have floor : ∀ (jx jy : Fin 6), LinkField Rv (fR q) jx jy (pR q).c →
      pgGe (Rv jx) (Rv jy) (pR q).P ∈ termsW Rv (pR q) (pR q) (pR q) [] →
      20 ≤ σ (Rv jx) → 20 ≤ μ (Rv jx) :=
    fun jx jy hFl hmem h0 => gap_floor_Ronly (fR q) domR jx jy (pR q).c 20 (pR q).P
      (by rw [hPc.1]; norm_num) (by rw [hPc.1]; exact hc21) hFl hflow' (tr _ hmem)
      (by rw [hRν]; exact h0)
  have g1 := floor 0 1 F1 (by simp [termsW, guardT]) hfl.1
  have g2 := floor 2 3 F2 (by simp [termsW, guardT]) hfl.2.1
  have g3 := floor 4 5 F3 (by simp [termsW, guardT]) hfl.2.2
  have hboxμ : Box Rv μ := (sat_domR μ).mp hpost.1.2.2
  have m := hRμ
  simp only [termsW, guardT, linT, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at m
  have a3 := m (pgGe (Rv 0) (Rv 1) (pR q).P) (by simp)
  have a4 := m (pgLe (Rv 0) (Rv 1) (pR q).U) (by simp)
  have b3 := m (pgGe (Rv 2) (Rv 3) (pR q).P) (by simp)
  have b4 := m (pgLe (Rv 2) (Rv 3) (pR q).U) (by simp)
  have d3 := m (pgGe (Rv 4) (Rv 5) (pR q).P) (by simp)
  have d4 := m (pgLe (Rv 4) (Rv 5) (pR q).U) (by simp)
  rw [hPc.1] at a3 b3 d3
  rw [hPc.2] at a4 b4 d4
  simp only [pgGe, pgLe, Term.eval, AOp.interp] at a3 a4 b3 b4 d3 d4
  obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hboxμ
  refine ⟨edgeW q q, edge_mem q q (by interval_cases q <;> simp [edgeList]), ?_, hpost⟩
  show Formula.sat (hostGuard vs 6 Side.R (mR q)) μ
  exact guardR_of q hq μ ⟨g1, x1, y0, y1, by linarith, by linarith⟩
    ⟨g2, x3, y2, y3, by linarith, by linarith⟩ ⟨g3, x5, y4, y5, by linarith, by linarith⟩

/-- The window, every admissible right start (in its guard and cuts): the start profile
stays and takes its legal self-loop; the BRAKE sinks are excluded by their (false) regions. -/
theorem HmultiG (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ →
      Formula.sat (hostGuard vs 6 Side.R (mR q)) σ → Formula.sat (region q) σ →
      GResp Gr q P (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hg hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  subst hP
  match q, hq, hg, hreg with
  | 0, _, hg, hreg => exact stayCaseG 0 0 (by norm_num) (by norm_num) dt h0 hσ hg hreg
  | 1, _, hg, hreg => exact stayCaseG 0 1 (by norm_num) (by norm_num) dt h1 hσ hg hreg
  | 2, _, hg, hreg => exact stayCaseG 0 2 (by norm_num) (by norm_num) dt h2 hσ hg hreg
  | 3, _, _, hreg => exact absurd hreg (not_sat_region_sink 3 (by norm_num) σ)
  | 4, _, _, hreg => exact absurd hreg (not_sat_region_sink 4 (by norm_num) σ)
  | 5, _, _, hreg => exact absurd hreg (not_sat_region_sink 5 (by norm_num) σ)

/-! ## Theorem 3 -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard (the operating range
for every profile) and its kept cut atoms. -/
noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vs 6 Side.R (mR q)) region q

theorem gregion_fv (q : ℕ) (hq : q < 6) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

/-- **`platoon3_profiles` (suite_v2), Theorem 3 over the GUARDED right automaton at the
mode-consistent region, the left window guard-gated** (the choice form;
`platoon3_profiles_leftAut` states it with the left automaton). Left: the `FOLLOW` window
(three follower links at 29), entered inside the deployed's operating range
(`21 ≤ g_i ≤ 59`, `|r_i| ≤ 10`, `20 ≤ g_i + 2 r_i ≤ 58`); right: the six-mode reference
automaton of the file (the gap profiles `NORMAL`/`CLOSE`/`FAR`, set points 30/28/32 under
the same operating-range guard `20 ≤ g_i ≤ 60`, `|r_i| ≤ 10`, `21 ≤ g_i + 2 r_i ≤ 59`, and
the AEB sinks `BRAKE1..3`, the nine profile `→ BRAKE` edges pruned), every edge testing the
entered mode's guard. Loop invariant: the declared 18-component row, the evolve envelope on
both sides, the right in the guard and kept cuts of its current mode. Response: the
certified joint segment in the start profile at the cover's λ = 1, then its self-loop
(legal: `stayCaseG`). Residuals: three stratified verdict packs (`modalVerdX`). -/
theorem platoon3_profiles_modal (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
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
    by_cases hq : q < 6
    · exact aux_notin_range_Rv 0 (region_fv q hq h)
    · simp only [region, show ¬ q < 3 from by omega, if_false] at h
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
        (fun P hP q hq σ hmv hσ hg hreg => HmultiG dt h0 h1 h2 P hP q hq σ hmv hσ hg hreg))
  · exact hddF_multiR_G Gr 0 1 dt leftData gregion (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

/-! ## The paper's left program: the guard-gated left automaton -/

/-- The file's left `next` lists, resolved to indices (`FOLLOW → [FOLLOW]`). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap
    (Handoff.leftModeIndex platoon3_profiles_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

noncomputable def AL (dt : ℝ) : LeftAut 6 := LeftAut.ofG leftData tg dt nextLA

abbrev uLA : Var 6 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 6 Side.L (mL l)) := rfl

/-- **`platoon3_profiles`, Theorem 3 with the paper's left program** (the guard-gated left
automaton against the guarded right automaton; the declared row; the right in its current
mode's guard and cuts). -/
theorem platoon3_profiles_leftAut (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL domR gregion _
    (platoon3_profiles_modal dt h0 h1 h2)
    (fun q hq => gregion_fv q hq) (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs)
    hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- The row lowers to exactly 18 components (so `g :: gs` is the whole row). -/
theorem comps_length : comps.length = 18 := by
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
  simp [comps, hostComps, platoon3_profiles_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    List.findIdx?_cons, hp00, hp10, hq0_25, hq0_5, hp20]

end V2Platoon3Profiles
end RelCertifier
