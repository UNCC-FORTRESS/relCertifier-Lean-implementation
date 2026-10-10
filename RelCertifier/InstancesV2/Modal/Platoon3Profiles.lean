/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_profiles` (suite_v2) — modal Theorem 3

Three-follower CACC string (`n = 6`: `g1, r1, g2, r2, g3, r3`), linear damped links on both
sides (roots `ρ = 1/4, 1/2`); one left window (`FOLLOW`, set point 29), right gap profiles
`NORMAL`/`CLOSE`/`FAR` (set points 30/28/32) plus the pruned AEB sinks `BRAKE1..3`.
Adapted from `InstancesV2/Modal/QuadLightProfiles.lean` (same generic layer, same structure).

* O2 for all 24 kept atoms per mode (linear forms and derived gap bounds) goes through the
  `CutLiftX` shape lemmas (`super_linear_*`, `super_derived_*` under `stay_given`);
* existence is discharged Z3-free by the EXPLICIT closed-form solution of the linear right
  modes (`q₁ = r + (g − c)/4`, `q₂ = r + (g − c)/2` decay at rates 1/2, 1/4); the kept
  linear-form atoms of the anchor (`|q₁| ≤ 2`, `|q₂| ≤ 3`) keep it inside the evolve box.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.platoon3_profiles

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Platoon3Profiles

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

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

/-- The four linear forms of one link (`ρ = 1/4` box `±2`, `ρ = 1/2` box `±3`). -/
noncomputable def linT (W : Fin 6 → Var 6) (jx jy : Fin 6) (c : ℝ) : List (Term (Var 6)) :=
  [linLe (W jx) (W jy) (1/4) c 2, linGe (W jx) (W jy) (1/4) c (-2),
   linLe (W jx) (W jy) (1/2) c 3, linGe (W jx) (W jy) (1/2) c (-3)]

/-- The four derived gap bounds of one link. -/
noncomputable def derT (W : Fin 6 → Var 6) (jx : Fin 6) (u1 l1 u2 l2 : ℝ) :
    List (Term (Var 6)) :=
  [thrLe (W jx) u1, thrGe (W jx) l1, thrLe (W jx) u2, thrGe (W jx) l2]

/-- A mode's 24 kept atoms (safe-side terms), in the certificate's order. -/
noncomputable def termsW (W : Fin 6 → Var 6) (c u1 l1 u2 l2 : ℝ) : List (Term (Var 6)) :=
  linT W 0 1 c ++ linT W 2 3 c ++ linT W 4 5 c ++
    derT W 0 u1 l1 u2 l2 ++ derT W 2 u1 l1 u2 l2 ++ derT W 4 u1 l1 u2 l2

theorem cL_terms : (cL 0).map Prod.snd = termsW Lv 29 37 21 35 23 := by
  simp [cL, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons,
    hq0_25, hq0_5, hq29, hq30, hq28, hq32, hq2, hqm2, hq3, hqm3, hq37, hq21, hq35, hq23, hq38,
    hq22, hq36, hq24, hq34, hq20, hq40, hq26, ITerm.toHost, termsW, linT, derT, linLe, linGe, linQ, thrLe, thrGe, Lv]

theorem cR_terms0 : (cR 0).map Prod.snd = termsW Rv 30 38 22 36 24 := by
  simp [cR, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons,
    hq0_25, hq0_5, hq29, hq30, hq28, hq32, hq2, hqm2, hq3, hqm3, hq37, hq21, hq35, hq23, hq38,
    hq22, hq36, hq24, hq34, hq20, hq40, hq26, ITerm.toHost, termsW, linT, derT, linLe, linGe,
    linQ, thrLe, thrGe, Rv]
theorem cR_terms1 : (cR 1).map Prod.snd = termsW Rv 28 36 20 34 22 := by
  simp [cR, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons,
    hq0_25, hq0_5, hq29, hq30, hq28, hq32, hq2, hqm2, hq3, hqm3, hq37, hq21, hq35, hq23, hq38,
    hq22, hq36, hq24, hq34, hq20, hq40, hq26, ITerm.toHost, termsW, linT, derT, linLe, linGe,
    linQ, thrLe, thrGe, Rv]
theorem cR_terms2 : (cR 2).map Prod.snd = termsW Rv 32 40 24 38 26 := by
  simp [cR, cutPairsX, cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2,
    hostAtomG, cutAtomG, Run.lowerE, vs, Run.resolveVar, List.findIdx?_cons,
    hq0_25, hq0_5, hq29, hq30, hq28, hq32, hq2, hqm2, hq3, hqm3, hq37, hq21, hq35, hq23, hq38,
    hq22, hq36, hq24, hq34, hq20, hq40, hq26, ITerm.toHost, termsW, linT, derT, linLe, linGe,
    linQ, thrLe, thrGe, Rv]

theorem atomsNonstrictL (l : ℕ) (hl : l < 1) :
    ∀ x ∈ cutAtomsOfX platoon3_profiles_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  obtain rfl : l = 0 := by omega
  intro x hx
  simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2] at hx
  simp at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX platoon3_profiles_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mR, platoon3_profiles_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 1) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp330 : Run.parseRat "33.0" = some (33 : ℚ) := by
  have h : parseQ "33.0" = some (⟨330, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm10 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hO1L (l : ℕ) (hl : l < 1) :
    ∀ ν, Formula.sat (hostGuard vs 6 Side.L (mL l)) ν → CutSat (cL l) ν := by
  obtain rfl : l = 0 := by omega
  intro ν hν
  refine cutSatL_of_guard platoon3_profiles_cutsV2X_wf (mL 0) ?_ ?_ ?_ ?_ ν hν
  · rfl
  · intro x hx
    simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x hx
    simp only [cutAtomsOfX, platoon3_profiles_cutsV2X, mL, platoon3_profiles_IRv2] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Run.lowerF, Run.lowerE, hq0_25, hq0_5, hq29, hq2, hqm2, hq3, hqm3, hq37, hq21, hq35,
        hq23, vs, Run.resolveVar, List.findIdx?_cons]
  · simp [mL, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hp250, hp330, hpm10, hp10, vs,
      Run.resolveVar, List.findIdx?_cons]

/-! ## O2: the kept atoms stay along the joint flows (`CutLiftX` linear/derived shapes) -/

theorem hroot4 : (1/4 : ℝ) * (1/4) - 3/4 * (1/4) + 1/8 = 0 := by norm_num
theorem hroot2 : (1/2 : ℝ) * (1/2) - 3/4 * (1/2) + 1/8 = 0 := by norm_num

/-- The narrowing formula of a given linear form (`q − K ≤ 0` / `K − q ≤ 0`). -/
def leF (t : Term (Var 6)) : Formula (Var 6) := Formula.cmp CompOp.le t (Term.const 0)

theorem sat_leF (t : Term (Var 6)) (z : State (Var 6)) :
    Formula.sat (leF t) z ↔ Term.eval t z ≤ 0 := by
  simp [leF, Formula.sat, CompOp.interp, Term.eval]


theorem stayR_linLe (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : 0 ≤ K)
    (hfx : ∀ z, Term.eval (fR jx) z = z (Rv jy))
    (hfy : ∀ z, Term.eval (fR jy) z = -(1/8) * (z (Rv jx) - c) - 3/4 * z (Rv jy))
    (ν : State (Var 6)) (h : Term.eval (linLe (Rv jx) (Rv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (linLe (Rv jx) (Rv jy) r c K) ω) ν :=
  boxle_R_of_super _ fL fR lamv hlam dom dom
    (fun i hi => by simp [linLe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_le_R (a := 1/8) (b := 3/4) hroot hσ hK fR dom (fun z _ => hfx z)
      (fun z _ => hfy z)) h

theorem stayR_linGe (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0)
    (hfx : ∀ z, Term.eval (fR jx) z = z (Rv jy))
    (hfy : ∀ z, Term.eval (fR jy) z = -(1/8) * (z (Rv jx) - c) - 3/4 * z (Rv jy))
    (ν : State (Var 6)) (h : Term.eval (linGe (Rv jx) (Rv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (linGe (Rv jx) (Rv jy) r c K) ω) ν :=
  boxle_R_of_super _ fL fR lamv hlam dom dom
    (fun i hi => by simp [linGe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_ge_R (a := 1/8) (b := 3/4) hroot hσ hK fR dom (fun z _ => hfx z)
      (fun z _ => hfy z)) h

theorem stayR_derLe (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K K' : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : 0 ≤ K) (hr : 0 ≤ r) (hKK : K ≤ r * (K' - c))
    (hfx : ∀ z, Term.eval (fR jx) z = z (Rv jy))
    (hfy : ∀ z, Term.eval (fR jy) z = -(1/8) * (z (Rv jx) - c) - 3/4 * z (Rv jy))
    (ν : State (Var 6)) (hq : Term.eval (linLe (Rv jx) (Rv jy) r c K) ν ≤ 0)
    (h : Term.eval (thrLe (Rv jx) K') ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (thrLe (Rv jx) K') ω) ν :=
  stay_given (Fq := leF (linLe (Rv jx) (Rv jy) r c K)) (fun z => sat_leF _ z)
    (fun ν' h' => stayR_linLe fL fR lamv hlam dom jx jy r c K hroot hσ hK hfx hfy ν' h')
    (fun ν' h' => boxle_R_of_super _ fL fR lamv hlam _ _
      (fun i hi => by simp [thrLe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_le_R hr hKK fR (Formula.and dom (leF (linLe (Rv jx) (Rv jy) r c K)))
        (fun z _ => hfx z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq h

theorem stayR_derGe (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K K' : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0) (hr : 0 ≤ r) (hKK : r * (K' - c) ≤ K)
    (hfx : ∀ z, Term.eval (fR jx) z = z (Rv jy))
    (hfy : ∀ z, Term.eval (fR jy) z = -(1/8) * (z (Rv jx) - c) - 3/4 * z (Rv jy))
    (ν : State (Var 6)) (hq : Term.eval (linGe (Rv jx) (Rv jy) r c K) ν ≤ 0)
    (h : Term.eval (thrGe (Rv jx) K') ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (thrGe (Rv jx) K') ω) ν :=
  stay_given (Fq := leF (linGe (Rv jx) (Rv jy) r c K)) (fun z => sat_leF _ z)
    (fun ν' h' => stayR_linGe fL fR lamv hlam dom jx jy r c K hroot hσ hK hfx hfy ν' h')
    (fun ν' h' => boxle_R_of_super _ fL fR lamv hlam _ _
      (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_ge_R hr hKK fR (Formula.and dom (leF (linGe (Rv jx) (Rv jy) r c K)))
        (fun z _ => hfx z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq h

/-- **All 24 right atoms stay** (each from a base where the whole family holds). -/
theorem stayR_terms (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv) (dom : Formula (Var 6))
    (c u1 l1 u2 l2 : ℝ) (hF : PairField Rv fR c)
    (h1 : 2 ≤ 1/4 * (u1 - c)) (h2 : 1/4 * (l1 - c) ≤ -2)
    (h3 : 3 ≤ 1/2 * (u2 - c)) (h4 : 1/2 * (l2 - c) ≤ -3) :
    ∀ t ∈ termsW Rv c u1 l1 u2 l2, ∀ ν, (∀ t' ∈ termsW Rv c u1 l1 u2 l2, Term.eval t' ν ≤ 0) →
      BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
        (fun ω => Term.eval t ω) ν := by
  intro t ht ν hall
  have hfx0 : ∀ z, Term.eval (fR 0) z = z (Rv 1) := fun z => (hF z).1
  have hfy0 : ∀ z, Term.eval (fR 1) z = -(1/8) * (z (Rv 0) - c) - 3/4 * z (Rv 1) :=
    fun z => (hF z).2.1
  have hfx1 : ∀ z, Term.eval (fR 2) z = z (Rv 3) := fun z => (hF z).2.2.1
  have hfy1 : ∀ z, Term.eval (fR 3) z = -(1/8) * (z (Rv 2) - c) - 3/4 * z (Rv 3) :=
    fun z => (hF z).2.2.2.1
  have hfx2 : ∀ z, Term.eval (fR 4) z = z (Rv 5) := fun z => (hF z).2.2.2.2.1
  have hfy2 : ∀ z, Term.eval (fR 5) z = -(1/8) * (z (Rv 4) - c) - 3/4 * z (Rv 5) :=
    fun z => (hF z).2.2.2.2.2
  have hm : ∀ t', t' ∈ termsW Rv c u1 l1 u2 l2 → Term.eval t' ν ≤ 0 := hall
  simp only [termsW, linT, derT, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ht hm
  have hs4 : (0:ℝ) ≤ 3/4 - 1/4 := by norm_num
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  have hr4 : (0:ℝ) ≤ 1/4 := by norm_num
  have hr2 : (0:ℝ) ≤ 1/2 := by norm_num
  have k2 : (0:ℝ) ≤ 2 := by norm_num
  have k3 : (0:ℝ) ≤ 3 := by norm_num
  have km2 : (-2:ℝ) ≤ 0 := by norm_num
  have km3 : (-3:ℝ) ≤ 0 := by norm_num
  rcases ht with ((((((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl))
  · exact stayR_linLe fL fR lamv hlam dom 0 1 _ c _ hroot4 hs4 k2 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayR_linGe fL fR lamv hlam dom 0 1 _ c _ hroot4 hs4 km2 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayR_linLe fL fR lamv hlam dom 0 1 _ c _ hroot2 hs2 k3 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayR_linGe fL fR lamv hlam dom 0 1 _ c _ hroot2 hs2 km3 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayR_linLe fL fR lamv hlam dom 2 3 _ c _ hroot4 hs4 k2 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayR_linGe fL fR lamv hlam dom 2 3 _ c _ hroot4 hs4 km2 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayR_linLe fL fR lamv hlam dom 2 3 _ c _ hroot2 hs2 k3 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayR_linGe fL fR lamv hlam dom 2 3 _ c _ hroot2 hs2 km3 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayR_linLe fL fR lamv hlam dom 4 5 _ c _ hroot4 hs4 k2 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayR_linGe fL fR lamv hlam dom 4 5 _ c _ hroot4 hs4 km2 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayR_linLe fL fR lamv hlam dom 4 5 _ c _ hroot2 hs2 k3 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayR_linGe fL fR lamv hlam dom 4 5 _ c _ hroot2 hs2 km3 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayR_derLe fL fR lamv hlam dom 0 1 _ c _ _ hroot4 hs4 k2 hr4 h1 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derGe fL fR lamv hlam dom 0 1 _ c _ _ hroot4 hs4 km2 hr4 h2 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derLe fL fR lamv hlam dom 0 1 _ c _ _ hroot2 hs2 k3 hr2 h3 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derGe fL fR lamv hlam dom 0 1 _ c _ _ hroot2 hs2 km3 hr2 h4 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derLe fL fR lamv hlam dom 2 3 _ c _ _ hroot4 hs4 k2 hr4 h1 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derGe fL fR lamv hlam dom 2 3 _ c _ _ hroot4 hs4 km2 hr4 h2 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derLe fL fR lamv hlam dom 2 3 _ c _ _ hroot2 hs2 k3 hr2 h3 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derGe fL fR lamv hlam dom 2 3 _ c _ _ hroot2 hs2 km3 hr2 h4 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derLe fL fR lamv hlam dom 4 5 _ c _ _ hroot4 hs4 k2 hr4 h1 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derGe fL fR lamv hlam dom 4 5 _ c _ _ hroot4 hs4 km2 hr4 h2 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derLe fL fR lamv hlam dom 4 5 _ c _ _ hroot2 hs2 k3 hr2 h3 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayR_derGe fL fR lamv hlam dom 4 5 _ c _ _ hroot2 hs2 km3 hr2 h4 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))


theorem stayL_linLe (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6)) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : 0 ≤ K)
    (hfx : ∀ z, Term.eval (fL jx) z = z (Lv jy))
    (hfy : ∀ z, Term.eval (fL jy) z = -(1/8) * (z (Lv jx) - c) - 3/4 * z (Lv jy))
    (ν : State (Var 6)) (h : Term.eval (linLe (Lv jx) (Lv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (linLe (Lv jx) (Lv jy) r c K) ω) ν :=
  boxle_L_of_super _ fL fR lam dom dom
    (fun i hi => by simp [linLe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_le_L (a := 1/8) (b := 3/4) hroot hσ hK fL dom (fun z _ => hfx z)
      (fun z _ => hfy z)) h

theorem stayL_linGe (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6)) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0)
    (hfx : ∀ z, Term.eval (fL jx) z = z (Lv jy))
    (hfy : ∀ z, Term.eval (fL jy) z = -(1/8) * (z (Lv jx) - c) - 3/4 * z (Lv jy))
    (ν : State (Var 6)) (h : Term.eval (linGe (Lv jx) (Lv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (linGe (Lv jx) (Lv jy) r c K) ω) ν :=
  boxle_L_of_super _ fL fR lam dom dom
    (fun i hi => by simp [linGe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_ge_L (a := 1/8) (b := 3/4) hroot hσ hK fL dom (fun z _ => hfx z)
      (fun z _ => hfy z)) h

theorem stayL_derLe (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6)) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K K' : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : 0 ≤ K) (hr : 0 ≤ r) (hKK : K ≤ r * (K' - c))
    (hfx : ∀ z, Term.eval (fL jx) z = z (Lv jy))
    (hfy : ∀ z, Term.eval (fL jy) z = -(1/8) * (z (Lv jx) - c) - 3/4 * z (Lv jy))
    (ν : State (Var 6)) (hq : Term.eval (linLe (Lv jx) (Lv jy) r c K) ν ≤ 0)
    (h : Term.eval (thrLe (Lv jx) K') ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (thrLe (Lv jx) K') ω) ν :=
  stay_given (Fq := leF (linLe (Lv jx) (Lv jy) r c K)) (fun z => sat_leF _ z)
    (fun ν' h' => stayL_linLe fL fR lam dom jx jy r c K hroot hσ hK hfx hfy ν' h')
    (fun ν' h' => boxle_L_of_super _ fL fR lam _ _
      (fun i hi => by simp [thrLe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_le_L hr hKK fL (Formula.and dom (leF (linLe (Lv jx) (Lv jy) r c K)))
        (fun z _ => hfx z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq h

theorem stayL_derGe (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6)) (dom : Formula (Var 6))
    (jx jy : Fin 6) (r c K K' : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0) (hr : 0 ≤ r) (hKK : r * (K' - c) ≤ K)
    (hfx : ∀ z, Term.eval (fL jx) z = z (Lv jy))
    (hfy : ∀ z, Term.eval (fL jy) z = -(1/8) * (z (Lv jx) - c) - 3/4 * z (Lv jy))
    (ν : State (Var 6)) (hq : Term.eval (linGe (Lv jx) (Lv jy) r c K) ν ≤ 0)
    (h : Term.eval (thrGe (Lv jx) K') ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (thrGe (Lv jx) K') ω) ν :=
  stay_given (Fq := leF (linGe (Lv jx) (Lv jy) r c K)) (fun z => sat_leF _ z)
    (fun ν' h' => stayL_linGe fL fR lam dom jx jy r c K hroot hσ hK hfx hfy ν' h')
    (fun ν' h' => boxle_L_of_super _ fL fR lam _ _
      (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_ge_L hr hKK fL (Formula.and dom (leF (linGe (Lv jx) (Lv jy) r c K)))
        (fun z _ => hfx z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq h

/-- **All 24 left atoms stay** (each from a base where the whole family holds). -/
theorem stayL_terms (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6)) (dom : Formula (Var 6))
    (c u1 l1 u2 l2 : ℝ) (hF : PairField Lv fL c)
    (h1 : 2 ≤ 1/4 * (u1 - c)) (h2 : 1/4 * (l1 - c) ≤ -2)
    (h3 : 3 ≤ 1/2 * (u2 - c)) (h4 : 1/2 * (l2 - c) ≤ -3) :
    ∀ t ∈ termsW Lv c u1 l1 u2 l2, ∀ ν, (∀ t' ∈ termsW Lv c u1 l1 u2 l2, Term.eval t' ν ≤ 0) →
      BoxLe (Program.ode (jointSys fL fR lam) dom)
        (fun ω => Term.eval t ω) ν := by
  intro t ht ν hall
  have hfx0 : ∀ z, Term.eval (fL 0) z = z (Lv 1) := fun z => (hF z).1
  have hfy0 : ∀ z, Term.eval (fL 1) z = -(1/8) * (z (Lv 0) - c) - 3/4 * z (Lv 1) :=
    fun z => (hF z).2.1
  have hfx1 : ∀ z, Term.eval (fL 2) z = z (Lv 3) := fun z => (hF z).2.2.1
  have hfy1 : ∀ z, Term.eval (fL 3) z = -(1/8) * (z (Lv 2) - c) - 3/4 * z (Lv 3) :=
    fun z => (hF z).2.2.2.1
  have hfx2 : ∀ z, Term.eval (fL 4) z = z (Lv 5) := fun z => (hF z).2.2.2.2.1
  have hfy2 : ∀ z, Term.eval (fL 5) z = -(1/8) * (z (Lv 4) - c) - 3/4 * z (Lv 5) :=
    fun z => (hF z).2.2.2.2.2
  have hm : ∀ t', t' ∈ termsW Lv c u1 l1 u2 l2 → Term.eval t' ν ≤ 0 := hall
  simp only [termsW, linT, derT, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ht hm
  have hs4 : (0:ℝ) ≤ 3/4 - 1/4 := by norm_num
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  have hr4 : (0:ℝ) ≤ 1/4 := by norm_num
  have hr2 : (0:ℝ) ≤ 1/2 := by norm_num
  have k2 : (0:ℝ) ≤ 2 := by norm_num
  have k3 : (0:ℝ) ≤ 3 := by norm_num
  have km2 : (-2:ℝ) ≤ 0 := by norm_num
  have km3 : (-3:ℝ) ≤ 0 := by norm_num
  rcases ht with ((((((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl))
  · exact stayL_linLe fL fR lam dom 0 1 _ c _ hroot4 hs4 k2 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayL_linGe fL fR lam dom 0 1 _ c _ hroot4 hs4 km2 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayL_linLe fL fR lam dom 0 1 _ c _ hroot2 hs2 k3 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayL_linGe fL fR lam dom 0 1 _ c _ hroot2 hs2 km3 hfx0 hfy0 ν (hm _ (by simp))
  · exact stayL_linLe fL fR lam dom 2 3 _ c _ hroot4 hs4 k2 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayL_linGe fL fR lam dom 2 3 _ c _ hroot4 hs4 km2 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayL_linLe fL fR lam dom 2 3 _ c _ hroot2 hs2 k3 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayL_linGe fL fR lam dom 2 3 _ c _ hroot2 hs2 km3 hfx1 hfy1 ν (hm _ (by simp))
  · exact stayL_linLe fL fR lam dom 4 5 _ c _ hroot4 hs4 k2 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayL_linGe fL fR lam dom 4 5 _ c _ hroot4 hs4 km2 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayL_linLe fL fR lam dom 4 5 _ c _ hroot2 hs2 k3 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayL_linGe fL fR lam dom 4 5 _ c _ hroot2 hs2 km3 hfx2 hfy2 ν (hm _ (by simp))
  · exact stayL_derLe fL fR lam dom 0 1 _ c _ _ hroot4 hs4 k2 hr4 h1 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derGe fL fR lam dom 0 1 _ c _ _ hroot4 hs4 km2 hr4 h2 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derLe fL fR lam dom 0 1 _ c _ _ hroot2 hs2 k3 hr2 h3 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derGe fL fR lam dom 0 1 _ c _ _ hroot2 hs2 km3 hr2 h4 hfx0 hfy0 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derLe fL fR lam dom 2 3 _ c _ _ hroot4 hs4 k2 hr4 h1 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derGe fL fR lam dom 2 3 _ c _ _ hroot4 hs4 km2 hr4 h2 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derLe fL fR lam dom 2 3 _ c _ _ hroot2 hs2 k3 hr2 h3 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derGe fL fR lam dom 2 3 _ c _ _ hroot2 hs2 km3 hr2 h4 hfx1 hfy1 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derLe fL fR lam dom 4 5 _ c _ _ hroot4 hs4 k2 hr4 h1 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derGe fL fR lam dom 4 5 _ c _ _ hroot4 hs4 km2 hr4 h2 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derLe fL fR lam dom 4 5 _ c _ _ hroot2 hs2 k3 hr2 h3 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))
  · exact stayL_derGe fL fR lam dom 4 5 _ c _ _ hroot2 hs2 km3 hr2 h4 hfx2 hfy2 ν
      (hm _ (by simp)) (hm _ (by simp))


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
noncomputable def E1 (t : ℝ) : ℝ := Real.exp (-(1/2) * t)
noncomputable def E2 (t : ℝ) : ℝ := Real.exp (-(1/4) * t)

theorem hasDerivAt_E1 (t : ℝ) : HasDerivAt E1 (-(1/2) * E1 t) t := by
  have hin : HasDerivAt (fun u : ℝ => -(1/2) * u) (-(1/2)) t := by
    have h := (hasDerivAt_id t).const_mul (-(1/2 : ℝ))
    simp only [id, mul_one] at h
    exact h
  have h := (Real.hasDerivAt_exp (-(1/2) * t)).comp t hin
  rw [mul_comm] at h
  exact h

theorem hasDerivAt_E2 (t : ℝ) : HasDerivAt E2 (-(1/4) * E2 t) t := by
  have hin : HasDerivAt (fun u : ℝ => -(1/4) * u) (-(1/4)) t := by
    have h := (hasDerivAt_id t).const_mul (-(1/4 : ℝ))
    simp only [id, mul_one] at h
    exact h
  have h := (Real.hasDerivAt_exp (-(1/4) * t)).comp t hin
  rw [mul_comm] at h
  exact h

theorem E1_pos (t : ℝ) : 0 < E1 t := Real.exp_pos _
theorem E2_pos (t : ℝ) : 0 < E2 t := Real.exp_pos _
theorem E1_le (t : ℝ) (ht : 0 ≤ t) : E1 t ≤ 1 := by
  unfold E1; rw [Real.exp_le_one_iff]; linarith
theorem E2_le (t : ℝ) (ht : 0 ≤ t) : E2 t ≤ 1 := by
  unfold E2; rw [Real.exp_le_one_iff]; linarith
theorem E1_zero : E1 0 = 1 := by simp [E1]
theorem E2_zero : E2 0 = 1 := by simp [E2]

/-- The two modal coordinates of a link at set point `c`. -/
noncomputable def Q1 (c x y : ℝ) : ℝ := y + 1/4 * (x - c)
noncomputable def Q2 (c x y : ℝ) : ℝ := y + 1/2 * (x - c)

/-- The explicit link solution. -/
noncomputable def gS (c x y t : ℝ) : ℝ := c + 4 * (Q2 c x y * E2 t - Q1 c x y * E1 t)
noncomputable def rS (c x y t : ℝ) : ℝ := 2 * Q1 c x y * E1 t - Q2 c x y * E2 t

theorem gS_zero (c x y : ℝ) : gS c x y 0 = x := by
  simp only [gS, Q1, Q2, E1_zero, E2_zero]; ring
theorem rS_zero (c x y : ℝ) : rS c x y 0 = y := by
  simp only [rS, Q1, Q2, E1_zero, E2_zero]; ring

theorem gS_hasDeriv (c x y t : ℝ) : HasDerivAt (fun u => gS c x y u) (rS c x y t) t := by
  have h : HasDerivAt (fun u => c + 4 * (Q2 c x y * E2 u - Q1 c x y * E1 u))
      (4 * (Q2 c x y * (-(1/4) * E2 t) - Q1 c x y * (-(1/2) * E1 t))) t :=
    ((((hasDerivAt_E2 t).const_mul (Q2 c x y)).sub
      ((hasDerivAt_E1 t).const_mul (Q1 c x y))).const_mul 4).const_add c
  have e : rS c x y t = 4 * (Q2 c x y * (-(1/4) * E2 t) - Q1 c x y * (-(1/2) * E1 t)) := by
    simp only [rS]; ring
  rw [e]
  exact h

theorem rS_hasDeriv (c x y t : ℝ) : HasDerivAt (fun u => rS c x y u)
    (-(1/8) * (gS c x y t - c) - 3/4 * rS c x y t) t := by
  have h : HasDerivAt (fun u => 2 * Q1 c x y * E1 u - Q2 c x y * E2 u)
      (2 * Q1 c x y * (-(1/2) * E1 t) - Q2 c x y * (-(1/4) * E2 t)) t :=
    ((hasDerivAt_E1 t).const_mul (2 * Q1 c x y)).sub ((hasDerivAt_E2 t).const_mul (Q2 c x y))
  have e : -(1/8) * (gS c x y t - c) - 3/4 * rS c x y t
      = 2 * Q1 c x y * (-(1/2) * E1 t) - Q2 c x y * (-(1/4) * E2 t) := by
    simp only [gS, rS]; ring
  rw [e]
  exact h

theorem link_box (c x y t : ℝ) (ht : 0 ≤ t) (hc1 : 20 ≤ c) (hc2 : c ≤ 40)
    (a1 : Q1 c x y ≤ 2) (a2 : -2 ≤ Q1 c x y) (a3 : Q2 c x y ≤ 3) (a4 : -3 ≤ Q2 c x y) :
    (0 ≤ gS c x y t ∧ gS c x y t ≤ 60) ∧ (-10 ≤ rS c x y t ∧ rS c x y t ≤ 10) := by
  have e1p := E1_pos t
  have e2p := E2_pos t
  have e1l := E1_le t ht
  have e2l := E2_le t ht
  have b1 : Q1 c x y * E1 t ≤ 2 := by nlinarith
  have b2 : -2 ≤ Q1 c x y * E1 t := by nlinarith
  have b3 : Q2 c x y * E2 t ≤ 3 := by nlinarith
  have b4 : -3 ≤ Q2 c x y * E2 t := by nlinarith
  simp only [gS, rS]
  refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-- The explicit right solution at set point `c` from base `b` (left and Aux coordinates
frozen). -/
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

/-- The anchor's modal-coordinate bounds (the kept linear-form atoms of the right mode). -/
def QBounds (c : ℝ) (b : State (Var 6)) : Prop :=
  (Q1 c (b (Rv 0)) (b (Rv 1)) ≤ 2 ∧ -2 ≤ Q1 c (b (Rv 0)) (b (Rv 1)) ∧
    Q2 c (b (Rv 0)) (b (Rv 1)) ≤ 3 ∧ -3 ≤ Q2 c (b (Rv 0)) (b (Rv 1))) ∧
  (Q1 c (b (Rv 2)) (b (Rv 3)) ≤ 2 ∧ -2 ≤ Q1 c (b (Rv 2)) (b (Rv 3)) ∧
    Q2 c (b (Rv 2)) (b (Rv 3)) ≤ 3 ∧ -3 ≤ Q2 c (b (Rv 2)) (b (Rv 3))) ∧
  (Q1 c (b (Rv 4)) (b (Rv 5)) ≤ 2 ∧ -2 ≤ Q1 c (b (Rv 4)) (b (Rv 5)) ∧
    Q2 c (b (Rv 4)) (b (Rv 5)) ≤ 3 ∧ -3 ≤ Q2 c (b (Rv 4)) (b (Rv 5)))

theorem solΦ_box (c : ℝ) (hc1 : 20 ≤ c) (hc2 : c ≤ 40) (b : State (Var 6)) (hb : QBounds c b)
    (t : ℝ) (ht : 0 ≤ t) : Box Rv (solΦ c b t) := by
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨d1, d2, d3, d4⟩⟩ := hb
  have k0 := link_box c _ _ t ht hc1 hc2 a1 a2 a3 a4
  have k1 := link_box c _ _ t ht hc1 hc2 b1 b2 b3 b4
  have k2 := link_box c _ _ t ht hc1 hc2 d1 d2 d3 d4
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

theorem cR_terms (q : ℕ) (hq : q < 3) : (cR q).map Prod.snd =
    termsW Rv (cRc q) (cRc q + 8) (cRc q - 8) (cRc q + 6) (cRc q - 6) := by
  interval_cases q
  · rw [cR_terms0]; norm_num [cRc]
  · rw [cR_terms1]; norm_num [cRc]
  · rw [cR_terms2]; norm_num [cRc]

theorem cRc_lo (q : ℕ) : 20 ≤ cRc q := by unfold cRc; split_ifs <;> norm_num
theorem cRc_hi (q : ℕ) : cRc q ≤ 40 := by unfold cRc; split_ifs <;> norm_num

/-- The stretch of the (single) left window: the emitted cover's λ = 1. -/
noncomputable def lam (_l : ℕ) : ℝ := 1

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; norm_num

/-- **The existence residual, discharged Z3-free by the explicit solution.** From any anchor
satisfying the right mode's kept atoms, the closed-form solution of the three damped links
solves the (λ = 1) right block, freezes every other coordinate, and stays in the evolve box. -/
theorem es (q : ℕ) (hq : q < 3) (dt : ℝ) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL 0) (cR q)))
        (Formula.and domL domR)) σ →
      HExistSegB (fL 0) (fR q) (Term.const (lam 0)) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ s ΦL hs0 _ _ _ hmaskL _
  have hatoms := ((sat_FM_append g gs _ σ).mp hσ.1).2
  have hR : ∀ t ∈ termsW Rv (cRc q) (cRc q + 8) (cRc q - 8) (cRc q + 6) (cRc q - 6),
      Term.eval t σ ≤ 0 := by
    intro t ht
    apply hatoms
    unfold atomTerms
    rw [List.map_append, cR_terms q hq]
    exact List.mem_append_right _ ht
  have hbR : ∀ j : Fin 6, ΦL s (Rv j) = σ (Rv j) := by
    intro j
    rw [hmaskL s ⟨hs0, le_rfl⟩ (Rv j) (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub _ _ h
      simp [Lv, Rv, Prod.ext_iff] at hi)]
    exact Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hQ : QBounds (cRc q) (ΦL s) := by
    have m : ∀ t, t ∈ termsW Rv (cRc q) (cRc q + 8) (cRc q - 8) (cRc q + 6) (cRc q - 6) →
        Term.eval t σ ≤ 0 := hR
    simp only [termsW, linT, derT, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at m
    have a1 := m (linLe (Rv 0) (Rv 1) (1/4) (cRc q) 2) (by simp)
    have a2 := m (linGe (Rv 0) (Rv 1) (1/4) (cRc q) (-2)) (by simp)
    have a3 := m (linLe (Rv 0) (Rv 1) (1/2) (cRc q) 3) (by simp)
    have a4 := m (linGe (Rv 0) (Rv 1) (1/2) (cRc q) (-3)) (by simp)
    have b1 := m (linLe (Rv 2) (Rv 3) (1/4) (cRc q) 2) (by simp)
    have b2 := m (linGe (Rv 2) (Rv 3) (1/4) (cRc q) (-2)) (by simp)
    have b3 := m (linLe (Rv 2) (Rv 3) (1/2) (cRc q) 3) (by simp)
    have b4 := m (linGe (Rv 2) (Rv 3) (1/2) (cRc q) (-3)) (by simp)
    have d1 := m (linLe (Rv 4) (Rv 5) (1/4) (cRc q) 2) (by simp)
    have d2 := m (linGe (Rv 4) (Rv 5) (1/4) (cRc q) (-2)) (by simp)
    have d3 := m (linLe (Rv 4) (Rv 5) (1/2) (cRc q) 3) (by simp)
    have d4 := m (linGe (Rv 4) (Rv 5) (1/2) (cRc q) (-3)) (by simp)
    simp only [linLe, linGe, eval_linQ, Term.eval, AOp.interp] at a1 a2 a3 a4 b1 b2 b3 b4
    simp only [linLe, linGe, eval_linQ, Term.eval, AOp.interp] at d1 d2 d3 d4
    simp only [QBounds, Q1, Q2, hbR]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> linarith
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
    exact solΦ_box (cRc q) (cRc_lo q) (cRc_hi q) _ hQ t ht.1

/-! ## O2 for the instance: both families stay along every joint flow -/

theorem stayL (l q : ℕ) (hl : l < 1) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  obtain rfl : l = 0 := by omega
  intro a ha ν hν
  have hall : ∀ t' ∈ termsW Lv 29 37 21 35 23, Term.eval t' ν ≤ 0 := by
    rw [← cL_terms]
    intro t' ht'
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ht'
    exact (hiffL 0 (by norm_num) a' ha' ν).mp (hν a' ha')
  exact stayL_terms (fL 0) (fR q) _ _ 29 37 21 35 23 fL_field (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) a.2 (by rw [← cL_terms]; exact List.mem_map_of_mem ha) ν hall

theorem stayR (l q : ℕ) (hq : q < 3) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hall : ∀ t' ∈ termsW Rv (cRc q) (cRc q + 8) (cRc q - 8) (cRc q + 6) (cRc q - 6),
      Term.eval t' ν ≤ 0 := by
    rw [← cR_terms q hq]
    intro t' ht'
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ht'
    exact (hiffR q hq a' ha' ν).mp (hν a' ha')
  exact stayR_terms (fL l) (fR q) (lam l) (le_of_lt (lam_pos l)) _ (cRc q) _ _ _ _
    (fR_field q hq) (by ring_nf; norm_num) (by ring_nf; norm_num) (by ring_nf; norm_num)
    (by ring_nf; norm_num) a.2 (by rw [← cR_terms q hq]; exact List.mem_map_of_mem ha) ν hall

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

theorem termsW_fv (W : Fin 6 → Var 6) (c u1 l1 u2 l2 : ℝ) :
    ∀ t ∈ termsW W c u1 l1 u2 l2, ∀ x ∈ t.fv, ∃ j, x = W j := by
  intro t ht x hx
  simp only [termsW, linT, derT, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with ((((((h | h | h | h) | (h | h | h | h)) | (h | h | h | h)) | (h | h | h | h)) |
    (h | h | h | h)) | (h | h | h | h)) <;> subst h <;>
    simp only [linLe, linGe, linQ, thrLe, thrGe, Term.fv, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, or_false, false_or] at hx <;>
    first | exact ⟨_, hx⟩ | (rcases hx with hx | hx <;> exact ⟨_, hx⟩)

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
  · obtain ⟨j, rfl⟩ := termsW_fv Lv _ _ _ _ _ c hc x hx
    exact Or.inl ⟨j, rfl⟩
  · obtain ⟨j, rfl⟩ := termsW_fv Rv _ _ _ _ _ c hc x hx
    exact Or.inr ⟨j, rfl⟩

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

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
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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

theorem stayCase (l q : ℕ) (hl : l < 1) (hq : q < 3) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 6)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 6))
        (gwindowSeg (hostGuard vs 6 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM g gs) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    refine ⟨Gr_modeAt q (by omega), edge_mem q q ?_⟩
    interval_cases q <;> simp [edgeList]
  · refine gate l dt _ _ (fun hguard => ?_)
    have hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ := by
      refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
      exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
        ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
    have := respond l q hl hq dt hv [] (by simp) hanchor
    simpa [modeW, qfOf, edgeW] using this

theorem Hmulti (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ → Formula.sat (region q) σ →
      ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 6)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM g gs) env) (region (qfOf segs q)))) σ := by
  intro P hP q hq σ _ hσ hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  subst hP
  match q, hq, hreg with
  | 0, _, hreg => exact stayCase 0 0 (by norm_num) (by norm_num) dt h0 hσ hreg
  | 1, _, hreg => exact stayCase 0 1 (by norm_num) (by norm_num) dt h1 hσ hreg
  | 2, _, hreg => exact stayCase 0 2 (by norm_num) (by norm_num) dt h2 hσ hreg
  | 3, _, hreg => exact absurd hreg (not_sat_region_sink 3 (by norm_num) σ)
  | 4, _, hreg => exact absurd hreg (not_sat_region_sink 4 (by norm_num) σ)
  | 5, _, hreg => exact absurd hreg (not_sat_region_sink 5 (by norm_num) σ)

/-! ## Theorem 3 -/

/-- **`platoon3_profiles` (suite_v2), modal Theorem 3 at the declared invariant.** Left: the
guard-gated `FOLLOW` window (three follower links `g_i' = r_i`,
`r_i' = −0.125 (g_i − 29) − 0.75 r_i`, entered inside its guard); right: the six-mode
reference automaton of the file (the gap profiles `NORMAL`/`CLOSE`/`FAR`, set points
30/28/32 on the same damped law, and the AEB sinks `BRAKE1..3`; declared edges, the nine
pruned profile `→ BRAKE` edges included); the loop invariant is the declared 18-component row
(the linear forms `Δr_i + ρ_j e_i ∈ [−2ρ_j, 2ρ_j]` and `|e_i| ≤ 2`), the evolve envelope
(`g_i ∈ [0, 60]`, `r_i ∈ [−10, 10]`) on both sides, and the right mode's region — its 24
kept cut atoms (per link the linear forms `r + ρ (g − c) ∈ [−2, 2]` (ρ = 1/4) and `[−3, 3]`
(ρ = 1/2) and their derived gap bounds), the sinks excluded (the right is never in them).
The response stays in the start profile on the certified joint segment at the cover's λ = 1.
Existence is discharged Z3-free by the explicit closed-form solution of the linear right
modes (the kept linear forms keep it in the evolve box). Residuals: three stratified verdict
packs over the cut-narrowed domains (`modalVerdX`, the tool's own queries). -/
theorem platoon3_profiles_modal (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
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
    by_cases hq : q < 6
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
      rcases vars_bodyU_sub Gr _ htt hRv hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · exact hstep_assembled_multiR Gr mv (FM g gs) env region (leftProgs dt) hmvF hmvenv hmvreg
      hfresh htt hlt (hframes dt) (Hmulti dt h0 h1 h2)
  · exact hddF_multiR Gr 0 1 dt leftData region (canonInvM g gs) domL domR
      (by decide) htt hRv hL (fun q hq => region_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

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
