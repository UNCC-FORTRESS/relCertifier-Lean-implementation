/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_weak` (suite_v2) — modal Theorem 3

Adapted from `InstancesV2/Modal/Sat3wDetumbleNominal.lean` (itself from the 4-D sibling
`SatDetumbleNominal.lean`; same generic layer, same structure). Lowered at `n = 6`
(`w1, w2, w3, h1, h2, h3` at coordinates 0..5), so `mv = (Aux, 0)` and `tg = (Aux, 1)` exist
without padding. The left `DETUMBLE` mode is the three-wheel gyrostat on weakened actuators
(`k_L = 0.4`) with BILINEAR gyroscopic and wheel-coupling terms; the right automaton has three
decoupled linear design profiles `NOMINAL` (`k = 0.5`), `ECONOMY` (`0.45`), `SURVIVAL`
(`0.42`), and `SAFE`, the pruned sink (excluded by the region). One window, λ = 1, strata
order `[0, 1]` for every right profile (the emitted cover).

Kept cut atoms (`E ≤ 1` on each side and every profile, `guardConj`/`membership`/`diStrict`):
O1 from the kernel-checked extended certificate; O2 RATIONAL (no Z3): `E_R' = −2 k_q E_R`
along each right profile, `E_L' = −0.8 E_L` along the left field (the six wheel-coupling and
the gyroscopic cubic terms cancel, a ring identity).

Each non-sink right region carries, besides the kept atom, the NONBLOCKING conjunct
`⋀_i −2 ≤ c_i ≤ 2` with `c1 = h1 + 2 w1`, `c2 = h2 + 4 w2`, `c3 = h3 + 5 w3` (right state):
not a tool cut, kept out of every verdict query; see `sat3w_detumble_weak_modal`. It rides
along the segment anchor through `couple_cutX_nb`, a local copy of `CutRespond.couple_cutX`
whose anchor may carry extra, separately preserved terms (here preserved because each `c_i`
is conserved by every right profile).
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_weak

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Sat3wDetumbleWeak

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["w1", "w2", "w3", "h1", "h2", "h3"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := sat3w_detumble_weak_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := sat3w_detumble_weak_IRv2.R.modes.getD q dm

abbrev mv : Var 6 := (Side.Aux, 0)
abbrev tg : Var 6 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.R (mR q)
noncomputable def domL : Formula (Var 6) := hostEvolve vs 6 Side.L (mL 0)
noncomputable def domR : Formula (Var 6) := hostEvolve vs 6 Side.R (mR 0)
noncomputable def env : Formula (Var 6) := Formula.and domL domR

noncomputable def comps : List (Term (Var 6)) :=
  hostComps vs 6 (sat3w_detumble_weak_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 6) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 6)) := [comps.getD 1 (Term.const 0)]

noncomputable def cL (l : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.L (cutAtomsOfX sat3w_detumble_weak_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.R (cutAtomsOfX sat3w_detumble_weak_cutsV2X.R (mR q).name)

theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp025 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm025 : Run.parseRat "-0.25" = some (-(1:ℚ)/4) := by
  have h : parseQ "-0.25" = some (⟨-25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm04 : Run.parseRat "-0.4" = some (-(2:ℚ)/5) := by
  have h : parseQ "-0.4" = some (⟨-4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm02 : Run.parseRat "-0.2" = some (-(1:ℚ)/5) := by
  have h : parseQ "-0.2" = some (⟨-2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp16 : Run.parseRat "1.6" = some ((8:ℚ)/5) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm045 : Run.parseRat "-0.45" = some (-(9:ℚ)/20) := by
  have h : parseQ "-0.45" = some (⟨-45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp09 : Run.parseRat "0.9" = some ((9:ℚ)/10) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp18 : Run.parseRat "1.8" = some ((9:ℚ)/5) := by
  have h : parseQ "1.8" = some (⟨18, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp225 : Run.parseRat "2.25" = some ((9:ℚ)/4) := by
  have h : parseQ "2.25" = some (⟨225, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm042 : Run.parseRat "-0.42" = some (-(21:ℚ)/50) := by
  have h : parseQ "-0.42" = some (⟨-42, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp084 : Run.parseRat "0.84" = some ((21:ℚ)/25) := by
  have h : parseQ "0.84" = some (⟨84, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp168 : Run.parseRat "1.68" = some ((42:ℚ)/25) := by
  have h : parseQ "1.68" = some (⟨168, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp21 : Run.parseRat "2.1" = some ((21:ℚ)/10) := by
  have h : parseQ "2.1" = some (⟨21, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp2 : Run.parseRat "2" = some (2 : ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp4 : Run.parseRat "4" = some (4 : ℚ) := by
  have h : parseQ "4" = some (⟨4, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp5 : Run.parseRat "5" = some (5 : ℚ) := by
  have h : parseQ "5" = some (⟨5, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm10 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- Body energy, left / right. -/
noncomputable def EL (x : State (Var 6)) : ℝ :=
  2 * x (Lv 0) ^ 2 + 4 * x (Lv 1) ^ 2 + 5 * x (Lv 2) ^ 2
noncomputable def ER (x : State (Var 6)) : ℝ :=
  2 * x (Rv 0) ^ 2 + 4 * x (Rv 1) ^ 2 + 5 * x (Rv 2) ^ 2

theorem fL0_eval (x : State (Var 6)) : Term.eval (fL 0 0) x =
    -(1/2) * (x (Lv 1) * x (Lv 2)) + 1/2 * (x (Lv 2) * x (Lv 4))
      - 1/2 * (x (Lv 1) * x (Lv 5)) - 2/5 * x (Lv 0) := by
  simp [fL, hostDyn, mL, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp075, hp025, hpm025, hpm04, hp04, hp02, hpm02, hp08, hp16, hp20, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]
  ring
theorem fL1_eval (x : State (Var 6)) : Term.eval (fL 0 1) x =
    3/4 * (x (Lv 2) * x (Lv 0)) + 1/4 * (x (Lv 0) * x (Lv 5))
      - 1/4 * (x (Lv 2) * x (Lv 3)) - 2/5 * x (Lv 1) := by
  simp [fL, hostDyn, mL, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp075, hp025, hpm025, hpm04, hp04, hp02, hpm02, hp08, hp16, hp20, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]
  ring
theorem fL2_eval (x : State (Var 6)) : Term.eval (fL 0 2) x =
    -(2/5) * (x (Lv 0) * x (Lv 1)) + 1/5 * (x (Lv 1) * x (Lv 3))
      - 1/5 * (x (Lv 0) * x (Lv 4)) - 2/5 * x (Lv 2) := by
  simp [fL, hostDyn, mL, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp075, hp025, hpm025, hpm04, hp04, hp02, hpm02, hp08, hp16, hp20, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]
  ring
theorem fL3_eval (x : State (Var 6)) : Term.eval (fL 0 3) x = 4/5 * x (Lv 0) := by
  simp [fL, hostDyn, mL, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp075, hp025, hpm025, hpm04, hp04, hp02, hpm02, hp08, hp16, hp20, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]
theorem fL4_eval (x : State (Var 6)) : Term.eval (fL 0 4) x = 8/5 * x (Lv 1) := by
  simp [fL, hostDyn, mL, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp075, hp025, hpm025, hpm04, hp04, hp02, hpm02, hp08, hp16, hp20, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]
theorem fL5_eval (x : State (Var 6)) : Term.eval (fL 0 5) x = 2 * x (Lv 2) := by
  simp [fL, hostDyn, mL, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp075, hp025, hpm025, hpm04, hp04, hp02, hpm02, hp08, hp16, hp20, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

/-- The right profiles' gains: `NOMINAL` 0.5, `ECONOMY` 0.45, `SURVIVAL` 0.42. -/
noncomputable def kR (q : ℕ) : ℝ := if q = 0 then 1/2 else if q = 1 then 9/20 else 21/50

theorem kR_nonneg (q : ℕ) : 0 ≤ kR q := by
  unfold kR; split_ifs <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 0) x = -(kR q) * x (Rv 0) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 1) x = -(kR q) * x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 2) x = -(kR q) * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR3_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 3) x = 2 * kR q * x (Rv 0) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR4_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 4) x = 4 * kR q * x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR5_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 5) x = 5 * kR q * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

theorem sat_domL (x : State (Var 6)) :
    Formula.sat domL x ↔ (-1 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 1 ∧ -1 ≤ x (Lv 1) ∧ x (Lv 1) ≤ 1 ∧
      -1 ≤ x (Lv 2) ∧ x (Lv 2) ≤ 1 ∧ -2 ≤ x (Lv 3) ∧ x (Lv 3) ≤ 2 ∧
      -2 ≤ x (Lv 4) ∧ x (Lv 4) ≤ 2 ∧ -2 ≤ x (Lv 5) ∧ x (Lv 5) ≤ 2) := by
  simp only [domL, hostEvolve, mL, sat3w_detumble_weak_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm10, hp10, hpm20, hp20, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv,
    and_assoc]

theorem sat_domR (x : State (Var 6)) :
    Formula.sat domR x ↔ (-1 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1 ∧ -1 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 1 ∧
      -1 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 1 ∧ -2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 2 ∧
      -2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 2 ∧ -2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 2) := by
  simp only [domR, hostEvolve, mR, sat3w_detumble_weak_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm10, hp10, hpm20, hp20, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]

/-- Every right mode (the three profiles and `SAFE`) declares the same evolve envelope. -/
theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 6 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-! ## The energy as a lowered term -/

/-- `w1*w1*2 + w2*w2*4 + w3*w3*5` on side `s`, exactly as `lowerE` builds it. -/
noncomputable def enT (s : Fin 6 → Var 6) : Term (Var 6) :=
  Term.binop .add
    (Term.binop .add
      (Term.binop .mul (Term.binop .mul (Term.var (s 0)) (Term.var (s 0))) (Term.const 2))
      (Term.binop .mul (Term.binop .mul (Term.var (s 1)) (Term.var (s 1))) (Term.const 4)))
    (Term.binop .mul (Term.binop .mul (Term.var (s 2)) (Term.var (s 2))) (Term.const 5))

theorem eval_enT_L (x : State (Var 6)) : Term.eval (enT Lv) x = EL x := by
  simp [enT, Term.eval, AOp.interp, EL]; ring
theorem eval_enT_R (x : State (Var 6)) : Term.eval (enT Rv) x = ER x := by
  simp [enT, Term.eval, AOp.interp, ER]; ring

theorem comps_eq : comps =
    [Term.binop .sub (enT Lv) (Term.binop .add (enT Rv) (Term.const (1/5))),
      Term.binop .sub (enT Rv) (enT Lv)] := by
  have hdL1 : ("L_w1".drop 2).copy = "w1" := by decide
  have hdL2 : ("L_w2".drop 2).copy = "w2" := by decide
  have hdL3 : ("L_w3".drop 2).copy = "w3" := by decide
  have hdR1 : ("R_w1".drop 2).copy = "w1" := by decide
  have hdR2 : ("R_w2".drop 2).copy = "w2" := by decide
  have hdR3 : ("R_w3".drop 2).copy = "w3" := by decide
  simp [comps, hostComps, sat3w_detumble_weak_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL1, hdL2, hdL3, hdR1, hdR2, hdR3, List.findIdx?_cons, hp2,
    hp4, hp5, hp02, ITerm.toHost, Lv, Rv, enT]

theorem eval_g (x : State (Var 6)) : Term.eval g x = EL x - (ER x + 1/5) := by
  simp [g, comps_eq, Term.eval, AOp.interp, eval_enT_L, eval_enT_R]
theorem eval_gs0 (x : State (Var 6)) :
    Term.eval (gs.getD 0 (Term.const 0)) x = ER x - EL x := by
  simp [gs, comps_eq, Term.eval, AOp.interp, eval_enT_L, eval_enT_R]

def Aen : PForm := .cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1"))
  (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4")))
  (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")

theorem gL_en : hostAtomG vs 6 Side.L Aen = Term.binop .sub (enT Lv) (Term.const 1) := by
  simp [Aen, hostAtomG, cutAtomG, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, enT, Lv]
theorem gR_en : hostAtomG vs 6 Side.R Aen = Term.binop .sub (enT Rv) (Term.const 1) := by
  simp [Aen, hostAtomG, cutAtomG, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, enT, Rv]

theorem cL_0 : cL 0 = [(hostAtomF vs 6 Side.L Aen, Term.binop .sub (enT Lv) (Term.const 1))] := by
  rw [← gL_en]; rfl
/-- Each of the three profiles keeps the same atom `E_R ≤ 1`. -/
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vs 6 Side.R Aen, Term.binop .sub (enT Rv) (Term.const 1))] := by
  rw [← gR_en]; interval_cases q <;> rfl

theorem atomsNonstrictL :
    ∀ x ∈ cutAtomsOfX sat3w_detumble_weak_cutsV2X.L (mL 0).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  simp [cutAtomsOfX, sat3w_detumble_weak_cutsV2X, mL, sat3w_detumble_weak_IRv2] at hx
  rcases hx with rfl
  exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX sat3w_detumble_weak_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  interval_cases q <;>
  · simp [cutAtomsOfX, sat3w_detumble_weak_cutsV2X, mR, sat3w_detumble_weak_IRv2] at hx
    rcases hx with rfl
    exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL : AtomsIff (cL 0) := atomsIff_cutPairsX atomsNonstrictL
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) := atomsIff_cutPairsX (atomsNonstrictR q hq)

/-! ## O1: the left guard implies the left atom (the extended certificate, kernel-checked) -/

theorem hO1L : ∀ ν, Formula.sat (hostGuard vs 6 Side.L (mL 0)) ν → CutSat (cL 0) ν := by
  intro ν hν
  refine cutSatL_of_guard sat3w_detumble_weak_cutsV2X_wf (mL 0) ?_ ?_ ?_ ?_ ν hν
  · rfl
  · intro x hx
    simp [cutAtomsOfX, sat3w_detumble_weak_cutsV2X, mL, sat3w_detumble_weak_IRv2] at hx
    rcases hx with rfl
    simp
  · intro x hx
    simp [cutAtomsOfX, sat3w_detumble_weak_cutsV2X, mL, sat3w_detumble_weak_IRv2] at hx
    rcases hx with rfl
    simp [Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar, List.findIdx?_cons]
  · simp [mL, sat3w_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10, vs,
      Run.resolveVar, List.findIdx?_cons]

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

theorem hfL : ∀ i, (fL 0 i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, sat3w_detumble_weak_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe 0 i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, sat3w_detumble_weak_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, sat3w_detumble_weak_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, sat3w_detumble_weak_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL : (hostGuard vs 6 Side.L (mL 0)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL 0).guard
    (by simp [mL, sat3w_detumble_weak_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree])
    x hx)

/-! ## O2: the kept atoms stay along the joint flow (rational: the energy decays on both sides) -/

theorem enT_fv (s : Fin 6 → Var 6) : (enT s).fv ⊆ {s 0, s 1, s 2} := by
  intro x hx
  simp only [enT, Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem lie_enR (q : ℕ) (hq : q < 3) (z : State (Var 6)) :
    Term.eval (lie1R (Term.binop .sub (enT Rv) (Term.const 1)) (fR q)) z = -(2 * kR q) * ER z := by
  rw [eval_lie1R, Fin.sum_univ_six, fR0_eval q hq, fR1_eval q hq, fR2_eval q hq, fR3_eval q hq,
    fR4_eval q hq, fR5_eval q hq]
  simp [enT, tderiv, Term.eval, AOp.interp, Rv, ER]
  ring

/-- The left `DETUMBLE` field's gyroscopic and wheel-coupling terms do no work: the energy
decays exactly, `E_L' = −0.8 E_L` (the cubic cancellation — the gyroscopic `w1 w2 w3` terms
and the six wheel-coupling terms `w_i w_j h_k` — a ring identity). -/
theorem lie_enL (z : State (Var 6)) :
    Term.eval (lie1L (Term.binop .sub (enT Lv) (Term.const 1)) (fL 0)) z = -(4/5) * EL z := by
  rw [eval_lie1L, Fin.sum_univ_six, fL0_eval, fL1_eval, fL2_eval, fL3_eval, fL4_eval, fL5_eval]
  simp [enT, tderiv, Term.eval, AOp.interp, Lv, EL]
  ring

theorem EL_nonneg (z : State (Var 6)) : 0 ≤ EL z := by unfold EL; positivity
theorem ER_nonneg (z : State (Var 6)) : 0 ≤ ER z := by unfold ER; positivity

theorem stayL (q : ℕ) (lamv : ℝ) :
    AtomsStayC (cL 0) (jointSys (fL 0) (fR q) (Term.const lamv)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL a ha ν).mp (hν a ha)
  rw [cL_0, List.mem_singleton] at ha
  subst ha
  refine boxle_L_of_super _ (fL 0) (fR q) _ (Formula.and domL domR) (Formula.and domL domR)
    (fun i h => ?_) (fun x h => h) (fun z _ _ => ?_) hinit
  · rcases enT_fv Lv (by simpa [Term.fv] using h) with h | h | h <;>
      simp [Lv, Rv, Prod.ext_iff] at h
  · rw [lie_enL]; nlinarith [EL_nonneg z]

theorem stayR (q : ℕ) (hq : q < 3) (lamv : ℝ) (hc : 0 ≤ lamv) :
    AtomsStayC (cR q) (jointSys (fL 0) (fR q) (Term.const lamv)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq, List.mem_singleton] at ha
  subst ha
  refine boxle_R_of_super _ (fL 0) (fR q) lamv hc (Formula.and domL domR) _ (fun i h => ?_)
    (fun x h => h) (fun z _ _ => ?_) hinit
  · rcases enT_fv Rv (by simpa [Term.fv] using h) with h | h | h <;>
      simp [Lv, Rv, Prod.ext_iff] at h
  · rw [lie_enR q hq]; nlinarith [ER_nonneg z, kR_nonneg q, mul_nonneg (kR_nonneg q) (ER_nonneg z)]

/-! ## The nonblocking quantities `c_i = h_i + J_i w_i` (conserved by every right profile) -/

/-- `c1 = h1 + 2 w1` on the right. -/
noncomputable def c1T : Term (Var 6) :=
  Term.binop .add (Term.var (Rv 3)) (Term.binop .mul (Term.const 2) (Term.var (Rv 0)))
/-- `c2 = h2 + 4 w2` on the right. -/
noncomputable def c2T : Term (Var 6) :=
  Term.binop .add (Term.var (Rv 4)) (Term.binop .mul (Term.const 4) (Term.var (Rv 1)))
/-- `c3 = h3 + 5 w3` on the right. -/
noncomputable def c3T : Term (Var 6) :=
  Term.binop .add (Term.var (Rv 5)) (Term.binop .mul (Term.const 5) (Term.var (Rv 2)))

/-- `c − 2 ≤ 0` and `−2 − c ≤ 0`. -/
noncomputable def nbU (c : Term (Var 6)) : Term (Var 6) := Term.binop .sub c (Term.const 2)
noncomputable def nbD (c : Term (Var 6)) : Term (Var 6) := Term.binop .sub (Term.const (-2)) c
noncomputable def nbT : List (Term (Var 6)) :=
  [nbU c1T, nbD c1T, nbU c2T, nbD c2T, nbU c3T, nbD c3T]

theorem eval_c1 (x : State (Var 6)) : Term.eval c1T x = x (Rv 3) + 2 * x (Rv 0) := by
  simp [c1T, Term.eval, AOp.interp]
theorem eval_c2 (x : State (Var 6)) : Term.eval c2T x = x (Rv 4) + 4 * x (Rv 1) := by
  simp [c2T, Term.eval, AOp.interp]
theorem eval_c3 (x : State (Var 6)) : Term.eval c3T x = x (Rv 5) + 5 * x (Rv 2) := by
  simp [c3T, Term.eval, AOp.interp]
theorem eval_nbU (c : Term (Var 6)) (x : State (Var 6)) :
    Term.eval (nbU c) x = Term.eval c x - 2 := by
  simp [nbU, Term.eval, AOp.interp]
theorem eval_nbD (c : Term (Var 6)) (x : State (Var 6)) :
    Term.eval (nbD c) x = -2 - Term.eval c x := by
  simp [nbD, Term.eval, AOp.interp]

theorem nb_fv : ∀ t ∈ nbT, t.fv ⊆ range Rv := by
  intro t ht
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · intro x hx
    simp only [nbU, nbD, c1T, c2T, c3T, Term.fv, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, or_false, false_or] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩

theorem lie_nb (q : ℕ) (hq : q < 3) (t : Term (Var 6)) (ht : t ∈ nbT) (z : State (Var 6)) :
    Term.eval (lie1R t (fR q)) z = 0 := by
  rw [eval_lie1R, Fin.sum_univ_six, fR0_eval q hq, fR1_eval q hq, fR2_eval q hq, fR3_eval q hq,
    fR4_eval q hq, fR5_eval q hq]
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [nbU, nbD, c1T, c2T, c3T, tderiv, Term.eval, AOp.interp, Rv] <;> ring

/-- **Conservation**: each nonblocking term stays `≤ 0` along the joint flow (its Lie
derivative along every right profile's field is identically `0`; it reads no left
variable). -/
theorem stayNB (q : ℕ) (hq : q < 3) (lamv : ℝ) (hc : 0 ≤ lamv) : ∀ t ∈ nbT, ∀ ν,
    Term.eval t ν ≤ 0 →
    BoxLe (Program.ode (jointSys (fL 0) (fR q) (Term.const lamv)) (Formula.and domL domR))
      (fun ω => Term.eval t ω) ν := by
  intro t ht ν hinit
  refine boxle_R_of_super t (fL 0) (fR q) lamv hc (Formula.and domL domR) _ (fun i h => ?_)
    (fun x h => h) (fun z _ _ => ?_) hinit
  · obtain ⟨j, hj⟩ := nb_fv t ht h
    simp [Lv, Rv, Prod.ext_iff] at hj
  · rw [lie_nb q hq t ht z]

/-! ## Variable sides of the anchor -/

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, comps_eq, List.getD_cons_zero, List.getD_cons_succ, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  have hL : (enT Lv).fv ⊆ range Lv ∪ range Rv := fun x hx => by
    rcases enT_fv Lv hx with rfl | rfl | rfl <;> exact Or.inl ⟨_, rfl⟩
  have hR : (enT Rv).fv ⊆ range Lv ∪ range Rv := fun x hx => by
    rcases enT_fv Rv hx with rfl | rfl | rfl <;> exact Or.inr ⟨_, rfl⟩
  rcases hc with rfl | rfl
  · intro x hx
    rcases hx with hx | hx | hx
    · exact hL hx
    · exact hR hx
    · simp [Term.fv] at hx
  · intro x hx
    rcases hx with hx | hx
    · exact hR hx
    · exact hL hx

theorem atom_fv (q : ℕ) (hq : q < 3) :
    ∀ c ∈ atomTerms (cL 0) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [atomTerms, cL_0, cR_eq q hq, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · intro x hx
    rcases hx with hx | hx
    · rcases enT_fv Lv hx with rfl | rfl | rfl <;> exact Or.inl ⟨_, rfl⟩
    · simp [Term.fv] at hx
  · intro x hx
    rcases hx with hx | hx
    · rcases enT_fv Rv hx with rfl | rfl | rfl <;> exact Or.inr ⟨_, rfl⟩
    · simp [Term.fv] at hx

/-- The joint-piece anchor's terms: the invariant components, the nonblocking terms, the two
modes' kept atoms. -/
theorem anchor_fv (q : ℕ) (hq : q < 3) :
    ∀ c ∈ g :: (gs ++ nbT) ++ atomTerms (cL 0) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact comps_fv _ List.mem_cons_self
    rcases List.mem_append.mp hc with hc | hc
    · exact comps_fv _ (List.mem_cons_of_mem _ hc)
    · exact fun x hx => Or.inr (nb_fv c hc hx)
  · exact atom_fv q hq c hc

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

/-- The declared transitions, as indices (`NOMINAL` 0, `ECONOMY` 1, `SURVIVAL` 2, `SAFE` 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 0), (1, 3), (2, 2), (2, 0), (2, 3), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range sat3w_detumble_weak_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (sat3w_detumble_weak_IRv2.R.modes.findIdx (·.name == nm))))) := by
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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [edgeW, Gr]

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

/-! ## Regions -/

/-- `−2 ≤ c ≤ 2` as a formula. -/
noncomputable def bandF (c : Term (Var 6)) : Formula (Var 6) :=
  Formula.and (Formula.cmp CompOp.le c (Term.const 2))
    (Formula.cmp CompOp.le (Term.const (-2)) c)

/-- The nonblocking conjunct `⋀_i −2 ≤ c_i ≤ 2` (NOT a tool cut; see the theorem). -/
noncomputable def nbF : Formula (Var 6) :=
  Formula.and (Formula.and (bandF c1T) (bandF c2T)) (bandF c3T)

theorem sat_nbF (ν : State (Var 6)) :
    Formula.sat nbF ν ↔
      ((ν (Rv 3) + 2 * ν (Rv 0) ≤ 2 ∧ -2 ≤ ν (Rv 3) + 2 * ν (Rv 0)) ∧
        (ν (Rv 4) + 4 * ν (Rv 1) ≤ 2 ∧ -2 ≤ ν (Rv 4) + 4 * ν (Rv 1))) ∧
      (ν (Rv 5) + 5 * ν (Rv 2) ≤ 2 ∧ -2 ≤ ν (Rv 5) + 5 * ν (Rv 2)) := by
  simp only [nbF, bandF, Formula.sat, CompOp.interp, eval_c1, eval_c2, eval_c3, Term.eval]

/-- Each profile (`q < 3`): its kept cut atom (`E_R ≤ 1`) and the nonblocking conjunct;
`SAFE` (the pruned sink) is excluded. -/
noncomputable def region (q : ℕ) : Formula (Var 6) :=
  if q < 3 then Formula.and (cutF (cR q)) nbF
  else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region (q : ℕ) (hq : q < 3) (ν : State (Var 6)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν ∧ Formula.sat nbF ν := by
  simp only [region, hq, if_true, Formula.sat, sat_cutF]

theorem not_sat_region3 (ν : State (Var 6)) : ¬ Formula.sat (region 3) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem nbF_fv : nbF.fv ⊆ range Rv := by
  intro x hx
  simp only [nbF, bandF, Formula.fv, c1T, c2T, c3T, Term.fv, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false, false_or] at hx
  rcases hx with (((hx | hx) | (hx | hx)) | ((hx | hx) | (hx | hx))) | ((hx | hx) | (hx | hx)) <;>
    subst hx <;> exact ⟨_, rfl⟩

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  by_cases h3 : q < 3
  · simp only [region, h3, if_true]
    intro x hx
    rcases hx with hx | hx
    · unfold cutF at hx
      rw [cR_eq q h3] at hx
      simp only [List.foldl_cons, List.foldl_nil] at hx
      rcases hx with hx | hx
      · simp [Formula.fv] at hx
      · exact side_eq_R_mem (by
          unfold hostAtomF at hx
          exact hostForm_side (resolvesTo_R vs) _
            (by simp [Aen, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)
    · exact nbF_fv hx
  · simp only [region, h3, if_false]
    simp [Formula.fv, Term.fv]

/-! ## Existence: each right profile's flow, explicitly, from a nonblocking start

At gain `k`: `w_i(t) = w_i0 e^{−kt}`, `h_i(t) = h_i0 + J_i w_i0 (1 − e^{−kt})`
(`J = (2, 4, 5)`): the rates contract toward 0 (inside `[−1, 1]`), and
`h_i(t) = e^{−kt} h_i0 + (1 − e^{−kt}) (h_i0 + J_i w_i0)` is a convex combination of `h_i0`
and the conserved `c_i = h_i0 + J_i w_i0` — inside `[−2, 2]` exactly when the nonblocking
conjunct holds. -/

noncomputable def ex (k t : ℝ) : ℝ := Real.exp (-k * t)

noncomputable def solR (k : ℝ) (b : State (Var 6)) (t : ℝ) : State (Var 6) := fun x =>
  if x = Rv 0 then b (Rv 0) * ex k t
  else if x = Rv 1 then b (Rv 1) * ex k t
  else if x = Rv 2 then b (Rv 2) * ex k t
  else if x = Rv 3 then b (Rv 3) + 2 * b (Rv 0) * (1 - ex k t)
  else if x = Rv 4 then b (Rv 4) + 4 * b (Rv 1) * (1 - ex k t)
  else if x = Rv 5 then b (Rv 5) + 5 * b (Rv 2) * (1 - ex k t)
  else b x

theorem solR_0 (k : ℝ) (b : State (Var 6)) (t : ℝ) : solR k b t (Rv 0) = b (Rv 0) * ex k t := by
  simp [solR]
theorem solR_1 (k : ℝ) (b : State (Var 6)) (t : ℝ) : solR k b t (Rv 1) = b (Rv 1) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_2 (k : ℝ) (b : State (Var 6)) (t : ℝ) : solR k b t (Rv 2) = b (Rv 2) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_3 (k : ℝ) (b : State (Var 6)) (t : ℝ) :
    solR k b t (Rv 3) = b (Rv 3) + 2 * b (Rv 0) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_4 (k : ℝ) (b : State (Var 6)) (t : ℝ) :
    solR k b t (Rv 4) = b (Rv 4) + 4 * b (Rv 1) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_5 (k : ℝ) (b : State (Var 6)) (t : ℝ) :
    solR k b t (Rv 5) = b (Rv 5) + 5 * b (Rv 2) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (k : ℝ) (b : State (Var 6)) (t : ℝ) {x : Var 6} (hx : ∀ i, x ≠ Rv i) :
    solR k b t x = b x := by
  simp [solR, hx]

theorem ex_hasDeriv (k t : ℝ) : HasDerivAt (ex k) (-k * ex k t) t := by
  have h := ((hasDerivAt_id t).const_mul (-k)).exp
  have h' : HasDerivAt (ex k) (Real.exp (-k * id t) * (-k * 1)) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring

theorem ex_zero (k : ℝ) : ex k 0 = 1 := by simp [ex]
theorem ex_pos (k t : ℝ) : 0 < ex k t := Real.exp_pos _
theorem ex_le_one {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) : ex k t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; nlinarith

/-- A rate contracted by `e ∈ (0, 1]` stays in `[−1, 1]`. -/
theorem rate_band {w e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hl : -1 ≤ w) (hu : w ≤ 1) :
    -1 ≤ w * e ∧ w * e ≤ 1 := by
  constructor <;> nlinarith [mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 1 + w),
    mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 1 - w)]

/-- A wheel momentum `h0 + a w0 (1 − e)` (convex combination of `h0` and `h0 + a w0`) stays
in `[−2, 2]` when both ends do. -/
theorem mom_band {h a w e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hl : -2 ≤ h) (hu : h ≤ 2)
    (hcu : h + a * w ≤ 2) (hcl : -2 ≤ h + a * w) :
    -2 ≤ h + a * w * (1 - e) ∧ h + a * w * (1 - e) ≤ 2 := by
  constructor <;> nlinarith [mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 2 + h),
    mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 2 - h),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - e) (by linarith : (0:ℝ) ≤ 2 + (h + a * w)),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - e) (by linarith : (0:ℝ) ≤ 2 - (h + a * w))]

theorem solR_stays {k : ℝ} (hk : 0 ≤ k) (b : State (Var 6)) (hb : Formula.sat domR b)
    (hnb : Formula.sat nbF b) {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR k b t) := by
  rw [sat_domR] at hb ⊢
  rw [sat_nbF] at hnb
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u⟩ := hb
  obtain ⟨⟨⟨hc1u, hc1l⟩, ⟨hc2u, hc2l⟩⟩, ⟨hc3u, hc3l⟩⟩ := hnb
  have he0 := ex_pos k t
  have he1 := ex_le_one hk ht
  rw [solR_0, solR_1, solR_2, solR_3, solR_4, solR_5]
  obtain ⟨a0, b0⟩ := rate_band he0 he1 h0l h0u
  obtain ⟨a1, b1⟩ := rate_band he0 he1 h1l h1u
  obtain ⟨a2, b2⟩ := rate_band he0 he1 h2l h2u
  obtain ⟨a3, b3⟩ := mom_band he0 he1 h3l h3u hc1u hc1l
  obtain ⟨a4, b4⟩ := mom_band he0 he1 h4l h4u hc2u hc2l
  obtain ⟨a5, b5⟩ := mom_band he0 he1 h5l h5u hc3u hc3l
  exact ⟨a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5⟩

theorem rightBlock_bound_mem (q : ℕ) (i : Fin 6) :
    Rv i ∈ (rightBlock (fR q) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- A rate coordinate `w0 e^{−kt}` has derivative `−k w0 e^{−kt}`. -/
theorem rate_deriv (k w0 : ℝ) (s t : ℝ) :
    HasDerivWithinAt (fun u => w0 * ex k u) (-k * (w0 * ex k t)) (Icc 0 s) t :=
  (((ex_hasDeriv k t).const_mul w0).hasDerivWithinAt).congr_deriv (by ring)

/-- A momentum coordinate `h0 + a w0 (1 − e^{−kt})` has derivative `a k w0 e^{−kt}`. -/
theorem mom_deriv (k h0 a w0 : ℝ) (s t : ℝ) :
    HasDerivWithinAt (fun u => h0 + a * w0 * (1 - ex k u)) (a * k * (w0 * ex k t)) (Icc 0 s) t :=
  ((((ex_hasDeriv k t).const_sub 1).const_mul (a * w0)).const_add h0).hasDerivWithinAt.congr_deriv
    (by ring)

/-- **Each right profile's flow exists, domain-staying, from every nonblocking start.** -/
theorem flowR_exists (q : ℕ) (hq : q < 3) (b : State (Var 6)) (hb : Formula.sat domR b)
    (hnb : Formula.sat nbF b) (s : ℝ) (_hs : 0 ≤ s) :
    ∃ ΦR : ℝ → State (Var 6), ΦR 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const 1),
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const 1)).bound →
        ΦR t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  refine ⟨solR (kR q) b, ?_, ?_, ?_, fun t ht => solR_stays (kR_nonneg q) b hb hnb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero, mul_one]
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero, mul_one]
    by_cases h2 : x = Rv 2
    · subst h2; rw [solR_2, ex_zero, mul_one]
    by_cases h3 : x = Rv 3
    · subst h3; rw [solR_3, ex_zero]; ring
    by_cases h4 : x = Rv 4
    · subst h4; rw [solR_4, ex_zero]; ring
    by_cases h5 : x = Rv 5
    · subst h5; rw [solR_5, ex_zero]; ring
    refine solR_other _ b 0 (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    fin_cases i
    · have hf : (fun u => solR (kR q) b u (Rv 0)) = fun u => b (Rv 0) * ex (kR q) u := by
        funext u; exact solR_0 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR0_eval q hq, solR_0]
      exact (rate_deriv _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 1)) = fun u => b (Rv 1) * ex (kR q) u := by
        funext u; exact solR_1 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 1)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR1_eval q hq, solR_1]
      exact (rate_deriv _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 2)) = fun u => b (Rv 2) * ex (kR q) u := by
        funext u; exact solR_2 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR2_eval q hq, solR_2]
      exact (rate_deriv _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 3))
          = fun u => b (Rv 3) + 2 * b (Rv 0) * (1 - ex (kR q) u) := by
        funext u; exact solR_3 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 3))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 3)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR3_eval q hq, solR_0]
      exact (mom_deriv _ _ _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 4))
          = fun u => b (Rv 4) + 4 * b (Rv 1) * (1 - ex (kR q) u) := by
        funext u; exact solR_4 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 4))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 4)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR4_eval q hq, solR_1]
      exact (mom_deriv _ _ _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 5))
          = fun u => b (Rv 5) + 5 * b (Rv 2) * (1 - ex (kR q) u) := by
        funext u; exact solR_5 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 5))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 5)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR5_eval q hq, solR_2]
      exact (mom_deriv _ _ _ _ s t).congr_deriv (by ring)
  · intro t _ x hx
    refine solR_other _ b t (fun i hi => hx ?_)
    rw [hi]; exact rightBlock_bound_mem q i

/-- **Within-segment existence from a nonblocking anchor.** The left run masks the right
coordinates, so the right start of the stretched segment is the anchor's right state, in
the envelope and nonblocking; `flowR_exists` supplies the domain-staying right run. -/
theorem es (q : ℕ) (hq : q < 3) (dt : ℝ) (σ : State (Var 6)) (hdom : Formula.sat domR σ)
    (hnb : Formula.sat nbF σ) :
    HExistSegB (fL 0) (fR q) (Term.const 1) domL domR dt (Function.update σ tg 0) := by
  intro s ΦL hs0 _ _ _ hmaskL _
  have hagree : ∀ i, ΦL s (Rv i) = σ (Rv i) := by
    intro i
    rw [hmaskL s (right_mem_Icc.mpr hs0) (Rv i) (fun hb => by
      obtain ⟨j, hj⟩ := leftBlock_bound_sub (fL 0) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))]
    exact Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hdom' : Formula.sat domR (ΦL s) := by
    refine (Formula.coincidence domR (fun x hx => ?_)).mp hdom
    obtain ⟨i, rfl⟩ := hdomR hx
    exact (hagree i).symm
  have hnb' : Formula.sat nbF (ΦL s) := by
    refine (Formula.coincidence nbF (fun x hx => ?_)).mp hnb
    obtain ⟨i, rfl⟩ := nbF_fv hx
    exact (hagree i).symm
  exact flowR_exists q hq (ΦL s) hdom' hnb' s hs0

/-! ## The coupling with the nonblocking conjunct riding along

`couple_cutX` (generic) with ONE change: the anchor's term list may carry extra terms `nb`
that are NOT invariant components and NOT cut atoms (so they do not enter the verdict
queries' narrowed domain `domCutX`); their preservation is supplied separately (`hnb`). The
existence hypothesis sees the whole anchor, `nb` included. (Verbatim copy of the 4-D
sibling's local lemma.) -/
theorem couple_cutX_nb {n : ℕ} (g : Term (Var n)) (gs comps nb : List (Term (Var n)))
    (cL cR : List (CutAtomP n)) (fL fR : Fin n → Term (Var n)) (lamv : ℝ) (hlam : 0 < lamv)
    (domL domR : Formula (Var n)) (b : Fin n) (dt : ℝ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    (hcompsLR : ∀ g' ∈ g :: gs ++ atomTerms cL cR, g'.fv ⊆ range Lv ∪ range Rv)
    (hsub1 : ∀ c ∈ comps, c ∈ g :: gs) (hsub2 : ∀ g' ∈ g :: gs, g' ∈ comps ∨ g' ∈ nb)
    (hnbsub : ∀ t ∈ nb, t ∈ gs)
    (hnb : ∀ t ∈ nb, ∀ ν, (∀ t' ∈ nb, Term.eval t' ν ≤ 0) →
      BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
        (fun ω => Term.eval t ω) ν)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR)
    (hstayL : AtomsStayC cL (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hstayR : AtomsStayC cR (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hverd : VerdXCore comps fL fR lamv (domCutX (Formula.and domL domR) cL cR))
    (hES : ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms cL cR))
        (Formula.and domL domR)) σ →
      HExistSegB fL fR (Term.const lamv) domL domR dt
        (Function.update σ ((Side.Aux, b) : Var n) 0)) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms cL cR))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, b) : Var n) (leftBlock fL)) domL)
        (Program.ode (rightBlock fR (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms cL cR)) (Formula.and domL domR))
        ((Side.Aux, b) : Var n) dt (Function.update σ ((Side.Aux, b) : Var n) 0) := by
  intro σ hσ
  set tg : Var n := ((Side.Aux, b) : Var n) with htgdef
  set A := FM g (gs ++ atomTerms cL cR) with hA
  have htgA : tg ∉ (Formula.and A (Formula.and domL domR)).fv := by
    intro h
    rcases h with h | h | h
    · exact notMem_FM_fv (fun g' hg' hx => by
        rcases hcompsLR g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
        · exact aux_ne_Lv b i hi.symm
        · exact aux_ne_Rv b i hi.symm) h
    · exact aux_notin_range_Lv b (hdomL h)
    · exact aux_notin_range_Rv b (hdomR h)
  set σ' := Function.update σ tg 0 with hσ'def
  have hσ' : Formula.sat (Formula.and A (Formula.and domL domR)) σ' := by
    rwa [(Formula.coincidence (Formula.and A (Formula.and domL domR)) (fun v hv =>
      Function.update_of_ne (fun hc => htgA (by rw [← hc]; exact hv)) _ _) :
        Formula.sat (Formula.and A (Formula.and domL domR)) _ ↔ _)]
  have hnarrow : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (domCutX (Formula.and domL domR) cL cR) :=
    segPresAll_from_strata_verdicts' fL fR (Term.const lamv) _ comps hverd
  have hnarrow' : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (Formula.and (Formula.and domL domR) (Formula.and (cutF cL) (cutF cR))) := by
    refine segPresAll_congr (fun x => ?_) hnarrow
    rw [sat_domCutX]
    simp only [Formula.sat, sat_cutF]
  have hlift := segPresAll_cut_liftX hiffL hiffR hstayL hstayR hnarrow'
  obtain ⟨hFσ, hatσ⟩ := (sat_FM_append g gs _ σ').mp hσ'.1
  obtain ⟨hLσ, hRσ⟩ := (atomTerms_iff hiffL hiffR σ').mp hatσ
  have hcompsσ : ∀ c ∈ comps, Term.eval c σ' ≤ 0 :=
    fun c hc => (sat_FM_iff g gs σ').mp hFσ c (hsub1 c hc)
  have hnbσ : ∀ t ∈ nb, Term.eval t σ' ≤ 0 :=
    fun t ht => (sat_FM_iff g gs σ').mp hFσ t (List.mem_cons_of_mem _ (hnbsub t ht))
  have hboxes : ∀ g' ∈ g :: (gs ++ atomTerms cL cR), Formula.sat (Formula.box
      (Program.ode (leftBlock fL ++ rightBlock fR (Term.const lamv))
        (Formula.and domL domR)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    rw [← jointSys_split] at hω
    obtain ⟨hcω, hLω, hRω⟩ := hlift σ' hLσ hRσ hcompsσ ω hω
    have hfam : ∀ g'' ∈ g :: gs, Term.eval g'' ω ≤ 0 := by
      intro g'' hg''
      rcases hsub2 g'' hg'' with hc | hn
      · exact hcω _ hc
      · exact hnb g'' hn σ' hnbσ ω hω
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hfam _ List.mem_cons_self
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact hfam _ (List.mem_cons_of_mem _ hg')
      · exact (atomTerms_iff hiffL hiffR ω).mpr ⟨hLω, hRω⟩ g' hg'
  have hbase := segment_faModalB_from_certB_list g (gs ++ atomTerms cL cR) fL fR
    (Term.const lamv) domL domR tg dt
    (LR_blocks_disjoint _ _ _ hfL hfR (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomL hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomR hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
      exact aux_ne_Lv b i hi)
    (fun h => aux_notin_range_Lv b (leftBlock_readVars_sub fL hfL h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub fR (Term.const lamv) _ h
      exact aux_ne_Rv b i hi)
    (fun h => aux_notin_range_Rv b (rightBlock_readVars_sub fR
      (Term.const lamv) hfR (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv b (rightBlock_boundSet_sub fR (Term.const lamv) h))
    (fun h => aux_notin_range_Lv b (hdomL h))
    (fun h => aux_notin_range_Rv b (hdomR h))
    (fun g' hg' hx => by
      rcases hcompsLR g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact aux_ne_Lv b i hi.symm
      · exact aux_ne_Rv b i hi.symm)
    hboxes (by
      have := hES σ hσ
      rwa [show Function.update σ' tg 0 = σ' from by
        rw [hσ'def, Function.update_idem]] at *)
  have hupd : Function.update σ' tg (0 : ℝ) = σ' := by
    rw [hσ'def, Function.update_idem]
  rw [hupd] at hbase
  have hstr : faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
      (Program.ode (rightBlock fR (Term.const lamv)) domR)
      (Formula.and A (Formula.and domL domR)) tg dt σ' := by
    refine faModalB_strengthen_plant ?_ hbase
    intro ν μ hplant hsem
    have hdomLν : Formula.sat domL ν := sem_ode_ends_in_domain hplant.1
    have hdomRμ : Formula.sat domR μ := sem_ode_ends_in_domain hsem
    have hdomLμ : Formula.sat domL μ := by
      rwa [(Formula.coincidence domL (fun v hv' => sem_ode_mask hsem (by
        obtain ⟨i, rfl⟩ := hdomL hv'
        intro hb
        obtain ⟨j, hj⟩ := rightBlock_bound_sub fR (Term.const lamv) _ hb
        exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
          Formula.sat domL μ ↔ Formula.sat domL ν)]
    exact ⟨hdomLμ, hdomRμ⟩
  refine faModalB_monoQ ?_ hstr
  intro ν μ hsem
  exact sem_rightBlock_reparam lamv 1 hlam one_pos hsem

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- The pack for right profile `q`: left window `DETUMBLE`, right mode `q`, at the cover's
λ = 1 and strata order `[0, 1]`, over the two evolves narrowed by the two modes' kept atoms
(`E ≤ 1` each). Used for `q = 0, 1, 2` (`NOMINAL`, `ECONOMY`, `SURVIVAL`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX sat3w_detumble_weak_IRv2 sat3w_detumble_weak_cutsV2X 6 0 [0, 1] 1 l q

theorem verd_core (q : ℕ) (hq : q < 3) (h : Verd 0 q) :
    VerdXCore (g :: gs) (fL 0) (fR q) 1 (domCutX (Formula.and domL domR) (cL 0) (cR q)) := by
  interval_cases q <;> exact h

/-! ## The coupling, the window response -/

/-- The joint-piece anchor: invariant components, the nonblocking terms, both modes' atoms. -/
noncomputable def anc (q : ℕ) : Formula (Var 6) := FM g ((gs ++ nbT) ++ atomTerms (cL 0) (cR q))

theorem anc_split (q : ℕ) (hq : q < 3) (ν : State (Var 6)) : Formula.sat (anc q) ν ↔
    (Formula.sat (FM g gs) ν ∧ (∀ t ∈ nbT, Term.eval t ν ≤ 0)) ∧
      (CutSat (cL 0) ν ∧ CutSat (cR q) ν) := by
  unfold anc
  rw [sat_FM_append, sat_FM_append, atomTerms_iff hiffL (hiffR q hq)]

theorem nb_iff (ν : State (Var 6)) : (∀ t ∈ nbT, Term.eval t ν ≤ 0) ↔ Formula.sat nbF ν := by
  rw [sat_nbF]
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    eval_nbU, eval_nbD, eval_c1, eval_c2, eval_c3]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
      ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨h5, h6⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem couple (q : ℕ) (hq : q < 3) (dt : ℝ) (hv : Verd 0 q) :
    ∀ σ, Formula.sat (Formula.and (anc q) (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 6))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL 0))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (anc q) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX_nb g (gs ++ nbT) (g :: gs) nbT (cL 0) (cR q) (fL 0) (fR q) 1 one_pos domL domR
    1 dt hfL (hfR q (by omega)) hdomL hdomR (anchor_fv q hq)
    (fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hc))
    (fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inl List.mem_cons_self
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inl (List.mem_cons_of_mem _ hc)
      · exact Or.inr hc)
    (fun t ht => List.mem_append_right _ ht)
    (fun t ht ν hν => stayNB q hq 1 zero_le_one t ht ν (hν t ht))
    hiffL (hiffR q hq) (stayL q 1) (stayR q hq 1 zero_le_one) (verd_core q hq hv)
    (fun σ hσ => es q hq dt σ hσ.2.2 ((nb_iff σ).mp ((anc_split q hq σ).mp hσ.1).1.2))

theorem sat_faModal_monoPost {P Q : Program (Var 6)} {A B : Formula (Var 6)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 6)}
    (h : Formula.sat (faModal (Equiv.refl (Var 6)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (q : ℕ) (hq : q < 3) (dt : ℝ) (hv : Verd 0 q) {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (anc q) (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
      (windowSeg (leftBlock (fL 0)) domL tg dt 1)
      (bigSeq (([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
        ++ [Program.ode (rightBlock (fR q) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM g gs) env) (region q))) σ := by
  have htgF : tg ∉ (anc q).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv q hq g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL 0) domL (anc q)
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 6)))
    (by simp)
    (fun σ' hσ' => hσ'.2.1)
    (by simp)
    hfL hdomL
    [Program.ode (rightBlock (fR q) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR q, Term.const 1, domR⟩ : RepoHop 6)
        (hfR q (by omega)) (by simp [Term.fv]) hdomR hfL hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple q hq dt hv σ' hσ')
    hσ
  rw [show (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 6))).map
      (fun h => h.progR)
      = ([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from by rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨⟨hFν, hnbν⟩, -, hRν⟩ := (anc_split q hq ν).mp hν.1
  exact ⟨⟨hFν, hν.2⟩, (sat_region q hq ν).mpr ⟨hRν, (nb_iff ν).mp hnbν⟩⟩

/-! ## The step provider: stay in the start profile (`NOMINAL`, `ECONOMY` or `SURVIVAL`) -/

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
  exact ⟨hguardL, hfL, hdomL⟩

theorem hframes (dt : ℝ) : ∀ P ∈ leftProgs dt, FramesMv P mv := by
  intro P hP
  simp only [leftProgs, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg dt d.2.2.2 mv (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

theorem gate (dt : ℝ) (R : Program (Var 6)) (ψ : Formula (Var 6))
    {σ : State (Var 6)}
    (hbody : Formula.sat (hostGuard vs 6 Side.L (mL 0)) σ →
      Formula.sat (faModal (Equiv.refl (Var 6))
        (windowSeg (leftBlock (fL 0)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
      (gwindowSeg (hostGuard vs 6 Side.L (mL 0)) (leftBlock (fL 0)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

theorem stayCase (q : ℕ) (hq : q < 3) (dt : ℝ) (hv : Verd 0 q)
    {σ : State (Var 6)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 6))
        (gwindowSeg (hostGuard vs 6 Side.L (mL 0)) (leftBlock (fL 0)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM g gs) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨Gr_modeAt q (by omega),
      edge_mem q q (by interval_cases q <;> simp [edgeList])⟩
  · refine gate dt _ _ (fun hguard => ?_)
    obtain ⟨hRσ, hnbσ⟩ := (sat_region q hq σ).mp hreg
    have hanchor : Formula.sat (Formula.and (anc q) (Formula.and domL domR)) σ :=
      ⟨(anc_split q hq σ).mpr ⟨⟨hσ.1, (nb_iff σ).mpr hnbσ⟩, hO1L σ hguard, hRσ⟩, hσ.2⟩
    have := respond q hq dt hv hanchor
    simpa [modeW, qfOf, edgeW] using this

theorem Hmulti (dt : ℝ) (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) :
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
  | 0, _, hreg => exact stayCase 0 (by norm_num) dt h00 hσ hreg
  | 1, _, hreg => exact stayCase 1 (by norm_num) dt h01 hσ hreg
  | 2, _, hreg => exact stayCase 2 (by norm_num) dt h02 hσ hreg
  | 3, _, hreg => exact absurd hreg (not_sat_region3 σ)

/-! ## Theorem 3 -/

/-- **`sat3w_detumble_weak` (suite_v2), modal Theorem 3 at the declared invariant, on the
nonblocking region.** Left: the guard-gated `DETUMBLE` window (the three-wheel gyrostat on
weakened actuators, `k_L = 0.4`, with its bilinear gyroscopic and wheel couplings, entered
with `E_L ≤ 1`); right: the four-mode automaton of the file (declared edges, the pruned
`NOMINAL/ECONOMY/SURVIVAL → SAFE` included). Loop invariant: the declared row
`E_L ≤ E_R + 0.2 ∧ E_R ≤ E_L` (`E = 2 w1² + 4 w2² + 5 w3²`), the evolve envelope, and the
right mode's region. The response stays in the start profile (`NOMINAL`, `ECONOMY` or
`SURVIVAL`) on the certified joint segment at the cover's λ = 1. Residual: THREE stratified
verdict packs over the cut-narrowed domain (`modalVerdX`, the tool's own queries, narrowed by
the kept atoms `E_L ≤ 1`, `E_R ≤ 1` only), one per profile. The kept atoms' O1 is the
kernel-checked extended certificate; their O2 is rational (both energies decay,
`E_R' = −2 k_q E_R` and `E_L' = −0.8 E_L`, the left one through the exact cancellation of the
cubic gyroscopic and wheel-coupling terms).

**The region.** Each profile's region is its kept cut atom `E_R ≤ 1` AND the nonblocking
conjunct `⋀_i −2 ≤ c_i ≤ 2` on the right state, `c1 = h1 + 2 w1`, `c2 = h2 + 4 w2`,
`c3 = h3 + 5 w3`; `SAFE` (the pruned sink) is excluded. The nonblocking conjunct is NOT a
tool cut and does NOT enter any verdict query. It is there because the benchmark MODEL's
wheel-momentum bands `|h_i| ≤ 2` block right profile flows: from `h3_R = 2, w3_R = 0.4`
(other coordinates 0; energy 0.8, inside the cut) every right profile leaves `h3 ≤ 2` at once
(`h3' = 5 k w3 > 0`), so the right cannot move, while a left state with the same energy and
`h_L = 0` flows and its energy decays, breaking `E_R ≤ E_L` — with the region equal to the
cut atoms alone, this theorem is FALSE. Each `c_i` is conserved by every right profile
(`c_i' = J_i k w_i − J_i k w_i = 0`) and `h_i(t)` stays between `h_i0` and `c_i`, so the
conjunct is exactly what keeps the right flow inside the bands (existence: the explicit
solution `flowR_exists`) and it is preserved by the stay response. A property of the
benchmark MODEL (the total angular momentum about each wheel axis stays within the wheel's
momentum capacity), not of the certificate. -/
theorem sat3w_detumble_weak_modal (dt : ℝ) (h00 : Verd 0 0) (h01 : Verd 0 1)
    (h02 : Verd 0 2) :
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
  have hmvreg : ∀ q, mv ∉ (region q).fv := fun q h =>
    aux_notin_range_Rv 0 (region_fv q h)
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
      hfresh htt hlt (hframes dt) (Hmulti dt h00 h01 h02)
  · exact hddF_multiR Gr 0 1 dt leftData region (canonInvM g gs) domL domR
      (by decide) htt hRv hL (fun q _ => region_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2Sat3wDetumbleWeak
end RelCertifier
