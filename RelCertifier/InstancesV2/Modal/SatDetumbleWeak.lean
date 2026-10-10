/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_weak` (suite_v2) — modal Theorem 3

Adapted from `InstancesV2/Modal/SatDetumbleNominal.lean` (same generic layer, same structure).
Lowered at `n = 4` (`w1, w2, w3, h`), `mv = (Aux, 0)`, `tg = (Aux, 1)`. The left `DETUMBLE`
mode is the weakened gyrostat (`k_L = 0.4`, BILINEAR gyroscopic and wheel couplings); the
right automaton offers three linear detumble profiles `NOMINAL`/`ECONOMY`/`SURVIVAL`
(`w_i' = −k_q w_i`, `h' = 5 k_q w3`, `k_q = 0.5, 0.45, 0.42`) and the pruned sink `SAFE`.
One window, λ = 1, strata order `[0, 1]`, one pack per right profile.

Kept cut atoms (`E ≤ 1` on each side): O1 from the kernel-checked extended certificate; O2
RATIONAL (no Z3): `E_R' = −2 k_q E_R` along every right profile, `E_L' = −0.8 E_L` along the
left (the cubic coupling terms cancel, a ring identity).

The right region carries, besides the kept atom, the NONBLOCKING conjunct
`−2 ≤ h_R + 5 w3_R ≤ 2` (`h + 5 w3` is conserved by every right profile: `(h + 5 w3)' =
5 k_q w3 − 5 k_q w3 = 0`). It is a property of the benchmark MODEL (the total momentum about
the wheel axis stays within the wheel's capacity), not a tool cut, and enters no verdict
query; see `sat_detumble_weak_modal`. It rides along the segment anchor through
`V2SatDetumbleNominal.couple_cutX_nb`.
-/
import RelCertifier.InstancesV2.Modal.SatDetumbleNominal
import RelCertifier.InstancesV2.Cuts.sat_detumble_weak

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2SatDetumbleWeak

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["w1", "w2", "w3", "h"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := sat_detumble_weak_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := sat_detumble_weak_IRv2.R.modes.getD q dm

abbrev mv : Var 4 := (Side.Aux, 0)
abbrev tg : Var 4 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 4 → Term (Var 4) := hostDyn vs 4 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vs 4 Side.R (mR q)
noncomputable def domL : Formula (Var 4) := hostEvolve vs 4 Side.L (mL 0)
noncomputable def domR : Formula (Var 4) := hostEvolve vs 4 Side.R (mR 0)
noncomputable def env : Formula (Var 4) := Formula.and domL domR

noncomputable def comps : List (Term (Var 4)) :=
  hostComps vs 4 (sat_detumble_weak_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 4) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 4)) := [comps.getD 1 (Term.const 0)]

noncomputable def cL (l : ℕ) : List (CutAtomP 4) :=
  cutPairsX vs 4 Side.L (cutAtomsOfX sat_detumble_weak_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 4) :=
  cutPairsX vs 4 Side.R (cutAtomsOfX sat_detumble_weak_cutsV2X.R (mR q).name)

theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp025 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm04 : Run.parseRat "-0.4" = some (-(2:ℚ)/5) := by
  have h : parseQ "-0.4" = some (⟨-4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm045 : Run.parseRat "-0.45" = some (-(9:ℚ)/20) := by
  have h : parseQ "-0.45" = some (⟨-45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp225 : Run.parseRat "2.25" = some ((9:ℚ)/4) := by
  have h : parseQ "2.25" = some (⟨225, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm042 : Run.parseRat "-0.42" = some (-(21:ℚ)/50) := by
  have h : parseQ "-0.42" = some (⟨-42, 100⟩ : QF) := by decide
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
theorem hp0205 : Run.parseRat "0.205" = some ((41:ℚ)/200) := by
  have h : parseQ "0.205" = some (⟨205, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- Body energy, left / right. -/
noncomputable def EL (x : State (Var 4)) : ℝ :=
  2 * x (Lv 0) ^ 2 + 4 * x (Lv 1) ^ 2 + 5 * x (Lv 2) ^ 2
noncomputable def ER (x : State (Var 4)) : ℝ :=
  2 * x (Rv 0) ^ 2 + 4 * x (Rv 1) ^ 2 + 5 * x (Rv 2) ^ 2

theorem fL0_eval (x : State (Var 4)) : Term.eval (fL 0 0) x =
    -(1/2) * (x (Lv 1) * x (Lv 2)) - 1/2 * (x (Lv 1) * x (Lv 3)) - 2/5 * x (Lv 0) := by
  simp [fL, hostDyn, mL, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp04, hp075, hp025, hpm04, hp20, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Lv]
  ring
theorem fL1_eval (x : State (Var 4)) : Term.eval (fL 0 1) x =
    3/4 * (x (Lv 2) * x (Lv 0)) + 1/4 * (x (Lv 0) * x (Lv 3)) - 2/5 * x (Lv 1) := by
  simp [fL, hostDyn, mL, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp04, hp075, hp025, hpm04, hp20, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Lv]
theorem fL2_eval (x : State (Var 4)) : Term.eval (fL 0 2) x =
    -(2/5) * (x (Lv 0) * x (Lv 1)) - 2/5 * x (Lv 2) := by
  simp [fL, hostDyn, mL, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp04, hp075, hp025, hpm04, hp20, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Lv]
  ring
theorem fL3_eval (x : State (Var 4)) : Term.eval (fL 0 3) x = 2 * x (Lv 2) := by
  simp [fL, hostDyn, mL, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp04, hp075, hp025, hpm04, hp20, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Lv]

/-- The right profiles' rates: `NOMINAL` 0.5, `ECONOMY` 0.45, `SURVIVAL` 0.42. -/
noncomputable def kR (q : ℕ) : ℝ := if q = 1 then 9/20 else if q = 2 then 21/50 else 1/2

theorem kR_pos (q : ℕ) : 0 < kR q := by
  unfold kR; split_ifs <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 0) x = -(kR q) * x (Rv 0) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> ring
theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 1) x = -(kR q) * x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> ring
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 2) x = -(kR q) * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> ring
theorem fR3_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 3) x = 5 * kR q * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> first | ring1 | norm_num

theorem sat_domR (x : State (Var 4)) :
    Formula.sat domR x ↔ ((((((((-1 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) ∧ -1 ≤ x (Rv 1)) ∧ x (Rv 1) ≤ 1)
      ∧ -1 ≤ x (Rv 2)) ∧ x (Rv 2) ≤ 1) ∧ -2 ≤ x (Rv 3)) ∧ x (Rv 3) ≤ 2)) := by
  simp only [domR, hostEvolve, mR, sat_detumble_weak_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm10, hp10, hpm20, hp20, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 4 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-! ## The energy as a lowered term -/

noncomputable def enT (s : Fin 4 → Var 4) : Term (Var 4) :=
  Term.binop .add
    (Term.binop .add
      (Term.binop .mul (Term.binop .mul (Term.var (s 0)) (Term.var (s 0))) (Term.const 2))
      (Term.binop .mul (Term.binop .mul (Term.var (s 1)) (Term.var (s 1))) (Term.const 4)))
    (Term.binop .mul (Term.binop .mul (Term.var (s 2)) (Term.var (s 2))) (Term.const 5))

theorem eval_enT_L (x : State (Var 4)) : Term.eval (enT Lv) x = EL x := by
  simp [enT, Term.eval, AOp.interp, EL]; ring
theorem eval_enT_R (x : State (Var 4)) : Term.eval (enT Rv) x = ER x := by
  simp [enT, Term.eval, AOp.interp, ER]; ring

/-- The row `E_L ≤ E_R + 0.205 ∧ E_R ≤ E_L`, lowered. -/
theorem comps_eq : comps =
    [Term.binop .sub (enT Lv) (Term.binop .add (enT Rv) (Term.const (41/200))),
     Term.binop .sub (enT Rv) (enT Lv)] := by
  have hdL1 : ("L_w1".drop 2).copy = "w1" := by decide
  have hdL2 : ("L_w2".drop 2).copy = "w2" := by decide
  have hdL3 : ("L_w3".drop 2).copy = "w3" := by decide
  have hdR1 : ("R_w1".drop 2).copy = "w1" := by decide
  have hdR2 : ("R_w2".drop 2).copy = "w2" := by decide
  have hdR3 : ("R_w3".drop 2).copy = "w3" := by decide
  simp [comps, hostComps, sat_detumble_weak_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL1, hdL2, hdL3, hdR1, hdR2, hdR3, List.findIdx?_cons, hp2,
    hp4, hp5, hp0205, ITerm.toHost, Lv, Rv, enT]

def Aen : PForm := .cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1"))
  (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4")))
  (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")

theorem gL_en : hostAtomG vs 4 Side.L Aen = Term.binop .sub (enT Lv) (Term.const 1) := by
  simp [Aen, hostAtomG, cutAtomG, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, enT, Lv]
theorem gR_en : hostAtomG vs 4 Side.R Aen = Term.binop .sub (enT Rv) (Term.const 1) := by
  simp [Aen, hostAtomG, cutAtomG, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, enT, Rv]

theorem cL_0 : cL 0 = [(hostAtomF vs 4 Side.L Aen, Term.binop .sub (enT Lv) (Term.const 1))] := by
  rw [← gL_en]; rfl
theorem cR_q (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vs 4 Side.R Aen, Term.binop .sub (enT Rv) (Term.const 1))] := by
  rw [← gR_en]; interval_cases q <;> rfl

theorem atomsNonstrictL :
    ∀ x ∈ cutAtomsOfX sat_detumble_weak_cutsV2X.L (mL 0).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  simp [cutAtomsOfX, sat_detumble_weak_cutsV2X, mL, sat_detumble_weak_IRv2] at hx
  rcases hx with rfl
  exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX sat_detumble_weak_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, sat_detumble_weak_cutsV2X, mR, sat_detumble_weak_IRv2] at hx
    rcases hx with rfl
    exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL : AtomsIff (cL 0) := atomsIff_cutPairsX atomsNonstrictL
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) := atomsIff_cutPairsX (atomsNonstrictR q hq)

/-! ## O1: the left guard implies the left atom (the extended certificate, kernel-checked) -/

theorem hO1L : ∀ ν, Formula.sat (hostGuard vs 4 Side.L (mL 0)) ν → CutSat (cL 0) ν := by
  intro ν hν
  refine cutSatL_of_guard sat_detumble_weak_cutsV2X_wf (mL 0) ?_ ?_ ?_ ?_ ν hν
  · rfl
  · intro x hx
    simp [cutAtomsOfX, sat_detumble_weak_cutsV2X, mL, sat_detumble_weak_IRv2] at hx
    rcases hx with rfl
    simp
  · intro x hx
    simp [cutAtomsOfX, sat_detumble_weak_cutsV2X, mL, sat_detumble_weak_IRv2] at hx
    rcases hx with rfl
    simp [Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar, List.findIdx?_cons]
  · simp [mL, sat_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10, vs,
      Run.resolveVar, List.findIdx?_cons]

/-! ## Side splits -/

theorem fL_pipe (l : ℕ) (i : Fin 4) : fL l i =
    (((some (mL l)).bind (Run.dynOf vs 4 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fR_pipe (q : ℕ) (i : Fin 4) : fR q i =
    (((some (mR q)).bind (Run.dynOf vs 4 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL_pipe : domL =
    (((some (mL 0)).bind (fun m => Run.lowerF vs 4 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domR_pipe : domR =
    (((some (mR 0)).bind (fun m => Run.lowerF vs 4 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL : ∀ i, (fL 0 i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, sat_detumble_weak_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe 0 i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, sat_detumble_weak_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, sat_detumble_weak_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, sat_detumble_weak_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL : (hostGuard vs 4 Side.L (mL 0)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL 0).guard
    (by simp [mL, sat_detumble_weak_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

/-! ## O2: the kept atoms stay along the joint flows (rational: both energies decay) -/

theorem enT_fv (s : Fin 4 → Var 4) : (enT s).fv ⊆ {s 0, s 1, s 2} := by
  intro x hx
  simp only [enT, Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem lie_enR (q : ℕ) (hq : q < 3) (z : State (Var 4)) :
    Term.eval (lie1R (Term.binop .sub (enT Rv) (Term.const 1)) (fR q)) z = -(2 * kR q) * ER z := by
  rw [eval_lie1R, Fin.sum_univ_four, fR0_eval q hq, fR1_eval q hq, fR2_eval q hq,
    fR3_eval q hq]
  simp [enT, tderiv, Term.eval, AOp.interp, Rv, ER]
  ring

/-- The weakened left field's couplings do no work: `E_L' = −0.8 E_L` (the cubic
cancellation, a ring identity). -/
theorem lie_enL (z : State (Var 4)) :
    Term.eval (lie1L (Term.binop .sub (enT Lv) (Term.const 1)) (fL 0)) z = -(4/5) * EL z := by
  rw [eval_lie1L, Fin.sum_univ_four, fL0_eval, fL1_eval, fL2_eval, fL3_eval]
  simp [enT, tderiv, Term.eval, AOp.interp, Lv, EL]
  ring

theorem EL_nonneg (z : State (Var 4)) : 0 ≤ EL z := by unfold EL; positivity
theorem ER_nonneg (z : State (Var 4)) : 0 ≤ ER z := by unfold ER; positivity

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
  rw [cR_q q hq, List.mem_singleton] at ha
  subst ha
  refine boxle_R_of_super _ (fL 0) (fR q) lamv hc (Formula.and domL domR) _ (fun i h => ?_)
    (fun x h => h) (fun z _ _ => ?_) hinit
  · rcases enT_fv Rv (by simpa [Term.fv] using h) with h | h | h <;>
      simp [Lv, Rv, Prod.ext_iff] at h
  · rw [lie_enR q hq]; nlinarith [ER_nonneg z, kR_pos q]

/-! ## The nonblocking quantity `h_R + 5 w3_R` (conserved by every right profile) -/

noncomputable def hw : Term (Var 4) :=
  Term.binop .add (Term.var (Rv 3)) (Term.binop .mul (Term.const 5) (Term.var (Rv 2)))
noncomputable def nb1 : Term (Var 4) := Term.binop .sub hw (Term.const 2)
noncomputable def nb2 : Term (Var 4) := Term.binop .sub (Term.const (-2)) hw
noncomputable def nbT : List (Term (Var 4)) := [nb1, nb2]

theorem eval_hw (x : State (Var 4)) : Term.eval hw x = x (Rv 3) + 5 * x (Rv 2) := by
  simp [hw, Term.eval, AOp.interp]
theorem eval_nb1 (x : State (Var 4)) : Term.eval nb1 x = x (Rv 3) + 5 * x (Rv 2) - 2 := by
  simp [nb1, eval_hw, Term.eval, AOp.interp]
theorem eval_nb2 (x : State (Var 4)) : Term.eval nb2 x = -2 - (x (Rv 3) + 5 * x (Rv 2)) := by
  simp [nb2, eval_hw, Term.eval, AOp.interp]

theorem nb_fv : ∀ t ∈ nbT, t.fv ⊆ range Rv := by
  intro t ht
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;>
  · intro x hx
    simp only [nb1, nb2, hw, Term.fv, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, or_false, false_or] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩

theorem lie_hw (q : ℕ) (hq : q < 3) (t : Term (Var 4)) (ht : t = nb1 ∨ t = nb2)
    (z : State (Var 4)) : Term.eval (lie1R t (fR q)) z = 0 := by
  rw [eval_lie1R, Fin.sum_univ_four, fR0_eval q hq, fR1_eval q hq, fR2_eval q hq,
    fR3_eval q hq]
  rcases ht with rfl | rfl <;> simp [nb1, nb2, hw, tderiv, Term.eval, AOp.interp, Rv] <;> ring

/-- **Conservation**: each nonblocking term stays `≤ 0` along the joint flow (its Lie
derivative along every right profile is identically `0`; it reads no left variable). -/
theorem stayNB (q : ℕ) (hq : q < 3) (lamv : ℝ) (hc : 0 ≤ lamv) : ∀ t ∈ nbT, ∀ ν,
    Term.eval t ν ≤ 0 →
    BoxLe (Program.ode (jointSys (fL 0) (fR q) (Term.const lamv)) (Formula.and domL domR))
      (fun ω => Term.eval t ω) ν := by
  intro t ht ν hinit
  refine boxle_R_of_super t (fL 0) (fR q) lamv hc (Formula.and domL domR) _ (fun i h => ?_)
    (fun x h => h) (fun z _ _ => ?_) hinit
  · obtain ⟨j, hj⟩ := nb_fv t ht h
    simp [Lv, Rv, Prod.ext_iff] at hj
  · have ht' : t = nb1 ∨ t = nb2 := by simpa [nbT] using ht
    rw [lie_hw q hq t ht' z]

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
  simp only [atomTerms, cL_0, cR_q q hq, List.cons_append, List.nil_append, List.map_cons,
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

noncomputable def modeW (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 4) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

/-- The declared transitions, as indices (`NOMINAL` 0, `ECONOMY` 1, `SURVIVAL` 2, `SAFE` 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 0), (1, 3), (2, 2), (2, 0), (2, 3), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range sat_detumble_weak_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (sat_detumble_weak_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 4) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 4 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 4)} (hm : Gr.modeAt q = some m) :
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

/-- The nonblocking conjunct `−2 ≤ h_R + 5 w3_R ≤ 2` (NOT a tool cut; see the theorem). -/
noncomputable def nbF : Formula (Var 4) :=
  Formula.and (Formula.cmp CompOp.le hw (Term.const 2))
    (Formula.cmp CompOp.le (Term.const (-2)) hw)

theorem sat_nbF (ν : State (Var 4)) :
    Formula.sat nbF ν ↔ (ν (Rv 3) + 5 * ν (Rv 2) ≤ 2 ∧ -2 ≤ ν (Rv 3) + 5 * ν (Rv 2)) := by
  simp [nbF, Formula.sat, CompOp.interp, eval_hw, Term.eval]

/-- The three profiles: their kept cut atom (`E_R ≤ 1`) and the nonblocking conjunct; `SAFE`
(the pruned sink) is excluded. -/
noncomputable def region (q : ℕ) : Formula (Var 4) :=
  if q < 3 then Formula.and (cutF (cR q)) nbF
  else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 3) (ν : State (Var 4)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν ∧ Formula.sat nbF ν := by
  simp only [region, hq, if_true, Formula.sat, sat_cutF]

theorem not_sat_region_sink (q : ℕ) (hq : ¬ q < 3) (ν : State (Var 4)) :
    ¬ Formula.sat (region q) ν := by
  simp [region, hq, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  by_cases h0 : q < 3
  · simp only [region, h0, if_true]
    intro x hx
    rcases hx with hx | hx
    · unfold cutF at hx
      rw [cR_q q h0] at hx
      simp only [List.foldl_cons, List.foldl_nil] at hx
      rcases hx with hx | hx
      · simp [Formula.fv] at hx
      · exact side_eq_R_mem (by
          unfold hostAtomF at hx
          exact hostForm_side (resolvesTo_R vs) _
            (by simp [Aen, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)
    · simp only [nbF, Formula.fv, hw, Term.fv, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, or_false, false_or] at hx
      rcases hx with (hx | hx) | (hx | hx) <;> subst hx <;> exact ⟨_, rfl⟩
  · simp only [region, h0, if_false]
    simp [Formula.fv, Term.fv]

/-! ## Existence: each right profile's flow, explicitly, from a nonblocking start

`w_i(t) = w_i0 e^{−k t}`, `h(t) = h0 + 5 w3_0 (1 − e^{−k t})`: the rates contract toward 0
and `h(t)` is a convex combination of `h0` and the conserved `h0 + 5 w3_0`. -/

noncomputable def ex (k t : ℝ) : ℝ := Real.exp (-k * t)

noncomputable def solR (k : ℝ) (b : State (Var 4)) (t : ℝ) : State (Var 4) := fun x =>
  if x = Rv 0 then b (Rv 0) * ex k t
  else if x = Rv 1 then b (Rv 1) * ex k t
  else if x = Rv 2 then b (Rv 2) * ex k t
  else if x = Rv 3 then b (Rv 3) + 5 * b (Rv 2) * (1 - ex k t)
  else b x

theorem solR_0 (k : ℝ) (b : State (Var 4)) (t : ℝ) : solR k b t (Rv 0) = b (Rv 0) * ex k t := by
  simp [solR]
theorem solR_1 (k : ℝ) (b : State (Var 4)) (t : ℝ) : solR k b t (Rv 1) = b (Rv 1) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_2 (k : ℝ) (b : State (Var 4)) (t : ℝ) : solR k b t (Rv 2) = b (Rv 2) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_3 (k : ℝ) (b : State (Var 4)) (t : ℝ) :
    solR k b t (Rv 3) = b (Rv 3) + 5 * b (Rv 2) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (k : ℝ) (b : State (Var 4)) (t : ℝ) {x : Var 4} (hx : ∀ i, x ≠ Rv i) :
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

theorem solR_stays (k : ℝ) (hk : 0 ≤ k) (b : State (Var 4)) (hb : Formula.sat domR b)
    (hnb : Formula.sat nbF b) {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR k b t) := by
  rw [sat_domR] at hb ⊢
  rw [sat_nbF] at hnb
  simp only [and_assoc] at hb ⊢
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u, h3l, h3u⟩ := hb
  obtain ⟨hnu, hnl⟩ := hnb
  have he0 := ex_pos k t
  have he1 := ex_le_one hk ht
  rw [solR_0, solR_1, solR_2, solR_3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem rightBlock_bound_mem (q : ℕ) (i : Fin 4) :
    Rv i ∈ (rightBlock (fR q) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- **Each right profile's flow exists, domain-staying, from every nonblocking start.** -/
theorem flowR_exists (q : ℕ) (hq : q < 3) (b : State (Var 4)) (hb : Formula.sat domR b)
    (hnb : Formula.sat nbF b) (s : ℝ) (_hs : 0 ≤ s) :
    ∃ ΦR : ℝ → State (Var 4), ΦR 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const 1),
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const 1)).bound →
        ΦR t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  set k := kR q with hk
  have hk0 : 0 ≤ k := (kR_pos q).le
  refine ⟨solR k b, ?_, ?_, ?_, fun t ht => solR_stays k hk0 b hb hnb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero, mul_one]
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero, mul_one]
    by_cases h2 : x = Rv 2
    · subst h2; rw [solR_2, ex_zero, mul_one]
    by_cases h3 : x = Rv 3
    · subst h3; rw [solR_3, ex_zero]; ring
    refine solR_other k b 0 (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hd := ex_hasDeriv k t
    fin_cases i
    · have h := ((hd.const_mul (b (Rv 0))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR k b u (Rv 0)) = fun u => b (Rv 0) * ex k u := by
        funext u; exact solR_0 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR0_eval q hq, solR_0, ← hk]
      exact h.congr_deriv (by ring)
    · have h := ((hd.const_mul (b (Rv 1))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR k b u (Rv 1)) = fun u => b (Rv 1) * ex k u := by
        funext u; exact solR_1 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 1)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR1_eval q hq, solR_1, ← hk]
      exact h.congr_deriv (by ring)
    · have h := ((hd.const_mul (b (Rv 2))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR k b u (Rv 2)) = fun u => b (Rv 2) * ex k u := by
        funext u; exact solR_2 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR2_eval q hq, solR_2, ← hk]
      exact h.congr_deriv (by ring)
    · have h := (((hd.const_sub 1).const_mul (5 * b (Rv 2))).const_add
        (b (Rv 3))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR k b u (Rv 3)) =
          fun u => b (Rv 3) + 5 * b (Rv 2) * (1 - ex k u) := by
        funext u; exact solR_3 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 3))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 3)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR3_eval q hq, solR_2, ← hk]
      exact h.congr_deriv (by ring)
  · intro t _ x hx
    refine solR_other k b t (fun i hi => hx ?_)
    rw [hi]; exact rightBlock_bound_mem q i

/-- **Within-segment existence from a nonblocking anchor.** -/
theorem es (q : ℕ) (hq : q < 3) (dt : ℝ) (σ : State (Var 4)) (hdom : Formula.sat domR σ)
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
    rw [sat_nbF] at hnb ⊢
    rw [hagree 2, hagree 3]
    exact hnb
  exact flowR_exists q hq (ΦL s) hdom' hnb' s hs0

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `DETUMBLE`, right profile `q`, at the cover's λ = 1 and strata order
`[0, 1]`, over the two evolves narrowed by the two modes' kept atoms (`E ≤ 1` each). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX sat_detumble_weak_IRv2 sat_detumble_weak_cutsV2X 4 0 [0, 1] 1 l q

theorem verd_core (q : ℕ) (hq : q < 4) (h : Verd 0 q) :
    VerdXCore (g :: gs) (fL 0) (fR q) 1 (domCutX (Formula.and domL domR) (cL 0) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

noncomputable def anc (q : ℕ) : Formula (Var 4) := FM g ((gs ++ nbT) ++ atomTerms (cL 0) (cR q))

theorem anc_split (q : ℕ) (hq : q < 3) (ν : State (Var 4)) : Formula.sat (anc q) ν ↔
    (Formula.sat (FM g gs) ν ∧ (∀ t ∈ nbT, Term.eval t ν ≤ 0)) ∧
      (CutSat (cL 0) ν ∧ CutSat (cR q) ν) := by
  unfold anc
  rw [sat_FM_append, sat_FM_append, atomTerms_iff hiffL (hiffR q hq)]

theorem nb_iff (ν : State (Var 4)) : (∀ t ∈ nbT, Term.eval t ν ≤ 0) ↔ Formula.sat nbF ν := by
  rw [sat_nbF]
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    eval_nb1, eval_nb2]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem couple (q : ℕ) (hq : q < 3) (dt : ℝ) (hv : Verd 0 q) :
    ∀ σ, Formula.sat (Formula.and (anc q) (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 4))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL 0))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (anc q) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  V2SatDetumbleNominal.couple_cutX_nb g (gs ++ nbT) (g :: gs) nbT (cL 0) (cR q) (fL 0) (fR q)
    1 one_pos domL domR 1 dt hfL (hfR q (by omega)) hdomL hdomR (anchor_fv q hq)
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
    hiffL (hiffR q hq) (stayL q 1) (stayR q hq 1 zero_le_one) (verd_core q (by omega) hv)
    (fun σ hσ => es q hq dt σ hσ.2.2 ((nb_iff σ).mp ((anc_split q hq σ).mp hσ.1).1.2))

theorem sat_faModal_monoPost {P Q : Program (Var 4)} {A B : Formula (Var 4)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 4)}
    (h : Formula.sat (faModal (Equiv.refl (Var 4)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 4)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (q : ℕ) (hq : q < 3) (dt : ℝ) (hv : Verd 0 q) {σ : State (Var 4)}
    (hσ : Formula.sat (Formula.and (anc q) (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 4))
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
    (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 4)))
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
      exact hdisH_progR (⟨fR q, Term.const 1, domR⟩ : RepoHop 4)
        (hfR q (by omega)) (by simp [Term.fv]) hdomR hfL hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple q hq dt hv σ' hσ')
    hσ
  rw [show (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 4))).map
      (fun h => h.progR)
      = ([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from by rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨⟨hFν, hnbν⟩, -, hRν⟩ := (anc_split q hq ν).mp hν.1
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt q hq ν).mpr ⟨hRν, (nb_iff ν).mp hnbν⟩⟩

/-! ## The step provider: stay in the certified start profile -/

noncomputable def leftData : List (Formula (Var 4) × (Fin 4 → Term (Var 4))
    × Formula (Var 4) × ℕ) :=
  [(hostGuard vs 4 Side.L (mL 0), fL 0, domL, 1)]

noncomputable def leftProgs (dt : ℝ) : List (Program (Var 4)) :=
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

theorem gate (dt : ℝ) (R : Program (Var 4)) (ψ : Formula (Var 4))
    {σ : State (Var 4)}
    (hbody : Formula.sat (hostGuard vs 4 Side.L (mL 0)) σ →
      Formula.sat (faModal (Equiv.refl (Var 4))
        (windowSeg (leftBlock (fL 0)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 4))
      (gwindowSeg (hostGuard vs 4 Side.L (mL 0)) (leftBlock (fL 0)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

theorem stayCase (q : ℕ) (hq : q < 3) (dt : ℝ) (hv : Verd 0 q)
    {σ : State (Var 4)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 4))
        (gwindowSeg (hostGuard vs 4 Side.L (mL 0)) (leftBlock (fL 0)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM g gs) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    refine ⟨Gr_modeAt q (by omega), edge_mem q q ?_⟩
    interval_cases q <;> simp [edgeList]
  · refine gate dt _ _ (fun hguard => ?_)
    obtain ⟨hRσ, hnbσ⟩ := (sat_region_lt q hq σ).mp hreg
    have hanchor : Formula.sat (Formula.and (anc q) (Formula.and domL domR)) σ :=
      ⟨(anc_split q hq σ).mpr ⟨⟨hσ.1, (nb_iff σ).mpr hnbσ⟩, hO1L σ hguard, hRσ⟩, hσ.2⟩
    have := respond q hq dt hv hanchor
    simpa [modeW, qfOf, edgeW] using this

theorem Hmulti (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ → Formula.sat (region q) σ →
      ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 4)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM g gs) env) (region (qfOf segs q)))) σ := by
  intro P hP q hq σ _ hσ hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  subst hP
  match q, hq, hreg with
  | 0, _, hreg => exact stayCase 0 (by norm_num) dt h0 hσ hreg
  | 1, _, hreg => exact stayCase 1 (by norm_num) dt h1 hσ hreg
  | 2, _, hreg => exact stayCase 2 (by norm_num) dt h2 hσ hreg
  | 3, _, hreg => exact absurd hreg (not_sat_region_sink 3 (by norm_num) σ)

/-! ## Theorem 3 -/

/-- **`sat_detumble_weak` (suite_v2), modal Theorem 3 at the declared invariant, on the
nonblocking region.** Left: the guard-gated `DETUMBLE` window (the weakened gyrostat, `k_L =
0.4`, with its bilinear gyroscopic and wheel couplings, entered with `E_L ≤ 1`); right: the
four-mode automaton of the file (the linear profiles `NOMINAL`/`ECONOMY`/`SURVIVAL` and the
sink `SAFE`; declared edges, the three pruned profile `→ SAFE` edges included). Loop
invariant: the declared row `E_L ≤ E_R + 0.205 ∧ E_R ≤ E_L` (`E = 2 w1² + 4 w2² + 5 w3²`),
the evolve envelope, and the right mode's region. The response stays in the start profile
on the certified joint segment at the cover's λ = 1. Residuals: three stratified verdict
packs over the cut-narrowed domains (`modalVerdX`, the tool's own queries, narrowed by the
kept atoms `E_L ≤ 1`, `E_R ≤ 1` only).

**The region.** Each profile's region is its kept cut atom `E_R ≤ 1` AND the nonblocking
conjunct `−2 ≤ h_R + 5 w3_R ≤ 2`; `SAFE` (the pruned sink) is excluded. The nonblocking
conjunct is a property of the benchmark MODEL, not of the certificate: `h + 5 w3` is the
total angular momentum about the wheel axis (over `J3 = 5`), exactly conserved by every right
profile (`(h + 5 w3)' = 5 k w3 − 5 k w3 = 0`), and the conjunct says it stays within the
wheel's momentum capacity `|h| ≤ 2`. Without it the evolve wall `|h| ≤ 2` blocks right flows
(from `h_R = 2`, `w3_R > 0` the right cannot move while the left does), and the theorem with
the cut atoms alone as the region is FALSE. It is NOT a tool cut and enters NO verdict query;
it keeps the explicit right solution inside the band (existence, `flowR_exists`) and is
preserved by the stay response (`stayNB`). -/
theorem sat_detumble_weak_modal (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
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
      hfresh htt hlt (hframes dt) (Hmulti dt h0 h1 h2)
  · exact hddF_multiR Gr 0 1 dt leftData region (canonInvM g gs) domL domR
      (by decide) htt hRv hL (fun q _ => region_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2SatDetumbleWeak
end RelCertifier
