/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_phases` (suite_v2) — the mode-keyed Theorem 3

The 6-D lift of `sat_detumble_phases` (three reaction wheels). The file declares one
relational row per LEFT mode (`E = 2 w1² + 4 w2² + 5 w3²`): `DETUMBLE`:
`E_L ≤ E_R ∧ E_R ≤ E_L` (exact), `FINE`: `E_L ≤ E_R + 0.08 ∧ E_R ≤ E_L`. This leaf states
Theorem 3 at exactly that mode-keyed invariant, keyed by the left mode variable
`u_L = (Aux, 2)`, over the left automaton of the file's `next` lists
(`DETUMBLE → [FINE, DETUMBLE]`, `FINE → [FINE]`, each window re-testing its mode's guard)
against the right automaton of the file (`DETUMBLE`, the pruned sink `SAFE`, declared edges).
Lowered at `n = 6` (`w1, w2, w3, h1, h2, h3` at coordinates 0..5), so the three auxiliaries
`mv = (Aux, 0)`, `tg = (Aux, 1)`, `u_L = (Aux, 2)` exist without padding.

Adapted from `InstancesV2/Modal/SatDetumblePhases.lean` (the 4-D one; same structure).

Kept cut atoms (`guardConj`/`membership`/`diStrict`, emitted certificate): left `DETUMBLE`
`E_L ≤ 1`, left `FINE` `E_L ≤ 0.2`, right `DETUMBLE` `E_R ≤ 1`. O1 is the kernel-checked
extended certificate; O2 is RATIONAL (no Z3): `E_R' = −E_R` along the right field and
`E_L' = −2k E_L` along the left one (`k = 0.5` in `DETUMBLE`, `0.3` in `FINE`; the cubic
gyroscopic and three-wheel coupling terms cancel, a ring identity).

The right region of `DETUMBLE` carries, besides the kept atom, the NONBLOCKING conjunct
`⋀ᵢ −2 ≤ c_i ≤ 2` over the three right momenta `c1 = h1 + 2 w1`, `c2 = h2 + 4 w2`,
`c3 = h3 + 5 w3` (each conserved by the right flow): NOT a tool cut, kept out of every
verdict query; see `sat3w_detumble_phases_modeKeyed`.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_phases

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Sat3wDetumblePhases

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["w1", "w2", "w3", "h1", "h2", "h3"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := sat3w_detumble_phases_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := sat3w_detumble_phases_IRv2.R.modes.getD q dm

abbrev mv : Var 6 := (Side.Aux, 0)
abbrev tg : Var 6 := (Side.Aux, 1)
abbrev uL : Var 6 := (Side.Aux, 2)

noncomputable def fL (l : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.R (mR q)
noncomputable def domL : Formula (Var 6) := hostEvolve vs 6 Side.L (mL 0)
noncomputable def domR : Formula (Var 6) := hostEvolve vs 6 Side.R (mR 0)
noncomputable def env : Formula (Var 6) := Formula.and domL domR

/-- The declared row of left mode `r` (`invComponents` of `invariants.getD r`). -/
noncomputable def comps (r : ℕ) : List (Term (Var 6)) :=
  hostComps vs 6 (sat3w_detumble_phases_IRv2.invariants.getD r ("", PForm.tt)).2
noncomputable def g (r : ℕ) : Term (Var 6) := (comps r).getD 0 (Term.const 0)
noncomputable def gs (r : ℕ) : List (Term (Var 6)) := [(comps r).getD 1 (Term.const 0)]

/-- The per-left-mode host row and its relational form. -/
noncomputable def FRow (r : ℕ) : Formula (Var 6) := FM (g r) (gs r)
noncomputable def ϕRow (r : ℕ) : RFormula (Var 6) := canonInvM (g r) (gs r)

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 6)) (ϕRow r) = FRow r :=
  encode_canonInvM _ _

/-- The kept cut atoms (extended certificate) of left mode `l` / right mode `q`. -/
noncomputable def cL (l : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.L (cutAtomsOfX sat3w_detumble_phases_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs 6 Side.R (cutAtomsOfX sat3w_detumble_phases_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
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
theorem hp15 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
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
theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp008 : Run.parseRat "0.08" = some ((2:ℚ)/25) := by
  have h : parseQ "0.08" = some (⟨8, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm025 : Run.parseRat "-0.25" = some (-(1:ℚ)/4) := by
  have h : parseQ "-0.25" = some (⟨-25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm02 : Run.parseRat "-0.2" = some (-(1:ℚ)/5) := by
  have h : parseQ "-0.2" = some (⟨-2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp12 : Run.parseRat "1.2" = some ((6:ℚ)/5) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Evaluations of the lowered data -/

/-- Body energy, left / right. -/
noncomputable def EL (x : State (Var 6)) : ℝ :=
  2 * x (Lv 0) ^ 2 + 4 * x (Lv 1) ^ 2 + 5 * x (Lv 2) ^ 2
noncomputable def ER (x : State (Var 6)) : ℝ :=
  2 * x (Rv 0) ^ 2 + 4 * x (Rv 1) ^ 2 + 5 * x (Rv 2) ^ 2

/-- The left damping gain: `DETUMBLE` 0.5, `FINE` 0.3. -/
noncomputable def kL (l : ℕ) : ℝ := if l = 0 then 1/2 else 3/10

theorem fL0_eval (l : ℕ) (hl : l < 2) (x : State (Var 6)) : Term.eval (fL l 0) x =
    -(1/2) * (x (Lv 1) * x (Lv 2)) + 1/2 * (x (Lv 2) * x (Lv 4))
      - 1/2 * (x (Lv 1) * x (Lv 5)) - kL l * x (Lv 0) := by
  interval_cases l <;>
  simp [fL, hostDyn, mL, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Lv, kL] <;> ring
theorem fL1_eval (l : ℕ) (hl : l < 2) (x : State (Var 6)) : Term.eval (fL l 1) x =
    3/4 * (x (Lv 2) * x (Lv 0)) + 1/4 * (x (Lv 0) * x (Lv 5))
      - 1/4 * (x (Lv 2) * x (Lv 3)) - kL l * x (Lv 1) := by
  interval_cases l <;>
  simp [fL, hostDyn, mL, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Lv, kL] <;> ring
theorem fL2_eval (l : ℕ) (hl : l < 2) (x : State (Var 6)) : Term.eval (fL l 2) x =
    -(2/5) * (x (Lv 0) * x (Lv 1)) + 1/5 * (x (Lv 1) * x (Lv 3))
      - 1/5 * (x (Lv 0) * x (Lv 4)) - kL l * x (Lv 2) := by
  interval_cases l <;>
  simp [fL, hostDyn, mL, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Lv, kL] <;> ring

theorem fR0_eval (x : State (Var 6)) : Term.eval (fR 0 0) x = -(1/2) * x (Rv 0) := by
  simp [fR, hostDyn, mR, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
  ring
theorem fR1_eval (x : State (Var 6)) : Term.eval (fR 0 1) x = -(1/2) * x (Rv 1) := by
  simp [fR, hostDyn, mR, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
  ring
theorem fR2_eval (x : State (Var 6)) : Term.eval (fR 0 2) x = -(1/2) * x (Rv 2) := by
  simp [fR, hostDyn, mR, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
  ring
theorem fR3_eval (x : State (Var 6)) : Term.eval (fR 0 3) x = 1 * x (Rv 0) := by
  simp [fR, hostDyn, mR, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
theorem fR4_eval (x : State (Var 6)) : Term.eval (fR 0 4) x = 2 * x (Rv 1) := by
  simp [fR, hostDyn, mR, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
theorem fR5_eval (x : State (Var 6)) : Term.eval (fR 0 5) x = 5/2 * x (Rv 2) := by
  simp [fR, hostDyn, mR, sat3w_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp05,
    hp03, hp075, hp025, hpm025, hpm04, hp02, hpm02, hp25, hp15, hp10, hp20, hp06, hp12,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domR (x : State (Var 6)) :
    Formula.sat domR x ↔ ((((((((((((-1 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1) ∧ -1 ≤ x (Rv 1))
      ∧ x (Rv 1) ≤ 1) ∧ -1 ≤ x (Rv 2)) ∧ x (Rv 2) ≤ 1) ∧ -2 ≤ x (Rv 3)) ∧ x (Rv 3) ≤ 2)
      ∧ -2 ≤ x (Rv 4)) ∧ x (Rv 4) ≤ 2) ∧ -2 ≤ x (Rv 5)) ∧ x (Rv 5) ≤ 2)) := by
  simp only [domR, hostEvolve, mR, sat3w_detumble_phases_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm10, hp10, hpm20, hp20, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 2) : hostEvolve vs 6 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 2) : hostEvolve vs 6 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-! ## The energy as a lowered term; the declared rows -/

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

theorem comps_eq0 : comps 0 =
    [Term.binop .sub (enT Lv) (enT Rv), Term.binop .sub (enT Rv) (enT Lv)] := by
  have hdL1 : ("L_w1".drop 2).copy = "w1" := by decide
  have hdL2 : ("L_w2".drop 2).copy = "w2" := by decide
  have hdL3 : ("L_w3".drop 2).copy = "w3" := by decide
  have hdR1 : ("R_w1".drop 2).copy = "w1" := by decide
  have hdR2 : ("R_w2".drop 2).copy = "w2" := by decide
  have hdR3 : ("R_w3".drop 2).copy = "w3" := by decide
  simp [comps, hostComps, sat3w_detumble_phases_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL1, hdL2, hdL3, hdR1, hdR2, hdR3, List.findIdx?_cons, hp2,
    hp4, hp5, ITerm.toHost, Lv, Rv, enT]

theorem comps_eq1 : comps 1 =
    [Term.binop .sub (enT Lv) (Term.binop .add (enT Rv) (Term.const (2/25))),
     Term.binop .sub (enT Rv) (enT Lv)] := by
  have hdL1 : ("L_w1".drop 2).copy = "w1" := by decide
  have hdL2 : ("L_w2".drop 2).copy = "w2" := by decide
  have hdL3 : ("L_w3".drop 2).copy = "w3" := by decide
  have hdR1 : ("R_w1".drop 2).copy = "w1" := by decide
  have hdR2 : ("R_w2".drop 2).copy = "w2" := by decide
  have hdR3 : ("R_w3".drop 2).copy = "w3" := by decide
  simp [comps, hostComps, sat3w_detumble_phases_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL1, hdL2, hdL3, hdR1, hdR2, hdR3, List.findIdx?_cons, hp2,
    hp4, hp5, hp008, ITerm.toHost, Lv, Rv, enT]

/-- The row slack: `DETUMBLE` 0 (exact), `FINE` 0.08. -/
noncomputable def slack (r : ℕ) : ℝ := if r = 0 then 0 else 2/25

theorem eval_g (r : ℕ) (hr : r < 2) (x : State (Var 6)) :
    Term.eval (g r) x = EL x - (ER x + slack r) := by
  interval_cases r
  · simp [g, comps_eq0, Term.eval, AOp.interp, eval_enT_L, eval_enT_R, slack]
  · simp [g, comps_eq1, Term.eval, AOp.interp, eval_enT_L, eval_enT_R, slack]

theorem eval_gs0 (r : ℕ) (hr : r < 2) (x : State (Var 6)) :
    Term.eval ((gs r).getD 0 (Term.const 0)) x = ER x - EL x := by
  interval_cases r
  · simp [gs, comps_eq0, Term.eval, AOp.interp, eval_enT_L, eval_enT_R]
  · simp [gs, comps_eq1, Term.eval, AOp.interp, eval_enT_L, eval_enT_R]

theorem sat_FRow (r : ℕ) (hr : r < 2) (ν : State (Var 6)) :
    Formula.sat (FRow r) ν ↔ (EL ν ≤ ER ν + slack r ∧ ER ν ≤ EL ν) := by
  rw [FRow, sat_FM_iff]
  have h1 := eval_g r hr ν
  have h2 := eval_gs0 r hr ν
  simp only [gs, List.getD_cons_zero] at h2
  constructor
  · intro h
    have a := h (g r) List.mem_cons_self
    have b := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [h1] at a; rw [h2] at b
    constructor <;> linarith
  · rintro ⟨a, b⟩ c hc
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [h1]; linarith
    · rw [h2]; linarith

/-- The window's row is the left mode's own declared row (by name, as the tool reads it). -/
theorem invRow_faithful (l : ℕ) (hl : l < 2) :
    Handoff.invRowOf sat3w_detumble_phases_IRv2 (mL l)
      = some (sat3w_detumble_phases_IRv2.invariants.getD l ("", PForm.tt)).2 := by
  interval_cases l <;> decide

theorem enT_fv (s : Fin 6 → Var 6) : (enT s).fv ⊆ {s 0, s 1, s 2} := by
  intro x hx
  simp only [enT, Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem enT_fv_L : (enT Lv).fv ⊆ range Lv ∪ range Rv := fun x hx => by
  rcases enT_fv Lv hx with rfl | rfl | rfl <;> exact Or.inl ⟨_, rfl⟩
theorem enT_fv_R : (enT Rv).fv ⊆ range Lv ∪ range Rv := fun x hx => by
  rcases enT_fv Rv hx with rfl | rfl | rfl <;> exact Or.inr ⟨_, rfl⟩

theorem comps_fv (r : ℕ) (hr : r < 2) : ∀ c ∈ g r :: gs r, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  interval_cases r <;>
  · simp only [g, gs, comps_eq0, comps_eq1, List.getD_cons_zero, List.getD_cons_succ,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    first
    | exact Set.union_subset enT_fv_L enT_fv_R
    | exact Set.union_subset enT_fv_R enT_fv_L
    | exact Set.union_subset enT_fv_L (Set.union_subset enT_fv_R (by simp [Term.fv]))

/-- Past the declared rows the lookup falls back to `tt`, which has no components. -/
theorem comps_nil (r : ℕ) (hr : 2 ≤ r) : comps r = [] := by
  unfold comps
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by simp [sat3w_detumble_phases_IRv2]; omega)]
  simp [hostComps, Oracle.invComponents]

theorem comps_fv_all (r : ℕ) : ∀ c ∈ g r :: gs r, c.fv ⊆ range Lv ∪ range Rv := by
  by_cases hr : r < 2
  · exact comps_fv r hr
  · intro c hc
    simp only [g, gs, comps_nil r (by omega), List.getD_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_self] at hc
    subst hc
    simp [Term.fv]

theorem aux_notin_FRow (a : Fin 6) (r : ℕ) :
    ((Side.Aux, a) : Var 6) ∉ (FRow r).fv :=
  notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv_all r g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The cut atoms, concretely -/

/-- `E ≤ 1.0` (left `DETUMBLE`, right `DETUMBLE`). -/
def Aen1 : PForm := .cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1"))
  (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4")))
  (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")
/-- `E ≤ 0.2` (left `FINE`). -/
def Aen02 : PForm := .cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1"))
  (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4")))
  (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "0.2")

/-- The left cap: `DETUMBLE` 1, `FINE` 0.2. -/
noncomputable def capL (l : ℕ) : ℝ := if l = 0 then 1 else 1/5

theorem gL_en1 : hostAtomG vs 6 Side.L Aen1 = Term.binop .sub (enT Lv) (Term.const 1) := by
  simp [Aen1, hostAtomG, cutAtomG, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, enT, Lv]
theorem gL_en02 : hostAtomG vs 6 Side.L Aen02 =
    Term.binop .sub (enT Lv) (Term.const (1/5)) := by
  simp [Aen02, hostAtomG, cutAtomG, Run.lowerE, hp2, hp4, hp5, hp02, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, enT, Lv]
theorem gR_en1 : hostAtomG vs 6 Side.R Aen1 = Term.binop .sub (enT Rv) (Term.const 1) := by
  simp [Aen1, hostAtomG, cutAtomG, Run.lowerE, hp2, hp4, hp5, hp10, vs, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, enT, Rv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 6 Side.L Aen1, Term.binop .sub (enT Lv) (Term.const 1))] := by
  rw [← gL_en1]; rfl
theorem cL_1 : cL 1 =
    [(hostAtomF vs 6 Side.L Aen02, Term.binop .sub (enT Lv) (Term.const (1/5)))] := by
  rw [← gL_en02]; rfl
theorem cR_0 : cR 0 =
    [(hostAtomF vs 6 Side.R Aen1, Term.binop .sub (enT Rv) (Term.const 1))] := by
  rw [← gR_en1]; rfl

theorem cL_val (l : ℕ) (hl : l < 2) : ∃ A : PForm, cL l =
    [(hostAtomF vs 6 Side.L A, Term.binop .sub (enT Lv) (Term.const (capL l)))] := by
  interval_cases l
  · exact ⟨Aen1, by rw [cL_0]; simp [capL]⟩
  · exact ⟨Aen02, by rw [cL_1]; simp [capL]⟩

theorem atomsNonstrictL (l : ℕ) (hl : l < 2) :
    ∀ x ∈ cutAtomsOfX sat3w_detumble_phases_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, sat3w_detumble_phases_cutsV2X, mL, sat3w_detumble_phases_IRv2] at hx
    rcases hx with rfl
    exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR :
    ∀ x ∈ cutAtomsOfX sat3w_detumble_phases_cutsV2X.R (mR 0).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  simp [cutAtomsOfX, sat3w_detumble_phases_cutsV2X, mR, sat3w_detumble_phases_IRv2] at hx
  rcases hx with rfl
  exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 2) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR : AtomsIff (cR 0) := atomsIff_cutPairsX atomsNonstrictR

/-! ## O1: the left guard implies the left atom (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 2) :
    ∀ ν, Formula.sat (hostGuard vs 6 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard sat3w_detumble_phases_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, sat3w_detumble_phases_cutsV2X, mL, sat3w_detumble_phases_IRv2] at hx
      rcases hx with rfl
      simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, sat3w_detumble_phases_cutsV2X, mL, sat3w_detumble_phases_IRv2] at hx
      rcases hx with rfl
      simp [Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10, hp02, vs, Run.resolveVar,
        List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, sat3w_detumble_phases_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10, hp02,
        vs, Run.resolveVar, List.findIdx?_cons]

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
    (by interval_cases l <;> simp [mL, sat3w_detumble_phases_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 2) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, sat3w_detumble_phases_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, sat3w_detumble_phases_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, sat3w_detumble_phases_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 2) : (hostGuard vs 6 Side.L (mL l)).fv ⊆ range Lv :=
  hostGuard_fv_L vs (mL l) (by
    interval_cases l <;>
      simp [mL, sat3w_detumble_phases_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree])

/-! ## O2: the kept atoms stay along the joint flows (rational: the energies decay) -/

theorem lie_enR (c : ℝ) (z : State (Var 6)) :
    Term.eval (lie1R (Term.binop .sub (enT Rv) (Term.const c)) (fR 0)) z = -ER z := by
  rw [eval_lie1R, Fin.sum_univ_six, fR0_eval, fR1_eval, fR2_eval, fR3_eval, fR4_eval,
    fR5_eval]
  simp [enT, tderiv, Term.eval, AOp.interp, Rv, ER]
  ring

/-- The left fields' gyroscopic and three-wheel coupling terms do no work: the energy decays
exactly, `E_L' = −2 k E_L` (the cubic cancellation, a ring identity), in both left modes. -/
theorem lie_enL (l : ℕ) (hl : l < 2) (c : ℝ) (z : State (Var 6)) :
    Term.eval (lie1L (Term.binop .sub (enT Lv) (Term.const c)) (fL l)) z
      = -(2 * kL l) * EL z := by
  rw [eval_lie1L, Fin.sum_univ_six, fL0_eval l hl, fL1_eval l hl, fL2_eval l hl]
  simp [enT, tderiv, Term.eval, AOp.interp, Lv, EL]
  ring

theorem EL_nonneg (z : State (Var 6)) : 0 ≤ EL z := by unfold EL; positivity
theorem ER_nonneg (z : State (Var 6)) : 0 ≤ ER z := by unfold ER; positivity
theorem kL_pos (l : ℕ) : 0 < kL l := by unfold kL; split_ifs <;> norm_num

theorem stayL (l : ℕ) (hl : l < 2) (lamv : ℝ) :
    AtomsStayC (cL l) (jointSys (fL l) (fR 0) (Term.const lamv)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  obtain ⟨A, hA⟩ := cL_val l hl
  rw [hA, List.mem_singleton] at ha
  subst ha
  refine boxle_L_of_super _ (fL l) (fR 0) _ (Formula.and domL domR) (Formula.and domL domR)
    (fun i h => ?_) (fun x h => h) (fun z _ _ => ?_) hinit
  · rcases enT_fv Lv (by simpa [Term.fv] using h) with h | h | h <;>
      simp [Lv, Rv, Prod.ext_iff] at h
  · rw [lie_enL l hl]
    have := kL_pos l
    have := EL_nonneg z
    nlinarith

theorem stayR (l : ℕ) (lamv : ℝ) (hc : 0 ≤ lamv) :
    AtomsStayC (cR 0) (jointSys (fL l) (fR 0) (Term.const lamv)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR a ha ν).mp (hν a ha)
  rw [cR_0, List.mem_singleton] at ha
  subst ha
  refine boxle_R_of_super _ (fL l) (fR 0) lamv hc (Formula.and domL domR) _ (fun i h => ?_)
    (fun x h => h) (fun z _ _ => ?_) hinit
  · rcases enT_fv Rv (by simpa [Term.fv] using h) with h | h | h <;>
      simp [Lv, Rv, Prod.ext_iff] at h
  · rw [lie_enR]; linarith [ER_nonneg z]

/-! ## The nonblocking momenta `c1 = h1 + 2 w1`, `c2 = h2 + 4 w2`, `c3 = h3 + 5 w3`
(right side; each conserved by the right `DETUMBLE` flow) -/

/-- `h_j + a w_i` on the right (`h_j` at coordinate `j`, `w_i` at `i`). -/
noncomputable def cw (j : Fin 6) (a : ℝ) (i : Fin 6) : Term (Var 6) :=
  Term.binop .add (Term.var (Rv j)) (Term.binop .mul (Term.const a) (Term.var (Rv i)))
noncomputable def c1 : Term (Var 6) := cw 3 2 0
noncomputable def c2 : Term (Var 6) := cw 4 4 1
noncomputable def c3 : Term (Var 6) := cw 5 5 2
/-- `c − 2 ≤ 0`. -/
noncomputable def nbU (c : Term (Var 6)) : Term (Var 6) := Term.binop .sub c (Term.const 2)
/-- `−2 − c ≤ 0`. -/
noncomputable def nbD (c : Term (Var 6)) : Term (Var 6) := Term.binop .sub (Term.const (-2)) c
noncomputable def nbT : List (Term (Var 6)) :=
  [nbU c1, nbD c1, nbU c2, nbD c2, nbU c3, nbD c3]

theorem eval_cw (j : Fin 6) (a : ℝ) (i : Fin 6) (x : State (Var 6)) :
    Term.eval (cw j a i) x = x (Rv j) + a * x (Rv i) := by
  simp [cw, Term.eval, AOp.interp]
theorem eval_nbU (c : Term (Var 6)) (x : State (Var 6)) :
    Term.eval (nbU c) x = Term.eval c x - 2 := by
  simp [nbU, Term.eval, AOp.interp]
theorem eval_nbD (c : Term (Var 6)) (x : State (Var 6)) :
    Term.eval (nbD c) x = -2 - Term.eval c x := by
  simp [nbD, Term.eval, AOp.interp]

theorem cw_fv (j : Fin 6) (a : ℝ) (i : Fin 6) : (cw j a i).fv ⊆ range Rv := by
  intro x hx
  simp only [cw, Term.fv, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, or_false, false_or] at hx
  rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩

theorem nb_fv : ∀ t ∈ nbT, t.fv ⊆ range Rv := by
  intro t ht
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · intro x hx
    simp only [nbU, nbD, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
      false_or] at hx
    exact cw_fv _ _ _ hx

theorem lie_hw (t : Term (Var 6)) (ht : t ∈ nbT) (z : State (Var 6)) :
    Term.eval (lie1R t (fR 0)) z = 0 := by
  rw [eval_lie1R, Fin.sum_univ_six, fR0_eval, fR1_eval, fR2_eval, fR3_eval, fR4_eval,
    fR5_eval]
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [nbU, nbD, c1, c2, c3, cw, tderiv, Term.eval, AOp.interp, Rv] <;> ring

/-- **Conservation**: each nonblocking term stays `≤ 0` along the joint flow (its Lie
derivative along the right `DETUMBLE` field is identically `0`; it reads no left variable),
whatever the left field. -/
theorem stayNB (l : ℕ) (lamv : ℝ) (hc : 0 ≤ lamv) : ∀ t ∈ nbT, ∀ ν, Term.eval t ν ≤ 0 →
    BoxLe (Program.ode (jointSys (fL l) (fR 0) (Term.const lamv)) (Formula.and domL domR))
      (fun ω => Term.eval t ω) ν := by
  intro t ht ν hinit
  refine boxle_R_of_super t (fL l) (fR 0) lamv hc (Formula.and domL domR) _ (fun i h => ?_)
    (fun x h => h) (fun z _ _ => ?_) hinit
  · obtain ⟨j, hj⟩ := nb_fv t ht h
    simp [Lv, Rv, Prod.ext_iff] at hj
  · rw [lie_hw t ht z]

/-! ## Variable sides of the anchor -/

theorem atom_fv (l : ℕ) (hl : l < 2) :
    ∀ c ∈ atomTerms (cL l) (cR 0), c.fv ⊆ range Lv ∪ range Rv := by
  obtain ⟨A, hA⟩ := cL_val l hl
  intro c hc
  simp only [atomTerms, hA, cR_0, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · intro x hx
    rcases hx with hx | hx
    · exact enT_fv_L hx
    · simp [Term.fv] at hx
  · intro x hx
    rcases hx with hx | hx
    · exact enT_fv_R hx
    · simp [Term.fv] at hx

/-- The joint-piece anchor's terms: the row's components, the six nonblocking terms, the two
modes' kept atoms. -/
theorem anchor_fv (l : ℕ) (hl : l < 2) :
    ∀ c ∈ g l :: (gs l ++ nbT) ++ atomTerms (cL l) (cR 0), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact comps_fv l hl _ List.mem_cons_self
    rcases List.mem_append.mp hc with hc | hc
    · exact comps_fv l hl _ (List.mem_cons_of_mem _ hc)
    · exact fun x hx => Or.inr (nb_fv c hc hx)
  · exact atom_fv l hl c hc

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

/-- The declared transitions, as indices (`DETUMBLE` 0, `SAFE` 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range sat3w_detumble_phases_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (sat3w_detumble_phases_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 2 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 6)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

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
  rcases hp with rfl | rfl | rfl <;> simp [edgeW, Gr]

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

/-- `−2 ≤ c ≤ 2`. -/
noncomputable def nbPair (c : Term (Var 6)) : Formula (Var 6) :=
  Formula.and (Formula.cmp CompOp.le c (Term.const 2))
    (Formula.cmp CompOp.le (Term.const (-2)) c)

/-- The nonblocking conjunct `⋀ᵢ −2 ≤ c_i ≤ 2` (NOT a tool cut; see the theorem). -/
noncomputable def nbF : Formula (Var 6) :=
  Formula.and (nbPair c1) (Formula.and (nbPair c2) (nbPair c3))

theorem sat_nbF (ν : State (Var 6)) :
    Formula.sat nbF ν ↔
      ((ν (Rv 3) + 2 * ν (Rv 0) ≤ 2 ∧ -2 ≤ ν (Rv 3) + 2 * ν (Rv 0)) ∧
       (ν (Rv 4) + 4 * ν (Rv 1) ≤ 2 ∧ -2 ≤ ν (Rv 4) + 4 * ν (Rv 1)) ∧
       (ν (Rv 5) + 5 * ν (Rv 2) ≤ 2 ∧ -2 ≤ ν (Rv 5) + 5 * ν (Rv 2))) := by
  simp [nbF, nbPair, c1, c2, c3, Formula.sat, CompOp.interp, eval_cw, Term.eval]

/-- `DETUMBLE`: its kept cut atom (`E_R ≤ 1`) and the nonblocking conjunct; `SAFE` (the
pruned sink) is excluded. -/
noncomputable def region (q : ℕ) : Formula (Var 6) :=
  if q = 0 then Formula.and (cutF (cR 0)) nbF
  else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region0 (ν : State (Var 6)) :
    Formula.sat (region 0) ν ↔ CutSat (cR 0) ν ∧ Formula.sat nbF ν := by
  simp only [region, if_true, Formula.sat, sat_cutF]

theorem not_sat_region1 (ν : State (Var 6)) : ¬ Formula.sat (region 1) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem nbPair_fv (j : Fin 6) (a : ℝ) (i : Fin 6) : (nbPair (cw j a i)).fv ⊆ range Rv := by
  intro x hx
  simp only [nbPair, Formula.fv, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
    false_or] at hx
  rcases hx with hx | hx <;> exact cw_fv _ _ _ hx

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  by_cases h0 : q = 0
  · subst h0
    simp only [region, if_true]
    intro x hx
    rcases hx with hx | hx
    · unfold cutF at hx
      rw [cR_0] at hx
      simp only [List.foldl_cons, List.foldl_nil] at hx
      rcases hx with hx | hx
      · simp [Formula.fv] at hx
      · exact side_eq_R_mem (by
          unfold hostAtomF at hx
          exact hostForm_side (resolvesTo_R vs) _
            (by simp [Aen1, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)
    · rcases hx with hx | hx | hx
      · exact nbPair_fv _ _ _ hx
      · exact nbPair_fv _ _ _ hx
      · exact nbPair_fv _ _ _ hx
  · simp only [region, h0, if_false]
    simp [Formula.fv, Term.fv]

/-! ## Existence: the right `DETUMBLE` flow, explicitly, from a nonblocking start

`w_i(t) = w_i0 e^{−t/2}`, `h_j(t) = h_j0 + a_j w_i0 (1 − e^{−t/2})` (`a = 2, 4, 5`): the
rates contract toward 0 (inside `[−1, 1]`), and
`h_j(t) = e^{−t/2} h_j0 + (1 − e^{−t/2}) (h_j0 + a_j w_i0)` is a convex combination of `h_j0`
and the conserved momentum `c_j = h_j0 + a_j w_i0` — inside `[−2, 2]` exactly when the
nonblocking conjunct holds. -/

noncomputable def ex (t : ℝ) : ℝ := Real.exp (-(1/2) * t)

noncomputable def solR (b : State (Var 6)) (t : ℝ) : State (Var 6) := fun x =>
  if x = Rv 0 then b (Rv 0) * ex t
  else if x = Rv 1 then b (Rv 1) * ex t
  else if x = Rv 2 then b (Rv 2) * ex t
  else if x = Rv 3 then b (Rv 3) + 2 * b (Rv 0) * (1 - ex t)
  else if x = Rv 4 then b (Rv 4) + 4 * b (Rv 1) * (1 - ex t)
  else if x = Rv 5 then b (Rv 5) + 5 * b (Rv 2) * (1 - ex t)
  else b x

theorem solR_0 (b : State (Var 6)) (t : ℝ) : solR b t (Rv 0) = b (Rv 0) * ex t := by
  simp [solR]
theorem solR_1 (b : State (Var 6)) (t : ℝ) : solR b t (Rv 1) = b (Rv 1) * ex t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_2 (b : State (Var 6)) (t : ℝ) : solR b t (Rv 2) = b (Rv 2) * ex t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_3 (b : State (Var 6)) (t : ℝ) :
    solR b t (Rv 3) = b (Rv 3) + 2 * b (Rv 0) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_4 (b : State (Var 6)) (t : ℝ) :
    solR b t (Rv 4) = b (Rv 4) + 4 * b (Rv 1) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_5 (b : State (Var 6)) (t : ℝ) :
    solR b t (Rv 5) = b (Rv 5) + 5 * b (Rv 2) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (b : State (Var 6)) (t : ℝ) {x : Var 6} (hx : ∀ i, x ≠ Rv i) :
    solR b t x = b x := by
  simp [solR, hx]

theorem ex_hasDeriv (t : ℝ) : HasDerivAt ex (-(1/2) * ex t) t := by
  have h := ((hasDerivAt_id t).const_mul (-(1/2 : ℝ))).exp
  have h' : HasDerivAt ex (Real.exp (-(1/2) * id t) * (-(1/2) * 1)) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring

theorem ex_zero : ex 0 = 1 := by simp [ex]
theorem ex_pos (t : ℝ) : 0 < ex t := Real.exp_pos _
theorem ex_le_one {t : ℝ} (ht : 0 ≤ t) : ex t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; linarith

theorem solR_stays (b : State (Var 6)) (hb : Formula.sat domR b)
    (hnb : Formula.sat nbF b) {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR b t) := by
  rw [sat_domR] at hb ⊢
  rw [sat_nbF] at hnb
  simp only [and_assoc] at hb ⊢
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u⟩ := hb
  obtain ⟨⟨hn1u, hn1l⟩, ⟨hn2u, hn2l⟩, ⟨hn3u, hn3l⟩⟩ := hnb
  have he0 := ex_pos t
  have he1 := ex_le_one ht
  rw [solR_0, solR_1, solR_2, solR_3, solR_4, solR_5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem rightBlock_bound_mem (i : Fin 6) : Rv i ∈ (rightBlock (fR 0) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- **The right `DETUMBLE` flow exists, domain-staying, from every nonblocking start.** -/
theorem flowR_exists (b : State (Var 6)) (hb : Formula.sat domR b) (hnb : Formula.sat nbF b)
    (s : ℝ) (_hs : 0 ≤ s) :
    ∃ ΦR : ℝ → State (Var 6), ΦR 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR 0) (Term.const 1),
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR 0) (Term.const 1)).bound →
        ΦR t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  refine ⟨solR b, ?_, ?_, ?_, fun t ht => solR_stays b hb hnb ht.1⟩
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
    refine solR_other b 0 (fun i => ?_)
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
    have hd := ex_hasDeriv t
    fin_cases i
    · have h := ((hd.const_mul (b (Rv 0))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR b u (Rv 0)) = fun u => b (Rv 0) * ex u := by
        funext u; exact solR_0 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 0)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR0_eval, solR_0]
      exact h.congr_deriv (by ring)
    · have h := ((hd.const_mul (b (Rv 1))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR b u (Rv 1)) = fun u => b (Rv 1) * ex u := by
        funext u; exact solR_1 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 1)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR1_eval, solR_1]
      exact h.congr_deriv (by ring)
    · have h := ((hd.const_mul (b (Rv 2))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR b u (Rv 2)) = fun u => b (Rv 2) * ex u := by
        funext u; exact solR_2 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 2)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR2_eval, solR_2]
      exact h.congr_deriv (by ring)
    · have h := (((hd.const_sub 1).const_mul (2 * b (Rv 0))).const_add
        (b (Rv 3))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR b u (Rv 3)) = fun u => b (Rv 3) + 2 * b (Rv 0) * (1 - ex u) := by
        funext u; exact solR_3 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 3))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 3)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR3_eval, solR_0]
      exact h.congr_deriv (by ring)
    · have h := (((hd.const_sub 1).const_mul (4 * b (Rv 1))).const_add
        (b (Rv 4))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR b u (Rv 4)) = fun u => b (Rv 4) + 4 * b (Rv 1) * (1 - ex u) := by
        funext u; exact solR_4 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 4))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 4)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR4_eval, solR_1]
      exact h.congr_deriv (by ring)
    · have h := (((hd.const_sub 1).const_mul (5 * b (Rv 2))).const_add
        (b (Rv 5))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR b u (Rv 5)) = fun u => b (Rv 5) + 5 * b (Rv 2) * (1 - ex u) := by
        funext u; exact solR_5 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 5))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 5)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR5_eval, solR_2]
      exact h.congr_deriv (by ring)
  · intro t _ x hx
    refine solR_other b t (fun i hi => hx ?_)
    rw [hi]; exact rightBlock_bound_mem i

/-- **Within-segment existence from a nonblocking anchor** (any left field). The left run
masks the right coordinates, so the right start of the stretched segment is the anchor's
right state, in the envelope and nonblocking; `flowR_exists` supplies the domain-staying
right run. -/
theorem es (l : ℕ) (dt : ℝ) (σ : State (Var 6)) (hdom : Formula.sat domR σ)
    (hnb : Formula.sat nbF σ) :
    HExistSegB (fL l) (fR 0) (Term.const 1) domL domR dt (Function.update σ tg 0) := by
  intro s ΦL hs0 _ _ _ hmaskL _
  have hagree : ∀ i, ΦL s (Rv i) = σ (Rv i) := by
    intro i
    rw [hmaskL s (right_mem_Icc.mpr hs0) (Rv i) (fun hb => by
      obtain ⟨j, hj⟩ := leftBlock_bound_sub (fL l) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))]
    exact Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hdom' : Formula.sat domR (ΦL s) := by
    refine (Formula.coincidence domR (fun x hx => ?_)).mp hdom
    obtain ⟨i, rfl⟩ := hdomR hx
    exact (hagree i).symm
  have hnb' : Formula.sat nbF (ΦL s) := by
    rw [sat_nbF] at hnb ⊢
    rw [hagree 0, hagree 1, hagree 2, hagree 3, hagree 4, hagree 5]
    exact hnb
  exact flowR_exists (ΦL s) hdom' hnb' s hs0

/-! ## The coupling with the nonblocking conjunct riding along

`couple_cutX` (generic) with ONE change: the anchor's term list may carry extra terms `nb`
that are NOT invariant components and NOT cut atoms (so they do not enter the verdict
queries' narrowed domain `domCutX`); their preservation is supplied separately (`hnb`). The
existence hypothesis sees the whole anchor, `nb` included. (Local copy of the one in
`SatDetumbleNominal.lean`.) -/
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

/-- One pack: left window `l` at ITS OWN row (`invRow = l`), right mode `q`, at the cover's
λ = 1 and strata order `[0, 1]` (both left modes against right `DETUMBLE`,
`BenchCovers/sat3w_detumble_phases.lean`), over the two evolves narrowed by the two modes'
kept atoms. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX sat3w_detumble_phases_IRv2 sat3w_detumble_phases_cutsV2X 6 l [0, 1] 1 l q

theorem verd_core (l : ℕ) (hl : l < 2) (h : Verd l 0) :
    VerdXCore (g l :: gs l) (fL l) (fR 0) 1 (domCutX (Formula.and domL domR) (cL l) (cR 0)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ 0 (by norm_num)]
  exact h'

/-! ## The coupling, the window response -/

/-- The joint-piece anchor of window `l`: the row's components, the six nonblocking terms,
both modes' atoms. -/
noncomputable def anc (l : ℕ) : Formula (Var 6) := FM (g l) ((gs l ++ nbT) ++ atomTerms (cL l) (cR 0))

theorem anc_split (l : ℕ) (hl : l < 2) (ν : State (Var 6)) : Formula.sat (anc l) ν ↔
    (Formula.sat (FRow l) ν ∧ (∀ t ∈ nbT, Term.eval t ν ≤ 0)) ∧
      (CutSat (cL l) ν ∧ CutSat (cR 0) ν) := by
  unfold anc FRow
  rw [sat_FM_append, sat_FM_append, atomTerms_iff (hiffL l hl) hiffR]

theorem nb_iff (ν : State (Var 6)) : (∀ t ∈ nbT, Term.eval t ν ≤ 0) ↔ Formula.sat nbF ν := by
  rw [sat_nbF]
  simp only [nbT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    eval_nbU, eval_nbD, c1, c2, c3, eval_cw]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem couple (l : ℕ) (hl : l < 2) (dt : ℝ) (hv : Verd l 0) :
    ∀ σ, Formula.sat (Formula.and (anc l) (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 6))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR 0) (Term.const 1)) domR)
        (Formula.and (anc l) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX_nb (g l) (gs l ++ nbT) (g l :: gs l) nbT (cL l) (cR 0) (fL l) (fR 0) 1 one_pos
    domL domR 1 dt (hfL l hl) (hfR 0 (by norm_num)) hdomL hdomR (anchor_fv l hl)
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
    (fun t ht ν hν => stayNB l 1 zero_le_one t ht ν (hν t ht))
    (hiffL l hl) hiffR (stayL l hl 1) (stayR l 1 zero_le_one) (verd_core l hl hv)
    (fun σ hσ => es l dt σ hσ.2.2 ((nb_iff σ).mp ((anc_split l hl σ).mp hσ.1).1.2))

theorem sat_faModal_monoPost {P Q : Program (Var 6)} {A B : Formula (Var 6)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 6)}
    (h : Formula.sat (faModal (Equiv.refl (Var 6)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l : ℕ) (hl : l < 2) (dt : ℝ) (hv : Verd l 0) {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (anc l) (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq (([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
        ++ [Program.ode (rightBlock (fR 0) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FRow l) env) (region 0))) σ := by
  have htgF : tg ∉ (anc l).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv l hl g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (anc l)
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 6)))
    (by simp)
    (fun σ' hσ' => hσ'.2.1)
    (by simp)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fR 0) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR 0, Term.const 1, domR⟩ : RepoHop 6)
        (hfR 0 (by norm_num)) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l hl dt hv σ' hσ')
    hσ
  rw [show (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 6))).map
      (fun h => h.progR)
      = ([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from by rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨⟨hFν, hnbν⟩, -, hRν⟩ := (anc_split l hl ν).mp hν.1
  exact ⟨⟨hFν, hν.2⟩, (sat_region0 ν).mpr ⟨hRν, (nb_iff ν).mp hnbν⟩⟩

/-! ## The left automaton, from the file -/

/-- Left mode `l`'s window: re-test its guard, then the clock-capped window. -/
noncomputable def gw (dt : ℝ) (l : ℕ) : Program (Var 6) :=
  gwindowSeg (hostGuard vs 6 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1

/-- The file's `next` lists, resolved to indices. -/
def nextL : List (List ℕ) :=
  (List.range 2).map (fun l =>
    (mL l).next.filterMap (Handoff.leftModeIndex sat3w_detumble_phases_IRv2))

/-- `DETUMBLE → [FINE, DETUMBLE]`, `FINE → [FINE]`. -/
theorem nextL_eq : nextL = [[1, 0], [1]] := by decide

theorem nextL_transitions :
    ((List.range 2).flatMap (fun m' => (nextL.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions sat3w_detumble_phases_IRv2 := by decide

noncomputable def A (dt : ℝ) : LeftAut 6 :=
  { windows := [gw dt 0, gw dt 1],
    guards := [hostGuard vs 6 Side.L (mL 0), hostGuard vs 6 Side.L (mL 1)],
    next := nextL }

theorem A_numModes (dt : ℝ) : (A dt).numModes = 2 := rfl

theorem A_window (dt : ℝ) (t : ℕ) (ht : t < 2) : (A dt).window t = gw dt t := by
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

/-! ## Freshness of `mv` and `u_L` -/

theorem hmvenv : mv ∉ env.fv := by
  rintro (h | h)
  · exact aux_notin_range_Lv 0 (hdomL h)
  · exact aux_notin_range_Rv 0 (hdomR h)

theorem hmvreg : ∀ q, mv ∉ (region q).fv := fun q h => aux_notin_range_Rv 0 (region_fv q h)

theorem hulenv : uL ∉ env.fv := by
  rintro (h | h)
  · exact aux_notin_range_Lv 2 (hdomL h)
  · exact aux_notin_range_Rv 2 (hdomR h)

theorem hulBk : uL ∉ (mvRegion mv region Gr.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv region Gr.modes.length (fun q _ => region_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hulG (dt : ℝ) : ∀ t, uL ∉ ((A dt).guard t).fv := by
  intro t h
  by_cases ht : t < 2
  · exact aux_notin_range_Lv 2 (hgrd dt t ht h)
  · have : (A dt).guard t = Formula.tt := by
      unfold LeftAut.guard A
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUl (dt : ℝ) : ∀ t, FramesMv ((A dt).window t) uL := by
  intro t
  by_cases ht : t < 2
  · rw [A_window dt t ht]
    refine framesMv_gwindow _ (fL t) domL tg dt 1 uL (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
    exact aux_ne_Lv 2 i hi
  · have : (A dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window A
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulR : uL ∉ (rightAutomatonBody Gr mv).bv :=
  notMem_bv_rightAutomatonBody Gr mv uL (by decide) (aux_notin_range_Rv 2) htt hRv

/-! ## The handoff, in-kernel: `DETUMBLE → FINE` loosens the row -/

theorem handoff (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat env ω → Formula.sat ((A dt).guard t) ω →
      Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [A_numModes] at hm'
  rw [A_succ, nextL_eq] at ht
  interval_cases m' <;> simp at ht
  · rcases ht with rfl | rfl
    · -- DETUMBLE → FINE: `E_L ≤ E_R` implies `E_L ≤ E_R + 0.08`
      rw [sat_FRow 0 (by norm_num)] at hF
      rw [sat_FRow 1 (by norm_num)]
      simp only [slack] at hF ⊢
      norm_num at hF ⊢
      constructor <;> linarith [hF.1, hF.2]
    · exact hF
  · subst ht; exact hF

/-! ## The per-mode steps: stay in `DETUMBLE` (the only non-sink right mode) -/

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 6)) (ψ : Formula (Var 6))
    {σ : State (Var 6)}
    (hbody : Formula.sat (hostGuard vs 6 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 6))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 6)) (gw dt l) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

theorem stayCase (l : ℕ) (hl : l < 2) (dt : ℝ) (hv : Verd l 0)
    {σ : State (Var 6)} (hσ : Formula.sat (Formula.and (FRow l) env) σ)
    (hreg : Formula.sat (region 0) σ) :
    ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = 0) ∧
      Formula.sat (faModal (Equiv.refl (Var 6)) (gw dt l)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FRow l) env) (region (qfOf segs 0)))) σ := by
  refine ⟨[(0, modeW 0, edgeW 0 0)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨Gr_modeAt 0 (by norm_num), edge_mem 0 0 (by simp [edgeList])⟩
  · refine gate l dt _ _ (fun hguard => ?_)
    obtain ⟨hRσ, hnbσ⟩ := (sat_region0 σ).mp hreg
    have hanchor : Formula.sat (Formula.and (anc l) (Formula.and domL domR)) σ :=
      ⟨(anc_split l hl σ).mpr ⟨⟨hσ.1, (nb_iff σ).mpr hnbσ⟩, hO1L l hl σ hguard, hRσ⟩, hσ.2⟩
    have := respond l hl dt hv hanchor
    simpa [modeW, qfOf, edgeW] using this

theorem HmultiT (l : ℕ) (hl : l < 2) (dt : ℝ) (h0 : Verd l 0) :
    ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and (FRow l) env) (region q)) σ →
      ∃ segs : List (ℕ × RMode (Var 6) × REdge (Var 6)),
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 6)) (gw dt l)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FRow l) env) (region (qfOf segs q)))) σ := by
  intro q hq σ _ hσ
  rw [Gr_len] at hq
  match q, hq with
  | 0, _ => exact stayCase l hl dt h0 hσ.1 hσ.2
  | 1, _ => exact absurd hσ.2 (not_sat_region1 σ)

theorem hstepM (dt : ℝ) (h00 : Verd 0 0) (h10 : Verd 1 0) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv region Gr.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 6)) ((A dt).window t)
      (Program.star (rightAutomatonBody Gr mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv region Gr.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  have hframe : FramesMv (gw dt t) mv := by
    refine framesMv_gwindow _ (fL t) domL tg dt 1 mv (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
    exact aux_ne_Lv 0 i hi
  interval_cases t
  · exact hstepMode_multiR Gr mv (FRow 0) env region _ (aux_notin_FRow 0 0)
      hmvenv hmvreg hfresh htt hlt hframe (HmultiT 0 (by norm_num) dt h00)
  · exact hstepMode_multiR Gr mv (FRow 1) env region _ (aux_notin_FRow 0 1)
      hmvenv hmvreg hfresh htt hlt hframe (HmultiT 1 (by norm_num) dt h10)

/-! ## The composed theorem -/

/-- **`sat3w_detumble_phases` (suite_v2), Theorem 3 at the DECLARED mode-dependent invariant,
on the nonblocking region.** The 6-D (three-wheel) lift of `sat_detumble_phases`. `u_L`-keyed:
the `DETUMBLE` window at the exact row `E_L ≤ E_R ∧ E_R ≤ E_L`, the `FINE` window at
`E_L ≤ E_R + 0.08 ∧ E_R ≤ E_L` (`E = 2 w1² + 4 w2² + 5 w3²`), over the left automaton of the
file (`DETUMBLE → [FINE, DETUMBLE]`, `FINE → [FINE]`; each window re-tests its mode's guard,
`E_L ≤ 1` resp. `E_L ≤ 0.2`; both left fields carry the bilinear gyroscopic and three-wheel
couplings), against the two-mode right automaton of the file (declared edges, the pruned
`DETUMBLE → SAFE` included). The loop invariant also carries the evolve envelope on both
sides and the right mode's region. Response: STAY in right `DETUMBLE` on the certified joint
segment at the cover's λ = 1 (both left modes). Handoffs (in-kernel): `DETUMBLE → FINE`
loosens the slack 0 to 0.08, self-loops are trivial. Residuals: two stratified verdict packs
`Verd 0 0` (`DETUMBLE` window) and `Verd 1 0` (`FINE` window), each against right `DETUMBLE`
over the cut-narrowed domain (`modalVerdX` at `invRow = l`, strata order `[0, 1]`, λ = 1: the
tool's own queries, narrowed by the kept atoms `E_L ≤ 1` resp. `E_L ≤ 0.2` and `E_R ≤ 1`
only). The kept atoms' O1 is the kernel-checked extended certificate; their O2 is rational
(`E_R' = −E_R`; `E_L' = −E_L` in `DETUMBLE`, `−0.6 E_L` in `FINE`, through the exact
cancellation of the cubic coupling terms).

**The region.** `DETUMBLE`'s region is its kept cut atom `E_R ≤ 1` AND the nonblocking
conjunct `⋀ᵢ −2 ≤ c_i ≤ 2` (`c1 = h1 + 2 w1`, `c2 = h2 + 4 w2`, `c3 = h3 + 5 w3`, right side);
`SAFE` (the pruned sink) is excluded. The nonblocking conjunct is NOT a tool cut and does NOT
enter any verdict query. It is there because the benchmark MODEL's wheel-momentum bands
`|h_j| ≤ 2` block right `DETUMBLE` flows: from `h3_R = 2, w3_R = 0.4` the right flow leaves
`h3 ≤ 2` at once (`h3' = 2.5 w3 > 0`), so the right cannot move while the left flows and its
energy decays, breaking `E_R ≤ E_L` — with the region equal to the cut atoms alone, this
theorem is FALSE (in either left mode). Each `c_j` is conserved by the right `DETUMBLE` flow
and `h_j(t)` stays between `h_j0` and `c_j`, so the conjunct is exactly what keeps the right
flow inside the bands (existence: the explicit solution `flowR_exists`) and it is preserved by
the stay response. A property of the benchmark MODEL (the total angular momentum about each
wheel axis stays within the wheel's momentum capacity), not of the certificate. -/
theorem sat3w_detumble_phases_modeKeyed (dt : ℝ) (h00 : Verd 0 0) (h10 : Verd 1 0) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody Gr mv)
      (psiK uL ϕRow (A dt).numModes domL domR (mvRegionR mv region Gr.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL Gr mv FRow ϕRow domL domR
    (mvRegion mv region Gr.modes.length) (mvRegionR mv region Gr.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) htt hRv
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody Gr mv) FRow env
      (mvRegion mv region Gr.modes.length)
      (aux_notin_FRow 2)
      hulenv hulBk (hulG dt)
      (hframesUl dt) hulR (hnext dt) (hstepM dt h00 h10) (handoff dt)
  · exact hddF_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv region Gr.modes.length) (hwin dt) (hgrd dt) (hnext dt) htt hRv
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv region Gr.modes.length (fun q _ => region_fv q) hv)

end V2Sat3wDetumblePhases
end RelCertifier
