/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `insulin_basal_cgmloss`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
nine basal levels and their declared `next` lists), the lowered right guards, and `ε_r = 5`
read from the file.

The right model is the basal controller with a live glucose sensor: the insulin action `X`
(coordinate 0), the glucose `G` (coordinate 1) and the basal need `b` (coordinate 2, constant),
inside `0 ≤ X ≤ 1.6`, `40 ≤ G ≤ 400`, `0.5 ≤ b ≤ 1.3`. Level `q` (`SUSP` 0, `L1` … `L8`)
delivers `u_q = 0.2 q`: `X' = 0.018182 (u_q − X)`, `G' = 0.016667 ((120 + 50 (b − X)) − G)`,
`b' = 0`. The guards are glucose bands 30 mg/dL wide: `SUSP` `G < 70`, `L_q`
`[40 + 30 q, 70 + 30 q)`, `L8` `G ≥ 280` (each with the domain); `next` is the level and its
neighbours.
* Existence (i): `X` the exponential approach to `u_q ∈ [0, 1.6]`, `b` held, and `G` the
  variation-of-constants solution forced by `0.016667 (120 + 50 (b₀ − X(t))) ∈ [65 k, 185 k]`
  (`forcedSol`), which stays in `[min G₀ 65, max G₀ 185] ⊆ [40, 400]` (`forcedSol_between`).
* (ii), every level (style (b), exit): **the 5-minute glucose motion bound** (`G_step`). On the
  domain the field of `G` lies in `[0.016667 (65 − 400), 0.016667 (185 − 40)] ⊆ [−5.6, 2.42]`,
  so over one interval of at most 5 min `G` falls by at most 28 and rises by at most 12.1, less
  than one band width: the run ends in the level's band or a neighbour's, each a declared
  successor (`SUSP` cannot reach `L2`: it ends below `82.1 < 100`; `L8` cannot reach `L6`: it
  ends above `252 ≥ 250`).
Z3-free; modelled on `TankDos3to1.lean` (band steps) and `FurnaceProgramTimebase.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.insulin_basal_cgmloss

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2InsulinBasalCgmloss

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["X", "G", "b"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := insulin_basal_cgmloss_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_016667 : Run.parseRat "0.016667" = some ((16667:ℚ)/1000000) := by
  have h : parseQ "0.016667" = some (⟨16667, 1000000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_018182 : Run.parseRat "0.018182" = some ((9091:ℚ)/500000) := by
  have h : parseQ "0.018182" = some (⟨18182, 1000000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_2 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_4 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_8 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_2 : Run.parseRat "1.2" = some ((6:ℚ)/5) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_3 : Run.parseRat "1.3" = some ((13:ℚ)/10) := by
  have h : parseQ "1.3" = some (⟨13, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_4 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_6 : Run.parseRat "1.6" = some ((8:ℚ)/5) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_100 : Run.parseRat "100" = some (100 : ℚ) := by
  have h : parseQ "100" = some (⟨100, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_120_0 : Run.parseRat "120.0" = some (120 : ℚ) := by
  have h : parseQ "120.0" = some (⟨1200, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_130 : Run.parseRat "130" = some (130 : ℚ) := by
  have h : parseQ "130" = some (⟨130, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_160 : Run.parseRat "160" = some (160 : ℚ) := by
  have h : parseQ "160" = some (⟨160, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_190 : Run.parseRat "190" = some (190 : ℚ) := by
  have h : parseQ "190" = some (⟨190, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_220 : Run.parseRat "220" = some (220 : ℚ) := by
  have h : parseQ "220" = some (⟨220, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_250 : Run.parseRat "250" = some (250 : ℚ) := by
  have h : parseQ "250" = some (⟨250, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_280 : Run.parseRat "280" = some (280 : ℚ) := by
  have h : parseQ "280" = some (⟨280, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_40_0 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_400_0 : Run.parseRat "400.0" = some (400 : ℚ) := by
  have h : parseQ "400.0" = some (⟨4000, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_50_0 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_70 : Run.parseRat "70" = some (70 : ℚ) := by
  have h : parseQ "70" = some (⟨70, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_5_0 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The insulin-action rate `0.018182` (time constant 55 min) as written. -/
noncomputable def kX : ℝ := 18182 / 1000000

/-- The glucose rate `0.016667` (time constant 60 min) as written. -/
noncomputable def kG : ℝ := 16667 / 1000000

/-- Level `q`'s delivery `0.2 q`. -/
noncomputable def uR (q : ℕ) : ℝ := (q : ℝ) / 5

theorem fR0_eval (q : ℕ) (hq : q < 9) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kX * (uR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, insulin_basal_cgmloss_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, kX, uR] <;> norm_num

theorem fR1_eval (q : ℕ) (hq : q < 9) (x : State (Var 3)) :
    Term.eval (fR q 1) x = kG * (120 + 50 * x (Rv 2) - 50 * x (Rv 0)) - kG * x (Rv 1) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, insulin_basal_cgmloss_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, kG] <;> ring

theorem fR2_eval (q : ℕ) (hq : q < 9) (x : State (Var 3)) : Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, insulin_basal_cgmloss_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem sat_domR (ν : State (Var 3)) :
    Formula.sat domR ν ↔
      (0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧
        ν (Rv 2) ≤ 13/10) := by
  simp only [domR, hostEvolve, mR, insulin_basal_cgmloss_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (`SUSP` 0, `L1` … `L8` 1 … 8): each level and its
neighbours. -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4), (4, 5), (5, 4), (5, 5), (5, 6), (6, 5), (6, 6), (6, 7), (7, 6), (7, 7), (7, 8), (8, 7), (8, 8)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4, modeW 5, modeW 6, modeW 7, modeW 8]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 9) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 9 ∧ m = modeW q := by
  have hlen : q < 9 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 9 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

/-- `SUSP`'s guard, evaluated. -/
theorem sat_g0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 1) < 70 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L1`'s guard, evaluated. -/
theorem sat_g1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (70 ≤ ν (Rv 1) ∧ ν (Rv 1) < 100 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L2`'s guard, evaluated. -/
theorem sat_g2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      (100 ≤ ν (Rv 1) ∧ ν (Rv 1) < 130 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L3`'s guard, evaluated. -/
theorem sat_g3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔
      (130 ≤ ν (Rv 1) ∧ ν (Rv 1) < 160 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L4`'s guard, evaluated. -/
theorem sat_g4 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 4)) ν ↔
      (160 ≤ ν (Rv 1) ∧ ν (Rv 1) < 190 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L5`'s guard, evaluated. -/
theorem sat_g5 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 5)) ν ↔
      (190 ≤ ν (Rv 1) ∧ ν (Rv 1) < 220 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L6`'s guard, evaluated. -/
theorem sat_g6 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 6)) ν ↔
      (220 ≤ ν (Rv 1) ∧ ν (Rv 1) < 250 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L7`'s guard, evaluated. -/
theorem sat_g7 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 7)) ν ↔
      (250 ≤ ν (Rv 1) ∧ ν (Rv 1) < 280 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `L8`'s guard, evaluated. -/
theorem sat_g8 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 8)) ν ↔
      (280 ≤ ν (Rv 1) ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 8/5 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 400 ∧ 1/2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 13/10) := by
  simp [hostGuard, mR, insulin_basal_cgmloss_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_016667, hp_0_018182, hp_0_2, hp_0_4, hp_0_5, hp_0_6, hp_0_8, hp_1_0, hp_1_2, hp_1_3, hp_1_4, hp_1_6, hp_100, hp_120_0, hp_130, hp_160, hp_190, hp_220, hp_250, hp_280, hp_40_0, hp_400_0, hp_50_0, hp_70, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR insulin_basal_cgmloss_IRv2 = 5 := by
  simp [epsR, insulin_basal_cgmloss_IRv2, hp_5_0]

/-! ## Existence: the explicit run -/

/-- Level `q`'s insulin action from `X₀`. -/
noncomputable def xSol (q : ℕ) (X0 t : ℝ) : ℝ := uR q + (X0 - uR q) * Real.exp (-(kX * t))

theorem xSol_cont (q : ℕ) (X0 : ℝ) : Continuous (xSol q X0) := by unfold xSol; fun_prop

theorem FG_cont (q : ℕ) (X0 b0 : ℝ) :
    Continuous (fun u => kG * (120 + 50 * b0 - 50 * xSol q X0 u)) :=
  continuous_const.mul (continuous_const.sub (continuous_const.mul (xSol_cont q X0)))

/-- The run of level `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then xSol q (x (Rv 0)) t
  else if i.val = 1 then
    forcedSol kG (x (Rv 1)) (fun u => kG * (120 + 50 * x (Rv 2) - 50 * xSol q (x (Rv 0)) u)) t
  else x (Rv 2)

theorem phi_zero (q : ℕ) (x : State (Var 3)) : phi q x 0 = xSol q (x (Rv 0)) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 3)) :
    phi q x 1 =
      forcedSol kG (x (Rv 1)) (fun u => kG * (120 + 50 * x (Rv 2) - 50 * xSol q (x (Rv 0)) u)) := by
  funext t; simp [phi]

theorem phi_two (q : ℕ) (x : State (Var 3)) : phi q x 2 = fun _ => x (Rv 2) := by
  funext t; simp [phi]

theorem phi_der (q : ℕ) (hq : q < 9) (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, trajRs_R, phi_zero]
      exact hasDerivAt_expApproach kX (uR q) (x (Rv 0)) t
  | 1 =>
      rw [fR1_eval q hq, trajRs_R, trajRs_R, trajRs_R, phi_zero, phi_one, phi_two]
      exact (forcedSol_hasDerivAt kG (x (Rv 1)) (FG_cont q (x (Rv 0)) (x (Rv 2))) t).congr_deriv
        (by ring)
  | 2 =>
      rw [fR2_eval q hq, phi_two]
      exact hasDerivAt_const _ _

theorem xSol_box (q : ℕ) (hq : q < 9) (X0 t : ℝ) (h0 : 0 ≤ X0) (h1 : X0 ≤ 8/5) (ht : 0 ≤ t) :
    0 ≤ xSol q X0 t ∧ xSol q X0 t ≤ 8/5 := by
  have hu : 0 ≤ uR q ∧ uR q ≤ 8/5 := by
    unfold uR
    have : (q : ℝ) ≤ 8 := by exact_mod_cast Nat.lt_succ_iff.mp hq
    constructor <;> [positivity; linarith]
  have hk : 0 ≤ kX := by unfold kX; norm_num
  obtain ⟨l, u⟩ := exp_approach_between kX (uR q) X0 t hk ht
  exact ⟨le_trans (le_min h0 hu.1) l, le_trans u (max_le h1 hu.2)⟩

theorem exists_run (q : ℕ) (hq : q < 9) (x : State (Var 3)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, g0, g1, b0, b1⟩ := (sat_domR x).mp hd
  have hkG : 0 < kG := by unfold kG; norm_num
  refine ⟨_, trajRs_sol x (phi q x) ε hε (fun i => ?_) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht hte => ?_)⟩
  · match i with
    | 0 => rw [phi_zero]; simp [xSol]
    | 1 => rw [phi_one, forcedSol_zero]
    | 2 => rw [phi_two]
  · have hG := forcedSol_between kG (x (Rv 1)) (FG_cont q (x (Rv 0)) (x (Rv 2)))
      (lo := kG * 65) (hi := kG * 185) (T := ε) hkG (fun u hu => by
        have := xSol_box q hq (x (Rv 0)) u a0 a1 hu.1
        show kG * 65 ≤ kG * (120 + 50 * x (Rv 2) - 50 * xSol q (x (Rv 0)) u) ∧
          kG * (120 + 50 * x (Rv 2) - 50 * xSol q (x (Rv 0)) u) ≤ kG * 185
        constructor
        · apply mul_le_mul_of_nonneg_left _ hkG.le; linarith [this.1, this.2]
        · apply mul_le_mul_of_nonneg_left _ hkG.le; linarith [this.1, this.2]) t ⟨ht, hte⟩
    rw [mul_div_cancel_left₀ _ hkG.ne', mul_div_cancel_left₀ _ hkG.ne'] at hG
    obtain ⟨c0, c1⟩ := xSol_box q hq (x (Rv 0)) t a0 a1 ht
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R, phi_zero, phi_one, phi_two]
    exact ⟨c0, c1, le_trans (le_min g0 (by norm_num)) hG.1,
      le_trans hG.2 (max_le g1 (by norm_num)), b0, b1⟩

/-! ## The 5-minute glucose motion bound -/

theorem memG (q : ℕ) : (Rv 1, Term.binop .mul (Term.const 1) (fR q 1)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 1

/-- **Over one interval (at most 5 min) the glucose falls by at most 28 and rises by at most
12.1** (the field of `G` lies in `[−5.6, 2.42]` on the domain). -/
theorem G_step (q : ℕ) (hq : q < 9) (x : State (Var 3)) (t : ℝ) (Φ : ℝ → State (Var 3))
    (ht : t ≤ 5) (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    x (Rv 1) - 28 ≤ Φ t (Rv 1) ∧ Φ t (Rv 1) ≤ x (Rv 1) + 121/10 := by
  have h0 := H.hr
  have hup := H.rate_le (memG q) (121/50) (fun s hs => by
    obtain ⟨a0, a1, g0, g1, b0, b1⟩ := (sat_domR s).mp hs
    rw [eval_unit_mul, fR1_eval q hq]; unfold kG; linarith)
  have hdn := H.rate_ge (memG q) (-(28/5)) (fun s hs => by
    obtain ⟨a0, a1, g0, g1, b0, b1⟩ := (sat_domR s).mp hs
    rw [eval_unit_mul, fR1_eval q hq]; unfold kG; linarith)
  constructor <;> nlinarith

/-- **Assumption 1 for `insulin_basal_cgmloss`**, every mode, Z3-free. -/
theorem insulin_basal_cgmloss_wellFormedR :
    WellFormedR Gr guardR (epsR insulin_basal_cgmloss_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq9, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- SUSP
    have hg' := (sat_g0 x).mp hg
    refine ⟨exists_run 0 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 0 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 70
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr ⟨h1, e0, e1, e2, e3, e4, e5⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_g1 _).mpr ⟨by linarith, by linarith [hg'.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- L1
    have hg' := (sat_g1 x).mp hg
    refine ⟨exists_run 1 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 1 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 70
    · exact ⟨edgeW 1 0, edge_mem 1 0 (by decide), (sat_g0 _).mpr ⟨h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 1) < 100
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide), (sat_g2 _).mpr ⟨by linarith, by linarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- L2
    have hg' := (sat_g2 x).mp hg
    refine ⟨exists_run 2 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 2 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 100
    · exact ⟨edgeW 2 1, edge_mem 2 1 (by decide), (sat_g1 _).mpr ⟨by linarith [hg'.1], h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 1) < 130
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_g3 _).mpr ⟨by linarith, by linarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- L3
    have hg' := (sat_g3 x).mp hg
    refine ⟨exists_run 3 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 3 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 130
    · exact ⟨edgeW 3 2, edge_mem 3 2 (by decide), (sat_g2 _).mpr ⟨by linarith [hg'.1], h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 1) < 160
      · exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_g3 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 3 4, edge_mem 3 4 (by decide), (sat_g4 _).mpr ⟨by linarith, by linarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- L4
    have hg' := (sat_g4 x).mp hg
    refine ⟨exists_run 4 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 4 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 160
    · exact ⟨edgeW 4 3, edge_mem 4 3 (by decide), (sat_g3 _).mpr ⟨by linarith [hg'.1], h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 1) < 190
      · exact ⟨edgeW 4 4, edge_mem 4 4 (by decide), (sat_g4 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 4 5, edge_mem 4 5 (by decide), (sat_g5 _).mpr ⟨by linarith, by linarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- L5
    have hg' := (sat_g5 x).mp hg
    refine ⟨exists_run 5 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 5 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 190
    · exact ⟨edgeW 5 4, edge_mem 5 4 (by decide), (sat_g4 _).mpr ⟨by linarith [hg'.1], h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 1) < 220
      · exact ⟨edgeW 5 5, edge_mem 5 5 (by decide), (sat_g5 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 5 6, edge_mem 5 6 (by decide), (sat_g6 _).mpr ⟨by linarith, by linarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- L6
    have hg' := (sat_g6 x).mp hg
    refine ⟨exists_run 6 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 6 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 220
    · exact ⟨edgeW 6 5, edge_mem 6 5 (by decide), (sat_g5 _).mpr ⟨by linarith [hg'.1], h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 1) < 250
      · exact ⟨edgeW 6 6, edge_mem 6 6 (by decide), (sat_g6 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 6 7, edge_mem 6 7 (by decide), (sat_g7 _).mpr ⟨by linarith, by linarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- L7
    have hg' := (sat_g7 x).mp hg
    refine ⟨exists_run 7 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 7 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 250
    · exact ⟨edgeW 7 6, edge_mem 7 6 (by decide), (sat_g6 _).mpr ⟨by linarith [hg'.1], h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 1) < 280
      · exact ⟨edgeW 7 7, edge_mem 7 7 (by decide), (sat_g7 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 7 8, edge_mem 7 8 (by decide), (sat_g8 _).mpr ⟨by linarith, e0, e1, e2, e3, e4, e5⟩⟩
  · -- L8
    have hg' := (sat_g8 x).mp hg
    refine ⟨exists_run 8 (by norm_num) x hd 5 (by norm_num), ?_⟩
    intro t Φ ht H
    obtain ⟨hlo, hhi⟩ := G_step 8 (by norm_num) x t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 1) < 280
    · exact ⟨edgeW 8 7, edge_mem 8 7 (by decide), (sat_g7 _).mpr ⟨by linarith [hg'.1], h1, e0, e1, e2, e3, e4, e5⟩⟩
    · exact ⟨edgeW 8 8, edge_mem 8 8 (by decide), (sat_g8 _).mpr ⟨by linarith, e0, e1, e2, e3, e4, e5⟩⟩

end V2InsulinBasalCgmloss
end RelCertifier
