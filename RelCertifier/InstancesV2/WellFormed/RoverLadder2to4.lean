/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_2to4`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverLadder2to4Guarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder without speed caps, `s' = v`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to4
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverLadder2to4Pins

open Parse

/-! Parse pins of the numerals the guards and fields of `rover_ladder_2to4` write (the `GuardedPins` lemmas this file uses, local). -/

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_65 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_4 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

end RoverLadder2to4Pins

namespace RoverLadder2to4Modal

open DL DLCalTiming DLRel Parse Set

def vsQ2 : List String := ["v", "s", "psi", "theta_p"]

def dummyQ2 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRQ2 (q : ℕ) : Parse.PMode := rover_ladder_2to4_IRv2.R.modes.getD q dummyQ2

noncomputable def fRQ2 (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsQ2 4 Side.R (mRQ2 q)

noncomputable def domRQ2 : Formula (Var 4) := hostEvolve vsQ2 4 Side.R (mRQ2 0)

noncomputable def modeQ2 (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fRQ2 q) (Term.const 1), dom := domRQ2, weight := 1 }

theorem hq3n : Run.parseRat "3" = some (3) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hqm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cQ2 (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRQ20_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRQ2 q 0) x = 3 * (cQ2 q - x (Rv 0)) := by
  interval_cases q <;>
    · simp [fRQ2, hostDyn, mRQ2, rover_ladder_2to4_IRv2, vsQ2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cQ2]
      try norm_num

theorem fRQ21_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRQ2 q 1) x = x (Rv 0) := by
  interval_cases q <;>
    · simp [fRQ2, hostDyn, mRQ2, rover_ladder_2to4_IRv2, vsQ2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRQ22_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRQ2 q 2) x = 0 := by
  interval_cases q <;>
    · simp [fRQ2, hostDyn, mRQ2, rover_ladder_2to4_IRv2, vsQ2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num

theorem fRQ23_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRQ2 q 3) x = 0 := by
  interval_cases q <;>
    · simp [fRQ2, hostDyn, mRQ2, rover_ladder_2to4_IRv2, vsQ2, Run.dynOf,
      Run.lowerE, hq3n, hq030, hq050, hq065, hq0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try norm_num

theorem sat_domRQ2 (x : State (Var 4)) : Formula.sat domRQ2 x ↔
    (-(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/5 ∧ 0 ≤ x (Rv 1) ∧
      -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/5 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 4/5) := by
  simp only [domRQ2, hostEvolve, mRQ2, rover_ladder_2to4_IRv2, vsQ2]
  simp [Run.lowerF, Run.lowerE, hqm05, hq06, hq00, hq08,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end RoverLadder2to4Modal

namespace RoverLadder2to4Guarded

open DL DLCalTiming DLRel Parse Set RoverLadder2to4Modal RoverLadder2to4Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 4) :=
  { src := st, tgt := tgt, guard := hostGuard vsQ2 4 Side.R (mRQ2 tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 4) :=
  { modes := [modeQ2 0, modeQ2 1, modeQ2 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeQ2 q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 4)) : Formula.sat (hostGuard vsQ2 4 Side.R (mRQ2 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRQ2, rover_ladder_2to4_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsQ2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 4)) : Formula.sat (hostGuard vsQ2 4 Side.R (mRQ2 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRQ2, rover_ladder_2to4_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsQ2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 4)) : Formula.sat (hostGuard vsQ2 4 Side.R (mRQ2 2)) x ↔
    (7/5 ≤ x (Rv 1)) := by
  simp [hostGuard, mRQ2, rover_ladder_2to4_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsQ2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cQ2_eq (q : ℕ) : cQ2 q = ladC q := rfl

noncomputable def aR : Fin 4 → ℝ := ![0, 0, 0, 0]

noncomputable def bR : Fin 4 → ℝ := fun _ => 0

theorem aR_nonneg : ∀ k, 0 ≤ aR k := by
  intro k; fin_cases k <;> simp [aR]

noncomputable def LR : LadderRun GrG domRQ2 :=
  LadderRun.ofLinear GrG domRQ2 modeQ2 fRQ2 aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRQ20_eval q hq, cQ2_eq])
    (fun q hq x => fRQ21_eval q hq x)
    (fun q hq i h0 h1 x => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRQ22_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRQ23_eval q hq]; simp [aR, bR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRQ2 ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 2) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 2) hD.2.2.2.2.2.1 ht).2
      have hc := ladC_bounds q
      have hk : ∀ k : Fin 4, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) (bR k) ≤ phiLin aR bR q ρ k t ∧
            phiLin aR bR q ρ k t ≤ max (ρ (Rv k)) (bR k) :=
        fun k h0 h1 => phiLin_other_between aR bR q ρ k h0 h1 (aR_nonneg k) ht
      rw [sat_domRQ2]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num [bR])) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num [bR])),
        le_trans hD.2.2.1 hs,
        le_trans (le_min hD.2.2.2.1 (by norm_num [bR])) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2 (by linarith [hc.2]))⟩)
    (fun ρ hρ => by have hD := (sat_domRQ2 ρ).mp hρ; exact hD.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsQ2 4 Side.R (mRQ2 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsQ2 4 Side.R (mRQ2 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsQ2 4 Side.R (mRQ2 2)) x
      rw [sat_guardR2]; exact hs)

theorem epsR_eq : epsR rover_ladder_2to4_IRv2 = 1 := by
  simp [epsR, rover_ladder_2to4_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 4) := hostGuard vsQ2 4 Side.R (mRQ2 q)

noncomputable def WF : LadderWF GrG guardR domRQ2 where
  m := modeQ2
  fR := fRQ2
  vcap := False
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRQ20_eval q hq, cQ2_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRQ2] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRQ2] at hs; tauto
    rw [fRQ21_eval q hq]; exact ⟨h0, h1⟩
  g0 := fun x => by rw [guardR, sat_guardR0]; simp
  g1 := fun x => by rw [guardR, sat_guardR1]; simp
  g2 := fun x => by rw [guardR, sat_guardR2]; simp
  e00 := edgeG 0 0
  e01 := edgeG 0 1
  e11 := edgeG 1 1
  e12 := edgeG 1 2
  e22 := edgeG 2 2
  e00_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e01_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e11_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e12_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e22_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e00_tgt := rfl
  e01_tgt := rfl
  e11_tgt := rfl
  e12_tgt := rfl
  e22_tgt := rfl
  exists_run := LR.exists_run GrG_modeAt

/-- **Assumption 1 for `rover_ladder_2to4`**, every mode, Z3-free. -/
theorem rover_ladder_2to4_wellFormedR :
    WellFormedR GrG guardR (epsR rover_ladder_2to4_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverLadder2to4Guarded

end RelCertifier
