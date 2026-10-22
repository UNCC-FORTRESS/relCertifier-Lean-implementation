/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung3`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverDofTerrainRung3Guarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed caps, `s' = v`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung3
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverDofTerrainRung3Pins

open Parse

/-! Parse pins of the numerals the guards and fields of `rover_dof_terrain_rung3` write (the `GuardedPins` lemmas this file uses, local). -/

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

end RoverDofTerrainRung3Pins

namespace RoverDofTerrainRung3Modal

open DL DLCalTiming DLRel Parse Set

def vsW : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]

def dummyW : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRW (q : ℕ) : Parse.PMode := rover_dof_terrain_rung3_IRv2.R.modes.getD q dummyW

noncomputable def fRW (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsW 12 Side.R (mRW q)

noncomputable def domRW : Formula (Var 12) := hostEvolve vsW 12 Side.R (mRW 0)

noncomputable def modeW (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fRW q) (Term.const 1), dom := domRW, weight := 1 }

theorem hw030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hw050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hw065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hw3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hwm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hw0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hw00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hw08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hwm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hw015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hwm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hw11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

noncomputable def cstW (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRW0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 0) x = 3 * (cstW q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstW]

theorem fRW1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 3) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 5) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW7_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 7) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 8) x = -1 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW9_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 9) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW10_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 10) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW11_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 11) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_dof_terrain_rung3_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRW (x : State (Var 12)) : Formula.sat domRW x ↔
    (-(1:ℝ) ≤ x (Rv 10) ∧ x (Rv 10) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 11) ∧ x (Rv 11) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 7) ∧ x (Rv 7) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 5) ∧ x (Rv 5) ≤ (11:ℝ)/10 ∧ -(1:ℝ)/2 ≤ x (Rv 6) ∧ x (Rv 6) ≤ (3:ℝ)/20 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (4:ℝ)/5 ∧ -(1:ℝ) ≤ x (Rv 9) ∧ x (Rv 9) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 8) ∧ x (Rv 8) ≤ (3:ℝ)/20) := by
  simp only [domRW, hostEvolve, mRW, rover_dof_terrain_rung3_IRv2, vsW]
  simp [Run.lowerF, Run.lowerE, hwm05, hw015, hw00, hw08, hwm10, hw11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end RoverDofTerrainRung3Modal

namespace RoverDofTerrainRung3Guarded

open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung3Modal RoverDofTerrainRung3Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsW 12 Side.R (mRW tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeW 0, modeW 1, modeW 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsW 12 Side.R (mRW 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRW, rover_dof_terrain_rung3_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsW, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsW 12 Side.R (mRW 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRW, rover_dof_terrain_rung3_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsW, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsW 12 Side.R (mRW 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRW, rover_dof_terrain_rung3_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsW, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cstW_eq (q : ℕ) : cstW q = ladC q := rfl

noncomputable def aR : Fin 12 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0]

noncomputable def bR : Fin 12 → ℝ := fun _ => 0

theorem aR_nonneg : ∀ k, 0 ≤ aR k := by
  intro k; fin_cases k <;> simp [aR]

noncomputable def LR : LadderRun GrG domRW :=
  LadderRun.ofLinear GrG domRW modeW fRW aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRW0_eval q hq, cstW_eq])
    (fun q hq x => fRW1_eval q hq x)
    (fun q hq i h0 h1 x => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW2_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW3_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW4_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW5_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW6_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW7_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW8_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW9_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW10_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRW11_eval q hq]; simp [aR, bR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRW ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 10) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 10) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht).2
      have hc := ladC_bounds q
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) (bR k) ≤ phiLin aR bR q ρ k t ∧
            phiLin aR bR q ρ k t ≤ max (ρ (Rv k)) (bR k) :=
        fun k h0 h1 => phiLin_other_between aR bR q ρ k h0 h1 (aR_nonneg k) ht
      rw [sat_domRW]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num [bR])) (hk 10 (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.1 (by norm_num [bR])) (hk 11 (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num [bR])) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 9 (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 8 (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num [bR]))⟩)
    (fun ρ hρ => by have hD := (sat_domRW ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsW 12 Side.R (mRW 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsW 12 Side.R (mRW 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsW 12 Side.R (mRW 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

theorem epsR_eq : epsR rover_dof_terrain_rung3_IRv2 = 1 := by
  simp [epsR, rover_dof_terrain_rung3_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vsW 12 Side.R (mRW q)

noncomputable def WF : LadderWF GrG guardR domRW where
  m := modeW
  fR := fRW
  vcap := True
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRW0_eval q hq, cstW_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRW] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRW] at hs; tauto
    rw [fRW1_eval q hq]; exact ⟨h0, h1⟩
  g0 := fun x => by rw [guardR, sat_guardR0]; simp [and_assoc]
  g1 := fun x => by rw [guardR, sat_guardR1]; simp [and_assoc]
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

/-- **Assumption 1 for `rover_dof_terrain_rung3`**, every mode, Z3-free. -/
theorem rover_dof_terrain_rung3_wellFormedR :
    WellFormedR GrG guardR (epsR rover_dof_terrain_rung3_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverDofTerrainRung3Guarded

end RelCertifier
