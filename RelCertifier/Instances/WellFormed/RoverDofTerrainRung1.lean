/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung1`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverDofTerrainRung1Guarded.lean`), the lowered right guards, `ε_r = 1` (the
literal is the suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed
caps, `s' = v`: `wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`);
existence from the instance's explicit ladder runs (`LR.sol`). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung1
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverDofTerrainRung1Pins

open Parse

/-! Parse pins of the numerals the guards and fields of `rover_dof_terrain_rung1` write (the `GuardedPins` lemmas this file uses, local). -/

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

end RoverDofTerrainRung1Pins

namespace RoverDofTerrainRung1Modal

open DL DLCalTiming DLRel Parse Set

def vsE : List String := ["v", "s", "psi"]

def dummyE : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRE (q : ℕ) : Parse.PMode :=
  rover_dof_terrain_rung1_IRv2.R.modes.getD q dummyE

noncomputable def fRE (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsE 3 Side.R (mRE q)

noncomputable def domRE : Formula (Var 3) := hostEvolve vsE 3 Side.R (mRE 0)

noncomputable def modeE (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fRE q) (Term.const 1), dom := domRE, weight := 1 }

theorem he030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem he00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem he08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hem05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

noncomputable def cstE (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRE0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 0) x = 3 * (cstE q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, rover_dof_terrain_rung1_IRv2, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, he0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstE]

theorem fRE1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, rover_dof_terrain_rung1_IRv2, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, he0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRE2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 2) x = 0 := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, rover_dof_terrain_rung1_IRv2, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, he0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRE (x : State (Var 3)) : Formula.sat domRE x ↔
    (-(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/5 ∧ 0 ≤ x (Rv 1) ∧ 0 ≤ x (Rv 0)
      ∧ x (Rv 0) ≤ 4/5) := by
  simp only [domRE, hostEvolve, mRE, rover_dof_terrain_rung1_IRv2, vsE]
  simp [Run.lowerF, Run.lowerE, he00, he08, hem05, he06, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
    Term.eval, Rv]
  tauto

end RoverDofTerrainRung1Modal

namespace RoverDofTerrainRung1Guarded

open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung1Modal RoverDofTerrainRung1Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsE 3 Side.R (mRE tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeE 0, modeE 1, modeE 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeE q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRE, rover_dof_terrain_rung1_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRE, rover_dof_terrain_rung1_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRE, rover_dof_terrain_rung1_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit; `ψ_R` frozen) -/

theorem cstE_eq (q : ℕ) : cstE q = ladC q := rfl

noncomputable def aR : Fin 3 → ℝ := fun _ => 0

noncomputable def bR : Fin 3 → ℝ := fun _ => 0

noncomputable def LR : LadderRun GrG domRE :=
  LadderRun.ofLinear GrG domRE modeE fRE aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRE0_eval q hq, cstE_eq])
    (fun q hq x => fRE1_eval q hq x)
    (fun q hq i h0 h1 x => by
      have hi : i = 2 := by fin_cases i <;> simp_all
      subst hi
      rw [fRE2_eval q hq]; simp [aR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRE ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 1) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 1) hD.2.2.2.1 ht).2
      have hp := phiLin_other aR bR q ρ (n := 1) 2 (by decide) (by decide) t
      have hc := ladC_bounds q
      rw [sat_domRE, trajR_R, trajR_R, trajR_R]
      simp only [aR, bR, zero_mul, neg_zero, Real.exp_zero, mul_one, zero_add, sub_zero] at hp
      rw [hp]
      refine ⟨hD.1, hD.2.1, by linarith [hD.2.2.1], ?_, ?_⟩
      · exact le_trans (le_min hD.2.2.2.1 (by linarith)) hv.1
      · exact le_trans hv.2 (max_le hD.2.2.2.2 (by linarith)))
    (fun ρ hρ => ((sat_domRE ρ).mp hρ).2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

theorem epsR_eq : epsR rover_dof_terrain_rung1_IRv2 = 1 := by
  simp [epsR, rover_dof_terrain_rung1_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vsE 3 Side.R (mRE q)

noncomputable def WF : LadderWF GrG guardR domRE where
  m := modeE
  fR := fRE
  vcap := True
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRE0_eval q hq, cstE_eq]
  fs := fun q hq s hs => by
    have := (sat_domRE s).mp hs
    rw [fRE1_eval q hq]; exact ⟨this.2.2.2.1, this.2.2.2.2⟩
  g0 := fun x => by rw [guardR, sat_guardR0]; simp [and_assoc]
  g1 := fun x => by rw [guardR, sat_guardR1]; simp [and_assoc]
  g2 := fun x => by rw [guardR, sat_guardR2]; simp
  e00 := edgeG 0 0
  e01 := edgeG 0 1
  e11 := edgeG 1 1
  e12 := edgeG 1 2
  e22 := edgeG 2 2
  e00_mem := edgeG_mem 0 0 (by simp [GrG])
  e01_mem := edgeG_mem 0 1 (by simp [GrG])
  e11_mem := edgeG_mem 1 1 (by simp [GrG])
  e12_mem := edgeG_mem 1 2 (by simp [GrG])
  e22_mem := edgeG_mem 2 2 (by simp [GrG])
  e00_tgt := rfl
  e01_tgt := rfl
  e11_tgt := rfl
  e12_tgt := rfl
  e22_tgt := rfl
  exists_run := LR.exists_run GrG_modeAt

/-- **Assumption 1 for `rover_dof_terrain_rung1`**, every mode, Z3-free. -/
theorem rover_dof_terrain_rung1_wellFormedR :
    WellFormedR GrG guardR (epsR rover_dof_terrain_rung1_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverDofTerrainRung1Guarded

end RelCertifier
