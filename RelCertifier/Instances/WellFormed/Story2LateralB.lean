/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story2_lateral_rung_b_12dof`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/Story2LateralBGuarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder without speed caps, `s' = v ((1 − ψ²/2) − 0.3 θ²)`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.story2_lateral_rung_b_12dof
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 12800000
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace Story2LateralBPins

open Parse

/-! Parse pins of the numerals the guards and fields of `story2_lateral_rung_b_12dof` write (the `GuardedPins` lemmas this file uses, local). -/

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
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

end Story2LateralBPins

namespace Story2LateralBModal

open DL DLCalTiming DLRel Parse Set

def vsZ : List String := ["v", "s", "psi", "theta_p", "y", "y2", "z", "phi_r", "w", "w2", "w3", "w4"]

def dummyZ : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRZ (q : ℕ) : Parse.PMode := story2_lateral_rung_b_12dof_IRv2.R.modes.getD q dummyZ

noncomputable def fRZ (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsZ 12 Side.R (mRZ q)

noncomputable def domRZ : Formula (Var 12) := hostEvolve vsZ 12 Side.R (mRZ 0)

noncomputable def modeZ (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fRZ q) (Term.const 1), dom := domRZ, weight := 1 }

/-! ## Parse pins -/

theorem hz030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz3 : Run.parseRat "3" = some (3) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hzm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hzm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hz0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hz1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hz05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hzm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hz08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hz11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Field and shape pins -/

noncomputable def cstZ (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRZ0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 0) x = 3 * (cstZ q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstZ]

theorem fRZ1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 1) x = x (Rv 0) * ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3))) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 3) x = -1 * x (Rv 3) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 5) x = -1 * x (Rv 5) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ7_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 7) x = 0 := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 8) x = -1 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ9_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 9) x = 0 := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ10_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 10) x = 0 := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRZ11_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRZ q 11) x = 0 := by
  interval_cases q <;>
    simp [fRZ, hostDyn, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ, Run.dynOf,
      Run.lowerE, hz030, hz050, hz065, hz3, hzm1, hzm10, hz0, hz1, hz05, hz03, hzm05, hz06, hz015, hz00, hz08, hz11, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRZ (x : State (Var 12)) : Formula.sat domRZ x ↔
    (-(1:ℝ)/2 ≤ x (Rv 7) ∧ x (Rv 7) ≤ (3:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (4:ℝ)/5 ∧ -(1:ℝ) ≤ x (Rv 8) ∧ x (Rv 8) ≤ (3:ℝ)/20 ∧ -(1:ℝ) ≤ x (Rv 9) ∧ x (Rv 9) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 10) ∧ x (Rv 10) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 11) ∧ x (Rv 11) ≤ (11:ℝ)/10 ∧ 0 ≤ x (Rv 4) ∧ x (Rv 4) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 5) ∧ x (Rv 5) ≤ (3:ℝ)/20 ∧ -(1:ℝ) ≤ x (Rv 6) ∧ x (Rv 6) ≤ (3:ℝ)/20) := by
  simp only [domRZ, hostEvolve, mRZ, story2_lateral_rung_b_12dof_IRv2, vsZ]
  simp [Run.lowerF, Run.lowerE, hzm05, hz06, hz015, hz00, hz08, hzm10, hz11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end Story2LateralBModal

namespace Story2LateralBGuarded

open DL DLCalTiming DLRel Parse Set Story2LateralBModal Story2LateralBPins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsZ 12 Side.R (mRZ tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeZ 0, modeZ 1, modeZ 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeZ q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsZ 12 Side.R (mRZ 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRZ, story2_lateral_rung_b_12dof_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    vsZ, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsZ 12 Side.R (mRZ 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRZ, story2_lateral_rung_b_12dof_IRv2, Run.lowerF, Run.lowerE, gp_0_6, gp_1_4,
    vsZ, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsZ 12 Side.R (mRZ 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mRZ, story2_lateral_rung_b_12dof_IRv2, Run.lowerF, Run.lowerE, gp_1_4, vsZ,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
    Term.eval, Rv, and_assoc]

/-! ## The reference's band runs (explicit; the attitude-weighted odometer) -/

/-- The reference's laws for every coordinate other than `v` and `s`: decay `e^{−t}` or frozen. -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0]

noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ²`. -/
noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 3 t * φo ρ 3 t)

theorem dR_nonneg (k : Fin 12) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRZ ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 3 t ∧ φo ρ 3 t ≤ 3/20) := by
  have hD := (sat_domRZ ρ).mp hρ
  obtain ⟨_, _, h2l, h2h, _, h3l, h3h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b3 := decay_between (ρ (Rv 3)) (dR 3) t (dR_nonneg 3) ht
  unfold φo
  exact ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
    le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b3.1,
    le_trans b3.2 (max_le h3h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRZ ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h3l, h3h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem cstZ_eq (q : ℕ) : cstZ q = ladC q := rfl

noncomputable def LR : LadderRun GrG domRZ :=
  LadderRun.ofKappa GrG domRZ modeZ fRZ φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRZ0_eval q hq, cstZ_eq])
    (fun ρ i h0 h1 => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ2_eval q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ3_eval q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ4_eval q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ6_eval q hq]
        have hf : φo ρ 6 = fun u => ρ (Rv 6) * Real.exp (-(dR 6 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ8_eval q hq]
        have hf : φo ρ 8 = fun u => ρ (Rv 8) * Real.exp (-(dR 8 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 8 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ9_eval q hq]
        have hf : φo ρ 9 = fun u => ρ (Rv 9) * Real.exp (-(dR 9 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 9 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ10_eval q hq]
        have hf : φo ρ 10 = fun u => ρ (Rv 10) * Real.exp (-(dR 10 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 10 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRZ11_eval q hq]
        have hf : φo ρ 11 = fun u => ρ (Rv 11) * Real.exp (-(dR 11 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 11 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRZ1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 3 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRZ ρ).mp hρ
      obtain ⟨h7l, h7h, h2l, h2h, h1l, h3l, h3h, h0l, h0h, h8l, h8h, h9l, h9h, h10l, h10h, h11l, h11h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hD
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) h0l ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domRZ]
      simp only [trajR_R]
      exact ⟨le_trans (le_min h7l (by norm_num)) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le h7h (by norm_num)),
        le_trans (le_min h2l (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le h2h (by norm_num)),
        le_trans h1l hs,
        le_trans (le_min h3l (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le h3h (by norm_num)),
        le_trans (le_min h0l (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le h0h (by linarith [hc.2])),
        le_trans (le_min h8l (by norm_num)) (hk 8 (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide)).2 (max_le h8h (by norm_num)),
        le_trans (le_min h9l (by norm_num)) (hk 9 (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide)).2 (max_le h9h (by norm_num)),
        le_trans (le_min h10l (by norm_num)) (hk 10 (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide)).2 (max_le h10h (by norm_num)),
        le_trans (le_min h11l (by norm_num)) (hk 11 (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide)).2 (max_le h11h (by norm_num)),
        le_trans (le_min h4l (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le h4h (by norm_num)),
        le_trans (le_min h5l (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le h5h (by norm_num)),
        le_trans (le_min h6l (by norm_num)) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le h6h (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRZ ρ).mp hρ; exact hD.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs _ => by
      show Formula.sat (hostGuard vsZ 12 Side.R (mRZ 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsZ 12 Side.R (mRZ 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsZ 12 Side.R (mRZ 2)) x
      rw [sat_guardR2]; exact hs)

theorem epsR_eq : epsR story2_lateral_rung_b_12dof_IRv2 = 1 := by
  simp [epsR, story2_lateral_rung_b_12dof_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vsZ 12 Side.R (mRZ q)

noncomputable def WF : LadderWF GrG guardR domRZ where
  m := modeZ
  fR := fRZ
  vcap := False
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRZ0_eval q hq, cstZ_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRZ] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRZ] at hs; tauto
    have ha0 : -(1:ℝ)/2 ≤ s (Rv 2) := by rw [sat_domRZ] at hs; tauto
    have ha1 : s (Rv 2) ≤ (3:ℝ)/20 := by rw [sat_domRZ] at hs; tauto
    have hb0 : -(1:ℝ)/2 ≤ s (Rv 3) := by rw [sat_domRZ] at hs; tauto
    have hb1 : s (Rv 3) ≤ (3:ℝ)/20 := by rw [sat_domRZ] at hs; tauto
    rw [fRZ1_eval q hq]
    exact odo_rate2 _ _ _ h0 h1 (by linarith) (by linarith) (by linarith) (by linarith)
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

/-- **Assumption 1 for `story2_lateral_rung_b_12dof`**, every mode, Z3-free. -/
theorem story2_lateral_rung_b_12dof_wellFormedR :
    WellFormedR GrG guardR (epsR story2_lateral_rung_b_12dof_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end Story2LateralBGuarded

end RelCertifier
