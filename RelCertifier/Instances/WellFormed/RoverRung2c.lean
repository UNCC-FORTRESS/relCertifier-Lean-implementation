/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2c_6dof`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverRung2cGuarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder without speed caps, `s' = v ((1 − ψ²/2) − 0.3 θ²)`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2c_6dof
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverRung2cPins

open Parse

/-! Parse pins of the numerals the guards and fields of `refinement_ladder_rover_rung2c_6dof` write (the `GuardedPins` lemmas this file uses, local). -/

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

end RoverRung2cPins

namespace RoverRung2cModal

open DL DLCalTiming DLRel Parse Set

def vs6 : List String := ["v", "s", "psi", "theta_p", "z", "phi_r"]

def dummy6 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mR6 (q : ℕ) : Parse.PMode :=
  refinement_ladder_rover_rung2c_6dof_IRv2.R.modes.getD q dummy6

noncomputable def fR6 (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs6 6 Side.R (mR6 q)

noncomputable def domR6 : Formula (Var 6) := hostEvolve vs6 6 Side.R (mR6 0)

noncomputable def mode6 (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR6 q) (Term.const 1), dom := domR6, weight := 1 }

theorem hq3 : Run.parseRat "3" = some 3 := by
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

theorem hqm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq1 : Run.parseRat "1" = some 1 := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hqm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hqm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## The lowered right fields (kernel pins) -/

/-- The per-mode velocity drive: `0.30`, `0.50`, `0.65`. -/
noncomputable def cst6 (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fR6_eval0 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 0) x = 3 * (cst6 q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cst6]

theorem fR6_eval1 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 1) x = x (Rv 0) *
      ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 3) * x (Rv 3))) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval2 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval3 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 3) x = -1 * x (Rv 3) := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval4 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 4) x = 0 := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR6_eval5 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR6 q 5) x = 0 := by
  interval_cases q <;>
    simp [fR6, hostDyn, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, vs6, Run.dynOf,
      Run.lowerE, hq3, hq030, hq050, hq065, hqm1, hq1, hq05, hq03, hq0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domR6 (x : State (Var 6)) : Formula.sat domR6 x ↔
    (-(1:ℝ)/2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/20 ∧
     0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/20 ∧ 0 ≤ x (Rv 0) ∧
     x (Rv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Rv 4) ∧ x (Rv 4) ≤ 11/10) := by
  simp only [domR6, hostEvolve, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, vs6]
  simp [Run.lowerF, Run.lowerE, hqm05, hq06, hq015, hq00, hq08, hqm10, hq11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  push_cast
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩

end RoverRung2cModal

namespace RoverRung2cGuarded

open DL DLCalTiming DLRel Parse Set RoverRung2cModal RoverRung2cPins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := hostGuard vs6 6 Side.R (mR6 tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [mode6 0, mode6 1, mode6 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (mode6 q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated (odometer bands only) -/

theorem sat_guardR0 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, Run.lowerF, Run.lowerE, gp_0_0,
    gp_0_6, vs6, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, Run.lowerF, Run.lowerE, gp_0_6,
    gp_1_4, vs6, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2c_6dof_IRv2, Run.lowerF, Run.lowerE, gp_1_4,
    vs6, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- `ψ, θ` decay `e^{−t}`, `z, φ` are frozen. -/
noncomputable def dR : Fin 6 → ℝ := ![0, 0, 1, 1, 0, 0]

noncomputable def φo (ρ : State (Var 6)) (i : Fin 6) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

noncomputable def kapT (ρ : State (Var 6)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 3 t * φo ρ 3 t)

theorem dR_nonneg (k : Fin 6) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 6)) (hρ : Formula.sat domR6 ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 3 t ∧ φo ρ 3 t ≤ 3/20) := by
  have hD := (sat_domR6 ρ).mp hρ
  obtain ⟨_, _, h2l, h2h, _, h3l, h3h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b3 := decay_between (ρ (Rv 3)) (dR 3) t (dR_nonneg 3) ht
  unfold φo
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b3.1, le_trans b3.2 (max_le h3h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 6)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 6)) (hρ : Formula.sat domR6 ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h3l, h3h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem cst6_eq (q : ℕ) : cst6 q = ladC q := rfl

noncomputable def LR : LadderRun GrG domR6 :=
  LadderRun.ofKappa GrG domR6 mode6 fR6 φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fR6_eval0 q hq, cst6_eq])
    (fun ρ i h0 h1 => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval2 q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval3 q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval4 q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval5 q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fR6_eval1 q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 3 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domR6 ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) hD.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domR6]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domR6 ρ).mp hρ; exact hD.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs _ => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs _ => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs _ => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x
      rw [sat_guardR2]; exact hs)

theorem epsR_eq : epsR refinement_ladder_rover_rung2c_6dof_IRv2 = 1 := by
  simp [epsR, refinement_ladder_rover_rung2c_6dof_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs6 6 Side.R (mR6 q)

noncomputable def WF : LadderWF GrG guardR domR6 where
  m := mode6
  fR := fR6
  vcap := False
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fR6_eval0 q hq, cst6_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domR6] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domR6] at hs; tauto
    have ha0 : -(1:ℝ)/2 ≤ s (Rv 2) := by rw [sat_domR6] at hs; tauto
    have ha1 : s (Rv 2) ≤ 3/20 := by rw [sat_domR6] at hs; tauto
    have hb0 : -(1:ℝ)/2 ≤ s (Rv 3) := by rw [sat_domR6] at hs; tauto
    have hb1 : s (Rv 3) ≤ 3/20 := by rw [sat_domR6] at hs; tauto
    rw [fR6_eval1 q hq]
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

/-- **Assumption 1 for `refinement_ladder_rover_rung2c_6dof`**, every mode, Z3-free. -/
theorem refinement_ladder_rover_rung2c_6dof_wellFormedR :
    WellFormedR GrG guardR (epsR refinement_ladder_rover_rung2c_6dof_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverRung2cGuarded

end RelCertifier
