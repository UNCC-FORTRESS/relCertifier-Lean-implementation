/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_b_12dof`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/Story1AttdistRungBGuarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder without speed caps, `s' = v ((1 − ψ²/2) − 0.3 θ²)`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.story1_attdist_rung_b_12dof
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 12800000
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace Story1AttdistRungBPins

open Parse

/-! Parse pins of the numerals the guards and fields of `story1_attdist_rung_b_12dof` write (the `GuardedPins` lemmas this file uses, local). -/

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

end Story1AttdistRungBPins

namespace Story1AttdistRungBModal

open DL DLCalTiming DLRel Parse Set

def vsF : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]

def dummyF : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRF (q : ℕ) : Parse.PMode := story1_attdist_rung_b_12dof_IRv2.R.modes.getD q dummyF

noncomputable def fRF (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsF 12 Side.R (mRF q)

noncomputable def domRF : Formula (Var 12) := hostEvolve vsF 12 Side.R (mRF 0)

noncomputable def modeF (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fRF q) (Term.const 1), dom := domRF, weight := 1 }

/-! ## Parse pins -/

theorem hf030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hf050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hf065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hf3 : Run.parseRat "3" = some (3) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hfm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hf0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hf1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hf05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hf03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hfm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hf06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hfm06 : Run.parseRat "-0.6" = some (-(3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hf015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hf00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hf08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hfm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hfm04 : Run.parseRat "-0.4" = some (-(2:ℚ)/5) := by
  have h : parseQ "-0.4" = some (⟨-4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cstF (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRF0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 0) x = 3 * (cstF q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstF]

theorem fRF1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 1) x = x (Rv 0) * ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 4) * x (Rv 4))) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 2) x = x (Rv 3) - x (Rv 2) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 3) x = -1 * x (Rv 3) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 4) x = x (Rv 5) - x (Rv 4) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 5) x = -1 * x (Rv 5) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF7_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 7) x = 0 := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 8) x = -1 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF9_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 9) x = 0 := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF10_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 10) x = -1 * x (Rv 10) := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRF11_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRF q 11) x = 0 := by
  interval_cases q <;>
    simp [fRF, hostDyn, mRF, story1_attdist_rung_b_12dof_IRv2, vsF, Run.dynOf,
      Run.lowerE, hf030, hf050, hf065, hf3, hfm1, hf0, hf1, hf05, hf03, hfm05, hf06, hfm06, hf015, hf00, hf08, hfm10, hfm04, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRF (x : State (Var 12)) : Formula.sat domRF x ↔
    (-(2:ℝ)/5 ≤ x (Rv 9) ∧ x (Rv 9) ≤ (1:ℝ)/2 ∧ -(3:ℝ)/5 ≤ x (Rv 3) ∧ x (Rv 3) ≤ (3:ℝ)/5 ∧ -(3:ℝ)/5 ≤ x (Rv 5) ∧ x (Rv 5) ≤ (3:ℝ)/5 ∧ -(2:ℝ)/5 ≤ x (Rv 11) ∧ x (Rv 11) ≤ (1:ℝ)/2 ∧ -(2:ℝ)/5 ≤ x (Rv 7) ∧ x (Rv 7) ≤ (1:ℝ)/2 ∧ -(1:ℝ)/2 ≤ x (Rv 8) ∧ x (Rv 8) ≤ (3:ℝ)/20 ∧ -(3:ℝ)/5 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (3:ℝ)/5 ∧ 0 ≤ x (Rv 1) ∧ -(3:ℝ)/5 ≤ x (Rv 4) ∧ x (Rv 4) ≤ (3:ℝ)/5 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (4:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 10) ∧ x (Rv 10) ≤ (3:ℝ)/20 ∧ -(1:ℝ) ≤ x (Rv 6) ∧ x (Rv 6) ≤ (3:ℝ)/20) := by
  simp only [domRF, hostEvolve, mRF, story1_attdist_rung_b_12dof_IRv2, vsF]
  simp [Run.lowerF, Run.lowerE, hfm04, hf05, hfm06, hf06, hfm05, hf015, hf00, hf08, hfm10,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end Story1AttdistRungBModal

namespace Story1AttdistRungBGuarded

open DL DLCalTiming DLRel Parse Set Story1AttdistRungBModal Story1AttdistRungBPins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsF 12 Side.R (mRF tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeF 0, modeF 1, modeF 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeF q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRF, story1_attdist_rung_b_12dof_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRF, story1_attdist_rung_b_12dof_IRv2, Run.lowerF, Run.lowerE, gp_0_6, gp_1_4,
    vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x ↔
    (7/5 ≤ x (Rv 1)) := by
  simp [hostGuard, mRF, story1_attdist_rung_b_12dof_IRv2, Run.lowerF, Run.lowerE, gp_1_4, vsF,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
    Term.eval, Rv, and_assoc]

theorem cstF_eq (q : ℕ) : cstF q = ladC q := rfl

/-- The attitude/heave laws: `ψ = (ψ₀ + ω_ψ₀ t) e^{−t}`, `θ` alike, the rates and the
`z/φ/y` coordinates decaying `e^{−t}`, the `ω_z/ω_φ/ω_y` rates frozen. -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]

noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  if i = 2 then (ρ (Rv 2) + ρ (Rv 3) * t) * Real.exp (-t)
  else if i = 4 then (ρ (Rv 4) + ρ (Rv 5) * t) * Real.exp (-t)
  else ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ²`. -/
noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem φo_2 (ρ : State (Var 12)) (t : ℝ) :
    φo ρ 2 t = (ρ (Rv 2) + ρ (Rv 3) * t) * Real.exp (-t) := by simp [φo]

theorem φo_4 (ρ : State (Var 12)) (t : ℝ) :
    φo ρ 4 t = (ρ (Rv 4) + ρ (Rv 5) * t) * Real.exp (-t) := by simp [φo]

theorem φo_dec (ρ : State (Var 12)) (i : Fin 12) (h2 : i ≠ 2) (h4 : i ≠ 4) (t : ℝ) :
    φo ρ i t = ρ (Rv i) * Real.exp (-(dR i * t)) := by simp [φo, h2, h4]

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRF ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(3/5:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/5) ∧ (-(3/5:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/5) := by
  have hD := (sat_domRF ρ).mp hρ
  obtain ⟨_, _, h3l, h3h, h5l, h5h, _, _, _, _, _, _, h2l, h2h, _, h4l, h4h, _⟩ := hD
  rw [φo_2, φo_4]
  exact ⟨coupled_bound _ _ (3/5) t ⟨by linarith, h2h⟩ ⟨by linarith, h3h⟩ ht,
    coupled_bound _ _ (3/5) t ⟨by linarith, h4h⟩ ⟨by linarith, h5h⟩ ht⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT; simp only [φo_2, φo_4]; fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRF ρ) {t : ℝ} (ht : 0 ≤ t) :
    7/10 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

noncomputable def LR : LadderRun GrG domRF :=
  LadderRun.ofKappa GrG domRF modeF fRF φo kapT (7/10) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRF0_eval q hq, cstF_eq])
    (fun ρ i h0 h1 => by
      by_cases h2 : i = 2
      · subst h2; simp [φo]
      by_cases h4 : i = 4
      · subst h4; simp [φo]
      · rw [φo_dec ρ i h2 h4]; simp)
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF2_eval q hq, trajR_R, trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide),
          phiK_other _ _ q ρ 3 (by decide) (by decide), φo_dec ρ 3 (by decide) (by decide), φo_2]
        have h := hasDerivAt_coupled (ρ (Rv 2)) (ρ (Rv 3)) t
        have hf : φo ρ 2 = fun u => (ρ (Rv 2) + ρ (Rv 3) * u) * Real.exp (-u) := by
          funext u; exact φo_2 ρ u
        rw [hf]; convert h using 1; simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF3_eval q hq, trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide),
          φo_dec ρ 3 (by decide) (by decide)]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := by
          funext u; exact φo_dec ρ 3 (by decide) (by decide) u
        rw [hf]; convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF4_eval q hq, trajR_R, trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide),
          phiK_other _ _ q ρ 5 (by decide) (by decide), φo_dec ρ 5 (by decide) (by decide), φo_4]
        have h := hasDerivAt_coupled (ρ (Rv 4)) (ρ (Rv 5)) t
        have hf : φo ρ 4 = fun u => (ρ (Rv 4) + ρ (Rv 5) * u) * Real.exp (-u) := by
          funext u; exact φo_4 ρ u
        rw [hf]; convert h using 1; simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := by
          funext u; exact φo_dec ρ 5 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide), φo_dec ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF6_eval q hq]
        have hf : φo ρ 6 = fun u => ρ (Rv 6) * Real.exp (-(dR 6 * u)) := by
          funext u; exact φo_dec ρ 6 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide), φo_dec ρ 6 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := by
          funext u; exact φo_dec ρ 7 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide), φo_dec ρ 7 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF8_eval q hq]
        have hf : φo ρ 8 = fun u => ρ (Rv 8) * Real.exp (-(dR 8 * u)) := by
          funext u; exact φo_dec ρ 8 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 8 (by decide) (by decide), φo_dec ρ 8 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF9_eval q hq]
        have hf : φo ρ 9 = fun u => ρ (Rv 9) * Real.exp (-(dR 9 * u)) := by
          funext u; exact φo_dec ρ 9 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 9 (by decide) (by decide), φo_dec ρ 9 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF10_eval q hq]
        have hf : φo ρ 10 = fun u => ρ (Rv 10) * Real.exp (-(dR 10 * u)) := by
          funext u; exact φo_dec ρ 10 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 10 (by decide) (by decide), φo_dec ρ 10 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF11_eval q hq]
        have hf : φo ρ 11 = fun u => ρ (Rv 11) * Real.exp (-(dR 11 * u)) := by
          funext u; exact φo_dec ρ 11 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 11 (by decide) (by decide), φo_dec ρ 11 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRF1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRF ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hb2 : -(3/5:ℝ) ≤ phiK φo kapT q ρ 2 t ∧ phiK φo kapT q ρ 2 t ≤ 3/5 := by
        rw [phiK_other φo kapT q ρ 2 (by decide) (by decide)]; exact (φo_bounds ρ hρ ht).1
      have hb4 : -(3/5:ℝ) ≤ phiK φo kapT q ρ 4 t ∧ phiK φo kapT q ρ 4 t ≤ 3/5 := by
        rw [phiK_other φo kapT q ρ 4 (by decide) (by decide)]; exact (φo_bounds ρ hρ ht).2
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (7/10) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 4 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 h2 h4 => by
          rw [phiK_other φo kapT q ρ k h0 h1, φo_dec ρ k h2 h4]
          exact decay_between _ _ t (by fin_cases k <;> simp [dR]) ht
      rw [sat_domRF]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 9 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 11 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 8 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        by linarith [hb2.1],
        hb2.2,
        le_trans hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs,
        by linarith [hb4.1],
        hb4.2,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 10 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 6 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRF ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
      rw [sat_guardR2]; exact hs)

theorem epsR_eq : epsR story1_attdist_rung_b_12dof_IRv2 = 1 := by
  simp [epsR, story1_attdist_rung_b_12dof_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vsF 12 Side.R (mRF q)

noncomputable def WF : LadderWF GrG guardR domRF where
  m := modeF
  fR := fRF
  vcap := False
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRF0_eval q hq, cstF_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRF] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRF] at hs; tauto
    have ha0 : -(3:ℝ)/5 ≤ s (Rv 2) := by rw [sat_domRF] at hs; tauto
    have ha1 : s (Rv 2) ≤ (3:ℝ)/5 := by rw [sat_domRF] at hs; tauto
    have hb0 : -(3:ℝ)/5 ≤ s (Rv 4) := by rw [sat_domRF] at hs; tauto
    have hb1 : s (Rv 4) ≤ (3:ℝ)/5 := by rw [sat_domRF] at hs; tauto
    rw [fRF1_eval q hq]
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

/-- **Assumption 1 for `story1_attdist_rung_b_12dof`**, every mode, Z3-free. -/
theorem story1_attdist_rung_b_12dof_wellFormedR :
    WellFormedR GrG guardR (epsR story1_attdist_rung_b_12dof_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end Story1AttdistRungBGuarded

end RelCertifier
