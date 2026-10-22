/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b`: Assumption 1 of the right model (`WellFormedR`)

Self-contained: the right model of the suite_v2 file (`Story3RolloverRungBModal`: state
variables, right modes, fields, evolve domain, parse pins, field evaluations), the guarded
right automaton `GrG` with the lowered right guards and the explicit ladder runs
(`V2Story3RolloverRungBGuarded`: `edgeG`, `GrG`, `sat_guardR*`, `LR`), `ε_r = 1` of the
suite_v2 file. A terrain ladder without speed caps, `s' = v ((1 − ψ²/2) − 0.3 θ²)`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
explicit ladder runs (`LR.sol`). Z3-free. The Theorem 3 instances
(`Instances/Story3RolloverRungBModal`, `InstancesV2/Modal/Story3RolloverRungB*`) import this
file for the right model.
-/
import RelCertifier.InstancesV2.BenchIR.story3_rollover_ladder_rung_b
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 12800000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace Story3RolloverRungBPins

open Parse

/-! Parse pins of the numerals the right guards and `ε_r` of `story3_rollover_ladder_rung_b`
write (the `GuardedPins` lemmas this file uses, local). -/


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

end Story3RolloverRungBPins

namespace Story3RolloverRungBModal

open DL DLCalTiming DLRel Parse Set

/-! ## The right model of the suite_v2 file -/

def vsV : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "e", "r", "phi_r", "omega_phi", "z", "y"]

def dummyV : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRV (q : ℕ) : Parse.PMode := story3_rollover_ladder_rung_b_IRv2.R.modes.getD q dummyV

noncomputable def fRV (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsV 12 Side.R (mRV q)

noncomputable def domRV : Formula (Var 12) := hostEvolve vsV 12 Side.R (mRV 0)

noncomputable def modeV (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fRV q) (Term.const 1), dom := domRV, weight := 1 }

/-! ## Parse pins -/

theorem hv030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv3 : Run.parseRat "3" = some (3) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hvm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hv0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hv1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hv05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hvm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hv08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hvm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hvm152 : Run.parseRat "-1.52" = some (-(38:ℚ)/25) := by
  have h : parseQ "-1.52" = some (⟨-152, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv152 : Run.parseRat "1.52" = some ((38:ℚ)/25) := by
  have h : parseQ "1.52" = some (⟨152, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hvm304 : Run.parseRat "-3.04" = some (-(76:ℚ)/25) := by
  have h : parseQ "-3.04" = some (⟨-304, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv304 : Run.parseRat "3.04" = some ((76:ℚ)/25) := by
  have h : parseQ "3.04" = some (⟨304, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hv11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hv2 : Run.parseRat "2" = some (2) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hv025 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hvm2 : Run.parseRat "-2" = some (-2) := by
  have h : parseQ "-2" = some (⟨-2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Field and shape pins -/

noncomputable def cstV (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRV0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 0) x = 3 * (cstV q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstV]

theorem fRV1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 1) x = x (Rv 0) * ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 4) * x (Rv 4))) := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 3) x = 0 := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 5) x = 0 := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 6) x = x (Rv 7) - 2 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV7_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 7) x = -2 * x (Rv 7) := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 8) x = -1 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV9_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 9) x = 0 := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV10_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 10) x = 0 := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRV11_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRV q 11) x = 0 := by
  interval_cases q <;>
    simp [fRV, hostDyn, mRV, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hvm05, hv06, hv015, hv00, hv08, hvm10, hvm152, hv152, hvm304, hv304, hv11, hv2, hv025, hvm2, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRV (x : State (Var 12)) : Formula.sat domRV x ↔
    (-(38:ℝ)/25 ≤ x (Rv 6) ∧ x (Rv 6) ≤ (38:ℝ)/25 ∧ -(1:ℝ)/2 ≤ x (Rv 9) ∧ x (Rv 9) ≤ (3:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ (3:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ (3:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 8) ∧ x (Rv 8) ≤ (3:ℝ)/20 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (3:ℝ)/20 ∧ -(76:ℝ)/25 ≤ x (Rv 7) ∧ x (Rv 7) ≤ (76:ℝ)/25 ∧ 0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (4:ℝ)/5 ∧ -(1:ℝ) ≤ x (Rv 11) ∧ x (Rv 11) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 10) ∧ x (Rv 10) ≤ (11:ℝ)/10) := by
  simp only [domRV, hostEvolve, mRV, story3_rollover_ladder_rung_b_IRv2, vsV]
  simp [Run.lowerF, Run.lowerE, hvm152, hv152, hvm05, hv06, hv015, hvm304, hv304, hv00, hv08, hvm10, hv11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end Story3RolloverRungBModal

namespace V2Story3RolloverRungBGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle Story3RolloverRungBModal
  Story3RolloverRungBPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsV 12 Side.R (mRV tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeV 0, modeV 1, modeV 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeV q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated (odometer bands only) -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsV 12 Side.R (mRV 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRV, story3_rollover_ladder_rung_b_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
    vsV,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsV 12 Side.R (mRV 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRV, story3_rollover_ladder_rung_b_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
    vsV,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mRV, story3_rollover_ladder_rung_b_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
    vsV,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The reference's band runs (explicit; the attitude-weighted odometer) -/

/-- The attitude/heave laws: `ψ, θ, φ` decay `e^{−t}`, the yaw-rate pair `(e, r)` is the
critically damped `e = (e₀ + r₀ t) e^{−2t}`, `r = r₀ e^{−2t}`, the rest are frozen. -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0]

noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  if i = 6 then (ρ (Rv 6) + ρ (Rv 7) * t) * Real.exp (-(2 * t))
  else ρ (Rv i) * Real.exp (-(dR i * t))

noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem dR_nonneg (k : Fin 12) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_6 (ρ : State (Var 12)) (t : ℝ) :
    φo ρ 6 t = (ρ (Rv 6) + ρ (Rv 7) * t) * Real.exp (-(2 * t)) := by simp [φo]

theorem φo_dec (ρ : State (Var 12)) (i : Fin 12) (h6 : i ≠ 6) (t : ℝ) :
    φo ρ i t = ρ (Rv i) * Real.exp (-(dR i * t)) := by simp [φo, h6]

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRV ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) := by
  have hD := (sat_domRV ρ).mp hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h2l, h2h, _, _, _, h4l, h4h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b4 := decay_between (ρ (Rv 4)) (dR 4) t (dR_nonneg 4) ht
  rw [φo_dec ρ 2 (by decide), φo_dec ρ 4 (by decide)]
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b4.1, le_trans b4.2 (max_le h4h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT; simp only [φo_dec ρ 2 (by decide), φo_dec ρ 4 (by decide)]; fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRV ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem cstV_eq (q : ℕ) : cstV q = ladC q := rfl

noncomputable def LR : LadderRun GrG domRV :=
  LadderRun.ofKappa GrG domRV modeV fRV φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRV0_eval q hq, cstV_eq])
    (fun ρ i h0 h1 => by
      by_cases h6 : i = 6
      · subst h6; simp [φo]
      · rw [φo_dec ρ i h6]; simp)
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV2_eval q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := by
          funext u; exact φo_dec ρ 2 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide), φo_dec ρ 2 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV3_eval q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := by
          funext u; exact φo_dec ρ 3 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide), φo_dec ρ 3 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV4_eval q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := by
          funext u; exact φo_dec ρ 4 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide), φo_dec ρ 4 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := by
          funext u; exact φo_dec ρ 5 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide), φo_dec ρ 5 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV6_eval q hq, trajR_R, trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide),
          phiK_other _ _ q ρ 7 (by decide) (by decide), φo_dec ρ 7 (by decide), φo_6]
        have hf : φo ρ 6 = fun u => (ρ (Rv 6) + ρ (Rv 7) * u) * Real.exp (-(2 * u)) := by
          funext u; exact φo_6 ρ u
        rw [hf]
        convert hasDerivAt_coupledK (ρ (Rv 6)) (ρ (Rv 7)) 2 t using 1
        simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := by
          funext u; exact φo_dec ρ 7 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide), φo_dec ρ 7 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV8_eval q hq]
        have hf : φo ρ 8 = fun u => ρ (Rv 8) * Real.exp (-(dR 8 * u)) := by
          funext u; exact φo_dec ρ 8 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 8 (by decide) (by decide), φo_dec ρ 8 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV9_eval q hq]
        have hf : φo ρ 9 = fun u => ρ (Rv 9) * Real.exp (-(dR 9 * u)) := by
          funext u; exact φo_dec ρ 9 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 9 (by decide) (by decide), φo_dec ρ 9 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV10_eval q hq]
        have hf : φo ρ 10 = fun u => ρ (Rv 10) * Real.exp (-(dR 10 * u)) := by
          funext u; exact φo_dec ρ 10 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 10 (by decide) (by decide), φo_dec ρ 10 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV11_eval q hq]
        have hf : φo ρ 11 = fun u => ρ (Rv 11) * Real.exp (-(dR 11 * u)) := by
          funext u; exact φo_dec ρ 11 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 11 (by decide) (by decide), φo_dec ρ 11 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRV1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRV ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 → k ≠ 6 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 h6 => by
          rw [phiK_other φo kapT q ρ k h0 h1, φo_dec ρ k h6]
          exact decay_between _ _ t (dR_nonneg k) ht
      have he : -(38/25:ℝ) ≤ phiK φo kapT q ρ 6 t ∧ phiK φo kapT q ρ 6 t ≤ 38/25 := by
        rw [phiK_other φo kapT q ρ 6 (by decide) (by decide), φo_6]
        obtain ⟨h6l, h6h, _, _, _, _, _, _, _, _, _, _, h7l, h7h, _⟩ := hD
        exact coupled_boundK _ _ 2 (38/25) t (by norm_num) ⟨by linarith, h6h⟩
          ⟨by linarith, by linarith⟩ ht
      rw [sat_domRV]
      simp only [trajR_R]
      exact ⟨by linarith [he.1],
        he.2,
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 9 (by decide) (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 8 (by decide) (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 11 (by decide) (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 10 (by decide) (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRV ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs _ => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) x
      rw [sat_guardR2]; exact hs)

/-! ## Assumption 1 -/

/-- `ε_r` of the suite_v2 file. -/
theorem epsR_eq : epsR story3_rollover_ladder_rung_b_IRv2 = 1 := by
  simp [epsR, story3_rollover_ladder_rung_b_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vsV 12 Side.R (mRV q)

noncomputable def WF : LadderWF GrG guardR domRV where
  m := modeV
  fR := fRV
  vcap := False
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRV0_eval q hq, cstV_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRV] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRV] at hs; tauto
    have ha0 : -(1:ℝ)/2 ≤ s (Rv 2) := by rw [sat_domRV] at hs; tauto
    have ha1 : s (Rv 2) ≤ (3:ℝ)/20 := by rw [sat_domRV] at hs; tauto
    have hb0 : -(1:ℝ)/2 ≤ s (Rv 4) := by rw [sat_domRV] at hs; tauto
    have hb1 : s (Rv 4) ≤ (3:ℝ)/20 := by rw [sat_domRV] at hs; tauto
    rw [fRV1_eval q hq]
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

/-- **Assumption 1 for `story3_rollover_ladder_rung_b`**, every mode, Z3-free. -/
theorem story3_rollover_ladder_rung_b_wellFormedR :
    WellFormedR GrG guardR (epsR story3_rollover_ladder_rung_b_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end V2Story3RolloverRungBGuarded
end RelCertifier
