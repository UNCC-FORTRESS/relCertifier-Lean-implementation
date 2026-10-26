/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_6to7`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverRollover6to7Guarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed caps, `s' = v ((1 − ψ²/2) − 0.3 θ²)`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.rover_rollover_6to7
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverRollover6to7Pins

open Parse

/-! Parse pins of the numerals the guards and fields of `rover_rollover_6to7` write (the `GuardedPins` lemmas this file uses, local). -/

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

end RoverRollover6to7Pins

namespace RoverRollover6to7Modal

open DL DLCalTiming DLRel Parse Set

def vsA : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "e", "r", "phi_r", "omega_phi", "z", "y"]

def dummyA : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRA (q : ℕ) : Parse.PMode := rover_rollover_6to7_IRv2.R.modes.getD q dummyA

noncomputable def fRA (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsA 12 Side.R (mRA q)

noncomputable def domRA : Formula (Var 12) := hostEvolve vsA 12 Side.R (mRA 0)

noncomputable def modeA (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fRA q) (Term.const 1), dom := domRA, weight := 1 }

/-! ## Parse pins -/

theorem hp030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp3 : Run.parseRat "3" = some (3) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hp0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hp1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hp08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hpm10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpm15 : Run.parseRat "-1.5" = some (-(3:ℚ)/2) := by
  have h : parseQ "-1.5" = some (⟨-15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hpm152 : Run.parseRat "-1.52" = some (-(38:ℚ)/25) := by
  have h : parseQ "-1.52" = some (⟨-152, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp162 : Run.parseRat "1.62" = some ((81:ℚ)/50) := by
  have h : parseQ "1.62" = some (⟨162, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cstA (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRA0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 0) x = 3 * (cstA q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstA]

theorem fRA1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 1) x = x (Rv 0) * ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 4) * x (Rv 4))) := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 3) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 5) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA7_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 7) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 8) x = -1 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA9_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 9) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA10_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 10) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRA11_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRA q 11) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, rover_rollover_6to7_IRv2, vsA, Run.dynOf,
      Run.lowerE, hp030, hp050, hp065, hp3, hpm1, hp0, hp1, hp05, hp03, hpm05, hp06, hp015, hp00, hp08, hpm10, hpm15, hp11, hpm152, hp162, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRA (x : State (Var 12)) : Formula.sat domRA x ↔
    (-(3:ℝ)/2 ≤ x (Rv 6) ∧ x (Rv 6) ≤ (3:ℝ)/20 ∧ -(1:ℝ)/2 ≤ x (Rv 9) ∧ x (Rv 9) ≤ (3:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ (3:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ (3:ℝ)/5 ∧ -(1:ℝ)/2 ≤ x (Rv 8) ∧ x (Rv 8) ≤ (3:ℝ)/20 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (3:ℝ)/20 ∧ -(38:ℝ)/25 ≤ x (Rv 7) ∧ x (Rv 7) ≤ (81:ℝ)/50 ∧ 0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (4:ℝ)/5 ∧ -(1:ℝ) ≤ x (Rv 11) ∧ x (Rv 11) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 10) ∧ x (Rv 10) ≤ (11:ℝ)/10) := by
  simp only [domRA, hostEvolve, mRA, rover_rollover_6to7_IRv2, vsA]
  simp [Run.lowerF, Run.lowerE, hpm15, hp015, hpm05, hp06, hpm152, hp162, hp00, hp08, hpm10, hp11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end RoverRollover6to7Modal

namespace RoverRollover6to7Guarded

open DL DLCalTiming DLRel Parse Set RoverRollover6to7Modal RoverRollover6to7Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsA 12 Side.R (mRA tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeA 0, modeA 1, modeA 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeA q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsA 12 Side.R (mRA 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRA, rover_rollover_6to7_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsA, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsA 12 Side.R (mRA 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRA, rover_rollover_6to7_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsA, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsA 12 Side.R (mRA 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRA, rover_rollover_6to7_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsA, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem cstA_eq (q : ℕ) : cstA q = ladC q := rfl

/-- The attitude/heave laws: every coordinate other than `v` and `s` decays `e^{−t}` or is
frozen (the reference's `ψ, θ, e, φ` relax, their rates and `z, y` are constant). -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0]

noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ²`. -/
noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem dR_nonneg (k : Fin 12) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRA ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) := by
  have hD := (sat_domRA ρ).mp hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h2l, h2h, _, _, _, h4l, h4h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b4 := decay_between (ρ (Rv 4)) (dR 4) t (dR_nonneg 4) ht
  unfold φo
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b4.1, le_trans b4.2 (max_le h4h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRA ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

noncomputable def LR : LadderRun GrG domRA :=
  LadderRun.ofKappa GrG domRA modeA fRA φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRA0_eval q hq, cstA_eq])
    (fun ρ i h0 h1 => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA2_eval q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA3_eval q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA4_eval q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA6_eval q hq]
        have hf : φo ρ 6 = fun u => ρ (Rv 6) * Real.exp (-(dR 6 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA8_eval q hq]
        have hf : φo ρ 8 = fun u => ρ (Rv 8) * Real.exp (-(dR 8 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 8 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA9_eval q hq]
        have hf : φo ρ 9 = fun u => ρ (Rv 9) * Real.exp (-(dR 9 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 9 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA10_eval q hq]
        have hf : φo ρ 10 = fun u => ρ (Rv 10) * Real.exp (-(dR 10 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 10 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRA11_eval q hq]
        have hf : φo ρ 11 = fun u => ρ (Rv 11) * Real.exp (-(dR 11 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 11 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRA1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRA ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domRA]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 9 (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 8 (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 11 (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 10 (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRA ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsA 12 Side.R (mRA 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsA 12 Side.R (mRA 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsA 12 Side.R (mRA 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

theorem epsR_eq : epsR rover_rollover_6to7_IRv2 = 1 := by
  simp [epsR, rover_rollover_6to7_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vsA 12 Side.R (mRA q)

noncomputable def WF : LadderWF GrG guardR domRA where
  m := modeA
  fR := fRA
  vcap := True
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRA0_eval q hq, cstA_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRA] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRA] at hs; tauto
    have ha0 : -(1:ℝ)/2 ≤ s (Rv 2) := by rw [sat_domRA] at hs; tauto
    have ha1 : s (Rv 2) ≤ (3:ℝ)/20 := by rw [sat_domRA] at hs; tauto
    have hb0 : -(1:ℝ)/2 ≤ s (Rv 4) := by rw [sat_domRA] at hs; tauto
    have hb1 : s (Rv 4) ≤ (3:ℝ)/20 := by rw [sat_domRA] at hs; tauto
    rw [fRA1_eval q hq]
    exact odo_rate2 _ _ _ h0 h1 (by linarith) (by linarith) (by linarith) (by linarith)
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

/-- **Assumption 1 for `rover_rollover_6to7`**, every mode, Z3-free. -/
theorem rover_rollover_6to7_wellFormedR :
    WellFormedR GrG guardR (epsR rover_rollover_6to7_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverRollover6to7Guarded

end RelCertifier
