/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_8to12`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (the file's three route zones `STEEP`, `MODER`, `FLAT`
and their declared `next` lists), the lowered right guards, `ε_r = 1`. The right is the
canonical rover's level `L8` (yaw and pitch inertia; the heave rate `ω_z`, roll rate `ω_φ` and
the slip offset `y`, `ω_y` pinned at 0): per zone `q` (set point `c_q` = 3, 5, 6.5 m/s, grade
`g_q` = 0.15, 0.05, 0, cross-slope `x_q` = 0.1, 0.05, 0)
`v' = (c_q − v)/2`, `s' = v (1 − ψ²/2 − 0.3 θ² − 0.2 φ²)`, `ψ' = ω_ψ − ψ`, `ω_ψ' = −ω_ψ`,
`θ' = ω_θ − θ`, `ω_θ' = −ω_θ + g_q + z/2`, `z' = −z`, `φ' = −φ + x_q + 0.015 v (ω_ψ − ψ)`, the
pinned rates 0; the guards are the odometer zones `[0, 60)`, `[60, 140)`, `[140, ∞)`; the
evolve box `0 ≤ v ≤ 8`, `s ≥ 0`, `|ψ|, |ω_ψ|, |θ|, |ω_θ| ≤ 0.6`, `|z| ≤ 0.15`, `|φ| ≤ 0.5`, the
pinned coordinates 0.
`wellFormedR_terrain` (the shared three-band lemma, no caps: `0 ≤ s' ≤ 8` on the box, so a
`STEEP` run ends below `60 + 8 ≤ 140`, inside `STEEP` or `MODER`, a `MODER` run in `MODER` or
`FLAT`, `FLAT` is forward invariant). Existence: the explicit run of the cascade
`ω_ψ → ψ`, `z → ω_θ → θ`, `(v, ω_ψ, ψ) → φ`, all `→ s` (`forcedSol`, `intSol`), kept in the
box by the comparison bounds (`forcedSol_between`: each forced contraction between its start
and its forcing's range, `ω_θ`'s forcing in `[−0.075, 0.225]`, `φ`'s in `[−0.144, 0.244]`).
Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_ladder_8to12
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverLadder8to12Pins

open Parse

/-! Parse pins of the numerals the right guards, fields and domain of `rover_ladder_8to12`
write. -/

theorem gp_0 : Run.parseRat "0" = some (0:ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1 : Run.parseRat "1" = some (1:ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m1 : Run.parseRat "-1" = some (-1:ℚ) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_015 : Run.parseRat "0.015" = some ((3:ℚ)/200) := by
  have h : parseQ "0.015" = some (⟨15, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_15 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_15 : Run.parseRat "-0.15" = some (-(3:ℚ)/20) := by
  have h : parseQ "-0.15" = some (⟨-15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_2 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
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

theorem gp_m0_5 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_6 : Run.parseRat "-0.6" = some (-(3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3_0 : Run.parseRat "3.0" = some (3:ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_5_0 : Run.parseRat "5.0" = some (5:ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_6_5 : Run.parseRat "6.5" = some ((13:ℚ)/2) := by
  have h : parseQ "6.5" = some (⟨65, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_8_0 : Run.parseRat "8.0" = some (8:ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_60_0 : Run.parseRat "60.0" = some (60:ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_140_0 : Run.parseRat "140.0" = some (140:ℚ) := by
  have h : parseQ "140.0" = some (⟨1400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

end RoverLadder8to12Pins

namespace RoverLadder8to12Modal

open DL DLCalTiming DLRel Parse Set RoverLadder8to12Pins

def vsR : List String :=
  ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi",
   "y", "omega_y"]

def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRR (q : ℕ) : Parse.PMode := rover_ladder_8to12_IRv2.R.modes.getD q dummyR

noncomputable def fRR (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsR 12 Side.R (mRR q)

noncomputable def domRR : Formula (Var 12) := hostEvolve vsR 12 Side.R (mRR 0)

noncomputable def modeR (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

/-- The zones' speed set points `c_q` (`STEEP` 3, `MODER` 5, `FLAT` 6.5 m/s). -/
noncomputable def cZ (q : ℕ) : ℝ := if q = 0 then 3 else if q = 1 then 5 else 13/2
/-- The zones' grades `g_q` (0.15, 0.05, 0). -/
noncomputable def gZ (q : ℕ) : ℝ := if q = 0 then 3/20 else if q = 1 then 1/20 else 0
/-- The zones' cross-slopes `x_q` (0.1, 0.05, 0). -/
noncomputable def xZ (q : ℕ) : ℝ := if q = 0 then 1/10 else if q = 1 then 1/20 else 0

theorem fRR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 0) x = 1/2 * (cZ q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, cZ]

theorem fRR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 1) x = x (Rv 0) * (((1 - 1/2 * (x (Rv 2) * x (Rv 2))) -
      3/10 * (x (Rv 4) * x (Rv 4))) - 1/5 * (x (Rv 8) * x (Rv 8))) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 2) x = x (Rv 3) - x (Rv 2) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRR3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 3) x = -1 * x (Rv 3) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRR4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 4) x = x (Rv 5) - x (Rv 4) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRR5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 5) x = -1 * x (Rv 5) + gZ q + 1/2 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, gZ] <;> try ring

theorem fRR6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fRR8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRR q 8) x =
      -1 * x (Rv 8) + xZ q + 3/200 * (x (Rv 0) * (x (Rv 3) - x (Rv 2))) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, xZ] <;> try ring

/-- The pinned coordinates (`ω_z`, `ω_φ`, `y`, `ω_y`) do not move. -/
theorem fRR_pinned (q : ℕ) (hq : q < 3) (x : State (Var 12)) (i : Fin 12)
    (h : i = 7 ∨ i = 9 ∨ i = 10 ∨ i = 11) : Term.eval (fRR q i) x = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;>
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_8to12_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15, gp_m0_15,
      gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0,
      gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domRR (x : State (Var 12)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8 ∧ 0 ≤ x (Rv 1) ∧
      -(3/5) ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/5 ∧ -(3/5) ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/5 ∧
      -(3/5) ≤ x (Rv 4) ∧ x (Rv 4) ≤ 3/5 ∧ -(3/5) ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧
      -(3/20) ≤ x (Rv 6) ∧ x (Rv 6) ≤ 3/20 ∧ 0 ≤ x (Rv 7) ∧ x (Rv 7) ≤ 0 ∧
      -(1/2) ≤ x (Rv 8) ∧ x (Rv 8) ≤ 1/2 ∧ 0 ≤ x (Rv 9) ∧ x (Rv 9) ≤ 0 ∧
      0 ≤ x (Rv 10) ∧ x (Rv 10) ≤ 0 ∧ 0 ≤ x (Rv 11) ∧ x (Rv 11) ≤ 0) := by
  simp only [domRR, hostEvolve, mRR, rover_ladder_8to12_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_015, gp_0_05, gp_0_1, gp_0_15,
    gp_m0_15, gp_0_2, gp_0_3, gp_0_5, gp_m0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0, gp_6_5,
    gp_8_0, gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

end RoverLadder8to12Modal

namespace RoverLadder8to12Guarded

open DL DLCalTiming DLRel Parse Set RoverLadder8to12Modal RoverLadder8to12Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 12 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsR 12 Side.R (mRR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 60) := by
  simp [hostGuard, mRR, rover_ladder_8to12_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsR 12 Side.R (mRR 1)) x ↔
    (60 ≤ x (Rv 1) ∧ x (Rv 1) < 140) := by
  simp [hostGuard, mRR, rover_ladder_8to12_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsR 12 Side.R (mRR 2)) x ↔
    140 ≤ x (Rv 1) := by
  simp [hostGuard, mRR, rover_ladder_8to12_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

/-! ## The explicit runs (the cascade `ω_ψ → ψ`, `z → ω_θ → θ`, `(v, ω_ψ, ψ) → φ`, all `→ s`) -/

theorem consts (q : ℕ) (hq : q < 3) :
    3 ≤ cZ q ∧ cZ q ≤ 13/2 ∧ 0 ≤ gZ q ∧ gZ q ≤ 3/20 ∧ 0 ≤ xZ q ∧ xZ q ≤ 1/10 := by
  interval_cases q <;> norm_num [cZ, gZ, xZ]

/-- The attitude-weighted odometer rate `v ((1 − ψ²/2 − 0.3 θ²) − 0.2 φ²)` lies in `[0, 8]`
on the box. -/
theorem odo_rate (v a b c : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 8) (ha0 : -(3/5) ≤ a) (ha1 : a ≤ 3/5)
    (hb0 : -(3/5) ≤ b) (hb1 : b ≤ 3/5) (hc0 : -(1/2) ≤ c) (hc1 : c ≤ 1/2) :
    0 ≤ v * (((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c)) ∧
      v * (((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c)) ≤ 8 := by
  have ha2 : a * a ≤ 9/25 := by nlinarith
  have hb2 : b * b ≤ 9/25 := by nlinarith
  have hc2 : c * c ≤ 1/4 := by nlinarith
  have hk0 : 0 ≤ ((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c) := by nlinarith
  have hk1 : ((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c) ≤ 1 := by
    nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]
  exact ⟨mul_nonneg hv0 hk0, by nlinarith [mul_le_mul_of_nonneg_left hk1 hv0]⟩

noncomputable def φv (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ :=
  forcedSol (1/2) (ρ (Rv 0)) (fun _ => 1/2 * cZ q)

noncomputable def φop (ρ : State (Var 12)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 3)) (fun _ => 0)

noncomputable def φps (ρ : State (Var 12)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 2)) (φop ρ)

noncomputable def φz (ρ : State (Var 12)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 6)) (fun _ => 0)

noncomputable def φotF (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ := fun τ => gZ q + 1/2 * φz ρ τ

noncomputable def φot (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ :=
  forcedSol 1 (ρ (Rv 5)) (φotF q ρ)

noncomputable def φth (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 4)) (φot q ρ)

noncomputable def φphF (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ :=
  fun τ => xZ q + 3/200 * (φv q ρ τ * (φop ρ τ - φps ρ τ))

noncomputable def φph (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ :=
  forcedSol 1 (ρ (Rv 8)) (φphF q ρ)

noncomputable def φsF (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ :=
  fun τ => φv q ρ τ * (((1 - 1/2 * (φps ρ τ * φps ρ τ)) - 3/10 * (φth q ρ τ * φth q ρ τ)) -
    1/5 * (φph q ρ τ * φph q ρ τ))

noncomputable def φs (q : ℕ) (ρ : State (Var 12)) : ℝ → ℝ := intSol (ρ (Rv 1)) (φsF q ρ)

theorem φv_cont (q : ℕ) (ρ : State (Var 12)) : Continuous (φv q ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φop_cont (ρ : State (Var 12)) : Continuous (φop ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φps_cont (ρ : State (Var 12)) : Continuous (φps ρ) :=
  forcedSol_continuous _ _ (φop_cont ρ)

theorem φz_cont (ρ : State (Var 12)) : Continuous (φz ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φotF_cont (q : ℕ) (ρ : State (Var 12)) : Continuous (φotF q ρ) := by
  have h := φz_cont ρ
  unfold φotF; fun_prop

theorem φot_cont (q : ℕ) (ρ : State (Var 12)) : Continuous (φot q ρ) :=
  forcedSol_continuous _ _ (φotF_cont q ρ)

theorem φth_cont (q : ℕ) (ρ : State (Var 12)) : Continuous (φth q ρ) :=
  forcedSol_continuous _ _ (φot_cont q ρ)

theorem φphF_cont (q : ℕ) (ρ : State (Var 12)) : Continuous (φphF q ρ) := by
  have h1 := φv_cont q ρ
  have h2 := φop_cont ρ
  have h3 := φps_cont ρ
  unfold φphF; fun_prop

theorem φph_cont (q : ℕ) (ρ : State (Var 12)) : Continuous (φph q ρ) :=
  forcedSol_continuous _ _ (φphF_cont q ρ)

theorem φsF_cont (q : ℕ) (ρ : State (Var 12)) : Continuous (φsF q ρ) := by
  have h1 := φv_cont q ρ
  have h2 := φps_cont ρ
  have h3 := φth_cont q ρ
  have h4 := φph_cont q ρ
  unfold φsF; fun_prop

/-- The run: every right coordinate along its explicit law (the pinned ones frozen). -/
noncomputable def φR (q : ℕ) (ρ : State (Var 12)) (i : Fin 12) : ℝ → ℝ :=
  if i = 0 then φv q ρ else if i = 1 then φs q ρ else if i = 2 then φps ρ
  else if i = 3 then φop ρ else if i = 4 then φth q ρ else if i = 5 then φot q ρ
  else if i = 6 then φz ρ else if i = 8 then φph q ρ else fun _ => ρ (Rv i)

theorem φR_zero (q : ℕ) (ρ : State (Var 12)) (i : Fin 12) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φv, φs, φps, φop, φth, φot, φz, φph, forcedSol_zero, intSol_zero]

theorem φR_der (q : ℕ) (hq : q < 3) (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) :
    HasDerivAt (φR q ρ i) (Term.eval (fRR q i) (trajRs ρ (φR q ρ) t)) t := by
  by_cases h0 : i = 0
  · subst h0
    rw [fRR0_eval q hq]
    simp only [trajRs_R, φR, if_true]
    refine (forcedSol_hasDerivAt (1/2) (ρ (Rv 0)) continuous_const t).congr_deriv ?_
    simp only [φv]; ring
  by_cases h1 : i = 1
  · subst h1
    rw [fRR1_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.mk_one, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φsF_cont q ρ) t
  by_cases h2 : i = 2
  · subst h2
    rw [fRR2_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 1 (ρ (Rv 2)) (φop_cont ρ) t).congr_deriv ?_
    simp only [φps]; ring
  by_cases h3 : i = 3
  · subst h3
    rw [fRR3_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 1 (ρ (Rv 3)) continuous_const t).congr_deriv ?_
    simp only [φop]; ring
  by_cases h4 : i = 4
  · subst h4
    rw [fRR4_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 1 (ρ (Rv 4)) (φot_cont q ρ) t).congr_deriv ?_
    simp only [φth]; ring
  by_cases h5 : i = 5
  · subst h5
    rw [fRR5_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 1 (ρ (Rv 5)) (φotF_cont q ρ) t).congr_deriv ?_
    simp only [φot, φotF]; ring
  by_cases h6 : i = 6
  · subst h6
    rw [fRR6_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 1 (ρ (Rv 6)) continuous_const t).congr_deriv ?_
    simp only [φz]; ring
  by_cases h8 : i = 8
  · subst h8
    rw [fRR8_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 1 (ρ (Rv 8)) (φphF_cont q ρ) t).congr_deriv ?_
    simp only [φph, φphF]; ring
  have hp : i = 7 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
  rw [fRR_pinned q hq _ i hp]
  simp only [φR, h0, h1, h2, h3, h4, h5, h6, h8, if_false]
  exact hasDerivAt_const t _

/-- The run stays in the evolve box over one control interval. -/
theorem φR_dom (q : ℕ) (hq : q < 3) (ρ : State (Var 12)) (hρ : Formula.sat domRR ρ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hv0, hv1, hs0, hp0, hp1, ho0, ho1, hth0, hth1, hot0, hot1, hz0, hz1, h70, h71,
    hph0, hph1, h90, h91, h100, h101, h110, h111⟩ := (sat_domRR ρ).mp hρ
  obtain ⟨hc0, hc1, hg0, hg1, hx0, hx1⟩ := consts q hq
  have hv : ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8 := by
    intro τ hτ
    have h := forcedSol_between (1/2) (ρ (Rv 0)) (F := fun _ => 1/2 * cZ q) continuous_const
      (lo := 1/2 * cZ q) (hi := 1/2 * cZ q) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    have he : 1/2 * cZ q / (1/2) = cZ q := by ring
    rw [he] at h
    exact ⟨le_trans (le_min hv0 (by linarith)) h.1, le_trans h.2 (max_le hv1 (by linarith))⟩
  have hop : ∀ τ ∈ Icc (0:ℝ) 1, -(3/5) ≤ φop ρ τ ∧ φop ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 3)) (F := fun _ => (0:ℝ)) continuous_const
      (lo := 0) (hi := 0) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    simp only [zero_div] at h
    exact ⟨le_trans (le_min ho0 (by norm_num)) h.1, le_trans h.2 (max_le ho1 (by norm_num))⟩
  have hps : ∀ τ ∈ Icc (0:ℝ) 1, -(3/5) ≤ φps ρ τ ∧ φps ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 2)) (φop_cont ρ) (lo := -(3/5)) (hi := 3/5)
      (by norm_num) (fun s hs => hop s hs) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hp0 le_rfl) h.1, le_trans h.2 (max_le hp1 le_rfl)⟩
  have hz : ∀ τ ∈ Icc (0:ℝ) 1, -(3/20) ≤ φz ρ τ ∧ φz ρ τ ≤ 3/20 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 6)) (F := fun _ => (0:ℝ)) continuous_const
      (lo := 0) (hi := 0) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    simp only [zero_div] at h
    exact ⟨le_trans (le_min hz0 (by norm_num)) h.1, le_trans h.2 (max_le hz1 (by norm_num))⟩
  have hot : ∀ τ ∈ Icc (0:ℝ) 1, -(3/5) ≤ φot q ρ τ ∧ φot q ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 5)) (φotF_cont q ρ) (lo := -(3/40)) (hi := 9/40)
      (by norm_num) (fun s hs => by
        obtain ⟨a0, a1⟩ := hz s hs
        simp only [φotF]; constructor <;> linarith) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hot0 (by norm_num)) h.1, le_trans h.2 (max_le hot1 (by norm_num))⟩
  have hth : ∀ τ ∈ Icc (0:ℝ) 1, -(3/5) ≤ φth q ρ τ ∧ φth q ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 4)) (φot_cont q ρ) (lo := -(3/5)) (hi := 3/5)
      (by norm_num) (fun s hs => hot s hs) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hth0 le_rfl) h.1, le_trans h.2 (max_le hth1 le_rfl)⟩
  have hph : ∀ τ ∈ Icc (0:ℝ) 1, -(1/2) ≤ φph q ρ τ ∧ φph q ρ τ ≤ 1/2 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 8)) (φphF_cont q ρ) (lo := -(18/125)) (hi := 61/250)
      (by norm_num) (fun s hs => by
        obtain ⟨a0, a1⟩ := hv s hs
        obtain ⟨b0, b1⟩ := hop s hs
        obtain ⟨c0, c1⟩ := hps s hs
        have hd0 : -(6/5) ≤ φop ρ s - φps ρ s := by linarith
        have hd1 : φop ρ s - φps ρ s ≤ 6/5 := by linarith
        have m1 : φv q ρ s * (φop ρ s - φps ρ s) ≤ φv q ρ s * (6/5) :=
          mul_le_mul_of_nonneg_left hd1 a0
        have m2 : φv q ρ s * (-(6/5)) ≤ φv q ρ s * (φop ρ s - φps ρ s) :=
          mul_le_mul_of_nonneg_left hd0 a0
        simp only [φphF]; constructor <;> nlinarith) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hph0 (by norm_num)) h.1, le_trans h.2 (max_le hph1 (by norm_num))⟩
  have hs : 0 ≤ φs q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 1)) (φsF_cont q ρ) τ)
      (fun τ hτ => (odo_rate _ _ _ _ (hv τ hτ).1 (hv τ hτ).2 (hps τ hτ).1 (hps τ hτ).2
        (hth τ hτ).1 (hth τ hτ).2 (hph τ hτ).1 (hph τ hτ).2).1) t ht
    simp only [intSol_zero] at h
    simp only [φs]; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true,
    Fin.reduceEq, if_false]
  exact ⟨(hv t ht).1, (hv t ht).2, hs, (hps t ht).1, (hps t ht).2, (hop t ht).1, (hop t ht).2,
    (hth t ht).1, (hth t ht).2, (hot t ht).1, (hot t ht).2, (hz t ht).1, (hz t ht).2, h70, h71,
    (hph t ht).1, (hph t ht).2, h90, h91, h100, h101, h110, h111⟩

theorem epsR_eq : epsR rover_ladder_8to12_IRv2 = 1 := by
  simp [epsR, rover_ladder_8to12_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vsR 12 Side.R (mRR q)

noncomputable def WF : TerrainWF GrG guardR domRR where
  m := modeR
  fR := fRR
  s1 := 60
  s2 := 140
  B := 8
  B0 := by norm_num
  band := by norm_num
  vcap := False
  is := 1
  ic := 0
  kc := 0
  kc0 := le_rfl
  cap := fun _ => 0
  cap01 := le_rfl
  cap12 := le_rfl
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fc := fun h => h.elim
  fs := fun q hq s hs => by
    obtain ⟨h0, h1, _, h2l, h2h, _, _, h4l, h4h, _, _, _, _, _, _, h8l, h8h, _⟩ :=
      (sat_domRR s).mp hs
    rw [fRR1_eval q hq]; exact odo_rate _ _ _ _ h0 h1 h2l h2h h4l h4h h8l h8h
  g0 := fun x => by rw [guardR, sat_guardR0]; simp
  g1 := fun x => by rw [guardR, sat_guardR1]; simp
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
  exists_run := fun q hq x hx =>
    ⟨_, trajRs_sol x (φR q x) 1 (by norm_num) (φR_zero q x) (fun i t _ _ => φR_der q hq x i t)
      (fun t h0 h1 => φR_dom q hq x hx t ⟨h0, h1⟩)⟩

/-- **Assumption 1 for `rover_ladder_8to12`**, every mode, Z3-free. -/
theorem rover_ladder_8to12_wellFormedR :
    WellFormedR GrG guardR (epsR rover_ladder_8to12_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_terrain WF

end RoverLadder8to12Guarded

end RelCertifier
