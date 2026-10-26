/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_6to12`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (the file's three zones and their declared `next`
lists), the lowered right guards, `ε_r = 1`. The right is the terrain 6-DOF model in the
12-coordinate chart (rates, vertical velocity and accelerations pinned):
`s' = v ((1 − ψ²/2) − 0.3 θ² − 0.2 φ²)` (roll costs progress), pitch driven by heave
`θ' = −θ + z/2` (explicit law `(θ₀ + z₀ t/2) e^{−t}`, as in `RoverTerrain6to8.lean`) (since
2026-10-26): `wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence
from the explicit ladder runs (`LR.sol`). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_terrain_6to12
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverTerrain6to12Pins

open Parse

/-! Parse pins of the numerals the guards and fields of `rover_terrain_6to12` write (the `GuardedPins` lemmas this file uses, local). -/

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

end RoverTerrain6to12Pins

namespace RoverTerrain6to12Modal

open DL DLCalTiming DLRel Parse Set

def vsW : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]

def dummyW : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRW (q : ℕ) : Parse.PMode := rover_terrain_6to12_IRv2.R.modes.getD q dummyW

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

theorem hwp1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hwp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num

theorem hwp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num

theorem hw02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

noncomputable def cstW (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRW0_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 0) x = 3 * (cstW q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstW]

theorem fRW1_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 1) x = x (Rv 0) * (((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 4) * x (Rv 4)))
      - 1/5 * (x (Rv 6) * x (Rv 6))) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW2_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW3_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 3) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW4_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 4) x = -1 * x (Rv 4) + 1/2 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW5_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 5) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW6_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW7_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 7) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW8_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 8) x = -1 * x (Rv 8) := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW9_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 9) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW10_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 10) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRW11_eval (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fRW q 11) x = 0 := by
  interval_cases q <;>
    simp [fRW, hostDyn, mRW, rover_terrain_6to12_IRv2, vsW, Run.dynOf,
      Run.lowerE, hw3, hw030, hw050, hw065, hwm1, hw0, hwp1, hwp05, hwp03, hw02, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRW (x : State (Var 12)) : Formula.sat domRW x ↔
    (-(1:ℝ) ≤ x (Rv 10) ∧ x (Rv 10) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 11) ∧ x (Rv 11) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 7) ∧ x (Rv 7) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 5) ∧ x (Rv 5) ≤ (11:ℝ)/10 ∧ -(1:ℝ)/2 ≤ x (Rv 6) ∧ x (Rv 6) ≤ (3:ℝ)/20 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ (3:ℝ)/20 ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (4:ℝ)/5 ∧ -(1:ℝ) ≤ x (Rv 9) ∧ x (Rv 9) ≤ (11:ℝ)/10 ∧ -(1:ℝ) ≤ x (Rv 8) ∧ x (Rv 8) ≤ (3:ℝ)/20) := by
  simp only [domRW, hostEvolve, mRW, rover_terrain_6to12_IRv2, vsW]
  simp [Run.lowerF, Run.lowerE, hwm05, hw015, hw00, hw08, hwm10, hw11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end RoverTerrain6to12Modal

namespace RoverTerrain6to12Guarded

open DL DLCalTiming DLRel Parse Set RoverTerrain6to12Modal RoverTerrain6to12Pins

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
  simp [hostGuard, mRW, rover_terrain_6to12_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsW, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsW 12 Side.R (mRW 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRW, rover_terrain_6to12_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsW, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsW 12 Side.R (mRW 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRW, rover_terrain_6to12_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsW, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cstW_eq (q : ℕ) : cstW q = ladC q := rfl

/-- Decay rates of the uncoupled attitude coordinates (`ψ`, `φ`, `z` at rate 1; the pinned
coordinates frozen). Pitch (index 4) is driven by heave and has its own law, `φo` below. -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]

/-- The explicit attitude laws: pitch `θ(t) = (θ₀ + z₀ t / 2) e^{−t}` (`θ' = −θ + z/2`,
`z = z₀ e^{−t}`), every other coordinate `ρ_i e^{−d_i t}`. -/
noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  if i = 4 then (ρ (Rv 4) + 1/2 * ρ (Rv 8) * t) * Real.exp (-t)
  else ρ (Rv i) * Real.exp (-(dR i * t))

theorem φo_4 (ρ : State (Var 12)) (t : ℝ) :
    φo ρ 4 t = (ρ (Rv 4) + 1/2 * ρ (Rv 8) * t) * Real.exp (-t) := by simp [φo]

theorem φo_ne (ρ : State (Var 12)) (i : Fin 12) (h : i ≠ 4) (t : ℝ) :
    φo ρ i t = ρ (Rv i) * Real.exp (-(dR i * t)) := by simp [φo, h]

/-- The heave-driven pitch stays in `[−1/2, 3/20]` from that box, with heave in `[−1, 3/20]`. -/
theorem pitch_bound (a z t : ℝ) (ha0 : -(1:ℝ)/2 ≤ a) (ha1 : a ≤ (3:ℝ)/20) (hz0 : -(1:ℝ) ≤ z)
    (hz1 : z ≤ (3:ℝ)/20) (ht : 0 ≤ t) :
    -(1:ℝ)/2 ≤ (a + 1/2 * z * t) * Real.exp (-t) ∧ (a + 1/2 * z * t) * Real.exp (-t) ≤ 3/20 := by
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have h1 : 1 + t ≤ Real.exp t := by have := Real.add_one_le_exp t; linarith
  have hinv : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hk : (1 + t) * Real.exp (-t) ≤ 1 := by nlinarith
  have hup : a + 1/2 * z * t ≤ 3/20 * (1 + t) := by nlinarith
  have hlo : -(1/2) * (1 + t) ≤ a + 1/2 * z * t := by nlinarith
  constructor <;> nlinarith

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ² − 0.2 φ²`. -/
noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t) - 1/5 * (φo ρ 6 t * φo ρ 6 t)

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRW ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1:ℝ)/2 ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) ∧
    (-(1/2:ℝ) ≤ φo ρ 6 t ∧ φo ρ 6 t ≤ 3/20) := by
  have hD := (sat_domRW ρ).mp hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h6l, h6h, h2l, h2h, _, h4l, h4h, _, _, _, _, h8l, h8h⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (by simp [dR]) ht
  have b6 := decay_between (ρ (Rv 6)) (dR 6) t (by simp [dR]) ht
  rw [φo_ne ρ 2 (by decide), φo_ne ρ 6 (by decide), φo_4]
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    pitch_bound _ _ t h4l h4h h8l h8h ht,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b6.1,
      le_trans b6.2 (max_le h6h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT
  simp only [φo_4, φo_ne ρ 2 (by decide), φo_ne ρ 6 (by decide)]
  fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRW ρ) {t : ℝ} (ht : 0 ≤ t) :
    7/10 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩, ⟨h6l, h6h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem hfoR (q : ℕ) (hq : q < 3) (ρ : State (Var 12)) (i : Fin 12) (h0 : i ≠ 0) (h1 : i ≠ 1)
    (t : ℝ) : HasDerivAt (φo ρ i) (Term.eval (fRW q i) (trajR ρ (phiK φo kapT q ρ) t)) t := by
  by_cases h4 : i = 4
  · subst h4
    have hf : φo ρ 4 = fun u => (ρ (Rv 4) + 1/2 * ρ (Rv 8) * u) * Real.exp (-u) := by
      funext u; exact φo_4 ρ u
    have hd := hasDerivAt_coupled (ρ (Rv 4)) (1/2 * ρ (Rv 8)) t
    rw [hf]
    convert hd using 1
    rw [fRW4_eval q hq]
    simp [trajR_R, phiK, φo, dR]
    try ring
  · have hf : φo ρ i = fun u => ρ (Rv i) * Real.exp (-(dR i * u)) := by
      funext u; exact φo_ne ρ i h4 u
    have hd := hasDerivAt_decay (ρ (Rv i)) (dR i) t
    rw [hf]
    convert hd using 1
    fin_cases i
    · exact absurd rfl h0
    · exact absurd rfl h1
    all_goals
      simp only [Fin.reduceFinMk, Fin.isValue]
      first
        | exact absurd rfl h4
        | (rw [fRW2_eval q hq]) | (rw [fRW3_eval q hq]) | (rw [fRW5_eval q hq])
        | (rw [fRW6_eval q hq]) | (rw [fRW7_eval q hq]) | (rw [fRW8_eval q hq])
        | (rw [fRW9_eval q hq]) | (rw [fRW10_eval q hq]) | (rw [fRW11_eval q hq])
      try simp [trajR_R, phiK, φo, dR]

/-- The odometer rate `v ((1 − ψ²/2 − 0.3 θ²) − 0.2 φ²)` lies in `[0, 0.8]`. -/
theorem odo_rate3 (v a b c : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 4/5) (ha0 : -(3/5) ≤ a) (ha1 : a ≤ 3/5)
    (hb0 : -(3/5) ≤ b) (hb1 : b ≤ 3/5) (hc0 : -(3/5) ≤ c) (hc1 : c ≤ 3/5) :
    0 ≤ v * (((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c)) ∧
      v * (((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c)) ≤ 4/5 := by
  have ha2 : a * a ≤ 9/25 := by nlinarith
  have hb2 : b * b ≤ 9/25 := by nlinarith
  have hc2 : c * c ≤ 9/25 := by nlinarith
  have hk0 : 0 ≤ ((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c) := by nlinarith
  have hk1 : ((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c) ≤ 1 := by
    nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]
  exact ⟨mul_nonneg hv0 hk0, by nlinarith [mul_le_mul_of_nonneg_left hk1 hv0]⟩

noncomputable def LR : LadderRun GrG domRW :=
  LadderRun.ofKappa GrG domRW modeW fRW φo kapT (7/10) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRW0_eval q hq, cstW_eq])
    (fun ρ i _ _ => by
      by_cases h : i = 4
      · subst h; simp [φo]
      · simp [φo, h])
    (fun q hq ρ _ i h0 h1 t _ => hfoR q hq ρ i h0 h1 t)
    (fun q hq ρ _ t _ => by
      rw [fRW1_eval q hq, trajR_R, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide),
        phiK_other _ _ q ρ 6 (by decide) (by decide)]
      simp only [kapT]
      try ring)
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRW ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (7/10) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 → k ≠ 4 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 h4 => by
          rw [phiK_other φo kapT q ρ k h0 h1, φo_ne ρ k h4]
          exact decay_between _ _ t (by fin_cases k <;> simp [dR]) ht
      have hp := (φo_bounds ρ hρ ht).2.1
      rw [← phiK_other φo kapT q ρ 4 (by decide) (by decide)] at hp
      obtain ⟨h10l, h10h, h11l, h11h, h7l, h7h, h3l, h3h, h5l, h5h, h6l, h6h, h2l, h2h, h1l, h4l,
        h4h, h0l, h0h, h9l, h9h, h8l, h8h⟩ := hD
      rw [sat_domRW]
      simp only [trajR_R]
      exact ⟨le_trans (le_min h10l (by norm_num)) (hk 10 (by decide) (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide) (by decide)).2 (max_le h10h (by norm_num)),
        le_trans (le_min h11l (by norm_num)) (hk 11 (by decide) (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide) (by decide)).2 (max_le h11h (by norm_num)),
        le_trans (le_min h7l (by norm_num)) (hk 7 (by decide) (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide) (by decide)).2 (max_le h7h (by norm_num)),
        le_trans (le_min h3l (by norm_num)) (hk 3 (by decide) (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide) (by decide)).2 (max_le h3h (by norm_num)),
        le_trans (le_min h5l (by norm_num)) (hk 5 (by decide) (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide) (by decide)).2 (max_le h5h (by norm_num)),
        le_trans (le_min h6l (by norm_num)) (hk 6 (by decide) (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide) (by decide)).2 (max_le h6h (by norm_num)),
        le_trans (le_min h2l (by norm_num)) (hk 2 (by decide) (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide) (by decide)).2 (max_le h2h (by norm_num)),
        le_trans h1l hs,
        hp.1, hp.2,
        le_trans (le_min h0l (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le h0h (by linarith [hc.2])),
        le_trans (le_min h9l (by norm_num)) (hk 9 (by decide) (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide) (by decide)).2 (max_le h9h (by norm_num)),
        le_trans (le_min h8l (by norm_num)) (hk 8 (by decide) (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide) (by decide)).2 (max_le h8h (by norm_num))⟩)
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

theorem epsR_eq : epsR rover_terrain_6to12_IRv2 = 1 := by
  simp [epsR, rover_terrain_6to12_IRv2, gp_1_0]

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
    have ha0 : -(1:ℝ)/2 ≤ s (Rv 2) := by rw [sat_domRW] at hs; tauto
    have ha1 : s (Rv 2) ≤ (3:ℝ)/20 := by rw [sat_domRW] at hs; tauto
    have hb0 : -(1:ℝ)/2 ≤ s (Rv 4) := by rw [sat_domRW] at hs; tauto
    have hb1 : s (Rv 4) ≤ (3:ℝ)/20 := by rw [sat_domRW] at hs; tauto
    have hc0 : -(1:ℝ)/2 ≤ s (Rv 6) := by rw [sat_domRW] at hs; tauto
    have hc1 : s (Rv 6) ≤ (3:ℝ)/20 := by rw [sat_domRW] at hs; tauto
    rw [fRW1_eval q hq]
    exact odo_rate3 _ _ _ _ h0 h1 (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
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

/-- **Assumption 1 for `rover_terrain_6to12`**, every mode, Z3-free. -/
theorem rover_terrain_6to12_wellFormedR :
    WellFormedR GrG guardR (epsR rover_terrain_6to12_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverTerrain6to12Guarded

end RelCertifier
