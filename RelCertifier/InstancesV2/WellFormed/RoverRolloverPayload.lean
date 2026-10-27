/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_payload`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three route zones `STEEP`, `MODER`, `FLAT` with their band guards and declared `next` lists,
back edges included), the lowered right guards, and `ε_r = 1` read from the file.

The right model is the canonical rover at the nominal payload, level `L12` with the roll-slip
coupling live: per zone `q` (speed set point `c_q` = 3, 5, 6.5 m/s, grade `g_q` = 0.15, 0.05, 0,
cross-slope `x_q` = 0.1, 0.05, 0), with the lateral load `G = v (ω_ψ − ψ)`,
`v' = (c_q − v)/2`, `s' = v (1 − ψ²/2 − 0.3 θ² − 0.2 φ²)`, `ψ' = ω_ψ − ψ`, `ω_ψ' = −ω_ψ`,
`θ' = ω_θ − θ`, `ω_θ' = −ω_θ + g_q + z/2`, `z' = ω_z − z`, `ω_z' = −ω_z`, `φ' = ω_φ − φ`,
`ω_φ' = −ω_φ + x_q + 0.015 (G + (y − 2 ω_y) + 0.03 (G + 9.81 φ))`, `y' = ω_y − y`,
`ω_y' = −ω_y + 0.03 (G + 9.81 φ)`; the evolve box `0 ≤ v ≤ 8`, `s ≥ 0`, `|ψ|, |ω_ψ|, |θ|, |ω_θ|
≤ 0.6`, `|z|, |ω_z| ≤ 0.15`, `|φ|, |ω_φ|, |y|, |ω_y| ≤ 0.5`; the guards are the odometer bands
`[0, 62)`, `[58, 142)`, `[138, ∞)`; `STEEP → {MODER, STEEP}`, `MODER → {FLAT, MODER, STEEP}`,
`FLAT → {FLAT, MODER}`.

* (ii), every zone: on the box `0 ≤ s' ≤ 8` (the attitude factor lies in `[0.66, 1]`), so the
  odometer does not fall and grows by at most 8 in one interval: a `STEEP` run ends in
  `[0, 70)`, inside `STEEP` or `MODER`; a `MODER` run in `[58, 150)`, inside `MODER` or `FLAT`;
  `FLAT` (`s ≥ 138`) is kept. The back edges are never needed.
* Existence (i). The roll-slip block `(φ, ω_φ, y, ω_y)` is coupled both ways (`φ → ω_y → y →
  ω_φ → φ`), so there is no explicit cascade run. The run is built by Picard–Lindelöf on a
  slightly ENLARGED box `B_δ` (bounds `8.01`, `0.62/0.61`, `0.17/0.16`, `0.52/0.51`, `v ≥ −0.01`,
  `s` free), on which every face is STRICTLY inflowing (`strict_faces_raw`: the position faces
  gain the margin `0.01` from their rate partners, the rate faces from the forcing bounds
  `|ω_φ| ≤ 0.28`, `|ω_y| ≤ 0.45` with `|G| ≤ 9.86`); the field reads no `s`, no left and no
  auxiliary coordinate, so its Lipschitz constant and bound on every ball around a `B_δ` point
  are those on one fixed ball (`proj`, as `odeField_slab_lipschitz`); `chainN` glues uniform
  Picard steps to duration 1. On that run the TRUE box is then recovered coordinate by
  coordinate (`drive_le`, the driven-contraction bound): `v`, `ω_ψ`, `ω_z` first, then `ψ`, `z`,
  `ω_θ`, `θ`, then `ω_φ` (forcing at most `0.28` over `B_δ`), `ω_y` (at most `0.45`), then `φ`,
  `y`, and `s ≥ s₀` (`s' ≥ 0`).
Z3-free; the Picard machinery of `Proofs/Flow/PicardBridge.lean` and
`Proofs/Flow/BoxViability.lean`, modelled on `hExist_cubic`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Flow.BoxViability
import RelCertifier.InstancesV2.BenchIR.rover_rollover_payload

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverRolloverPayload

open DL DLCalTiming DLRel Parse Set

def vs : List String :=
  ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi",
   "y", "omega_y"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := rover_rollover_payload_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 12 → Term (Var 12) := hostDyn vs 12 Side.R (mR q)
noncomputable def domR : Formula (Var 12) := hostEvolve vs 12 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_m0_15 : Run.parseRat "-0.15" = some ((-3:ℚ)/20) := by
  have h : parseQ "-0.15" = some (⟨-15, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m0_5 : Run.parseRat "-0.5" = some ((-1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m0_6 : Run.parseRat "-0.6" = some ((-3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m1 : Run.parseRat "-1" = some (-1 : ℚ) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_015 : Run.parseRat "0.015" = some ((3:ℚ)/200) := by
  have h : parseQ "0.015" = some (⟨15, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_03 : Run.parseRat "0.03" = some ((3:ℚ)/100) := by
  have h : parseQ "0.03" = some (⟨3, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_15 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_2 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_138_0 : Run.parseRat "138.0" = some (138 : ℚ) := by
  have h : parseQ "138.0" = some (⟨1380, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_142_0 : Run.parseRat "142.0" = some (142 : ℚ) := by
  have h : parseQ "142.0" = some (⟨1420, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_2 : Run.parseRat "2" = some (2 : ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_3_0 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_5_0 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_58_0 : Run.parseRat "58.0" = some (58 : ℚ) := by
  have h : parseQ "58.0" = some (⟨580, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_6_5 : Run.parseRat "6.5" = some ((13:ℚ)/2) := by
  have h : parseQ "6.5" = some (⟨65, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_62_0 : Run.parseRat "62.0" = some (62 : ℚ) := by
  have h : parseQ "62.0" = some (⟨620, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_8_0 : Run.parseRat "8.0" = some (8 : ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_9_81 : Run.parseRat "9.81" = some ((981:ℚ)/100) := by
  have h : parseQ "9.81" = some (⟨981, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The zones' speed set points (3, 5, 6.5 m/s). -/
noncomputable def cV (q : ℕ) : ℝ := if q = 0 then 3 else if q = 1 then 5 else 13/2
/-- The zones' grades (0.15, 0.05, 0). -/
noncomputable def cT (q : ℕ) : ℝ := if q = 0 then 3/20 else if q = 1 then 1/20 else 0
/-- The zones' cross-slopes (0.1, 0.05, 0). -/
noncomputable def cP (q : ℕ) : ℝ := if q = 0 then 1/10 else if q = 1 then 1/20 else 0

theorem consts (q : ℕ) (hq : q < 3) :
    3 ≤ cV q ∧ cV q ≤ 13/2 ∧ 0 ≤ cT q ∧ cT q ≤ 3/20 ∧ 0 ≤ cP q ∧ cP q ≤ 1/10 := by
  interval_cases q <;> norm_num [cV, cT, cP]

theorem f0 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 0) x = 1/2 * (cV q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cV]

theorem f1 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 1) x = x (Rv 0) * (((1 - 1/2 * (x (Rv 2) * x (Rv 2))) -
      3/10 * (x (Rv 4) * x (Rv 4))) - 1/5 * (x (Rv 8) * x (Rv 8))) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem f2 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 2) x = x (Rv 3) - x (Rv 2) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem f3 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 3) x = -1 * x (Rv 3) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem f4 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 4) x = x (Rv 5) - x (Rv 4) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem f5 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 5) x = -1 * x (Rv 5) + cT q + 1/2 * x (Rv 6) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cT] <;> ring

theorem f6 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 6) x = x (Rv 7) - x (Rv 6) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem f7 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 7) x = -1 * x (Rv 7) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem f8 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 8) x = x (Rv 9) - x (Rv 8) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

/-- The lateral load `G = v (ω_ψ − ψ)`. -/
def lat (x : State (Var 12)) : ℝ := x (Rv 0) * (x (Rv 3) - x (Rv 2))

theorem f9 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 9) x = -1 * x (Rv 9) + cP q +
      3/200 * (lat x + (x (Rv 10) - 2 * x (Rv 11)) + 3/100 * (lat x + 981/100 * x (Rv 8))) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cP, lat] <;> ring

theorem f10 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 10) x = x (Rv 11) - x (Rv 10) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem f11 (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    Term.eval (fR q 11) x = -1 * x (Rv 11) + 3/100 * (lat x + 981/100 * x (Rv 8)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_rollover_payload_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, lat] <;> ring

/-- The evolve box (every zone's). -/
def Box (x : State (Var 12)) : Prop :=
  0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8 ∧ 0 ≤ x (Rv 1) ∧
    -3/5 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/5 ∧ -3/5 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/5 ∧
    -3/5 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 3/5 ∧ -3/5 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧
    -3/20 ≤ x (Rv 6) ∧ x (Rv 6) ≤ 3/20 ∧ -3/20 ≤ x (Rv 7) ∧ x (Rv 7) ≤ 3/20 ∧
    -1/2 ≤ x (Rv 8) ∧ x (Rv 8) ≤ 1/2 ∧ -1/2 ≤ x (Rv 9) ∧ x (Rv 9) ≤ 1/2 ∧
    -1/2 ≤ x (Rv 10) ∧ x (Rv 10) ≤ 1/2 ∧ -1/2 ≤ x (Rv 11) ∧ x (Rv 11) ≤ 1/2

theorem sat_domR (x : State (Var 12)) : Formula.sat domR x ↔ Box x := by
  simp only [domR, hostEvolve, mR, rover_rollover_payload_IRv2, vs, Box]
  simp [Run.lowerF, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 12) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 12) :=
  { src := s, tgt := t, guard := hostGuard vs 12 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (STEEP 0, MODER 1, FLAT 2), back edges included. -/
def edgeList : List (ℕ × ℕ) := [(0, 1), (0, 0), (1, 2), (1, 1), (1, 0), (2, 2), (2, 1)]

noncomputable def Gr : SearchGraph (Var 12) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 12)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  have hlen : q < 3 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 3 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_g0 (ν : State (Var 12)) :
    Formula.sat (hostGuard vs 12 Side.R (mR 0)) ν ↔ (0 ≤ ν (Rv 1) ∧ ν (Rv 1) < 62) := by
  simp [hostGuard, mR, rover_rollover_payload_IRv2, Run.lowerF, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g1 (ν : State (Var 12)) :
    Formula.sat (hostGuard vs 12 Side.R (mR 1)) ν ↔ (58 ≤ ν (Rv 1) ∧ ν (Rv 1) < 142) := by
  simp [hostGuard, mR, rover_rollover_payload_IRv2, Run.lowerF, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g2 (ν : State (Var 12)) :
    Formula.sat (hostGuard vs 12 Side.R (mR 2)) ν ↔ 138 ≤ ν (Rv 1) := by
  simp [hostGuard, mR, rover_rollover_payload_IRv2, Run.lowerF, Run.lowerE, hp_m0_15, hp_m0_5, hp_m0_6, hp_m1, hp_0_0, hp_0_015, hp_0_03, hp_0_05, hp_0_1, hp_0_15, hp_0_2, hp_0_3, hp_0_5, hp_0_6, hp_1, hp_138_0, hp_142_0, hp_2, hp_3_0, hp_5_0, hp_58_0, hp_6_5, hp_62_0, hp_8_0, hp_9_81, hp_1_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vs 12 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR rover_rollover_payload_IRv2 = 1 := by
  simp [epsR, rover_rollover_payload_IRv2, hp_1_0]

/-! ## The odometer rate on the box -/

/-- The attitude factor `1 − ψ²/2 − 0.3 θ² − 0.2 φ²` is positive for `|ψ|, |θ| ≤ 0.62`,
`|φ| ≤ 0.52`. -/
theorem factor_pos (a b c : ℝ) (ha1 : -31/50 ≤ a) (ha2 : a ≤ 31/50) (hb1 : -31/50 ≤ b)
    (hb2 : b ≤ 31/50) (hc1 : -13/25 ≤ c) (hc2 : c ≤ 13/25) :
    0 ≤ ((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c) := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 31/50 - a) (by linarith : (0:ℝ) ≤ 31/50 + a),
    mul_nonneg (by linarith : (0:ℝ) ≤ 31/50 - b) (by linarith : (0:ℝ) ≤ 31/50 + b),
    mul_nonneg (by linarith : (0:ℝ) ≤ 13/25 - c) (by linarith : (0:ℝ) ≤ 13/25 + c)]

theorem factor_le_one (a b c : ℝ) :
    ((1 - 1/2 * (a * a)) - 3/10 * (b * b)) - 1/5 * (c * c) ≤ 1 := by
  nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]

theorem s_rate (q : ℕ) (hq : q < 3) (x : State (Var 12)) (h : Box x) :
    0 ≤ Term.eval (fR q 1) x ∧ Term.eval (fR q 1) x ≤ 8 := by
  obtain ⟨v0, v1, -, a1, a2, -, -, b1, b2, -, -, -, -, -, -, c1, c2, -⟩ := h
  rw [f1 q hq]
  have hf := factor_pos (x (Rv 2)) (x (Rv 4)) (x (Rv 8)) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hf1 := factor_le_one (x (Rv 2)) (x (Rv 4)) (x (Rv 8))
  exact ⟨mul_nonneg v0 hf, by nlinarith [mul_le_mul_of_nonneg_left hf1 v0]⟩

/-! ## Existence: Picard on the enlarged box, then the true box -/

/-- The right block of zone `q`. -/
noncomputable abbrev sysR (q : ℕ) : ODESystem (Var 12) := rightBlock (fR q) (Term.const 1)

theorem hwfR (q : ℕ) : (sysR q).WellFormed := rightBlock_wellFormed _ _

theorem field_R (q : ℕ) (x : State (Var 12)) (i : Fin 12) :
    odeField (sysR q) x (Rv i) = Term.eval (fR q i) x :=
  odeField_rightBlock_unit _ _ _

theorem field_nonR (q : ℕ) (x : State (Var 12)) (y : Var 12) (hy : y.1 ≠ Side.R) :
    odeField (sysR q) x y = 0 := by
  have hb : y ∉ (sysR q).bound := by
    intro hb
    simp only [sysR, rightBlock, ODESystem.bound, List.map_map, List.mem_map] at hb
    obtain ⟨i, -, hi⟩ := hb
    apply hy; rw [← hi]; rfl
  simp only [odeField, if_neg hb]

/-! ### Uniform Picard data: the field reads neither `s` nor any non-right coordinate -/

/-- Zero every coordinate the right fields do not read (the odometer, the left, the auxiliary
coordinates). -/
noncomputable def proj (x : State (Var 12)) : State (Var 12) :=
  fun y => if y.1 = Side.R ∧ y.2 ≠ 1 then x y else 0

theorem proj_lip : LipschitzWith 1 proj := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  by_cases h : i.1 = Side.R ∧ i.2 ≠ 1
  · simp only [proj, if_pos h]; exact dist_le_pi_dist x y i
  · simp only [proj, if_neg h, dist_self]; exact dist_nonneg

theorem field_proj (q : ℕ) (hq : q < 3) (x : State (Var 12)) :
    odeField (sysR q) x = odeField (sysR q) (proj x) := by
  funext y
  rcases y with ⟨sd, i⟩
  cases sd
  · rw [field_nonR q x _ (by simp), field_nonR q _ _ (by simp)]
  · show odeField (sysR q) x (Rv i) = odeField (sysR q) (proj x) (Rv i)
    rw [field_R, field_R]
    match i with
    | 0 => rw [f0 q hq, f0 q hq]; simp [proj, Rv]
    | 1 => rw [f1 q hq, f1 q hq]; simp [proj, Rv]
    | 2 => rw [f2 q hq, f2 q hq]; simp [proj, Rv]
    | 3 => rw [f3 q hq, f3 q hq]; simp [proj, Rv]
    | 4 => rw [f4 q hq, f4 q hq]; simp [proj, Rv]
    | 5 => rw [f5 q hq, f5 q hq]; simp [proj, Rv]
    | 6 => rw [f6 q hq, f6 q hq]; simp [proj, Rv]
    | 7 => rw [f7 q hq, f7 q hq]; simp [proj, Rv]
    | 8 => rw [f8 q hq, f8 q hq]; simp [proj, Rv]
    | 9 => rw [f9 q hq, f9 q hq]; simp [proj, Rv, lat]
    | 10 => rw [f10 q hq, f10 q hq]; simp [proj, Rv]
    | 11 => rw [f11 q hq, f11 q hq]; simp [proj, Rv, lat]
  · rw [field_nonR q x _ (by simp), field_nonR q _ _ (by simp)]

/-- The enlarged box `B_δ` (no bound on `s`). -/
def BoxD (x : State (Var 12)) : Prop :=
  -1/100 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 801/100 ∧
    -31/50 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 31/50 ∧ -61/100 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 61/100 ∧
    -31/50 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 31/50 ∧ -61/100 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 61/100 ∧
    -17/100 ≤ x (Rv 6) ∧ x (Rv 6) ≤ 17/100 ∧ -4/25 ≤ x (Rv 7) ∧ x (Rv 7) ≤ 4/25 ∧
    -13/25 ≤ x (Rv 8) ∧ x (Rv 8) ≤ 13/25 ∧ -51/100 ≤ x (Rv 9) ∧ x (Rv 9) ≤ 51/100 ∧
    -13/25 ≤ x (Rv 10) ∧ x (Rv 10) ≤ 13/25 ∧ -51/100 ≤ x (Rv 11) ∧ x (Rv 11) ≤ 51/100

theorem boxD_of_box {x : State (Var 12)} (h : Box x) : BoxD x := by
  obtain ⟨h0, h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21⟩ := h
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem proj_R (ν : State (Var 12)) (j : Fin 12) (hj : j ≠ 1) :
    proj ν (Side.R, j) = ν (Side.R, j) := by simp [proj, hj]

theorem proj_s (ν : State (Var 12)) : proj ν (Side.R, 1) = 0 := by simp [proj]

theorem proj_nonR (ν : State (Var 12)) (y : Var 12) (hy : y.1 ≠ Side.R) : proj ν y = 0 := by
  simp [proj, hy]

theorem proj_norm {ν : State (Var 12)} (h : BoxD ν) : ‖proj ν‖ ≤ 9 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := h
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun y => ?_)
  rw [Real.norm_eq_abs, abs_le]
  rcases y with ⟨sd, i⟩
  cases sd
  · rw [proj_nonR ν _ (by simp)]; norm_num
  · by_cases hi : i = 1
    · subst hi; rw [proj_s]; norm_num
    · rw [proj_R ν i hi]
      match i with
      | 0 => show -9 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 9; constructor <;> linarith
      | 1 => exact absurd rfl hi
      | 2 => show -9 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 9; constructor <;> linarith
      | 3 => show -9 ≤ ν (Rv 3) ∧ ν (Rv 3) ≤ 9; constructor <;> linarith
      | 4 => show -9 ≤ ν (Rv 4) ∧ ν (Rv 4) ≤ 9; constructor <;> linarith
      | 5 => show -9 ≤ ν (Rv 5) ∧ ν (Rv 5) ≤ 9; constructor <;> linarith
      | 6 => show -9 ≤ ν (Rv 6) ∧ ν (Rv 6) ≤ 9; constructor <;> linarith
      | 7 => show -9 ≤ ν (Rv 7) ∧ ν (Rv 7) ≤ 9; constructor <;> linarith
      | 8 => show -9 ≤ ν (Rv 8) ∧ ν (Rv 8) ≤ 9; constructor <;> linarith
      | 9 => show -9 ≤ ν (Rv 9) ∧ ν (Rv 9) ≤ 9; constructor <;> linarith
      | 10 => show -9 ≤ ν (Rv 10) ∧ ν (Rv 10) ≤ 9; constructor <;> linarith
      | 11 => show -9 ≤ ν (Rv 11) ∧ ν (Rv 11) ≤ 9; constructor <;> linarith
  · rw [proj_nonR ν _ (by simp)]; norm_num

/-- The projected ball around a `B_δ` point lies in the fixed ball `closedBall 0 11`. -/
theorem proj_ball {ν x : State (Var 12)} (h : BoxD ν) (hx : x ∈ Metric.closedBall ν 1) :
    proj x ∈ Metric.closedBall (0 : State (Var 12)) 11 := by
  rw [Metric.mem_closedBall] at hx ⊢
  have h1 : dist (proj x) (proj ν) ≤ dist x ν := by
    have := proj_lip.dist_le_mul x ν
    simpa using this
  have h2 : dist (proj ν) 0 ≤ 9 := by rw [dist_zero_right]; exact proj_norm h
  linarith [dist_triangle (proj x) (proj ν) 0]

theorem picard_data (q : ℕ) (hq : q < 3) : ∃ K L : NNReal,
    (∀ ν, BoxD ν → LipschitzOnWith K (odeField (sysR q)) (Metric.closedBall ν 1)) ∧
    (∀ ν, BoxD ν → ∀ x ∈ Metric.closedBall ν 1, ‖odeField (sysR q) x‖ ≤ (L : ℝ)) := by
  obtain ⟨K, hK⟩ := odeField_lipschitzOnWith (sysR q) (0 : State (Var 12)) 11
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : State (Var 12)) 11).exists_bound_of_continuousOn
    ((odeField_contDiff (sysR q)).continuous.continuousOn)
  refine ⟨K, C.toNNReal, fun ν hν => ?_, fun ν hν x hx => ?_⟩
  · intro x hx y hy
    rw [field_proj q hq x, field_proj q hq y]
    calc edist (odeField (sysR q) (proj x)) (odeField (sysR q) (proj y))
        ≤ K * edist (proj x) (proj y) := hK (proj_ball hν hx) (proj_ball hν hy)
      _ ≤ K * edist x y := by
          apply mul_le_mul_left'
          calc edist (proj x) (proj y) ≤ 1 * edist x y := proj_lip.edist_le_mul x y
            _ = edist x y := by rw [one_mul]
  · rw [field_proj q hq x]
    calc ‖odeField (sysR q) (proj x)‖ ≤ C := hC _ (proj_ball hν hx)
      _ ≤ max C 0 := le_max_left _ _
      _ = (C.toNNReal : ℝ) := (Real.coe_toNNReal' C).symm

/-! ### The enlarged box is strictly inflowing -/

/-- The 22 faces of `B_δ`, each `≤ 0` inside. -/
noncomputable def faces : List (State (Var 12) → ℝ) :=
  [fun y => y (Rv 0) - 801/100, fun y => -1/100 - y (Rv 0),
   fun y => y (Rv 2) - 31/50, fun y => -31/50 - y (Rv 2),
   fun y => y (Rv 3) - 61/100, fun y => -61/100 - y (Rv 3),
   fun y => y (Rv 4) - 31/50, fun y => -31/50 - y (Rv 4),
   fun y => y (Rv 5) - 61/100, fun y => -61/100 - y (Rv 5),
   fun y => y (Rv 6) - 17/100, fun y => -17/100 - y (Rv 6),
   fun y => y (Rv 7) - 4/25, fun y => -4/25 - y (Rv 7),
   fun y => y (Rv 8) - 13/25, fun y => -13/25 - y (Rv 8),
   fun y => y (Rv 9) - 51/100, fun y => -51/100 - y (Rv 9),
   fun y => y (Rv 10) - 13/25, fun y => -13/25 - y (Rv 10),
   fun y => y (Rv 11) - 51/100, fun y => -51/100 - y (Rv 11)]

theorem faces_iff (x : State (Var 12)) : (∀ g ∈ faces, g x ≤ 0) ↔ BoxD x := by
  constructor
  · intro h
    simp only [faces, List.forall_mem_cons, List.forall_mem_nil, and_true] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      h18, h19, h20, h21⟩ := h
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩
  · intro hB g hg
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      h18, h19, h20, h21⟩ := hB
    simp only [faces, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only; linarith)

theorem faces_diff : ∀ g ∈ faces, Differentiable ℝ g := by
  intro g hg
  simp only [faces, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fun_prop

theorem lie_up (q : ℕ) (i : Fin 12) (c : ℝ) (x : State (Var 12)) :
    Lie (sysR q) (fun y => y (Rv i) - c) x = Term.eval (fR q i) x := by
  have heq : (fun y : State (Var 12) => y (Rv i) - c) = (fun y => (1:ℝ) * y (Rv i) + (-c)) := by
    funext y; ring
  rw [heq, lie_affine_coord _ (hwfR q) (Rv i) 1 (-c) x, field_R]; ring

theorem lie_dn (q : ℕ) (i : Fin 12) (c : ℝ) (x : State (Var 12)) :
    Lie (sysR q) (fun y => c - y (Rv i)) x = -Term.eval (fR q i) x := by
  have heq : (fun y : State (Var 12) => c - y (Rv i)) = (fun y => (-1:ℝ) * y (Rv i) + c) := by
    funext y; ring
  rw [heq, lie_affine_coord _ (hwfR q) (Rv i) (-1) c x, field_R]; ring

/-- `|v (ω_ψ − ψ)| ≤ 9.86` for `v ∈ [−0.01, 8.01]`, `|ω_ψ − ψ| ≤ 1.23`. -/
theorem prod_bd (a w : ℝ) (h1 : -1/100 ≤ a) (h2 : a ≤ 801/100) (h3 : -123/100 ≤ w)
    (h4 : w ≤ 123/100) : -986/100 ≤ a * w ∧ a * w ≤ 986/100 := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h4),
      mul_nonneg (by linarith : (0:ℝ) ≤ a + 1/100) (by linarith : (0:ℝ) ≤ w + 123/100)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0:ℝ) ≤ w + 123/100),
      mul_nonneg (by linarith : (0:ℝ) ≤ a + 1/100) (sub_nonneg.2 h4)]

theorem lat_bd {x : State (Var 12)} (h : BoxD x) : -986/100 ≤ lat x ∧ lat x ≤ 986/100 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := h
  unfold lat
  exact prod_bd _ _ h0 h1 (by linarith) (by linarith)

theorem faces_strict (q : ℕ) (hq : q < 3) :
    ∀ g ∈ faces, ∀ x, (∀ g' ∈ faces, g' x ≤ 0) → g x = 0 → Lie (sysR q) g x < 0 := by
  intro g hg x hx hgx
  have hB := (faces_iff x).mp hx
  have hG := lat_bd hB
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := hB
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := consts q hq
  simp only [faces, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only at hgx; rw [lie_up, f0 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f0 q hq]; linarith
  · simp only at hgx; rw [lie_up, f2 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f2 q hq]; linarith
  · simp only at hgx; rw [lie_up, f3 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f3 q hq]; linarith
  · simp only at hgx; rw [lie_up, f4 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f4 q hq]; linarith
  · simp only at hgx; rw [lie_up, f5 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f5 q hq]; linarith
  · simp only at hgx; rw [lie_up, f6 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f6 q hq]; linarith
  · simp only at hgx; rw [lie_up, f7 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f7 q hq]; linarith
  · simp only at hgx; rw [lie_up, f8 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f8 q hq]; linarith
  · simp only at hgx; rw [lie_up, f9 q hq]; linarith [hG.1, hG.2]
  · simp only at hgx; rw [lie_dn, f9 q hq]; linarith [hG.1, hG.2]
  · simp only at hgx; rw [lie_up, f10 q hq]; linarith
  · simp only at hgx; rw [lie_dn, f10 q hq]; linarith
  · simp only at hgx; rw [lie_up, f11 q hq]; linarith [hG.1, hG.2]
  · simp only at hgx; rw [lie_dn, f11 q hq]; linarith [hG.1, hG.2]

/-- **Every integral curve from `B_δ` stays in `B_δ`** (strict faces, first-exit argument). -/
theorem boxD_inv (q : ℕ) (hq : q < 3) {r : ℝ} {Φ : ℝ → State (Var 12)}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField (sysR q)) (Icc 0 r)) (h0 : BoxD (Φ 0)) :
    ∀ t ∈ Icc (0:ℝ) r, BoxD (Φ t) := by
  have h := strict_faces_raw (hwfR q) faces faces_diff (faces_strict q hq) hcurve
    ((faces_iff _).mpr h0)
  exact fun t ht => (faces_iff _).mp (h t ht)

/-! ### The true box on the run (driven contractions) -/

/-- **Driven-contraction bound** (scalar form of `driven_bound_raw`): `y' ≤ M − λ y` and
`M ≤ λ C` keep `y ≤ C`. -/
theorem drive_le {y d : ℝ → ℝ} {r lam M C : ℝ} (hlam : 0 < lam) (hC : M ≤ lam * C)
    (hy : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt y (d t) (Icc 0 r) t)
    (hd : ∀ t ∈ Icc (0:ℝ) r, d t ≤ M - lam * y t) (h0 : y 0 ≤ C) :
    ∀ t ∈ Icc (0:ℝ) r, y t ≤ C := by
  set g : ℝ → ℝ := fun t => (y t - C) * Real.exp (lam * t) with hg
  have hgd : ∀ t ∈ Icc (0:ℝ) r,
      HasDerivWithinAt g ((d t + lam * (y t - C)) * Real.exp (lam * t)) (Icc 0 r) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun u => y u - C) (d t) (Icc 0 r) t := (hy t ht).sub_const C
    have h2 : HasDerivWithinAt (fun u => Real.exp (lam * u)) (lam * Real.exp (lam * t))
        (Icc 0 r) t := by
      have := (((hasDerivWithinAt_id t (Icc 0 r)).const_mul lam).exp)
      simpa [mul_comm] using this
    have hm := h1.mul h2
    have heq : d t * Real.exp (lam * t) + (y t - C) * (lam * Real.exp (lam * t))
        = (d t + lam * (y t - C)) * Real.exp (lam * t) := by ring
    rw [← heq]; exact hm
  have hcont : ContinuousOn g (Icc 0 r) := fun t ht => (hgd t ht).continuousWithinAt
  have hanti : AntitoneOn g (Icc 0 r) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hcont (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact ((hgd x (Ioo_subset_Icc_self hx)).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hxIcc := Ioo_subset_Icc_self hx
      rw [((hgd x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
      have hexp : 0 < Real.exp (lam * x) := Real.exp_pos _
      have hdr := hd x hxIcc
      have : d x + lam * (y x - C) ≤ 0 := by nlinarith [hdr, hC]
      exact mul_nonpos_of_nonpos_of_nonneg this (le_of_lt hexp)
  intro t ht
  have hle := hanti (left_mem_Icc.mpr (le_trans ht.1 ht.2)) ht ht.1
  simp only [hg, mul_zero, Real.exp_zero, mul_one] at hle
  have hexp : 0 < Real.exp (lam * t) := Real.exp_pos _
  have hle0 : (y t - C) * Real.exp (lam * t) ≤ 0 := le_trans hle (by linarith [h0])
  have hneg : y t - C ≤ 0 := by
    by_contra h; push_neg at h
    nlinarith [mul_pos h hexp, hle0]
  linarith [hneg]

/-- Both sides of a driven coordinate: `y' ≤ Mu − λ y`, `−y' ≤ Ml + λ y`. -/
theorem drive_two {y d : ℝ → ℝ} {r lam Mu Ml lo hi : ℝ} (hlam : 0 < lam)
    (hy : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt y (d t) (Icc 0 r) t)
    (hu : ∀ t ∈ Icc (0:ℝ) r, d t ≤ Mu - lam * y t) (hMu : Mu ≤ lam * hi)
    (hl : ∀ t ∈ Icc (0:ℝ) r, -d t ≤ Ml + lam * y t) (hMl : Ml ≤ lam * (-lo))
    (h0 : lo ≤ y 0 ∧ y 0 ≤ hi) : ∀ t ∈ Icc (0:ℝ) r, lo ≤ y t ∧ y t ≤ hi := by
  have hup := drive_le hlam hMu hy hu h0.2
  have hdn := drive_le (y := fun u => -y u) (d := fun u => -d u) hlam hMl
    (fun t ht => (hy t ht).neg) (fun t ht => by have := hl t ht; linarith)
    (by linarith [h0.1])
  intro t ht
  exact ⟨by have := hdn t ht; linarith, hup t ht⟩

theorem coord_der (q : ℕ) {r : ℝ} {Φ : ℝ → State (Var 12)}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField (sysR q)) (Icc 0 r)) (i : Fin 12) :
    ∀ t ∈ Icc (0:ℝ) r,
      HasDerivWithinAt (fun u => Φ u (Rv i)) (Term.eval (fR q i) (Φ t)) (Icc 0 r) t := by
  intro t ht
  have h1 : HasDerivWithinAt (fun u => Φ u (Rv i)) (odeField (sysR q) (Φ t) (Rv i)) (Icc 0 r) t :=
    (hasDerivWithinAt_pi.mp (hcurve t ht)) (Rv i)
  rw [field_R] at h1
  exact h1

/-- **The run of zone `q` from a box state stays in the box** (all its coordinates). -/
theorem box_refine (q : ℕ) (hq : q < 3) {r : ℝ} {Φ : ℝ → State (Var 12)}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField (sysR q)) (Icc 0 r)) (h0 : Box (Φ 0)) :
    ∀ t ∈ Icc (0:ℝ) r, Box (Φ t) := by
  have hD := boxD_inv q hq hcurve (boxD_of_box h0)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := consts q hq
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18,
    i19, i20, i21, i22⟩ := h0
  -- `v`
  have hv := drive_two (lam := 1/2) (Mu := 13/4) (Ml := -3/2) (lo := 0) (hi := 8) (by norm_num)
    (coord_der q hcurve 0) (fun t _ => by rw [f0 q hq]; linarith) (by norm_num)
    (fun t _ => by rw [f0 q hq]; linarith) (by norm_num) ⟨i0, i1⟩
  -- `ω_ψ`, `ω_z`
  have hwp := drive_two (lam := 1) (Mu := 0) (Ml := 0) (lo := -3/5) (hi := 3/5) (by norm_num)
    (coord_der q hcurve 3) (fun t _ => by rw [f3 q hq]; linarith) (by norm_num)
    (fun t _ => by rw [f3 q hq]; linarith) (by norm_num) ⟨i5, i6⟩
  have hwz := drive_two (lam := 1) (Mu := 0) (Ml := 0) (lo := -3/20) (hi := 3/20) (by norm_num)
    (coord_der q hcurve 7) (fun t _ => by rw [f7 q hq]; linarith) (by norm_num)
    (fun t _ => by rw [f7 q hq]; linarith) (by norm_num) ⟨i13, i14⟩
  -- `ψ` (driven by `ω_ψ`), `z` (by `ω_z`)
  have hps := drive_two (lam := 1) (Mu := 3/5) (Ml := 3/5) (lo := -3/5) (hi := 3/5)
    (by norm_num) (coord_der q hcurve 2)
    (fun t ht => by rw [f2 q hq]; linarith [(hwp t ht).2])  (by norm_num)
    (fun t ht => by rw [f2 q hq]; linarith [(hwp t ht).1]) (by norm_num) ⟨i3, i4⟩
  have hz := drive_two (lam := 1) (Mu := 3/20) (Ml := 3/20) (lo := -3/20) (hi := 3/20)
    (by norm_num) (coord_der q hcurve 6)
    (fun t ht => by rw [f6 q hq]; linarith [(hwz t ht).2]) (by norm_num)
    (fun t ht => by rw [f6 q hq]; linarith [(hwz t ht).1]) (by norm_num) ⟨i11, i12⟩
  -- `ω_θ` (forced by the grade and `z`), then `θ`
  have hwt := drive_two (lam := 1) (Mu := 9/40) (Ml := 3/40) (lo := -3/5) (hi := 3/5)
    (by norm_num) (coord_der q hcurve 5)
    (fun t ht => by rw [f5 q hq]; linarith [(hz t ht).2]) (by norm_num)
    (fun t ht => by rw [f5 q hq]; linarith [(hz t ht).1]) (by norm_num) ⟨i9, i10⟩
  have hth := drive_two (lam := 1) (Mu := 3/5) (Ml := 3/5) (lo := -3/5) (hi := 3/5)
    (by norm_num) (coord_der q hcurve 4)
    (fun t ht => by rw [f4 q hq]; linarith [(hwt t ht).2]) (by norm_num)
    (fun t ht => by rw [f4 q hq]; linarith [(hwt t ht).1]) (by norm_num) ⟨i7, i8⟩
  -- `ω_φ` (forcing at most 0.28 over `B_δ`), `ω_y` (at most 0.45)
  have hwf := drive_two (lam := 1) (Mu := 7/25) (Ml := 7/25) (lo := -1/2) (hi := 1/2)
    (by norm_num) (coord_der q hcurve 9)
    (fun t ht => by
      have hG := lat_bd (hD t ht)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, d14, d15, -, -, d18, d19, d20, d21⟩ :=
        hD t ht
      rw [f9 q hq]; linarith [hG.1, hG.2]) (by norm_num)
    (fun t ht => by
      have hG := lat_bd (hD t ht)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, d14, d15, -, -, d18, d19, d20, d21⟩ :=
        hD t ht
      rw [f9 q hq]; linarith [hG.1, hG.2]) (by norm_num) ⟨i17, i18⟩
  have hwy := drive_two (lam := 1) (Mu := 9/20) (Ml := 9/20) (lo := -1/2) (hi := 1/2)
    (by norm_num) (coord_der q hcurve 11)
    (fun t ht => by
      have hG := lat_bd (hD t ht)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, d14, d15, -⟩ := hD t ht
      rw [f11 q hq]; linarith [hG.1, hG.2]) (by norm_num)
    (fun t ht => by
      have hG := lat_bd (hD t ht)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, d14, d15, -⟩ := hD t ht
      rw [f11 q hq]; linarith [hG.1, hG.2]) (by norm_num) ⟨i21, i22⟩
  -- `φ` (driven by `ω_φ`), `y` (by `ω_y`)
  have hph := drive_two (lam := 1) (Mu := 1/2) (Ml := 1/2) (lo := -1/2) (hi := 1/2)
    (by norm_num) (coord_der q hcurve 8)
    (fun t ht => by rw [f8 q hq]; linarith [(hwf t ht).2]) (by norm_num)
    (fun t ht => by rw [f8 q hq]; linarith [(hwf t ht).1]) (by norm_num) ⟨i15, i16⟩
  have hy := drive_two (lam := 1) (Mu := 1/2) (Ml := 1/2) (lo := -1/2) (hi := 1/2)
    (by norm_num) (coord_der q hcurve 10)
    (fun t ht => by rw [f10 q hq]; linarith [(hwy t ht).2]) (by norm_num)
    (fun t ht => by rw [f10 q hq]; linarith [(hwy t ht).1]) (by norm_num) ⟨i19, i20⟩
  -- `s` does not fall
  have hs := growth_lower_bound_raw (sys := sysR q) (Rv 1) 0 hcurve (fun t ht => by
    rw [field_R, f1 q hq]
    obtain ⟨-, -, d2, d3, -, -, d6, d7, -, -, -, -, -, -, d14, d15, -⟩ := hD t ht
    exact mul_nonneg (hv t ht).1 (factor_pos _ _ _ d2 d3 d6 d7 d14 d15))
  intro t ht
  have hst := hs t ht
  simp only [zero_mul, add_zero] at hst
  exact ⟨(hv t ht).1, (hv t ht).2, by linarith, (hps t ht).1, (hps t ht).2, (hwp t ht).1,
    (hwp t ht).2, (hth t ht).1, (hth t ht).2, (hwt t ht).1, (hwt t ht).2, (hz t ht).1,
    (hz t ht).2, (hwz t ht).1, (hwz t ht).2, (hph t ht).1, (hph t ht).2, (hwf t ht).1,
    (hwf t ht).2, (hy t ht).1, (hy t ht).2, (hwy t ht).1, (hwy t ht).2⟩

/-- **Existence (clause (i))**: from a box state, a run of duration 1 inside the box. -/
theorem exists_run (q : ℕ) (hq : q < 3) (x : State (Var 12)) (hd : Formula.sat domR x) :
    ∃ Φ, ODESol (sysR q) domR x 1 Φ := by
  obtain ⟨K, L, hLip, hBnd⟩ := picard_data q hq
  have hL1 : (0:ℝ) < (L : ℝ) + 1 := by positivity
  set r₀ : ℝ := 1 / ((L : ℝ) + 1) with hr₀def
  have hr₀ : 0 < r₀ := by positivity
  have hr₀le : (L : ℝ) * r₀ ≤ 1 := by
    rw [hr₀def, mul_one_div, div_le_one hL1]; linarith
  have hstep := hstep_slab_lipschitz (dom := Formula.tt) K L 1 one_pos r₀ hr₀ hr₀le BoxD hLip
    hBnd (fun Φ ν hν hΦ0 hcurve t ht =>
      ⟨boxD_inv q hq hcurve (by rw [hΦ0]; exact hν) t ht, trivial⟩)
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / r₀)
  have hn1 : (1:ℝ) ≤ n * r₀ := by
    calc (1:ℝ) = (1 / r₀) * r₀ := by field_simp
      _ ≤ (n : ℝ) * r₀ := mul_le_mul_of_nonneg_right hn hr₀.le
  have hx := (sat_domR x).mp hd
  obtain ⟨ν', hrun⟩ := chainN hr₀ BoxD hstep (fun _ _ => trivial) n 1 zero_le_one hn1 x
    (boxD_of_box hx)
  obtain ⟨hs, Φ, hΦ0, hΦ1, hcurve, -⟩ := hrun
  have hB := box_refine q hq hcurve (by rw [hΦ0]; exact hx)
  have hrunR : RunFor (sysR q) domR 1 x ν' :=
    ⟨hs, Φ, hΦ0, hΦ1, hcurve, fun t ht => (sat_domR _).mpr (hB t ht)⟩
  obtain ⟨ΦR, h0, hder, hmask, hdom⟩ := RunFor_unpack (hwfR q) hrunR
  exact ⟨ΦR, ⟨zero_le_one, h0, hder, hmask, hdom⟩⟩

theorem memS (q : ℕ) : (Rv 1, Term.binop .mul (Term.const 1) (fR q 1)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 1

/-- **Assumption 1 for `rover_rollover_payload`**, every zone, Z3-free. -/
theorem rover_rollover_payload_wellFormedR :
    WellFormedR Gr guardR (epsR rover_rollover_payload_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq3 x hd, ?_⟩
  intro t Φ ht H
  have hmono := H.mono (memS q) (fun s hs => by
    rw [eval_unit_mul]; exact (s_rate q hq3 s ((sat_domR s).mp hs)).1)
  have hrate := H.rate_le (memS q) 8 (fun s hs => by
    rw [eval_unit_mul]; exact (s_rate q hq3 s ((sat_domR s).mp hs)).2)
  have hr := H.hr
  interval_cases q
  · -- STEEP: the odometer ends in `[0, 70)`: STEEP below 62, MODER from 62
    have hg0 := (sat_g0 x).mp hg
    by_cases h62 : Φ t (Rv 1) < 62
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr ⟨by linarith, h62⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_g1 _).mpr ⟨by linarith, by nlinarith⟩⟩
  · -- MODER: ends in `[58, 150)`: MODER below 142, FLAT from 142
    have hg1 := (sat_g1 x).mp hg
    by_cases h142 : Φ t (Rv 1) < 142
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr ⟨by linarith, h142⟩⟩
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide), (sat_g2 _).mpr (by linarith)⟩
  · -- FLAT: the odometer does not fall
    have hg2 := (sat_g2 x).mp hg
    exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr (by linarith)⟩

end V2RoverRolloverPayload
end RelCertifier
