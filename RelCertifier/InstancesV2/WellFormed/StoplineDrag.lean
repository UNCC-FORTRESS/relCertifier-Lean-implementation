/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (`CRUISE`, `BRAKE`, `STOP`), the lowered right guards,
`ε_r = 1/10`. The right is level `L11` of the stop-line rover
ladder: odometer `p` (0), along-track `s` (1), speed `v` (2), tyre-force deceleration `b` (3), hub
(pressure) deceleration `c` (4), heading `ψ` (5) and yaw rate `ω_ψ` (6), pitch `θ` (7) and pitch rate
`ω_θ` (8), heave `z` (9), roll `φ` (10); `CRUISE` `p' = v`, `s' = v (1 − ψ²/2 − 0.2 φ²)`, `v' = 0`,
`b' = 20 (c − b)`, `c' = −c/0.3`, `ψ' = ω_ψ − ψ`, `ω_ψ' = −ω_ψ`, `θ' = ω_θ − θ`,
`ω_θ' = −ω_θ + 0.5 z + 0.02 b`, `z' = −z`, `φ' = −φ + 0.015 v (ω_ψ − ψ)`; `BRAKE` the same with
`v' = −b`, `c' = (2.7 − c)/0.3`; `STOP` frozen; the evolve box `p, s ≥ 0`, `0 ≤ v ≤ 8`,
`0 ≤ b, c ≤ 3`, `|ψ|, |ω_ψ|, |θ|, |ω_θ| ≤ 0.6`, `|z| ≤ 0.15`, `|φ| ≤ 0.5`.
`wellFormedR_stopline` (the shared lemma). Existence: the explicit runs (`forcedSol` cascades
`c → b`, `ω_ψ → ψ`, `(z, b) → ω_θ → θ`, `(v, ω_ψ, ψ) → φ`; `intSol` for `v`, `p`, `s`). Z3-free.
The right also declares the left's extra states (frozen at their start values, which stay in
the box; host order = the left's state list), and the evolve box is one box on every mode of both
sides, with `0 ≤ b, c ≤ 3`.
-/
import RelCertifier.InstancesV2.BenchIR.stopline_drag
import RelCertifier.Proofs.Encoding.WellFormedStopline
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace StoplineDrag

open DL DLCalTiming DLRel Parse Set

/-! ## Parse pins -/

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_015 : Run.parseRat "0.015" = some ((3:ℚ)/200) := by
  have h : parseQ "0.015" = some (⟨15, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_0_02 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_15 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_m0_15 : Run.parseRat "-0.15" = some (-(3:ℚ)/20) := by
  have h : parseQ "-0.15" = some (⟨-15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_20_0 : Run.parseRat "20.0" = some (20:ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_0_2 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_35 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_m0_5 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_m0_6 : Run.parseRat "-0.6" = some (-(3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_2_7 : Run.parseRat "2.7" = some ((27:ℚ)/10) := by
  have h : parseQ "2.7" = some (⟨27, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_3_0 : Run.parseRat "3.0" = some (3:ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_8_0 : Run.parseRat "8.0" = some (8:ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_100_0 : Run.parseRat "100.0" = some (100:ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The right model, evaluated -/

def vsR : List String := ["p", "s", "v", "b", "c", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]
def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mRR (q : ℕ) : Parse.PMode := stopline_drag_IRv2.R.modes.getD q dummyR
noncomputable def fRR (q : ℕ) : Fin 15 → Term (Var 15) := hostDyn vsR 15 Side.R (mRR q)
noncomputable def domRR : Formula (Var 15) := hostEvolve vsR 15 Side.R (mRR 0)
noncomputable def modeR (q : ℕ) : RMode (Var 15) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

macro "ev_simp" : tactic => `(tactic| (
  simp [fRR, hostDyn, mRR, stopline_drag_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0,
    gp_0_015, gp_0_02, gp_0_2, gp_0_3, gp_0_5, gp_1_0, gp_2_7, gp_20_0, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
  try norm_num
  try ring))

theorem fR_p0 (x : State (Var 15)) : Term.eval (fRR 0 0) x = x (Rv 2) := by ev_simp
theorem fR_p1 (x : State (Var 15)) : Term.eval (fRR 1 0) x = x (Rv 2) := by ev_simp
theorem fR_p2 (x : State (Var 15)) : Term.eval (fRR 2 0) x = 0 := by ev_simp
theorem fR_s0 (x : State (Var 15)) : Term.eval (fRR 0 1) x =
    x (Rv 2) * ((1 - 1/2 * (x (Rv 5) * x (Rv 5))) - 1/5 * (x (Rv 11) * x (Rv 11))) := by ev_simp
theorem fR_s1 (x : State (Var 15)) : Term.eval (fRR 1 1) x =
    x (Rv 2) * ((1 - 1/2 * (x (Rv 5) * x (Rv 5))) - 1/5 * (x (Rv 11) * x (Rv 11))) := by ev_simp
theorem fR_s2 (x : State (Var 15)) : Term.eval (fRR 2 1) x = 0 := by ev_simp
theorem fR_v0 (x : State (Var 15)) : Term.eval (fRR 0 2) x = 0 := by ev_simp
theorem fR_v1 (x : State (Var 15)) : Term.eval (fRR 1 2) x = -x (Rv 3) := by ev_simp
theorem fR_v2 (x : State (Var 15)) : Term.eval (fRR 2 2) x = 0 := by ev_simp
theorem fR_b0 (x : State (Var 15)) : Term.eval (fRR 0 3) x = 20 * x (Rv 4) - 20 * x (Rv 3) := by ev_simp
theorem fR_b1 (x : State (Var 15)) : Term.eval (fRR 1 3) x = 20 * x (Rv 4) - 20 * x (Rv 3) := by ev_simp
theorem fR_b2 (x : State (Var 15)) : Term.eval (fRR 2 3) x = 0 := by ev_simp
theorem fR_c0 (x : State (Var 15)) : Term.eval (fRR 0 4) x = 0 - 10/3 * x (Rv 4) := by ev_simp
theorem fR_c1 (x : State (Var 15)) : Term.eval (fRR 1 4) x = 9 - 10/3 * x (Rv 4) := by ev_simp
theorem fR_c2 (x : State (Var 15)) : Term.eval (fRR 2 4) x = 0 := by ev_simp
theorem fR_ps0 (x : State (Var 15)) : Term.eval (fRR 0 5) x = x (Rv 6) - 1 * x (Rv 5) := by ev_simp
theorem fR_ps1 (x : State (Var 15)) : Term.eval (fRR 1 5) x = x (Rv 6) - 1 * x (Rv 5) := by ev_simp
theorem fR_ps2 (x : State (Var 15)) : Term.eval (fRR 2 5) x = 0 := by ev_simp
theorem fR_om0 (x : State (Var 15)) : Term.eval (fRR 0 6) x = 0 - 1 * x (Rv 6) := by ev_simp
theorem fR_om1 (x : State (Var 15)) : Term.eval (fRR 1 6) x = 0 - 1 * x (Rv 6) := by ev_simp
theorem fR_om2 (x : State (Var 15)) : Term.eval (fRR 2 6) x = 0 := by ev_simp
theorem fR_th0 (x : State (Var 15)) : Term.eval (fRR 0 7) x = x (Rv 8) - 1 * x (Rv 7) := by ev_simp
theorem fR_th1 (x : State (Var 15)) : Term.eval (fRR 1 7) x = x (Rv 8) - 1 * x (Rv 7) := by ev_simp
theorem fR_th2 (x : State (Var 15)) : Term.eval (fRR 2 7) x = 0 := by ev_simp
theorem fR_ot0 (x : State (Var 15)) : Term.eval (fRR 0 8) x =
    (1/2 * x (Rv 9) + 1/50 * x (Rv 3)) - 1 * x (Rv 8) := by ev_simp
theorem fR_ot1 (x : State (Var 15)) : Term.eval (fRR 1 8) x =
    (1/2 * x (Rv 9) + 1/50 * x (Rv 3)) - 1 * x (Rv 8) := by ev_simp
theorem fR_ot2 (x : State (Var 15)) : Term.eval (fRR 2 8) x = 0 := by ev_simp
theorem fR_z0 (x : State (Var 15)) : Term.eval (fRR 0 9) x = 0 - 1 * x (Rv 9) := by ev_simp
theorem fR_z1 (x : State (Var 15)) : Term.eval (fRR 1 9) x = 0 - 1 * x (Rv 9) := by ev_simp
theorem fR_z2 (x : State (Var 15)) : Term.eval (fRR 2 9) x = 0 := by ev_simp
theorem fR_ph0 (x : State (Var 15)) : Term.eval (fRR 0 11) x =
    3/200 * (x (Rv 2) * (x (Rv 6) - x (Rv 5))) - 1 * x (Rv 11) := by ev_simp
theorem fR_ph1 (x : State (Var 15)) : Term.eval (fRR 1 11) x =
    3/200 * (x (Rv 2) * (x (Rv 6) - x (Rv 5))) - 1 * x (Rv 11) := by ev_simp
theorem fR_ph2 (x : State (Var 15)) : Term.eval (fRR 2 11) x = 0 := by ev_simp

theorem fR_pad10_0 (x : State (Var 15)) : Term.eval (fRR 0 10) x = 0 := by ev_simp
theorem fR_pad10_1 (x : State (Var 15)) : Term.eval (fRR 1 10) x = 0 := by ev_simp
theorem fR_pad10_2 (x : State (Var 15)) : Term.eval (fRR 2 10) x = 0 := by ev_simp
theorem fR_pad12_0 (x : State (Var 15)) : Term.eval (fRR 0 12) x = 0 := by ev_simp
theorem fR_pad12_1 (x : State (Var 15)) : Term.eval (fRR 1 12) x = 0 := by ev_simp
theorem fR_pad12_2 (x : State (Var 15)) : Term.eval (fRR 2 12) x = 0 := by ev_simp
theorem fR_pad13_0 (x : State (Var 15)) : Term.eval (fRR 0 13) x = 0 := by ev_simp
theorem fR_pad13_1 (x : State (Var 15)) : Term.eval (fRR 1 13) x = 0 := by ev_simp
theorem fR_pad13_2 (x : State (Var 15)) : Term.eval (fRR 2 13) x = 0 := by ev_simp
theorem fR_pad14_0 (x : State (Var 15)) : Term.eval (fRR 0 14) x = 0 := by ev_simp
theorem fR_pad14_1 (x : State (Var 15)) : Term.eval (fRR 1 14) x = 0 := by ev_simp
theorem fR_pad14_2 (x : State (Var 15)) : Term.eval (fRR 2 14) x = 0 := by ev_simp

theorem sat_domRR (x : State (Var 15)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 8 ∧ 0 ≤ x (Rv 3) ∧
      x (Rv 3) ≤ 3 ∧ 0 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 3 ∧ -(3/5) ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧
      -(3/5) ≤ x (Rv 6) ∧ x (Rv 6) ≤ 3/5 ∧ -(3/5) ≤ x (Rv 7) ∧ x (Rv 7) ≤ 3/5 ∧
      -(3/5) ≤ x (Rv 8) ∧ x (Rv 8) ≤ 3/5 ∧ -(3/20) ≤ x (Rv 9) ∧ x (Rv 9) ≤ 3/20 ∧
      -(3/20) ≤ x (Rv 10) ∧ x (Rv 10) ≤ 3/20 ∧ -(1/2) ≤ x (Rv 11) ∧ x (Rv 11) ≤ 1/2 ∧
      -(1/2) ≤ x (Rv 12) ∧ x (Rv 12) ≤ 1/2 ∧ -(1/2) ≤ x (Rv 13) ∧ x (Rv 13) ≤ 1/2 ∧
      -(1/2) ≤ x (Rv 14) ∧ x (Rv 14) ≤ 1/2) := by
  simp only [domRR, hostEvolve, mRR, stopline_drag_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0_0, gp_8_0, gp_2_7, gp_3_0, gp_0_6, gp_m0_6, gp_0_15, gp_m0_15,
    gp_0_5, gp_m0_5, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto
noncomputable def edgeG (st tgt : ℕ) : REdge (Var 15) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 15 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 15) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 0, edgeG 0 1, edgeG 1 1, edgeG 1 2, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

noncomputable def guardR (q : ℕ) : Formula (Var 15) := hostGuard vsR 15 Side.R (mRR q)

macro "guard_simp" : tactic => `(tactic| (
  simp [guardR, hostGuard, mRR, stopline_drag_IRv2, Run.lowerF, Run.lowerE, gp_0_35,
    gp_100_0, vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  try norm_num))

theorem sat_guardR0 (x : State (Var 15)) : Formula.sat (guardR 0) x ↔
    (x (Rv 0) < 100 ∧ 7/20 ≤ x (Rv 2)) := by guard_simp
theorem sat_guardR1 (x : State (Var 15)) : Formula.sat (guardR 1) x ↔
    (100 ≤ x (Rv 0) ∧ 7/20 ≤ x (Rv 2)) := by guard_simp
theorem sat_guardR2 (x : State (Var 15)) : Formula.sat (guardR 2) x ↔
    (100 ≤ x (Rv 0) ∧ x (Rv 2) ≤ 7/20) := by guard_simp

/-! ## The explicit runs -/

/-- The attitude-weighted odometer rate `v (1 − ψ²/2 − 0.2 φ²)` lies in `[0, 8]` on the box. -/
theorem odo_rate (v a c : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 8) (ha0 : -(3/5) ≤ a) (ha1 : a ≤ 3/5)
    (hc0 : -(1/2) ≤ c) (hc1 : c ≤ 1/2) :
    0 ≤ v * ((1 - 1/2 * (a * a)) - 1/5 * (c * c)) ∧
      v * ((1 - 1/2 * (a * a)) - 1/5 * (c * c)) ≤ 8 := by
  have ha2 : a * a ≤ 9/25 := by nlinarith
  have hc2 : c * c ≤ 1/4 := by nlinarith
  have hk0 : 0 ≤ (1 - 1/2 * (a * a)) - 1/5 * (c * c) := by nlinarith
  have hk1 : (1 - 1/2 * (a * a)) - 1/5 * (c * c) ≤ 1 := by
    nlinarith [mul_self_nonneg a, mul_self_nonneg c]
  exact ⟨mul_nonneg hv0 hk0, by nlinarith [mul_le_mul_of_nonneg_left hk1 hv0]⟩

noncomputable def φom (ρ : State (Var 15)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 6)) (fun _ => 0)
noncomputable def φps (ρ : State (Var 15)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 5)) (φom ρ)
noncomputable def φz (ρ : State (Var 15)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 9)) (fun _ => 0)
noncomputable def φc (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ :=
  forcedSol (10/3) (ρ (Rv 4)) (fun _ => if q = 1 then 9 else 0)
noncomputable def φbF (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ := fun τ => 20 * φc q ρ τ
noncomputable def φb (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ := forcedSol 20 (ρ (Rv 3)) (φbF q ρ)
noncomputable def φv (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ :=
  if q = 1 then intSol (ρ (Rv 2)) (fun τ => -φb q ρ τ) else fun _ => ρ (Rv 2)
noncomputable def φp (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ := intSol (ρ (Rv 0)) (φv q ρ)
noncomputable def φotF (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ :=
  fun τ => 1/2 * φz ρ τ + 1/50 * φb q ρ τ
noncomputable def φot (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 8)) (φotF q ρ)
noncomputable def φth (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 7)) (φot q ρ)
noncomputable def φphF (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ :=
  fun τ => 3/200 * (φv q ρ τ * (φom ρ τ - φps ρ τ))
noncomputable def φph (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 11)) (φphF q ρ)
noncomputable def φsF (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ :=
  fun τ => φv q ρ τ * ((1 - 1/2 * (φps ρ τ * φps ρ τ)) - 1/5 * (φph q ρ τ * φph q ρ τ))
noncomputable def φs (q : ℕ) (ρ : State (Var 15)) : ℝ → ℝ := intSol (ρ (Rv 1)) (φsF q ρ)

theorem φom_cont (ρ : State (Var 15)) : Continuous (φom ρ) :=
  forcedSol_continuous _ _ continuous_const
theorem φps_cont (ρ : State (Var 15)) : Continuous (φps ρ) :=
  forcedSol_continuous _ _ (φom_cont ρ)
theorem φz_cont (ρ : State (Var 15)) : Continuous (φz ρ) :=
  forcedSol_continuous _ _ continuous_const
theorem φc_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φc q ρ) :=
  forcedSol_continuous _ _ continuous_const
theorem φbF_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φbF q ρ) := by
  have h := φc_cont q ρ; unfold φbF; fun_prop
theorem φb_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φb q ρ) :=
  forcedSol_continuous _ _ (φbF_cont q ρ)
theorem φv_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φv q ρ) := by
  unfold φv; split_ifs
  · exact continuous_iff_continuousAt.mpr fun t =>
      (intSol_hasDerivAt _ (φb_cont q ρ).neg t).continuousAt
  · exact continuous_const
theorem φotF_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φotF q ρ) := by
  have h1 := φz_cont ρ; have h2 := φb_cont q ρ
  unfold φotF; fun_prop
theorem φot_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φot q ρ) :=
  forcedSol_continuous _ _ (φotF_cont q ρ)
theorem φth_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φth q ρ) :=
  forcedSol_continuous _ _ (φot_cont q ρ)
theorem φphF_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φphF q ρ) := by
  have h1 := φv_cont q ρ; have h2 := φps_cont ρ; have h3 := φom_cont ρ
  unfold φphF; fun_prop
theorem φph_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φph q ρ) :=
  forcedSol_continuous _ _ (φphF_cont q ρ)
theorem φsF_cont (q : ℕ) (ρ : State (Var 15)) : Continuous (φsF q ρ) := by
  have h1 := φv_cont q ρ; have h2 := φps_cont ρ; have h3 := φph_cont q ρ
  unfold φsF; fun_prop

noncomputable def φR (q : ℕ) (ρ : State (Var 15)) (i : Fin 15) : ℝ → ℝ :=
  if i = 0 then φp q ρ else if i = 1 then φs q ρ else if i = 2 then φv q ρ
  else if i = 3 then φb q ρ else if i = 4 then φc q ρ else if i = 5 then φps ρ
  else if i = 6 then φom ρ else if i = 7 then φth q ρ else if i = 8 then φot q ρ
  else if i = 9 then φz ρ else if i = 11 then φph q ρ else fun _ => ρ (Rv i)

theorem φR_zero (q : ℕ) (ρ : State (Var 15)) (i : Fin 15) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φp, φs, φv, φb, φc, φps, φom, φth, φot, φz, φph, forcedSol_zero,
    intSol_zero] <;> split_ifs <;> simp [intSol_zero]

theorem φR_der (q : ℕ) (hq : q < 2) (ρ : State (Var 15)) (i : Fin 15) (t : ℝ) :
    HasDerivAt (φR q ρ i) (Term.eval (fRR q i) (trajRs ρ (φR q ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · have h : ∀ q < 2, Term.eval (fRR q 0) (trajRs ρ (φR q ρ) t) = φv q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_p0]; simp [trajRs_R, φR]
      · rw [fR_p1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont q ρ) t
  · have h : ∀ q < 2, Term.eval (fRR q 1) (trajRs ρ (φR q ρ) t) = φsF q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_s0]; simp [trajRs_R, φR, φsF]
      · rw [fR_s1]; simp [trajRs_R, φR, φsF]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φsF_cont q ρ) t
  · interval_cases q
    · rw [fR_v0]
      simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false, φv]
      exact hasDerivAt_const t _
    · rw [fR_v1]
      simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false, φv]
      exact intSol_hasDerivAt _ (φb_cont 1 ρ).neg t
  · have h : ∀ q < 2, Term.eval (fRR q 3) (trajRs ρ (φR q ρ) t) = φbF q ρ t - 20 * φb q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_b0]; simp [trajRs_R, φR, φbF]
      · rw [fR_b1]; simp [trajRs_R, φR, φbF]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 20 (ρ (Rv 3)) (φbF_cont q ρ) t
  · have h : ∀ q < 2, Term.eval (fRR q 4) (trajRs ρ (φR q ρ) t) =
        (if q = 1 then (9:ℝ) else 0) - 10/3 * φc q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_c0]; simp [trajRs_R, φR]
      · rw [fR_c1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt (10/3) (ρ (Rv 4)) continuous_const t
  · have h : ∀ q < 2, Term.eval (fRR q 5) (trajRs ρ (φR q ρ) t) = φom ρ t - 1 * φps ρ t := by
      intro q hq; interval_cases q
      · rw [fR_ps0]; simp [trajRs_R, φR]
      · rw [fR_ps1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 5)) (φom_cont ρ) t
  · have h : ∀ q < 2, Term.eval (fRR q 6) (trajRs ρ (φR q ρ) t) = 0 - 1 * φom ρ t := by
      intro q hq; interval_cases q
      · rw [fR_om0]; simp [trajRs_R, φR]
      · rw [fR_om1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 6)) continuous_const t
  · have h : ∀ q < 2, Term.eval (fRR q 7) (trajRs ρ (φR q ρ) t) = φot q ρ t - 1 * φth q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_th0]; simp [trajRs_R, φR]
      · rw [fR_th1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 7)) (φot_cont q ρ) t
  · have h : ∀ q < 2, Term.eval (fRR q 8) (trajRs ρ (φR q ρ) t) = φotF q ρ t - 1 * φot q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_ot0]; simp [trajRs_R, φR, φotF]
      · rw [fR_ot1]; simp [trajRs_R, φR, φotF]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 8)) (φotF_cont q ρ) t
  · have h : ∀ q < 2, Term.eval (fRR q 9) (trajRs ρ (φR q ρ) t) = 0 - 1 * φz ρ t := by
      intro q hq; interval_cases q
      · rw [fR_z0]; simp [trajRs_R, φR]
      · rw [fR_z1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 9)) continuous_const t
  · have h : ∀ q < 2, Term.eval (fRR q 10) (trajRs ρ (φR q ρ) t) = 0 := by
      intro q hq; interval_cases q
      · exact fR_pad10_0 _
      · exact fR_pad10_1 _
    rw [h q hq]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · have h : ∀ q < 2, Term.eval (fRR q 11) (trajRs ρ (φR q ρ) t) = φphF q ρ t - 1 * φph q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_ph0]; simp [trajRs_R, φR, φphF]
      · rw [fR_ph1]; simp [trajRs_R, φR, φphF]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 11)) (φphF_cont q ρ) t


  · have h : ∀ q < 2, Term.eval (fRR q 12) (trajRs ρ (φR q ρ) t) = 0 := by
      intro q hq; interval_cases q
      · exact fR_pad12_0 _
      · exact fR_pad12_1 _
    rw [h q hq]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · have h : ∀ q < 2, Term.eval (fRR q 13) (trajRs ρ (φR q ρ) t) = 0 := by
      intro q hq; interval_cases q
      · exact fR_pad13_0 _
      · exact fR_pad13_1 _
    rw [h q hq]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · have h : ∀ q < 2, Term.eval (fRR q 14) (trajRs ρ (φR q ρ) t) = 0 := by
      intro q hq; interval_cases q
      · exact fR_pad14_0 _
      · exact fR_pad14_1 _
    rw [h q hq]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _

theorem φ_bounds (q : ℕ) (hq : q < 2) (ρ : State (Var 15)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) :
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φom ρ τ ∧ φom ρ τ ≤ 3/5) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φps ρ τ ∧ φps ρ τ ≤ 3/5) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/20) ≤ φz ρ τ ∧ φz ρ τ ≤ 3/20) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φc q ρ τ ∧ φc q ρ τ ≤ 3) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φot q ρ τ ∧ φot q ρ τ ≤ 3/5) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φth q ρ τ ∧ φth q ρ τ ≤ 3/5) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(1/2) ≤ φph q ρ τ ∧ φph q ρ τ ≤ 1/2) := by
  obtain ⟨hp0, hs0, hv0, hv1, hb0, hb1, hc0, hc1, hps0, hps1, hom0, hom1, hth0, hth1, hot0, hot1,
    hz0, hz1, hwz0, hwz1, hph0, hph1, hwp0, hwp1, hy0, hy1, hwy0, hwy1⟩ := (sat_domRR ρ).mp hρ
  have hom : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φom ρ τ ∧ φom ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 6)) (F := fun _ => (0:ℝ)) continuous_const
      (lo := 0) (hi := 0) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    simp only [zero_div] at h
    exact ⟨le_trans (le_min hom0 (by norm_num)) h.1, le_trans h.2 (max_le hom1 (by norm_num))⟩
  have hps : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φps ρ τ ∧ φps ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 5)) (φom_cont ρ) (lo := -(3/5)) (hi := 3/5)
      (by norm_num) (fun s hs => hom s hs) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hps0 le_rfl) h.1, le_trans h.2 (max_le hps1 le_rfl)⟩
  have hz : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/20) ≤ φz ρ τ ∧ φz ρ τ ≤ 3/20 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 9)) (F := fun _ => (0:ℝ)) continuous_const
      (lo := 0) (hi := 0) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    simp only [zero_div] at h
    exact ⟨le_trans (le_min hz0 (by norm_num)) h.1, le_trans h.2 (max_le hz1 (by norm_num))⟩
  have hc : ∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φc q ρ τ ∧ φc q ρ τ ≤ 3 := by
    intro τ hτ
    have h := forcedSol_between (10/3) (ρ (Rv 4)) (F := fun _ => if q = 1 then (9:ℝ) else 0)
      continuous_const (lo := 0) (hi := 9) (by norm_num)
      (fun _ _ => by split_ifs <;> norm_num) τ hτ
    have h9 : (9:ℝ) / (10/3) = 27/10 := by norm_num
    rw [zero_div, h9] at h
    exact ⟨le_trans (le_min hc0 le_rfl) h.1, le_trans h.2 (max_le hc1 (by norm_num))⟩
  have hb : ∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3 := by
    intro τ hτ
    have h := forcedSol_between 20 (ρ (Rv 3)) (φbF_cont q ρ) (lo := 0) (hi := 60)
      (by norm_num) (fun s hs => by
        obtain ⟨a0, a1⟩ := hc s hs
        simp only [φbF]; constructor <;> linarith) τ hτ
    have h54 : (60:ℝ) / 20 = 3 := by norm_num
    rw [zero_div, h54] at h
    exact ⟨le_trans (le_min hb0 le_rfl) h.1, le_trans h.2 (max_le hb1 le_rfl)⟩
  have hv : ∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8 := by
    intro τ hτ
    interval_cases q
    · simp only [φv, Fin.isValue]; simp only [zero_ne_one, if_false]; exact ⟨hv0, hv1⟩
    · obtain ⟨_, hv35⟩ := (sat_guardR1 ρ).mp hg
      have hd : ∀ u, HasDerivAt (φv 1 ρ) (-φb 1 ρ u) u := fun u => by
        simp only [φv, if_true]; exact intSol_hasDerivAt _ (φb_cont 1 ρ).neg u
      constructor
      · have h := mono_of_deriv_nonneg (φ := fun u => φv 1 ρ u + 3 * u)
          (g := fun u => 3 - φb 1 ρ u)
          (fun u => by
            have h1 : HasDerivAt (fun u => φv 1 ρ u + 3 * u) (-φb 1 ρ u + 3 * 1) u :=
              (hd u).add ((hasDerivAt_id u).const_mul 3)
            exact h1.congr_deriv (by ring)) (fun u hu => by linarith [(hb u hu).2]) τ hτ
        simp only [φv, if_true, intSol_zero] at h ⊢; linarith [hτ.2]
      · have h := mono_of_deriv_nonneg (φ := fun u => -φv 1 ρ u) (g := fun u => φb 1 ρ u)
          (fun u => by
            have h1 : HasDerivAt (fun u => -φv 1 ρ u) (-(-φb 1 ρ u)) u := (hd u).neg
            exact h1.congr_deriv (by ring)) (fun u hu => (hb u hu).1) τ hτ
        simp only [φv, if_true, intSol_zero] at h ⊢; linarith
  have hot : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φot q ρ τ ∧ φot q ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 8)) (φotF_cont q ρ) (lo := -(3/40)) (hi := 27/200)
      (by norm_num) (fun s hs => by
        obtain ⟨a0, a1⟩ := hz s hs
        obtain ⟨b0, b1⟩ := hb s hs
        simp only [φotF]; constructor <;> linarith) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hot0 (by norm_num)) h.1, le_trans h.2 (max_le hot1 (by norm_num))⟩
  have hth : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φth q ρ τ ∧ φth q ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 7)) (φot_cont q ρ) (lo := -(3/5)) (hi := 3/5)
      (by norm_num) (fun s hs => hot s hs) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hth0 le_rfl) h.1, le_trans h.2 (max_le hth1 le_rfl)⟩
  have hph : ∀ τ ∈ Icc (0:ℝ) (1/10), -(1/2) ≤ φph q ρ τ ∧ φph q ρ τ ≤ 1/2 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 11)) (φphF_cont q ρ) (lo := -(18/125)) (hi := 18/125)
      (by norm_num) (fun s hs => by
        obtain ⟨a0, a1⟩ := hv s hs
        obtain ⟨c0, c1⟩ := hps s hs
        obtain ⟨d0, d1⟩ := hom s hs
        have hd0 : -(6/5) ≤ φom ρ s - φps ρ s := by linarith
        have hd1 : φom ρ s - φps ρ s ≤ 6/5 := by linarith
        have m1 : φv q ρ s * (φom ρ s - φps ρ s) ≤ φv q ρ s * (6/5) :=
          mul_le_mul_of_nonneg_left hd1 a0
        have m2 : φv q ρ s * (-(6/5)) ≤ φv q ρ s * (φom ρ s - φps ρ s) :=
          mul_le_mul_of_nonneg_left hd0 a0
        simp only [φphF]; constructor <;> nlinarith) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hph0 (by norm_num)) h.1, le_trans h.2 (max_le hph1 (by norm_num))⟩
  exact ⟨hom, hps, hz, hc, hb, hv, hot, hth, hph⟩

theorem φR_dom (q : ℕ) (hq : q < 2) (ρ : State (Var 15)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/10)) :
    Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hp0, hs0, hv0, hv1, hb0, hb1, hc0, hc1, hps0, hps1, hom0, hom1, hth0, hth1, hot0, hot1,
    hz0, hz1, hwz0, hwz1, hph0, hph1, hwp0, hwp1, hy0, hy1, hwy0, hwy1⟩ := (sat_domRR ρ).mp hρ
  obtain ⟨hom, hps, hz, hc, hb, hv, hot, hth, hph⟩ := φ_bounds q hq ρ hg hρ
  have hp : 0 ≤ φp q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 0)) (φv_cont q ρ) τ)
      (fun τ hτ => (hv τ hτ).1) t ht
    simp only [intSol_zero] at h; simp only [φp]; linarith
  have hs : 0 ≤ φs q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 1)) (φsF_cont q ρ) τ)
      (fun τ hτ => (odo_rate _ _ _ (hv τ hτ).1 (hv τ hτ).2 (hps τ hτ).1 (hps τ hτ).2
        (hph τ hτ).1 (hph τ hτ).2).1) t ht
    simp only [intSol_zero] at h; simp only [φs]; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true,
    Fin.reduceEq, if_false]
  exact ⟨hp, hs, (hv t ht).1, (hv t ht).2, (hb t ht).1, (hb t ht).2, (hc t ht).1, (hc t ht).2,
    (hps t ht).1, (hps t ht).2, (hom t ht).1, (hom t ht).2, (hth t ht).1, (hth t ht).2,
    (hot t ht).1, (hot t ht).2, (hz t ht).1, (hz t ht).2, hwz0, hwz1, (hph t ht).1, (hph t ht).2,
    hwp0, hwp1, hy0, hy1, hwy0, hwy1⟩

theorem epsR_eq : epsR stopline_drag_IRv2 = 1/10 := by
  simp [epsR, stopline_drag_IRv2, gp_0_1]

noncomputable def WF : StopWF GrG guardR domRR where
  m := modeR
  fR := fRR
  ip := 0
  iv := 2
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fp0 := fR_p0
  fp1 := fR_p1
  fp2 := fR_p2
  fv0 := fR_v0
  fv2 := fR_v2
  vdom := fun s hs => ((sat_domRR s).mp hs).2.2.1
  g0 := sat_guardR0
  g1 := sat_guardR1
  g2 := sat_guardR2
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
  exists_run := fun q hq x hg hx => by
    interval_cases q
    · exact ⟨_, trajRs_sol x (φR 0 x) (1/10) (by norm_num) (φR_zero 0 x)
        (fun i t _ _ => φR_der 0 (by norm_num) x i t)
        (fun t h0 h1 => φR_dom 0 (by norm_num) x hg hx t ⟨h0, h1⟩)⟩
    · exact ⟨_, trajRs_sol x (φR 1 x) (1/10) (by norm_num) (φR_zero 1 x)
        (fun i t _ _ => φR_der 1 (by norm_num) x i t)
        (fun t h0 h1 => φR_dom 1 (by norm_num) x hg hx t ⟨h0, h1⟩)⟩
    · exact ⟨_, const_sol (fun i s => by
        fin_cases i <;> simp [fR_p2, fR_s2, fR_v2, fR_b2, fR_c2, fR_ps2, fR_om2, fR_th2, fR_ot2,
          fR_z2, fR_ph2, fR_pad10_2, fR_pad12_2, fR_pad13_2, fR_pad14_2]) hx
        (by norm_num)⟩

/-- **Assumption 1 for `stopline_drag`**, every mode, Z3-free. -/
theorem stopline_drag_wellFormedR :
    WellFormedR GrG guardR (epsR stopline_drag_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_stopline WF

end StoplineDrag
end RelCertifier
