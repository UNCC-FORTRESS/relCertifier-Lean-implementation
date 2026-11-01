/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_tyre`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (`CRUISE`, `BRAKE`, `STOP`), the lowered right guards,
`ε_r = 1/10`. The right is level `L8` of the stop-line rover ladder: odometer `p` (0), along-track
`s` (1), speed `v` (2), realised deceleration `b` (3), heading `ψ` (4), pitch `θ` (5), heave `z`
(6), roll `φ` (7); `CRUISE` `p' = v`, `s' = v (1 − ψ²/2 − 0.2 φ²)`, `v' = 0`, `b' = −b/0.3`,
`ψ' = −ψ`, `θ' = −θ + 0.5 z + 0.02 b`, `z' = −z`, `φ' = −φ + 0.015 v (−ψ)`; `BRAKE` the same with
`v' = −b`, `b' = (2.7 − b)/0.3`; `STOP` frozen; the evolve box `p, s ≥ 0`, `0 ≤ v ≤ 8`,
`0 ≤ b ≤ 2.7`, `|ψ|, |θ| ≤ 0.6`, `|z| ≤ 0.15`, `|φ| ≤ 0.5`.
`wellFormedR_stopline` (the shared lemma). Existence: the explicit runs (`forcedSol` cascades
`z → θ`, `(v, ψ) → φ`, `b` toward its target; `intSol` for `v`, `p`, `s`). Z3-free.
Batch 15 (2026-11-01): the full-fidelity rung under the suite name, from the branch proof
`StoplineRover8to11` (cd7499f) adapted to the one shared box: the right declares the left's
extra states (frozen at their start values, which stay in the box; host order = the left's
state list) and the box reads `0 ≤ b, c ≤ 3` on every mode of both sides (the bounds above
that differ are the branch's per-side boxes).
-/
import RelCertifier.InstancesV2.BenchIR.stopline_tyre
import RelCertifier.Proofs.Encoding.WellFormedStopline
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace StoplineTyre

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

def vsR : List String := ["p", "s", "v", "b", "c", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mRR (q : ℕ) : Parse.PMode := stopline_tyre_IRv2.R.modes.getD q dummyR
noncomputable def fRR (q : ℕ) : Fin 11 → Term (Var 11) := hostDyn vsR 11 Side.R (mRR q)
noncomputable def domRR : Formula (Var 11) := hostEvolve vsR 11 Side.R (mRR 0)
noncomputable def modeR (q : ℕ) : RMode (Var 11) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

macro "ev_simp" : tactic => `(tactic| (
  simp [fRR, hostDyn, mRR, stopline_tyre_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0,
    gp_0_015, gp_0_02, gp_0_2, gp_0_3, gp_0_5, gp_1_0, gp_2_7, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
  try norm_num
  try ring))

theorem fR_p0 (x : State (Var 11)) : Term.eval (fRR 0 0) x = x (Rv 2) := by ev_simp
theorem fR_p1 (x : State (Var 11)) : Term.eval (fRR 1 0) x = x (Rv 2) := by ev_simp
theorem fR_p2 (x : State (Var 11)) : Term.eval (fRR 2 0) x = 0 := by ev_simp
theorem fR_s0 (x : State (Var 11)) : Term.eval (fRR 0 1) x =
    x (Rv 2) * ((1 - 1/2 * (x (Rv 5) * x (Rv 5))) - 1/5 * (x (Rv 10) * x (Rv 10))) := by ev_simp
theorem fR_s1 (x : State (Var 11)) : Term.eval (fRR 1 1) x =
    x (Rv 2) * ((1 - 1/2 * (x (Rv 5) * x (Rv 5))) - 1/5 * (x (Rv 10) * x (Rv 10))) := by ev_simp
theorem fR_s2 (x : State (Var 11)) : Term.eval (fRR 2 1) x = 0 := by ev_simp
theorem fR_v0 (x : State (Var 11)) : Term.eval (fRR 0 2) x = 0 := by ev_simp
theorem fR_v1 (x : State (Var 11)) : Term.eval (fRR 1 2) x = -x (Rv 3) := by ev_simp
theorem fR_v2 (x : State (Var 11)) : Term.eval (fRR 2 2) x = 0 := by ev_simp
theorem fR_b0 (x : State (Var 11)) : Term.eval (fRR 0 3) x = 0 - 10/3 * x (Rv 3) := by ev_simp
theorem fR_b1 (x : State (Var 11)) : Term.eval (fRR 1 3) x = 9 - 10/3 * x (Rv 3) := by ev_simp
theorem fR_b2 (x : State (Var 11)) : Term.eval (fRR 2 3) x = 0 := by ev_simp
theorem fR_ps0 (x : State (Var 11)) : Term.eval (fRR 0 5) x = 0 - 1 * x (Rv 5) := by ev_simp
theorem fR_ps1 (x : State (Var 11)) : Term.eval (fRR 1 5) x = 0 - 1 * x (Rv 5) := by ev_simp
theorem fR_ps2 (x : State (Var 11)) : Term.eval (fRR 2 5) x = 0 := by ev_simp
theorem fR_th0 (x : State (Var 11)) : Term.eval (fRR 0 7) x =
    (1/2 * x (Rv 9) + 1/50 * x (Rv 3)) - 1 * x (Rv 7) := by ev_simp
theorem fR_th1 (x : State (Var 11)) : Term.eval (fRR 1 7) x =
    (1/2 * x (Rv 9) + 1/50 * x (Rv 3)) - 1 * x (Rv 7) := by ev_simp
theorem fR_th2 (x : State (Var 11)) : Term.eval (fRR 2 7) x = 0 := by ev_simp
theorem fR_z0 (x : State (Var 11)) : Term.eval (fRR 0 9) x = 0 - 1 * x (Rv 9) := by ev_simp
theorem fR_z1 (x : State (Var 11)) : Term.eval (fRR 1 9) x = 0 - 1 * x (Rv 9) := by ev_simp
theorem fR_z2 (x : State (Var 11)) : Term.eval (fRR 2 9) x = 0 := by ev_simp
theorem fR_ph0 (x : State (Var 11)) : Term.eval (fRR 0 10) x =
    3/200 * (x (Rv 2) * (0 - x (Rv 5))) - 1 * x (Rv 10) := by ev_simp
theorem fR_ph1 (x : State (Var 11)) : Term.eval (fRR 1 10) x =
    3/200 * (x (Rv 2) * (0 - x (Rv 5))) - 1 * x (Rv 10) := by ev_simp
theorem fR_ph2 (x : State (Var 11)) : Term.eval (fRR 2 10) x = 0 := by ev_simp


theorem fR_pad4_0 (x : State (Var 11)) : Term.eval (fRR 0 4) x = 0 := by ev_simp
theorem fR_pad4_1 (x : State (Var 11)) : Term.eval (fRR 1 4) x = 0 := by ev_simp
theorem fR_pad4_2 (x : State (Var 11)) : Term.eval (fRR 2 4) x = 0 := by ev_simp
theorem fR_pad6_0 (x : State (Var 11)) : Term.eval (fRR 0 6) x = 0 := by ev_simp
theorem fR_pad6_1 (x : State (Var 11)) : Term.eval (fRR 1 6) x = 0 := by ev_simp
theorem fR_pad6_2 (x : State (Var 11)) : Term.eval (fRR 2 6) x = 0 := by ev_simp
theorem fR_pad8_0 (x : State (Var 11)) : Term.eval (fRR 0 8) x = 0 := by ev_simp
theorem fR_pad8_1 (x : State (Var 11)) : Term.eval (fRR 1 8) x = 0 := by ev_simp
theorem fR_pad8_2 (x : State (Var 11)) : Term.eval (fRR 2 8) x = 0 := by ev_simp

theorem sat_domRR (x : State (Var 11)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 8 ∧ 0 ≤ x (Rv 3) ∧
      x (Rv 3) ≤ 3 ∧ 0 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 3 ∧ -(3/5) ≤ x (Rv 5) ∧ x (Rv 5) ≤ 3/5 ∧
      -(3/5) ≤ x (Rv 6) ∧ x (Rv 6) ≤ 3/5 ∧ -(3/5) ≤ x (Rv 7) ∧ x (Rv 7) ≤ 3/5 ∧
      -(3/5) ≤ x (Rv 8) ∧ x (Rv 8) ≤ 3/5 ∧ -(3/20) ≤ x (Rv 9) ∧ x (Rv 9) ≤ 3/20 ∧
      -(1/2) ≤ x (Rv 10) ∧ x (Rv 10) ≤ 1/2) := by
  simp only [domRR, hostEvolve, mRR, stopline_tyre_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0_0, gp_8_0, gp_2_7, gp_3_0, gp_0_6, gp_m0_6, gp_0_15, gp_m0_15,
    gp_0_5, gp_m0_5, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 11) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 11 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 11) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 0, edgeG 0 1, edgeG 1 1, edgeG 1 2, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

noncomputable def guardR (q : ℕ) : Formula (Var 11) := hostGuard vsR 11 Side.R (mRR q)

macro "guard_simp" : tactic => `(tactic| (
  simp [guardR, hostGuard, mRR, stopline_tyre_IRv2, Run.lowerF, Run.lowerE, gp_0_35,
    gp_100_0, vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  try norm_num))

theorem sat_guardR0 (x : State (Var 11)) : Formula.sat (guardR 0) x ↔
    (x (Rv 0) < 100 ∧ 7/20 ≤ x (Rv 2)) := by guard_simp
theorem sat_guardR1 (x : State (Var 11)) : Formula.sat (guardR 1) x ↔
    (100 ≤ x (Rv 0) ∧ 7/20 ≤ x (Rv 2)) := by guard_simp
theorem sat_guardR2 (x : State (Var 11)) : Formula.sat (guardR 2) x ↔
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

noncomputable def φps (ρ : State (Var 11)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 5)) (fun _ => 0)
noncomputable def φz (ρ : State (Var 11)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 9)) (fun _ => 0)
noncomputable def φb (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ :=
  forcedSol (10/3) (ρ (Rv 3)) (fun _ => if q = 1 then 9 else 0)
noncomputable def φv (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ :=
  if q = 1 then intSol (ρ (Rv 2)) (fun τ => -φb q ρ τ) else fun _ => ρ (Rv 2)
noncomputable def φp (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ := intSol (ρ (Rv 0)) (φv q ρ)
noncomputable def φthF (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ :=
  fun τ => 1/2 * φz ρ τ + 1/50 * φb q ρ τ
noncomputable def φth (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 7)) (φthF q ρ)
noncomputable def φphF (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ :=
  fun τ => 3/200 * (φv q ρ τ * (0 - φps ρ τ))
noncomputable def φph (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 10)) (φphF q ρ)
noncomputable def φsF (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ :=
  fun τ => φv q ρ τ * ((1 - 1/2 * (φps ρ τ * φps ρ τ)) - 1/5 * (φph q ρ τ * φph q ρ τ))
noncomputable def φs (q : ℕ) (ρ : State (Var 11)) : ℝ → ℝ := intSol (ρ (Rv 1)) (φsF q ρ)

theorem φps_cont (ρ : State (Var 11)) : Continuous (φps ρ) :=
  forcedSol_continuous _ _ continuous_const
theorem φz_cont (ρ : State (Var 11)) : Continuous (φz ρ) :=
  forcedSol_continuous _ _ continuous_const
theorem φb_cont (q : ℕ) (ρ : State (Var 11)) : Continuous (φb q ρ) :=
  forcedSol_continuous _ _ continuous_const
theorem φv_cont (q : ℕ) (ρ : State (Var 11)) : Continuous (φv q ρ) := by
  unfold φv; split_ifs
  · exact continuous_iff_continuousAt.mpr fun t =>
      (intSol_hasDerivAt _ (φb_cont q ρ).neg t).continuousAt
  · exact continuous_const
theorem φthF_cont (q : ℕ) (ρ : State (Var 11)) : Continuous (φthF q ρ) := by
  have h1 := φz_cont ρ; have h2 := φb_cont q ρ
  unfold φthF; fun_prop
theorem φth_cont (q : ℕ) (ρ : State (Var 11)) : Continuous (φth q ρ) :=
  forcedSol_continuous _ _ (φthF_cont q ρ)
theorem φphF_cont (q : ℕ) (ρ : State (Var 11)) : Continuous (φphF q ρ) := by
  have h1 := φv_cont q ρ; have h2 := φps_cont ρ
  unfold φphF; fun_prop
theorem φph_cont (q : ℕ) (ρ : State (Var 11)) : Continuous (φph q ρ) :=
  forcedSol_continuous _ _ (φphF_cont q ρ)
theorem φsF_cont (q : ℕ) (ρ : State (Var 11)) : Continuous (φsF q ρ) := by
  have h1 := φv_cont q ρ; have h2 := φps_cont ρ; have h3 := φph_cont q ρ
  unfold φsF; fun_prop

noncomputable def φR (q : ℕ) (ρ : State (Var 11)) (i : Fin 11) : ℝ → ℝ :=
  if i = 0 then φp q ρ else if i = 1 then φs q ρ else if i = 2 then φv q ρ
  else if i = 3 then φb q ρ else if i = 5 then φps ρ else if i = 7 then φth q ρ
  else if i = 9 then φz ρ else if i = 10 then φph q ρ else fun _ => ρ (Rv i)

theorem φR_zero (q : ℕ) (ρ : State (Var 11)) (i : Fin 11) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φp, φs, φv, φb, φps, φth, φz, φph, forcedSol_zero, intSol_zero] <;>
    split_ifs <;> simp [intSol_zero]

theorem φR_der (q : ℕ) (hq : q < 2) (ρ : State (Var 11)) (i : Fin 11) (t : ℝ) :
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
  · have h : ∀ q < 2, Term.eval (fRR q 3) (trajRs ρ (φR q ρ) t) =
        (if q = 1 then (9:ℝ) else 0) - 10/3 * φb q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_b0]; simp [trajRs_R, φR]
      · rw [fR_b1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt (10/3) (ρ (Rv 3)) continuous_const t
  · have h : ∀ q < 2, Term.eval (fRR q 4) (trajRs ρ (φR q ρ) t) = 0 := by
      intro q hq; interval_cases q
      · exact fR_pad4_0 _
      · exact fR_pad4_1 _
    rw [h q hq]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · have h : ∀ q < 2, Term.eval (fRR q 5) (trajRs ρ (φR q ρ) t) = 0 - 1 * φps ρ t := by
      intro q hq; interval_cases q
      · rw [fR_ps0]; simp [trajRs_R, φR]
      · rw [fR_ps1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 5)) continuous_const t
  · have h : ∀ q < 2, Term.eval (fRR q 6) (trajRs ρ (φR q ρ) t) = 0 := by
      intro q hq; interval_cases q
      · exact fR_pad6_0 _
      · exact fR_pad6_1 _
    rw [h q hq]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · have h : ∀ q < 2, Term.eval (fRR q 7) (trajRs ρ (φR q ρ) t) = φthF q ρ t - 1 * φth q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_th0]; simp [trajRs_R, φR, φthF]
      · rw [fR_th1]; simp [trajRs_R, φR, φthF]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 7)) (φthF_cont q ρ) t
  · have h : ∀ q < 2, Term.eval (fRR q 8) (trajRs ρ (φR q ρ) t) = 0 := by
      intro q hq; interval_cases q
      · exact fR_pad8_0 _
      · exact fR_pad8_1 _
    rw [h q hq]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · have h : ∀ q < 2, Term.eval (fRR q 9) (trajRs ρ (φR q ρ) t) = 0 - 1 * φz ρ t := by
      intro q hq; interval_cases q
      · rw [fR_z0]; simp [trajRs_R, φR]
      · rw [fR_z1]; simp [trajRs_R, φR]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 9)) continuous_const t
  · have h : ∀ q < 2, Term.eval (fRR q 10) (trajRs ρ (φR q ρ) t) = φphF q ρ t - 1 * φph q ρ t := by
      intro q hq; interval_cases q
      · rw [fR_ph0]; simp [trajRs_R, φR, φphF]
      · rw [fR_ph1]; simp [trajRs_R, φR, φphF]
    rw [h q hq]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact forcedSol_hasDerivAt 1 (ρ (Rv 10)) (φphF_cont q ρ) t



theorem φ_bounds (q : ℕ) (hq : q < 2) (ρ : State (Var 11)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) :
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φps ρ τ ∧ φps ρ τ ≤ 3/5) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/20) ≤ φz ρ τ ∧ φz ρ τ ≤ 3/20) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φth q ρ τ ∧ φth q ρ τ ≤ 3/5) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), -(1/2) ≤ φph q ρ τ ∧ φph q ρ τ ≤ 1/2) := by
  obtain ⟨hp0, hs0, hv0, hv1, hb0, hb1, hc0, hc1, hps0, hps1, hw0, hw1, hth0, hth1, hwt0, hwt1,
    hz0, hz1, hph0, hph1⟩ :=
    (sat_domRR ρ).mp hρ
  have hps : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φps ρ τ ∧ φps ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 5)) (F := fun _ => (0:ℝ)) continuous_const
      (lo := 0) (hi := 0) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    simp only [zero_div] at h
    exact ⟨le_trans (le_min hps0 (by norm_num)) h.1, le_trans h.2 (max_le hps1 (by norm_num))⟩
  have hz : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/20) ≤ φz ρ τ ∧ φz ρ τ ≤ 3/20 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 9)) (F := fun _ => (0:ℝ)) continuous_const
      (lo := 0) (hi := 0) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    simp only [zero_div] at h
    exact ⟨le_trans (le_min hz0 (by norm_num)) h.1, le_trans h.2 (max_le hz1 (by norm_num))⟩
  have hb : ∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3 := by
    intro τ hτ
    have h := forcedSol_between (10/3) (ρ (Rv 3)) (F := fun _ => if q = 1 then (9:ℝ) else 0)
      continuous_const (lo := 0) (hi := 9) (by norm_num)
      (fun _ _ => by split_ifs <;> norm_num) τ hτ
    have h9 : (9:ℝ) / (10/3) = 27/10 := by norm_num
    rw [zero_div, h9] at h
    exact ⟨le_trans (le_min hb0 le_rfl) h.1, le_trans h.2 (max_le hb1 (by norm_num))⟩
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
  have hth : ∀ τ ∈ Icc (0:ℝ) (1/10), -(3/5) ≤ φth q ρ τ ∧ φth q ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 7)) (φthF_cont q ρ) (lo := -(3/40)) (hi := 27/200)
      (by norm_num) (fun s hs => by
        obtain ⟨a0, a1⟩ := hz s hs
        obtain ⟨b0, b1⟩ := hb s hs
        simp only [φthF]; constructor <;> linarith) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hth0 (by norm_num)) h.1, le_trans h.2 (max_le hth1 (by norm_num))⟩
  have hph : ∀ τ ∈ Icc (0:ℝ) (1/10), -(1/2) ≤ φph q ρ τ ∧ φph q ρ τ ≤ 1/2 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 10)) (φphF_cont q ρ) (lo := -(9/125)) (hi := 9/125)
      (by norm_num) (fun s hs => by
        obtain ⟨a0, a1⟩ := hv s hs
        obtain ⟨c0, c1⟩ := hps s hs
        have hd0 : -(3/5) ≤ 0 - φps ρ s := by linarith
        have hd1 : 0 - φps ρ s ≤ 3/5 := by linarith
        have m1 : φv q ρ s * (0 - φps ρ s) ≤ φv q ρ s * (3/5) :=
          mul_le_mul_of_nonneg_left hd1 a0
        have m2 : φv q ρ s * (-(3/5)) ≤ φv q ρ s * (0 - φps ρ s) :=
          mul_le_mul_of_nonneg_left hd0 a0
        simp only [φphF]; constructor <;> nlinarith) τ hτ
    simp only [div_one] at h
    exact ⟨le_trans (le_min hph0 (by norm_num)) h.1, le_trans h.2 (max_le hph1 (by norm_num))⟩
  exact ⟨hps, hz, hb, hv, hth, hph⟩

theorem φR_dom (q : ℕ) (hq : q < 2) (ρ : State (Var 11)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/10)) :
    Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hp0, hs0, hv0, hv1, hb0, hb1, hc0, hc1, hps0, hps1, hw0, hw1, hth0, hth1, hwt0, hwt1,
    hz0, hz1, hph0, hph1⟩ :=
    (sat_domRR ρ).mp hρ
  obtain ⟨hps, hz, hb, hv, hth, hph⟩ := φ_bounds q hq ρ hg hρ
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
  exact ⟨hp, hs, (hv t ht).1, (hv t ht).2, (hb t ht).1, (hb t ht).2, hc0, hc1, (hps t ht).1,
    (hps t ht).2, hw0, hw1, (hth t ht).1, (hth t ht).2, hwt0, hwt1, (hz t ht).1, (hz t ht).2,
    (hph t ht).1, (hph t ht).2⟩

theorem epsR_eq : epsR stopline_tyre_IRv2 = 1/10 := by
  simp [epsR, stopline_tyre_IRv2, gp_0_1]

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
        fin_cases i <;> simp [fR_p2, fR_s2, fR_v2, fR_b2, fR_ps2, fR_th2, fR_z2, fR_ph2, fR_pad4_2, fR_pad6_2, fR_pad8_2]) hx
        (by norm_num)⟩

/-- **Assumption 1 for `stopline_tyre`**, every mode, Z3-free. -/
theorem stopline_tyre_wellFormedR :
    WellFormedR GrG guardR (epsR stopline_tyre_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_stopline WF

end StoplineTyre
end RelCertifier
