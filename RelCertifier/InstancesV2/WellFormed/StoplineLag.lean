/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_lag` (suite_v2): Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (`CRUISE`, `BRAKE`, `STOP` and their declared `next`
lists), the lowered right guards, `ε_r = 1/10`. The right is level P2 of the stop-line ladder
(the planner's point model) with the shared box: odometer `p` (0), speed `v` (1), the brake
state `b` (2) declared and frozen; `CRUISE` `p' = v`, `v' = 0`; `BRAKE` `p' = v`, `v' = −3`;
`STOP` frozen; `b' = 0` everywhere; the shared evolve box `p ≥ 0`, `0 ≤ v ≤ 8`, `0 ≤ b ≤ 3`.
`wellFormedR_stopline` (the shared lemma). Existence: the explicit runs (`b` constant, `v`
constant or `v₀ − 3t ≥ 0.05` while braking, `intSol` for `p`). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.stopline_lag
import RelCertifier.Proofs.Encoding.WellFormedStopline
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace StoplineLag

open DL DLCalTiming DLRel Parse Set

/-! ## Parse pins -/

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_35 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
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

def vsR : List String := ["p", "v", "b"]
def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mRR (q : ℕ) : Parse.PMode := stopline_lag_IRv2.R.modes.getD q dummyR
noncomputable def fRR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsR 3 Side.R (mRR q)
noncomputable def domRR : Formula (Var 3) := hostEvolve vsR 3 Side.R (mRR 0)
noncomputable def modeR (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

macro "ev_simp" : tactic => `(tactic| (
  simp [fRR, hostDyn, mRR, stopline_lag_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0,
    gp_0_3, gp_1_0, gp_3_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
  try norm_num
  try ring))

theorem fR_p0 (x : State (Var 3)) : Term.eval (fRR 0 0) x = x (Rv 1) := by ev_simp
theorem fR_p1 (x : State (Var 3)) : Term.eval (fRR 1 0) x = x (Rv 1) := by ev_simp
theorem fR_p2 (x : State (Var 3)) : Term.eval (fRR 2 0) x = 0 := by ev_simp
theorem fR_v0 (x : State (Var 3)) : Term.eval (fRR 0 1) x = 0 := by ev_simp
theorem fR_v1 (x : State (Var 3)) : Term.eval (fRR 1 1) x = -3 := by ev_simp
theorem fR_v2 (x : State (Var 3)) : Term.eval (fRR 2 1) x = 0 := by ev_simp
theorem fR_b0 (x : State (Var 3)) : Term.eval (fRR 0 2) x = 0 := by ev_simp
theorem fR_b1 (x : State (Var 3)) : Term.eval (fRR 1 2) x = 0 := by ev_simp
theorem fR_b2 (x : State (Var 3)) : Term.eval (fRR 2 2) x = 0 := by ev_simp

theorem sat_domRR (x : State (Var 3)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 8 ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3) := by
  simp only [domRR, hostEvolve, mRR, stopline_lag_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0_0, gp_8_0, gp_3_0, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 3 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 0, edgeG 0 1, edgeG 1 1, edgeG 1 2, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vsR 3 Side.R (mRR q)

macro "guard_simp" : tactic => `(tactic| (
  simp [guardR, hostGuard, mRR, stopline_lag_IRv2, Run.lowerF, Run.lowerE, gp_0_35,
    gp_100_0, vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  try norm_num))

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (guardR 0) x ↔
    (x (Rv 0) < 100 ∧ 7/20 ≤ x (Rv 1)) := by guard_simp
theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (guardR 1) x ↔
    (100 ≤ x (Rv 0) ∧ 7/20 ≤ x (Rv 1)) := by guard_simp
theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (guardR 2) x ↔
    (100 ≤ x (Rv 0) ∧ x (Rv 1) ≤ 7/20) := by guard_simp

/-! ## The explicit runs -/

/-- The brake state is frozen; the speed is held (`CRUISE`) or falls at 3 (`BRAKE`); the
odometer integrates the speed. -/
noncomputable def φb (_q : ℕ) (ρ : State (Var 3)) : ℝ → ℝ := fun _ => ρ (Rv 2)
noncomputable def φv (q : ℕ) (ρ : State (Var 3)) : ℝ → ℝ :=
  if q = 1 then intSol (ρ (Rv 1)) (fun _ => -3) else fun _ => ρ (Rv 1)
noncomputable def φp (q : ℕ) (ρ : State (Var 3)) : ℝ → ℝ := intSol (ρ (Rv 0)) (φv q ρ)

theorem φv_cont (q : ℕ) (ρ : State (Var 3)) : Continuous (φv q ρ) := by
  unfold φv; split_ifs
  · exact continuous_iff_continuousAt.mpr fun t =>
      (intSol_hasDerivAt _ continuous_const t).continuousAt
  · exact continuous_const

/-- The moving runs (`CRUISE` `q = 0`, `BRAKE` `q = 1`). -/
noncomputable def φR (q : ℕ) (ρ : State (Var 3)) (i : Fin 3) : ℝ → ℝ :=
  if i = 0 then φp q ρ else if i = 1 then φv q ρ else φb q ρ

theorem φR_zero (q : ℕ) (ρ : State (Var 3)) (i : Fin 3) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φp, φv, φb, forcedSol_zero, intSol_zero] <;> split_ifs <;>
    simp [intSol_zero]

theorem φR_der0 (ρ : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (φR 0 ρ i) (Term.eval (fRR 0 i) (trajRs ρ (φR 0 ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fR_p0]
    simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont 0 ρ) t
  · rw [fR_v0]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false, φv]
    exact hasDerivAt_const t _
  · rw [fR_b0]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false, φb]
    exact hasDerivAt_const t _

theorem φR_der1 (ρ : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (φR 1 ρ i) (Term.eval (fRR 1 i) (trajRs ρ (φR 1 ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fR_p1]
    simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont 1 ρ) t
  · rw [fR_v1]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false, φv]
    exact intSol_hasDerivAt _ continuous_const t
  · rw [fR_b1]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false, φb]
    exact hasDerivAt_const t _

/-- The bounds of the explicit coordinates over one control interval. -/
theorem φ_bounds (q : ℕ) (hq : q < 2) (ρ : State (Var 3)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) :
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8) := by
  obtain ⟨hp0, hv0, hv1, hb0, hb1⟩ := (sat_domRR ρ).mp hρ
  have hb : ∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3 :=
    fun _ _ => ⟨hb0, hb1⟩
  refine ⟨hb, ?_⟩
  intro τ hτ
  interval_cases q
  · simp only [φv, Fin.isValue]; simp only [zero_ne_one, if_false]; exact ⟨hv0, hv1⟩
  · obtain ⟨_, hv35⟩ := (sat_guardR1 ρ).mp hg
    have hd : ∀ u, HasDerivAt (φv 1 ρ) (-3) u := fun u => by
      simp only [φv, if_true]; exact intSol_hasDerivAt _ continuous_const u
    constructor
    · have h := mono_of_deriv_nonneg (φ := fun u => φv 1 ρ u + 3 * u) (g := fun _ => 0)
        (fun u => by
          have h1 : HasDerivAt (fun u => φv 1 ρ u + 3 * u) (-3 + 3 * 1) u :=
            (hd u).add ((hasDerivAt_id u).const_mul 3)
          exact h1.congr_deriv (by ring)) (fun _ _ => le_rfl) τ hτ
      simp only [φv, if_true, intSol_zero] at h ⊢; linarith [hτ.2]
    · have h := mono_of_deriv_nonneg (φ := fun u => -φv 1 ρ u) (g := fun _ => 3)
        (fun u => by
          have h1 : HasDerivAt (fun u => -φv 1 ρ u) (-(-3)) u := (hd u).neg
          exact h1.congr_deriv (by ring)) (fun _ _ => by norm_num) τ hτ
      simp only [φv, if_true, intSol_zero] at h ⊢; linarith

theorem φR_dom (q : ℕ) (hq : q < 2) (ρ : State (Var 3)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/10)) :
    Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hb, hv⟩ := φ_bounds q hq ρ hg hρ
  obtain ⟨hp0, -⟩ := (sat_domRR ρ).mp hρ
  have hp : 0 ≤ φp q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 0)) (φv_cont q ρ) τ)
      (fun τ hτ => (hv τ hτ).1) t ht
    simp only [intSol_zero] at h; simp only [φp]; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true,
    Fin.reduceEq, if_false]
  exact ⟨hp, (hv t ht).1, (hv t ht).2, (hb t ht).1, (hb t ht).2⟩

theorem epsR_eq : epsR stopline_lag_IRv2 = 1/10 := by
  simp [epsR, stopline_lag_IRv2, gp_0_1]

noncomputable def WF : StopWF GrG guardR domRR where
  m := modeR
  fR := fRR
  ip := 0
  iv := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fp0 := fR_p0
  fp1 := fR_p1
  fp2 := fR_p2
  fv0 := fR_v0
  fv2 := fR_v2
  vdom := fun s hs => ((sat_domRR s).mp hs).2.1
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
        (fun i t _ _ => φR_der0 x i t) (fun t h0 h1 => φR_dom 0 (by norm_num) x hg hx t ⟨h0, h1⟩)⟩
    · exact ⟨_, trajRs_sol x (φR 1 x) (1/10) (by norm_num) (φR_zero 1 x)
        (fun i t _ _ => φR_der1 x i t) (fun t h0 h1 => φR_dom 1 (by norm_num) x hg hx t ⟨h0, h1⟩)⟩
    · exact ⟨_, const_sol (fun i s => by
        fin_cases i <;> simp [fR_p2, fR_v2, fR_b2]) hx (by norm_num)⟩

/-- **Assumption 1 for `stopline_lag`**, every mode, Z3-free. -/
theorem stopline_lag_wellFormedR :
    WellFormedR GrG guardR (epsR stopline_lag_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_stopline WF

end StoplineLag
end RelCertifier
