/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_tyre` (suite_v2): Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (`CRUISE`, `BRAKE`, `STOP` and their declared `next`
lists), the lowered right guards, `ε_r = 1/10`. The right is level P3f of the stop-line ladder
(`stopline_friction`'s left, the rover on gravel) with the shared box: odometer `p` (0), speed
`v` (1), realised deceleration `b` (2), the hub command `c` (3) declared and frozen; `CRUISE`
`p' = v`, `v' = 0`, `b' = −b/0.3`; `BRAKE` `p' = v`, `v' = −b`, `b' = (2.7 − b)/0.3`; `STOP`
frozen; `c' = 0` everywhere; the shared evolve box `p ≥ 0`, `0 ≤ v ≤ 8`, `0 ≤ b, c ≤ 3`.
`wellFormedR_stopline` (the shared lemma). Existence: the explicit runs (`forcedSol` for `b`,
`c` constant, `intSol` for `v` and `p`; while braking `v ≥ v₀ − 3t ≥ 0.05`). Z3-free.
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

def vsR : List String := ["p", "v", "b", "c"]
def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mRR (q : ℕ) : Parse.PMode := stopline_tyre_IRv2.R.modes.getD q dummyR
noncomputable def fRR (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsR 4 Side.R (mRR q)
noncomputable def domRR : Formula (Var 4) := hostEvolve vsR 4 Side.R (mRR 0)
noncomputable def modeR (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

macro "ev_simp" : tactic => `(tactic| (
  simp [fRR, hostDyn, mRR, stopline_tyre_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0,
    gp_0_3, gp_1_0, gp_2_7, gp_3_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
  try norm_num
  try ring))

theorem fR_p0 (x : State (Var 4)) : Term.eval (fRR 0 0) x = x (Rv 1) := by ev_simp
theorem fR_p1 (x : State (Var 4)) : Term.eval (fRR 1 0) x = x (Rv 1) := by ev_simp
theorem fR_p2 (x : State (Var 4)) : Term.eval (fRR 2 0) x = 0 := by ev_simp
theorem fR_v0 (x : State (Var 4)) : Term.eval (fRR 0 1) x = 0 := by ev_simp
theorem fR_v1 (x : State (Var 4)) : Term.eval (fRR 1 1) x = -x (Rv 2) := by ev_simp
theorem fR_v2 (x : State (Var 4)) : Term.eval (fRR 2 1) x = 0 := by ev_simp
theorem fR_b0 (x : State (Var 4)) : Term.eval (fRR 0 2) x = 0 - 10/3 * x (Rv 2) := by ev_simp
theorem fR_b1 (x : State (Var 4)) : Term.eval (fRR 1 2) x = 9 - 10/3 * x (Rv 2) := by ev_simp
theorem fR_b2 (x : State (Var 4)) : Term.eval (fRR 2 2) x = 0 := by ev_simp
theorem fR_c0 (x : State (Var 4)) : Term.eval (fRR 0 3) x = 0 := by ev_simp
theorem fR_c1 (x : State (Var 4)) : Term.eval (fRR 1 3) x = 0 := by ev_simp
theorem fR_c2 (x : State (Var 4)) : Term.eval (fRR 2 3) x = 0 := by ev_simp

theorem sat_domRR (x : State (Var 4)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 8 ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3 ∧
      0 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3) := by
  simp only [domRR, hostEvolve, mRR, stopline_tyre_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0_0, gp_8_0, gp_3_0, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 4) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 4 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 4) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 0, edgeG 0 1, edgeG 1 1, edgeG 1 2, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

noncomputable def guardR (q : ℕ) : Formula (Var 4) := hostGuard vsR 4 Side.R (mRR q)

macro "guard_simp" : tactic => `(tactic| (
  simp [guardR, hostGuard, mRR, stopline_tyre_IRv2, Run.lowerF, Run.lowerE, gp_0_35,
    gp_100_0, vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  try norm_num))

theorem sat_guardR0 (x : State (Var 4)) : Formula.sat (guardR 0) x ↔
    (x (Rv 0) < 100 ∧ 7/20 ≤ x (Rv 1)) := by guard_simp
theorem sat_guardR1 (x : State (Var 4)) : Formula.sat (guardR 1) x ↔
    (100 ≤ x (Rv 0) ∧ 7/20 ≤ x (Rv 1)) := by guard_simp
theorem sat_guardR2 (x : State (Var 4)) : Formula.sat (guardR 2) x ↔
    (100 ≤ x (Rv 0) ∧ x (Rv 1) ≤ 7/20) := by guard_simp

/-! ## The explicit runs -/

/-- The brake state relaxes toward its mode's target (`0` released, `2.7` applied); the hub
command is frozen; the speed is held or integrates `−b`; the odometer integrates the speed. -/
noncomputable def φb (q : ℕ) (ρ : State (Var 4)) : ℝ → ℝ :=
  forcedSol (10/3) (ρ (Rv 2)) (fun _ => if q = 1 then 9 else 0)
noncomputable def φv (q : ℕ) (ρ : State (Var 4)) : ℝ → ℝ :=
  if q = 1 then intSol (ρ (Rv 1)) (fun τ => -φb q ρ τ) else fun _ => ρ (Rv 1)
noncomputable def φp (q : ℕ) (ρ : State (Var 4)) : ℝ → ℝ := intSol (ρ (Rv 0)) (φv q ρ)

theorem φb_cont (q : ℕ) (ρ : State (Var 4)) : Continuous (φb q ρ) :=
  forcedSol_continuous _ _ continuous_const
theorem φv_cont (q : ℕ) (ρ : State (Var 4)) : Continuous (φv q ρ) := by
  unfold φv; split_ifs
  · exact continuous_iff_continuousAt.mpr fun t =>
      (intSol_hasDerivAt _ (φb_cont q ρ).neg t).continuousAt
  · exact continuous_const

/-- The moving runs (`CRUISE` `q = 0`, `BRAKE` `q = 1`). -/
noncomputable def φR (q : ℕ) (ρ : State (Var 4)) (i : Fin 4) : ℝ → ℝ :=
  if i = 0 then φp q ρ else if i = 1 then φv q ρ else if i = 2 then φb q ρ else fun _ => ρ (Rv 3)

theorem φR_zero (q : ℕ) (ρ : State (Var 4)) (i : Fin 4) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φp, φv, φb, forcedSol_zero, intSol_zero] <;> split_ifs <;>
    simp [intSol_zero]

theorem φR_der0 (ρ : State (Var 4)) (i : Fin 4) (t : ℝ) :
    HasDerivAt (φR 0 ρ i) (Term.eval (fRR 0 i) (trajRs ρ (φR 0 ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fR_p0]
    simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont 0 ρ) t
  · rw [fR_v0]
    simp only [φR, Fin.isValue, if_true, Fin.reduceEq, if_false, φv]
    exact hasDerivAt_const t _
  · rw [fR_b0]
    simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt (10/3) (ρ (Rv 2)) continuous_const t).congr_deriv ?_
    simp only [φb, Fin.isValue]; simp
  · rw [fR_c0]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _

theorem φR_der1 (ρ : State (Var 4)) (i : Fin 4) (t : ℝ) :
    HasDerivAt (φR 1 ρ i) (Term.eval (fRR 1 i) (trajRs ρ (φR 1 ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fR_p1]
    simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont 1 ρ) t
  · rw [fR_v1]
    simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false, φv]
    exact intSol_hasDerivAt _ (φb_cont 1 ρ).neg t
  · rw [fR_b1]
    simp only [trajRs_R, φR, Fin.isValue, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt (10/3) (ρ (Rv 2)) continuous_const t).congr_deriv ?_
    simp only [φb, Fin.isValue]; simp
  · rw [fR_c1]
    simp only [φR, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _

/-- The bounds of the explicit coordinates over one control interval. -/
theorem φ_bounds (q : ℕ) (hq : q < 2) (ρ : State (Var 4)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) :
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3) ∧
    (∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8) := by
  obtain ⟨hp0, hv0, hv1, hb0, hb1, -, -⟩ := (sat_domRR ρ).mp hρ
  have hb : ∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φb q ρ τ ∧ φb q ρ τ ≤ 3 := by
    intro τ hτ
    have h := forcedSol_between (10/3) (ρ (Rv 2)) (F := fun _ => if q = 1 then (9:ℝ) else 0)
      continuous_const (lo := 0) (hi := 9) (by norm_num)
      (fun _ _ => by split_ifs <;> norm_num) τ hτ
    have h9 : (9:ℝ) / (10/3) = 27/10 := by norm_num
    rw [zero_div, h9] at h
    exact ⟨le_trans (le_min hb0 le_rfl) h.1, le_trans h.2 (max_le hb1 (by norm_num))⟩
  refine ⟨hb, ?_⟩
  intro τ hτ
  interval_cases q
  · simp only [φv, Fin.isValue]; simp only [zero_ne_one, if_false]; exact ⟨hv0, hv1⟩
  · obtain ⟨_, hv35⟩ := (sat_guardR1 ρ).mp hg
    have hd : ∀ u, HasDerivAt (φv 1 ρ) (-φb 1 ρ u) u := fun u => by
      simp only [φv, if_true]; exact intSol_hasDerivAt _ (φb_cont 1 ρ).neg u
    constructor
    · have h := mono_of_deriv_nonneg (φ := fun u => φv 1 ρ u + 3 * u) (g := fun u => 3 - φb 1 ρ u)
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

theorem φR_dom (q : ℕ) (hq : q < 2) (ρ : State (Var 4)) (hg : Formula.sat (guardR q) ρ)
    (hρ : Formula.sat domRR ρ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/10)) :
    Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hb, hv⟩ := φ_bounds q hq ρ hg hρ
  obtain ⟨hp0, -, -, -, -, hc0, hc1⟩ := (sat_domRR ρ).mp hρ
  have hp : 0 ≤ φp q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 0)) (φv_cont q ρ) τ)
      (fun τ hτ => (hv τ hτ).1) t ht
    simp only [intSol_zero] at h; simp only [φp]; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true,
    Fin.reduceEq, if_false]
  exact ⟨hp, (hv t ht).1, (hv t ht).2, (hb t ht).1, (hb t ht).2, hc0, hc1⟩

theorem epsR_eq : epsR stopline_tyre_IRv2 = 1/10 := by
  simp [epsR, stopline_tyre_IRv2, gp_0_1]

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
        fin_cases i <;> simp [fR_p2, fR_v2, fR_b2, fR_c2]) hx (by norm_num)⟩

/-- **Assumption 1 for `stopline_tyre`**, every mode, Z3-free. -/
theorem stopline_tyre_wellFormedR :
    WellFormedR GrG guardR (epsR stopline_tyre_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_stopline WF

end StoplineTyre
end RelCertifier
