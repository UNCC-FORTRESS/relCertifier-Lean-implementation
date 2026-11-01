/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_rover_2to5`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (the file's `CRUISE`, `BRAKE`, `STOP` and their declared
`next` lists), the lowered right guards, `ε_r = 1/10`. The right is the planner's point model
`L2` of the stop-line rover ladder: odometer `p` (coordinate 0), speed `v` (coordinate 1);
`CRUISE` `p' = v`, `v' = 0`; `BRAKE` `p' = v`, `v' = -3`; `STOP` frozen; the evolve box
`p ≥ 0`, `0 ≤ v ≤ 8`.
`wellFormedR_stopline` (the shared lemma: a `CRUISE` run keeps its speed and does not move the
odometer backwards, a `BRAKE` run keeps `p ≥ 100`, `STOP` is constant). Existence: the explicit
runs (`intSol` for `p`; `v` constant while cruising, `v₀ − 3t ≥ 0.35 − 0.3` while braking;
`const_sol` at standstill). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.stopline_rover_2to5
import RelCertifier.Proofs.Encoding.WellFormedStopline
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace StoplineRover2to5

open DL DLCalTiming DLRel Parse Set

/-! ## Parse pins -/

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem gp_0_35 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
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

def vsR : List String := ["p", "s", "v", "b", "psi"]
def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mRR (q : ℕ) : Parse.PMode := stopline_rover_2to5_IRv2.R.modes.getD q dummyR
noncomputable def fRR (q : ℕ) : Fin 5 → Term (Var 5) := hostDyn vsR 5 Side.R (mRR q)
noncomputable def domRR : Formula (Var 5) := hostEvolve vsR 5 Side.R (mRR 0)
noncomputable def modeR (q : ℕ) : RMode (Var 5) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

macro "ev_simp" : tactic => `(tactic| (
  simp [fRR, hostDyn, mRR, stopline_rover_2to5_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0, gp_3_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
  try norm_num
  try ring))

theorem fR_p0 (x : State (Var 5)) : Term.eval (fRR 0 0) x = x (Rv 2) := by
  simp [fRR, hostDyn, mRR, stopline_rover_2to5_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0, gp_3_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fR_p1 (x : State (Var 5)) : Term.eval (fRR 1 0) x = x (Rv 2) := by
  simp [fRR, hostDyn, mRR, stopline_rover_2to5_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0, gp_3_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fR_p2 (x : State (Var 5)) : Term.eval (fRR 2 0) x = 0 := by
  simp [fRR, hostDyn, mRR, stopline_rover_2to5_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0, gp_3_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fR_v0 (x : State (Var 5)) : Term.eval (fRR 0 2) x = 0 := by
  simp [fRR, hostDyn, mRR, stopline_rover_2to5_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0, gp_3_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fR_v1 (x : State (Var 5)) : Term.eval (fRR 1 2) x = -3 := by
  simp [fRR, hostDyn, mRR, stopline_rover_2to5_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0, gp_3_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
theorem fR_v2 (x : State (Var 5)) : Term.eval (fRR 2 2) x = 0 := by
  simp [fRR, hostDyn, mRR, stopline_rover_2to5_IRv2, vsR, Run.dynOf, Run.lowerE, gp_0_0, gp_3_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]


theorem fR_pad1_0 (x : State (Var 5)) : Term.eval (fRR 0 1) x = 0 := by ev_simp
theorem fR_pad1_1 (x : State (Var 5)) : Term.eval (fRR 1 1) x = 0 := by ev_simp
theorem fR_pad1_2 (x : State (Var 5)) : Term.eval (fRR 2 1) x = 0 := by ev_simp
theorem fR_pad3_0 (x : State (Var 5)) : Term.eval (fRR 0 3) x = 0 := by ev_simp
theorem fR_pad3_1 (x : State (Var 5)) : Term.eval (fRR 1 3) x = 0 := by ev_simp
theorem fR_pad3_2 (x : State (Var 5)) : Term.eval (fRR 2 3) x = 0 := by ev_simp
theorem fR_pad4_0 (x : State (Var 5)) : Term.eval (fRR 0 4) x = 0 := by ev_simp
theorem fR_pad4_1 (x : State (Var 5)) : Term.eval (fRR 1 4) x = 0 := by ev_simp
theorem fR_pad4_2 (x : State (Var 5)) : Term.eval (fRR 2 4) x = 0 := by ev_simp

theorem sat_domRR (x : State (Var 5)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 8) := by
  simp only [domRR, hostEvolve, mRR, stopline_rover_2to5_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0_0, gp_8_0, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 5) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 5 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 5) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 0, edgeG 0 1, edgeG 1 1, edgeG 1 2, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

noncomputable def guardR (q : ℕ) : Formula (Var 5) := hostGuard vsR 5 Side.R (mRR q)

theorem sat_guardR0 (x : State (Var 5)) : Formula.sat (guardR 0) x ↔
    (x (Rv 0) < 100 ∧ 7/20 ≤ x (Rv 2)) := by
  simp [guardR, hostGuard, mRR, stopline_rover_2to5_IRv2, Run.lowerF, Run.lowerE, gp_0_35,
    gp_100_0, vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
theorem sat_guardR1 (x : State (Var 5)) : Formula.sat (guardR 1) x ↔
    (100 ≤ x (Rv 0) ∧ 7/20 ≤ x (Rv 2)) := by
  simp [guardR, hostGuard, mRR, stopline_rover_2to5_IRv2, Run.lowerF, Run.lowerE, gp_0_35,
    gp_100_0, vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
theorem sat_guardR2 (x : State (Var 5)) : Formula.sat (guardR 2) x ↔
    (100 ≤ x (Rv 0) ∧ x (Rv 2) ≤ 7/20) := by
  simp [guardR, hostGuard, mRR, stopline_rover_2to5_IRv2, Run.lowerF, Run.lowerE, gp_0_35,
    gp_100_0, vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-! ## The explicit runs -/

/-- Cruising: the speed held, the odometer its integral. -/
noncomputable def φC (ρ : State (Var 5)) (i : Fin 5) : ℝ → ℝ :=
  if i = 0 then intSol (ρ (Rv 0)) (fun _ => ρ (Rv 2)) else fun _ => ρ (Rv i)

theorem φC_zero (ρ : State (Var 5)) (i : Fin 5) : φC ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φC, intSol_zero]

theorem φC_der (ρ : State (Var 5)) (i : Fin 5) (t : ℝ) :
    HasDerivAt (φC ρ i) (Term.eval (fRR 0 i) (trajRs ρ (φC ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fR_p0]
    simp only [trajRs_R, φC, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ continuous_const t
  · rw [fR_pad1_0]; simp only [φC, Fin.isValue, Fin.reduceEq, if_false]; exact hasDerivAt_const t _
  · rw [fR_v0]
    simp only [φC, Fin.isValue, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · rw [fR_pad3_0]; simp only [φC, Fin.isValue, Fin.reduceEq, if_false]; exact hasDerivAt_const t _
  · rw [fR_pad4_0]; simp only [φC, Fin.isValue, Fin.reduceEq, if_false]; exact hasDerivAt_const t _

theorem φC_dom (ρ : State (Var 5)) (hρ : Formula.sat domRR ρ) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) (1/10)) : Formula.sat domRR (trajRs ρ (φC ρ) t) := by
  obtain ⟨hp0, hv0, hv1⟩ := (sat_domRR ρ).mp hρ
  have hp : 0 ≤ intSol (ρ (Rv 0)) (fun _ => ρ (Rv 2)) t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 0)) continuous_const τ)
      (fun _ _ => hv0) t ht
    simp only [intSol_zero] at h; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φC, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true, Fin.reduceEq, if_false]
  exact ⟨hp, hv0, hv1⟩

/-- Braking: the speed falls at 3 m/s², the odometer its integral. -/
noncomputable def φv (ρ : State (Var 5)) : ℝ → ℝ := intSol (ρ (Rv 2)) (fun _ => -3)

theorem φv_cont (ρ : State (Var 5)) : Continuous (φv ρ) :=
  continuous_iff_continuousAt.mpr fun t => (intSol_hasDerivAt _ continuous_const t).continuousAt

noncomputable def φB (ρ : State (Var 5)) (i : Fin 5) : ℝ → ℝ :=
  if i = 0 then intSol (ρ (Rv 0)) (φv ρ) else if i = 2 then φv ρ else fun _ => ρ (Rv i)

theorem φB_zero (ρ : State (Var 5)) (i : Fin 5) : φB ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φB, φv, intSol_zero]

theorem φB_der (ρ : State (Var 5)) (i : Fin 5) (t : ℝ) :
    HasDerivAt (φB ρ i) (Term.eval (fRR 1 i) (trajRs ρ (φB ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fR_p1]
    simp only [trajRs_R, φB, Fin.isValue, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont ρ) t
  · rw [fR_pad1_1]; simp only [φB, Fin.isValue, Fin.reduceEq, if_false]; exact hasDerivAt_const t _
  · rw [fR_v1]
    simp only [φB, Fin.isValue, Fin.reduceEq, if_false, if_true]
    exact intSol_hasDerivAt _ continuous_const t
  · rw [fR_pad3_1]; simp only [φB, Fin.isValue, Fin.reduceEq, if_false]; exact hasDerivAt_const t _
  · rw [fR_pad4_1]; simp only [φB, Fin.isValue, Fin.reduceEq, if_false]; exact hasDerivAt_const t _

/-- The braking speed stays between `v₀ − 3t` and `v₀`. -/
theorem φv_bounds (ρ : State (Var 5)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/10)) :
    ρ (Rv 2) - 3 * t ≤ φv ρ t ∧ φv ρ t ≤ ρ (Rv 2) := by
  have hd : ∀ τ, HasDerivAt (φv ρ) (-3) τ := fun τ => intSol_hasDerivAt _ continuous_const τ
  constructor
  · have h := mono_of_deriv_nonneg (φ := fun τ => φv ρ τ + 3 * τ) (g := fun _ => 0)
      (fun τ => by
        have h1 : HasDerivAt (fun τ => φv ρ τ + 3 * τ) (-3 + 3 * 1) τ :=
          (hd τ).add ((hasDerivAt_id τ).const_mul 3)
        exact h1.congr_deriv (by norm_num)) (fun _ _ => le_rfl) t ht
    simp only [φv, intSol_zero] at h ⊢; linarith
  · have h := mono_of_deriv_nonneg (φ := fun τ => -φv ρ τ) (g := fun _ => 3)
      (fun τ => by
        have h1 : HasDerivAt (fun τ => -φv ρ τ) (-(-3)) τ := (hd τ).neg
        exact h1.congr_deriv (by norm_num)) (fun _ _ => by norm_num) t ht
    simp only [φv, intSol_zero] at h ⊢; linarith

theorem φB_dom (ρ : State (Var 5)) (hg : Formula.sat (guardR 1) ρ) (hρ : Formula.sat domRR ρ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/10)) : Formula.sat domRR (trajRs ρ (φB ρ) t) := by
  obtain ⟨hp0, hv0, hv1⟩ := (sat_domRR ρ).mp hρ
  obtain ⟨_, hv35⟩ := (sat_guardR1 ρ).mp hg
  have hvt : ∀ τ ∈ Icc (0:ℝ) (1/10), 0 ≤ φv ρ τ ∧ φv ρ τ ≤ 8 := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := φv_bounds ρ τ hτ
    exact ⟨by linarith [hτ.2], by linarith⟩
  have hp : 0 ≤ intSol (ρ (Rv 0)) (φv ρ) t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 0)) (φv_cont ρ) τ)
      (fun τ hτ => (hvt τ hτ).1) t ht
    simp only [intSol_zero] at h; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φB, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true, Fin.reduceEq, if_false]
  exact ⟨hp, (hvt t ht).1, (hvt t ht).2⟩

theorem epsR_eq : epsR stopline_rover_2to5_IRv2 = 1/10 := by
  simp [epsR, stopline_rover_2to5_IRv2, gp_0_1]

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
    · exact ⟨_, trajRs_sol x (φC x) (1/10) (by norm_num) (φC_zero x)
        (fun i t _ _ => φC_der x i t) (fun t h0 h1 => φC_dom x hx t ⟨h0, h1⟩)⟩
    · exact ⟨_, trajRs_sol x (φB x) (1/10) (by norm_num) (φB_zero x)
        (fun i t _ _ => φB_der x i t) (fun t h0 h1 => φB_dom x hg hx t ⟨h0, h1⟩)⟩
    · exact ⟨_, const_sol (fun i s => by
        fin_cases i <;> simp [fR_p2, fR_v2, fR_pad1_2, fR_pad3_2, fR_pad4_2]) hx (by norm_num)⟩

/-- **Assumption 1 for `stopline_rover_2to5`**, every mode, Z3-free. -/
theorem stopline_rover_2to5_wellFormedR :
    WellFormedR GrG guardR (epsR stopline_rover_2to5_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_stopline WF

end StoplineRover2to5
end RelCertifier
