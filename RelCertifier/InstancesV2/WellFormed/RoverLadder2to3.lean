/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_2to3`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverLadder2to3Guarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed caps, `s' = v`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit band runs (`runE`, with their duration kept). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to3
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverLadder2to3Pins

open Parse

/-! Parse pins of the numerals the guards and fields of `rover_ladder_2to3` write (the `GuardedPins` lemmas this file uses, local). -/

theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

end RoverLadder2to3Pins

namespace RoverLadder2to3Modal

open DL DLCalTiming DLRel Parse Set

def vsE : List String := ["v", "s", "psi"]

def dummyE : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRE (q : ℕ) : Parse.PMode :=
  rover_ladder_2to3_IRv2.R.modes.getD q dummyE

noncomputable def fRE (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsE 3 Side.R (mRE q)

noncomputable def domRE : Formula (Var 3) := hostEvolve vsE 3 Side.R (mRE 0)

noncomputable def modeE (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fRE q) (Term.const 1), dom := domRE, weight := 1 }

theorem he030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem he00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem he08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

noncomputable def cstE (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRE0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 0) x = 3 * (cstE q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, rover_ladder_2to3_IRv2, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstE]

theorem fRE1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, rover_ladder_2to3_IRv2, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRE2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRE q 2) x = 0 := by
  interval_cases q <;>
    simp [fRE, hostDyn, mRE, rover_ladder_2to3_IRv2, vsE, Run.dynOf,
      Run.lowerE, he3, he030, he050, he065, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRE (x : State (Var 3)) : Formula.sat domRE x ↔
    (0 ≤ x (Rv 1) ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 4/5) := by
  simp only [domRE, hostEvolve, mRE, rover_ladder_2to3_IRv2, vsE]
  simp [Run.lowerF, Run.lowerE, he00, he08, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  tauto

end RoverLadder2to3Modal

namespace RoverLadder2to3Guarded

open DL DLCalTiming DLRel Parse Set RoverLadder2to3Modal RoverLadder2to3Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsE 3 Side.R (mRE tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeE 0, modeE 1, modeE 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeE q) := by
  interval_cases q <;> rfl

/-! ## The right guards, evaluated -/

theorem he04 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he14 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem he03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem he05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRE, rover_ladder_2to3_IRv2, Run.lowerF, Run.lowerE, he00,
    he04, he14, he03, he05, he065, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRE, rover_ladder_2to3_IRv2, Run.lowerF, Run.lowerE, he00,
    he04, he14, he03, he05, he065, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRE, rover_ladder_2to3_IRv2, Run.lowerF, Run.lowerE, he00,
    he04, he14, he03, he05, he065, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- Band `q`'s explicit run from `ρ`: `v → c_q` exponentially at rate 3, `s` its integral,
the unused third coordinate frozen. -/
noncomputable def phiE (q : ℕ) (ρ : State (Var 3)) : Fin 3 → ℝ → ℝ := fun i t =>
  if i = 0 then cstE q + (ρ (Rv 0) - cstE q) * Real.exp (-(3 * t))
  else if i = 1 then
    ρ (Rv 1) + cstE q * t + (ρ (Rv 0) - cstE q) * (1 - Real.exp (-(3 * t))) / 3
  else ρ (Rv i)

noncomputable def runE (q : ℕ) (ρ : State (Var 3)) (t : ℝ) : State (Var 3) :=
  trajR ρ (phiE q ρ) t

theorem runE_v (q : ℕ) (ρ : State (Var 3)) (t : ℝ) :
    runE q ρ t (Rv 0) = cstE q + (ρ (Rv 0) - cstE q) * Real.exp (-(3 * t)) := by
  simp [runE, trajR_R, phiE]

theorem runE_s (q : ℕ) (ρ : State (Var 3)) (t : ℝ) :
    runE q ρ t (Rv 1) =
      ρ (Rv 1) + cstE q * t + (ρ (Rv 0) - cstE q) * (1 - Real.exp (-(3 * t))) / 3 := by
  simp [runE, trajR_R, phiE]

theorem cstE_bounds (q : ℕ) (hq : q < 3) : 3/10 ≤ cstE q ∧ cstE q ≤ 13/20 := by
  interval_cases q <;> norm_num [cstE]

/-- `s(t) ≥ s₀ + c t − c/3 ≥ s₀` along the run (from `v₀ ≥ 0`). -/
theorem runE_s_low (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hv0 : 0 ≤ ρ (Rv 0)) {t : ℝ}
    (ht : 0 ≤ t) :
    ρ (Rv 1) + cstE q * t - cstE q / 3 ≤ runE q ρ t (Rv 1) ∧ ρ (Rv 1) ≤ runE q ρ t (Rv 1) := by
  rw [runE_s]
  have hc := cstE_bounds q hq
  have he0 : 0 < Real.exp (-(3 * t)) := Real.exp_pos _
  have he1 : Real.exp (-(3 * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have he2 : 1 - 3 * t ≤ Real.exp (-(3 * t)) := by
    have := Real.add_one_le_exp (-(3 * t)); linarith
  constructor
  · nlinarith
  · rcases le_total (ρ (Rv 0)) (cstE q) with h | h
    · nlinarith
    · nlinarith

theorem runE_sem (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hdom : Formula.sat domRE ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Program.sem (Program.ode (modeE q).sys (modeE q).dom) ρ (runE q ρ τ) := by
  have hD := (sat_domRE ρ).mp hdom
  refine explicit_run ρ (phiE q ρ) τ hτ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [phiE]
  · intro i t _ _
    fin_cases i
    · have h := hasDerivAt_expApproach 3 (cstE q) (ρ (Rv 0)) t
      simp only [Fin.zero_eta, Fin.isValue]
      rw [fRE0_eval q hq, trajR_R]
      convert h using 1
      · funext u; simp [phiE]
      · simp [phiE]
    · have h := hasDerivAt_expIntegral 3 (cstE q) (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
      simp only [Fin.mk_one, Fin.isValue]
      rw [fRE1_eval q hq, trajR_R]
      convert h using 1
      · funext u; simp [phiE]
      · simp [phiE]
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [fRE2_eval q hq]
      have hf : phiE q ρ 2 = fun _ => ρ (Rv 2) := by funext u; simp [phiE]
      rw [hf]
      exact hasDerivAt_const t _
  · intro t ht _
    have hb := exp_approach_between 3 (cstE q) (ρ (Rv 0)) t (by norm_num) ht
    have hc := cstE_bounds q hq
    have hs := (runE_s_low q hq ρ hD.2.1 ht).2
    show Formula.sat domRE (runE q ρ t)
    rw [sat_domRE]
    refine ⟨?_, ?_, ?_⟩
    · show 0 ≤ runE q ρ t (Rv 1); linarith [hD.1]
    · show 0 ≤ runE q ρ t (Rv 0)
      rw [runE_v]
      exact le_trans (le_min hD.2.1 (by linarith)) hb.1
    · show runE q ρ t (Rv 0) ≤ 4/5
      rw [runE_v]
      exact le_trans hb.2 (max_le hD.2.2 (by linarith))

theorem epsR_eq : epsR rover_ladder_2to3_IRv2 = 1 := by
  simp [epsR, rover_ladder_2to3_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vsE 3 Side.R (mRE q)

/-- The instance's explicit band run (`runE_sem`), with its duration kept. -/
theorem runE_sol (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hdom : Formula.sat domRE ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeE q).sys (modeE q).dom ρ τ (runE q ρ) := by
  have hD := (sat_domRE ρ).mp hdom
  refine explicit_sol ρ (phiE q ρ) τ hτ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [phiE]
  · intro i t _ _
    fin_cases i
    · have h := hasDerivAt_expApproach 3 (cstE q) (ρ (Rv 0)) t
      simp only [Fin.zero_eta, Fin.isValue]
      rw [fRE0_eval q hq, trajR_R]
      convert h using 1
      · funext u; simp [phiE]
      · simp [phiE]
    · have h := hasDerivAt_expIntegral 3 (cstE q) (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
      simp only [Fin.mk_one, Fin.isValue]
      rw [fRE1_eval q hq, trajR_R]
      convert h using 1
      · funext u; simp [phiE]
      · simp [phiE]
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [fRE2_eval q hq]
      have hf : phiE q ρ 2 = fun _ => ρ (Rv 2) := by funext u; simp [phiE]
      rw [hf]
      exact hasDerivAt_const t _
  · intro t ht _
    have hb := exp_approach_between 3 (cstE q) (ρ (Rv 0)) t (by norm_num) ht
    have hc := cstE_bounds q hq
    have hs := (runE_s_low q hq ρ hD.2.1 ht).2
    show Formula.sat domRE (runE q ρ t)
    rw [sat_domRE]
    refine ⟨?_, ?_, ?_⟩
    · show 0 ≤ runE q ρ t (Rv 1); linarith [hD.1]
    · show 0 ≤ runE q ρ t (Rv 0)
      rw [runE_v]
      exact le_trans (le_min hD.2.1 (by linarith)) hb.1
    · show runE q ρ t (Rv 0) ≤ 4/5
      rw [runE_v]
      exact le_trans hb.2 (max_le hD.2.2 (by linarith))

noncomputable def WF : LadderWF GrG guardR domRE where
  m := modeE
  fR := fRE
  vcap := True
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRE0_eval q hq]; rfl
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRE] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRE] at hs; tauto
    rw [fRE1_eval q hq]; exact ⟨h0, h1⟩
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
  exists_run := fun q hq x hx => ⟨_, runE_sol q hq x hx 1 (by norm_num)⟩

/-- **Assumption 1 for `rover_ladder_2to3`**, every mode, Z3-free. -/
theorem rover_ladder_2to3_wellFormedR :
    WellFormedR GrG guardR (epsR rover_ladder_2to3_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverLadder2to3Guarded

end RelCertifier
