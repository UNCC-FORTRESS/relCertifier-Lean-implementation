/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung1_2to3`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverLadderRung1Guarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed caps, `s' = v`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit band runs (`runE`, with their duration kept). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.Instances.RoverLadderRung1Guarded
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WellFormedLadder

namespace RelCertifier
namespace RoverLadderRung1Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung1Modal GPins

theorem epsR_eq : epsR refinement_ladder_rover_rung1_2to3_IR = 1 := by
  simp [epsR, refinement_ladder_rover_rung1_2to3_IR, gp_1_0]

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

/-- **Assumption 1 for `refinement_ladder_rover_rung1_2to3`**, every mode, Z3-free. -/
theorem refinement_ladder_rover_rung1_2to3_wellFormedR :
    WellFormedR GrG guardR (epsR refinement_ladder_rover_rung1_2to3_IR) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverLadderRung1Guarded
end RelCertifier
