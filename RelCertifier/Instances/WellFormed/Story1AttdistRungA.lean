/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_a_6to8`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/Story1AttdistRungAGuarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder without speed caps, `s' = v ((1 − ψ²/2) − 0.3 θ²)`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.Instances.Story1AttdistRungAGuarded
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WellFormedLadder

namespace RelCertifier
namespace Story1AttdistRungAGuarded

open DL DLCalTiming DLRel Parse Set Story1AttdistRungAModal Story1AttdistRungAHandoff GPins

theorem epsR_eq : epsR story1_attdist_rung_a_6to8_IR = 1 := by
  simp [epsR, story1_attdist_rung_a_6to8_IR, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 8) := hostGuard vsD 8 Side.R (mRD q)

noncomputable def WF : LadderWF GrG guardR domRD where
  m := modeD
  fR := fRD
  vcap := False
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRD0_eval q hq, cstD_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRD] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRD] at hs; tauto
    have ha0 : -(1:ℝ)/2 ≤ s (Rv 2) := by rw [sat_domRD] at hs; tauto
    have ha1 : s (Rv 2) ≤ (3:ℝ)/20 := by rw [sat_domRD] at hs; tauto
    have hb0 : -(1:ℝ)/2 ≤ s (Rv 4) := by rw [sat_domRD] at hs; tauto
    have hb1 : s (Rv 4) ≤ (3:ℝ)/20 := by rw [sat_domRD] at hs; tauto
    rw [fRD1_eval q hq]
    exact odo_rate2 _ _ _ h0 h1 (by linarith) (by linarith) (by linarith) (by linarith)
  g0 := fun x => by rw [guardR, sat_guardR0]; simp
  g1 := fun x => by rw [guardR, sat_guardR1]; simp
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

/-- **Assumption 1 for `story1_attdist_rung_a_6to8`**, every mode, Z3-free. -/
theorem story1_attdist_rung_a_6to8_wellFormedR :
    WellFormedR GrG guardR (epsR story1_attdist_rung_a_6to8_IR) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end Story1AttdistRungAGuarded
end RelCertifier
