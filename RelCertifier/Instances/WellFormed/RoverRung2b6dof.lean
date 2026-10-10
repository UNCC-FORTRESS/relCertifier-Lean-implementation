/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2b_6dof`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverRung2b6dofGuarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder without speed caps, `s' = v`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.Instances.RoverRung2b6dofGuarded
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WellFormedLadder

namespace RelCertifier
namespace RoverRung2b6dofGuarded

open DL DLCalTiming DLRel Parse Set RoverRung2b6dofModal GPins

theorem epsR_eq : epsR refinement_ladder_rover_rung2b_6dof_IR = 1 := by
  simp [epsR, refinement_ladder_rover_rung2b_6dof_IR, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vsB2 6 Side.R (mRB2 q)

noncomputable def WF : LadderWF GrG guardR domRB2 where
  m := modeB2
  fR := fRB2
  vcap := False
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRB20_eval q hq, cB2_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRB2] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRB2] at hs; tauto
    rw [fRB21_eval q hq]; exact ⟨h0, h1⟩
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

/-- **Assumption 1 for `refinement_ladder_rover_rung2b_6dof`**, every mode, Z3-free. -/
theorem refinement_ladder_rover_rung2b_6dof_wellFormedR :
    WellFormedR GrG guardR (epsR refinement_ladder_rover_rung2b_6dof_IR) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverRung2b6dofGuarded
end RelCertifier
