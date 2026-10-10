/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung3`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverDofTerrainRung3Guarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed caps, `s' = v`:
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.Instances.RoverDofTerrainRung3Guarded
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WellFormedLadder

namespace RelCertifier
namespace RoverDofTerrainRung3Guarded

open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung3Modal GPins

theorem epsR_eq : epsR rover_dof_terrain_rung3_IR = 1 := by
  simp [epsR, rover_dof_terrain_rung3_IR, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 12) := hostGuard vsW 12 Side.R (mRW q)

noncomputable def WF : LadderWF GrG guardR domRW where
  m := modeW
  fR := fRW
  vcap := True
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRW0_eval q hq, cstW_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRW] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRW] at hs; tauto
    rw [fRW1_eval q hq]; exact ⟨h0, h1⟩
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
  exists_run := LR.exists_run GrG_modeAt

/-- **Assumption 1 for `rover_dof_terrain_rung3`**, every mode, Z3-free. -/
theorem rover_dof_terrain_rung3_wellFormedR :
    WellFormedR GrG guardR (epsR rover_dof_terrain_rung3_IR) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverDofTerrainRung3Guarded
end RelCertifier
