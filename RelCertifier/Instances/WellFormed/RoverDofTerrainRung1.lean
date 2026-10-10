/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung1`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverDofTerrainRung1Guarded.lean`), the lowered right guards, `ε_r = 1` (the
literal is the suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed
caps, `s' = v`: `wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`);
existence from the instance's explicit ladder runs (`LR.sol`). Z3-free.
-/
import RelCertifier.Instances.RoverDofTerrainRung1Guarded
import RelCertifier.Proofs.Encoding.WellFormedLadder

namespace RelCertifier
namespace RoverDofTerrainRung1Guarded

open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung1Modal GPins

theorem epsR_eq : epsR rover_dof_terrain_rung1_IR = 1 := by
  simp [epsR, rover_dof_terrain_rung1_IR, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vsE 3 Side.R (mRE q)

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
  fv := fun q hq s => by rw [fRE0_eval q hq, cstE_eq]
  fs := fun q hq s hs => by
    have := (sat_domRE s).mp hs
    rw [fRE1_eval q hq]; exact ⟨this.2.2.2.1, this.2.2.2.2⟩
  g0 := fun x => by rw [guardR, sat_guardR0]; simp [and_assoc]
  g1 := fun x => by rw [guardR, sat_guardR1]; simp [and_assoc]
  g2 := fun x => by rw [guardR, sat_guardR2]; simp
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
  exists_run := LR.exists_run GrG_modeAt

/-- **Assumption 1 for `rover_dof_terrain_rung1`**, every mode, Z3-free. -/
theorem rover_dof_terrain_rung1_wellFormedR :
    WellFormedR GrG guardR (epsR rover_dof_terrain_rung1_IR) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverDofTerrainRung1Guarded
end RelCertifier
