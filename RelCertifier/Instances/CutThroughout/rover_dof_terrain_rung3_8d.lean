/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers.rover_dof_terrain_rung3_8d
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3_8d

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutRoverDofTerrainRung38d
open DL Parse

def vsRoverDofTerrainRung38d : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
def dummyRoverDofTerrainRung38d : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRoverDofTerrainRung38d (l : ℕ) : Parse.PMode := rover_dof_terrain_rung3_8d_IR.L.modes.getD l dummyRoverDofTerrainRung38d
def mRRoverDofTerrainRung38d (q : ℕ) : Parse.PMode := rover_dof_terrain_rung3_8d_IR.R.modes.getD q dummyRoverDofTerrainRung38d
def fRowRoverDofTerrainRung38d (l q : ℕ) : ModeFlagsE :=
  ((rover_dof_terrain_rung3_8d_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRoverDofTerrainRung38d (l : ℕ) : SearchGraph (Var 8) :=
  realGraphOf vsRoverDofTerrainRung38d 8 rover_dof_terrain_rung3_8d_IR (mLRoverDofTerrainRung38d l)
    ((rover_dof_terrain_rung3_8d_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover_dof_terrain_rung3_8d_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover_dof_terrain_rung3_8d_cover.pruned.contains (a, b))

theorem hsomeRoverDofTerrainRung38d_0 :
    (Run.lowerF vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0).guard : Option (IForm 8)).isSome = true := by
  simp [mRRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverDofTerrainRung38d_1 :
    (Run.lowerF vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1).guard : Option (IForm 8)).isSome = true := by
  simp [mRRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverDofTerrainRung38d_2 :
    (Run.lowerF vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2).guard : Option (IForm 8)).isSome = true := by
  simp [mRRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsRoverDofTerrainRung38d_0 : List (Term (Var 8)) :=
  hostComps vsRoverDofTerrainRung38d 8 (((rover_dof_terrain_rung3_8d_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung38d_0 : ℕ → List (CutAtomP 8)
  | 0 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung38d_0 : ℕ → Formula (Var 8)
  | 0 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)
  | 1 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)
  | 2 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung38d_0 : List (CutAtomP 8) := [(hostAtomF vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.0")))]

theorem GWRoverDofTerrainRung38d0_modes_eq : (GWRoverDofTerrainRung38d 0).modes =
    [realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 0 0) (mRRoverDofTerrainRung38d 0),
     realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 0 1) (mRRoverDofTerrainRung38d 1),
     realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 0 2) (mRRoverDofTerrainRung38d 2)] := rfl

theorem certRoverDofTerrainRung38d_0 (hs_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung38d 0) gsRoverDofTerrainRung38d_0 GdRoverDofTerrainRung38d_0 cutLRoverDofTerrainRung38d_0 cutRRoverDofTerrainRung38d_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung38d_0] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung38d_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung38d_0_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung38d_0_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung38d_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung38d_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung38d_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung38d_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung38d_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung38d_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung38d0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung3_8d_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 0)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 1)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_0) (cutF (cutRRoverDofTerrainRung38d_0 2)))) (gsRoverDofTerrainRung38d_0.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung38d_0 ν → CutSat cutLRoverDofTerrainRung38d_0 ν → CutSat (cutRRoverDofTerrainRung38d_0 q0) ν →
      Covered (GWRoverDofTerrainRung38d 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung38d 0) GdRoverDofTerrainRung38d_0 gsRoverDofTerrainRung38d_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung38d_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2RoverDofTerrainRung38d_0_0 hO2RoverDofTerrainRung38d_0_1 hO2RoverDofTerrainRung38d_1_0 hO2RoverDofTerrainRung38d_1_1 hO2RoverDofTerrainRung38d_2_0 hO2RoverDofTerrainRung38d_2_1 hO2LRoverDofTerrainRung38d_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverDofTerrainRung38d_1 : List (Term (Var 8)) :=
  hostComps vsRoverDofTerrainRung38d 8 (((rover_dof_terrain_rung3_8d_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung38d_1 : ℕ → List (CutAtomP 8)
  | 0 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung38d_1 : ℕ → Formula (Var 8)
  | 0 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)
  | 1 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)
  | 2 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung38d_1 : List (CutAtomP 8) := [(hostAtomF vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.6")))]

theorem GWRoverDofTerrainRung38d1_modes_eq : (GWRoverDofTerrainRung38d 1).modes =
    [realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 1 0) (mRRoverDofTerrainRung38d 0),
     realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 1 1) (mRRoverDofTerrainRung38d 1),
     realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 1 2) (mRRoverDofTerrainRung38d 2)] := rfl

theorem certRoverDofTerrainRung38d_1 (hdp_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung38d 1) gsRoverDofTerrainRung38d_1 GdRoverDofTerrainRung38d_1 cutLRoverDofTerrainRung38d_1 cutRRoverDofTerrainRung38d_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung38d_1] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung38d_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung38d_1_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung38d_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung38d_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung38d_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung38d_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung38d_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung38d_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung38d1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung3_8d_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 0)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 1)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_1) (cutF (cutRRoverDofTerrainRung38d_1 2)))) (gsRoverDofTerrainRung38d_1.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung38d_1 ν → CutSat cutLRoverDofTerrainRung38d_1 ν → CutSat (cutRRoverDofTerrainRung38d_1 q0) ν →
      Covered (GWRoverDofTerrainRung38d 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung38d 1) GdRoverDofTerrainRung38d_1 gsRoverDofTerrainRung38d_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung38d_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2RoverDofTerrainRung38d_0_0 hO2RoverDofTerrainRung38d_0_1 hO2RoverDofTerrainRung38d_1_0 hO2RoverDofTerrainRung38d_1_1 hO2RoverDofTerrainRung38d_2_0 hO2RoverDofTerrainRung38d_2_1 hO2LRoverDofTerrainRung38d_1_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverDofTerrainRung38d_2 : List (Term (Var 8)) :=
  hostComps vsRoverDofTerrainRung38d 8 (((rover_dof_terrain_rung3_8d_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung38d_2 : ℕ → List (CutAtomP 8)
  | 0 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung38d_2 : ℕ → Formula (Var 8)
  | 0 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)
  | 1 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)
  | 2 => hostGuard vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung38d_2 : List (CutAtomP 8) := [(hostAtomF vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "1.4")))]

theorem GWRoverDofTerrainRung38d2_modes_eq : (GWRoverDofTerrainRung38d 2).modes =
    [realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 2 0) (mRRoverDofTerrainRung38d 0),
     realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 2 1) (mRRoverDofTerrainRung38d 1),
     realModeOf vsRoverDofTerrainRung38d 8 (mLRoverDofTerrainRung38d 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung38d 2 2) (mRRoverDofTerrainRung38d 2)] := rfl

theorem certRoverDofTerrainRung38d_2 (hdp_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung38d 2) gsRoverDofTerrainRung38d_2 GdRoverDofTerrainRung38d_2 cutLRoverDofTerrainRung38d_2 cutRRoverDofTerrainRung38d_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung38d_2] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung38d) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung38d_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung38d_2_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung38d_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung38d) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung38d_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung38d_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung38d_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung38d_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung38d_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung38d_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung38d_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung38d_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung38d, rover_dof_terrain_rung3_8d_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung38d_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung38d2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung3_8d_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 0)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 1)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (hostGuard vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung38d_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung38d_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)) (hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2))) (Formula.and (cutF cutLRoverDofTerrainRung38d_2) (cutF (cutRRoverDofTerrainRung38d_2 2)))) (gsRoverDofTerrainRung38d_2.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung38d_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.R (mRRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung38d_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung38d 8 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung38d 8 Side.L (mLRoverDofTerrainRung38d 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung38d_2 ν → CutSat cutLRoverDofTerrainRung38d_2 ν → CutSat (cutRRoverDofTerrainRung38d_2 q0) ν →
      Covered (GWRoverDofTerrainRung38d 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung38d 2) GdRoverDofTerrainRung38d_2 gsRoverDofTerrainRung38d_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung38d_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2RoverDofTerrainRung38d_0_0 hO2RoverDofTerrainRung38d_0_1 hO2RoverDofTerrainRung38d_1_0 hO2RoverDofTerrainRung38d_1_1 hO2RoverDofTerrainRung38d_2_0 hO2RoverDofTerrainRung38d_2_1 hO2LRoverDofTerrainRung38d_2_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutRoverDofTerrainRung38d
end RelCertifier
