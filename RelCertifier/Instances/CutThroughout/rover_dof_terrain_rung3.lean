/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers.rover_dof_terrain_rung3
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutRoverDofTerrainRung3
open DL Parse

def vsRoverDofTerrainRung3 : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]
def dummyRoverDofTerrainRung3 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRoverDofTerrainRung3 (l : ℕ) : Parse.PMode := rover_dof_terrain_rung3_IR.L.modes.getD l dummyRoverDofTerrainRung3
def mRRoverDofTerrainRung3 (q : ℕ) : Parse.PMode := rover_dof_terrain_rung3_IR.R.modes.getD q dummyRoverDofTerrainRung3
def fRowRoverDofTerrainRung3 (l q : ℕ) : ModeFlagsE :=
  ((rover_dof_terrain_rung3_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRoverDofTerrainRung3 (l : ℕ) : SearchGraph (Var 12) :=
  realGraphOf vsRoverDofTerrainRung3 12 rover_dof_terrain_rung3_IR (mLRoverDofTerrainRung3 l)
    ((rover_dof_terrain_rung3_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover_dof_terrain_rung3_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover_dof_terrain_rung3_cover.pruned.contains (a, b))

theorem hsomeRoverDofTerrainRung3_0 :
    (Run.lowerF vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0).guard : Option (IForm 12)).isSome = true := by
  simp [mRRoverDofTerrainRung3, rover_dof_terrain_rung3_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverDofTerrainRung3_1 :
    (Run.lowerF vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1).guard : Option (IForm 12)).isSome = true := by
  simp [mRRoverDofTerrainRung3, rover_dof_terrain_rung3_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverDofTerrainRung3_2 :
    (Run.lowerF vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2).guard : Option (IForm 12)).isSome = true := by
  simp [mRRoverDofTerrainRung3, rover_dof_terrain_rung3_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsRoverDofTerrainRung3_0 : List (Term (Var 12)) :=
  hostComps vsRoverDofTerrainRung3 12 (((rover_dof_terrain_rung3_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung3_0 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung3_0 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)
  | 1 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)
  | 2 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung3_0 : List (CutAtomP 12) := [(hostAtomF vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")))]

theorem GWRoverDofTerrainRung30_modes_eq : (GWRoverDofTerrainRung3 0).modes =
    [realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 0 0) (mRRoverDofTerrainRung3 0),
     realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 0 1) (mRRoverDofTerrainRung3 1),
     realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 0 2) (mRRoverDofTerrainRung3 2)] := rfl

theorem certRoverDofTerrainRung3_0 (hs_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung3 0) gsRoverDofTerrainRung3_0 GdRoverDofTerrainRung3_0 cutLRoverDofTerrainRung3_0 cutRRoverDofTerrainRung3_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung3_0] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung3_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung3_0_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung3_0_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung3_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung3_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung3_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung3_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung3_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung3_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung30_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung3_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 0)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 1)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_0) (cutF (cutRRoverDofTerrainRung3_0 2)))) (gsRoverDofTerrainRung3_0.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung3_0 ν → CutSat cutLRoverDofTerrainRung3_0 ν → CutSat (cutRRoverDofTerrainRung3_0 q0) ν →
      Covered (GWRoverDofTerrainRung3 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung3 0) GdRoverDofTerrainRung3_0 gsRoverDofTerrainRung3_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung3_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2RoverDofTerrainRung3_0_0 hO2RoverDofTerrainRung3_0_1 hO2RoverDofTerrainRung3_1_0 hO2RoverDofTerrainRung3_1_1 hO2RoverDofTerrainRung3_2_0 hO2RoverDofTerrainRung3_2_1 hO2LRoverDofTerrainRung3_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverDofTerrainRung3_1 : List (Term (Var 12)) :=
  hostComps vsRoverDofTerrainRung3 12 (((rover_dof_terrain_rung3_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung3_1 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung3_1 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)
  | 1 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)
  | 2 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung3_1 : List (CutAtomP 12) := [(hostAtomF vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")))]

theorem GWRoverDofTerrainRung31_modes_eq : (GWRoverDofTerrainRung3 1).modes =
    [realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 1 0) (mRRoverDofTerrainRung3 0),
     realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 1 1) (mRRoverDofTerrainRung3 1),
     realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 1 2) (mRRoverDofTerrainRung3 2)] := rfl

theorem certRoverDofTerrainRung3_1 (hdp_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung3 1) gsRoverDofTerrainRung3_1 GdRoverDofTerrainRung3_1 cutLRoverDofTerrainRung3_1 cutRRoverDofTerrainRung3_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung3_1] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung3_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung3_1_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung3_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung3_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung3_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung3_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung3_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung3_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung31_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung3_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 0)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 1)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_1) (cutF (cutRRoverDofTerrainRung3_1 2)))) (gsRoverDofTerrainRung3_1.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung3_1 ν → CutSat cutLRoverDofTerrainRung3_1 ν → CutSat (cutRRoverDofTerrainRung3_1 q0) ν →
      Covered (GWRoverDofTerrainRung3 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung3 1) GdRoverDofTerrainRung3_1 gsRoverDofTerrainRung3_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung3_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2RoverDofTerrainRung3_0_0 hO2RoverDofTerrainRung3_0_1 hO2RoverDofTerrainRung3_1_0 hO2RoverDofTerrainRung3_1_1 hO2RoverDofTerrainRung3_2_0 hO2RoverDofTerrainRung3_2_1 hO2LRoverDofTerrainRung3_1_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverDofTerrainRung3_2 : List (Term (Var 12)) :=
  hostComps vsRoverDofTerrainRung3 12 (((rover_dof_terrain_rung3_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung3_2 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung3_2 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)
  | 1 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)
  | 2 => hostGuard vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung3_2 : List (CutAtomP 12) := [(hostAtomF vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")))]

theorem GWRoverDofTerrainRung32_modes_eq : (GWRoverDofTerrainRung3 2).modes =
    [realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 2 0) (mRRoverDofTerrainRung3 0),
     realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 2 1) (mRRoverDofTerrainRung3 1),
     realModeOf vsRoverDofTerrainRung3 12 (mLRoverDofTerrainRung3 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung3 2 2) (mRRoverDofTerrainRung3 2)] := rfl

theorem certRoverDofTerrainRung3_2 (hdp_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung3 2) gsRoverDofTerrainRung3_2 GdRoverDofTerrainRung3_2 cutLRoverDofTerrainRung3_2 cutRRoverDofTerrainRung3_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung3_2] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung3) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung3_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung3_2_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung3_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung3) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung3_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung3_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung3_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung3_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung3_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung3_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung3_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung3_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung3, rover_dof_terrain_rung3_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung3_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung32_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung3_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 0)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 1)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (hostGuard vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung3_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung3_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)) (hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2))) (Formula.and (cutF cutLRoverDofTerrainRung3_2) (cutF (cutRRoverDofTerrainRung3_2 2)))) (gsRoverDofTerrainRung3_2.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung3_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.R (mRRoverDofTerrainRung3 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung3_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung3 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung3 12 Side.L (mLRoverDofTerrainRung3 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung3_2 ν → CutSat cutLRoverDofTerrainRung3_2 ν → CutSat (cutRRoverDofTerrainRung3_2 q0) ν →
      Covered (GWRoverDofTerrainRung3 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung3 2) GdRoverDofTerrainRung3_2 gsRoverDofTerrainRung3_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung3_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2RoverDofTerrainRung3_0_0 hO2RoverDofTerrainRung3_0_1 hO2RoverDofTerrainRung3_1_0 hO2RoverDofTerrainRung3_1_1 hO2RoverDofTerrainRung3_2_0 hO2RoverDofTerrainRung3_2_1 hO2LRoverDofTerrainRung3_2_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutRoverDofTerrainRung3
end RelCertifier
