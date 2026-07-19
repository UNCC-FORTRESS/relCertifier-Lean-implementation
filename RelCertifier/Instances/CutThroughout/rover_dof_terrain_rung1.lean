/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers.rover_dof_terrain_rung1
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung1

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutRoverDofTerrainRung1
open DL Parse

def vsRoverDofTerrainRung1 : List String := ["v", "s", "psi"]
def dummyRoverDofTerrainRung1 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRoverDofTerrainRung1 (l : ℕ) : Parse.PMode := rover_dof_terrain_rung1_IR.L.modes.getD l dummyRoverDofTerrainRung1
def mRRoverDofTerrainRung1 (q : ℕ) : Parse.PMode := rover_dof_terrain_rung1_IR.R.modes.getD q dummyRoverDofTerrainRung1
def fRowRoverDofTerrainRung1 (l q : ℕ) : ModeFlagsE :=
  ((rover_dof_terrain_rung1_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRoverDofTerrainRung1 (l : ℕ) : SearchGraph (Var 3) :=
  realGraphOf vsRoverDofTerrainRung1 3 rover_dof_terrain_rung1_IR (mLRoverDofTerrainRung1 l)
    ((rover_dof_terrain_rung1_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover_dof_terrain_rung1_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover_dof_terrain_rung1_cover.pruned.contains (a, b))

theorem hsomeRoverDofTerrainRung1_0 :
    (Run.lowerF vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0).guard : Option (IForm 3)).isSome = true := by
  simp [mRRoverDofTerrainRung1, rover_dof_terrain_rung1_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverDofTerrainRung1_1 :
    (Run.lowerF vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1).guard : Option (IForm 3)).isSome = true := by
  simp [mRRoverDofTerrainRung1, rover_dof_terrain_rung1_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverDofTerrainRung1_2 :
    (Run.lowerF vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2).guard : Option (IForm 3)).isSome = true := by
  simp [mRRoverDofTerrainRung1, rover_dof_terrain_rung1_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsRoverDofTerrainRung1_0 : List (Term (Var 3)) :=
  hostComps vsRoverDofTerrainRung1 3 (((rover_dof_terrain_rung1_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung1_0 : ℕ → List (CutAtomP 3)
  | 0 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung1_0 : ℕ → Formula (Var 3)
  | 0 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)
  | 1 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)
  | 2 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung1_0 : List (CutAtomP 3) := [(hostAtomF vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.0")))]

theorem GWRoverDofTerrainRung10_modes_eq : (GWRoverDofTerrainRung1 0).modes =
    [realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 0 0) (mRRoverDofTerrainRung1 0),
     realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 0 1) (mRRoverDofTerrainRung1 1),
     realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 0) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 0 2) (mRRoverDofTerrainRung1 2)] := rfl

theorem certRoverDofTerrainRung1_0 (hs_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung1 0) gsRoverDofTerrainRung1_0 GdRoverDofTerrainRung1_0 cutLRoverDofTerrainRung1_0 cutRRoverDofTerrainRung1_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung1_0] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung1_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung1_0_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung1_0_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung1_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung1_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung1_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung1_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung1_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung1_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung10_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung1_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 0)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 1)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_0.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_0) (cutF (cutRRoverDofTerrainRung1_0 2)))) (gsRoverDofTerrainRung1_0.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung1_0 ν → CutSat cutLRoverDofTerrainRung1_0 ν → CutSat (cutRRoverDofTerrainRung1_0 q0) ν →
      Covered (GWRoverDofTerrainRung1 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung1 0) GdRoverDofTerrainRung1_0 gsRoverDofTerrainRung1_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung1_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2RoverDofTerrainRung1_0_0 hO2RoverDofTerrainRung1_0_1 hO2RoverDofTerrainRung1_1_0 hO2RoverDofTerrainRung1_1_1 hO2RoverDofTerrainRung1_2_0 hO2RoverDofTerrainRung1_2_1 hO2LRoverDofTerrainRung1_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverDofTerrainRung1_1 : List (Term (Var 3)) :=
  hostComps vsRoverDofTerrainRung1 3 (((rover_dof_terrain_rung1_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung1_1 : ℕ → List (CutAtomP 3)
  | 0 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung1_1 : ℕ → Formula (Var 3)
  | 0 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)
  | 1 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)
  | 2 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung1_1 : List (CutAtomP 3) := [(hostAtomF vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.6")))]

theorem GWRoverDofTerrainRung11_modes_eq : (GWRoverDofTerrainRung1 1).modes =
    [realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 1 0) (mRRoverDofTerrainRung1 0),
     realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 1 1) (mRRoverDofTerrainRung1 1),
     realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 1) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 1 2) (mRRoverDofTerrainRung1 2)] := rfl

theorem certRoverDofTerrainRung1_1 (hdp_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung1 1) gsRoverDofTerrainRung1_1 GdRoverDofTerrainRung1_1 cutLRoverDofTerrainRung1_1 cutRRoverDofTerrainRung1_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung1_1] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung1_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung1_1_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung1_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung1_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung1_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung1_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung1_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung1_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung11_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung1_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 0)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 1)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_1.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_1) (cutF (cutRRoverDofTerrainRung1_1 2)))) (gsRoverDofTerrainRung1_1.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung1_1 ν → CutSat cutLRoverDofTerrainRung1_1 ν → CutSat (cutRRoverDofTerrainRung1_1 q0) ν →
      Covered (GWRoverDofTerrainRung1 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung1 1) GdRoverDofTerrainRung1_1 gsRoverDofTerrainRung1_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung1_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2RoverDofTerrainRung1_0_0 hO2RoverDofTerrainRung1_0_1 hO2RoverDofTerrainRung1_1_0 hO2RoverDofTerrainRung1_1_1 hO2RoverDofTerrainRung1_2_0 hO2RoverDofTerrainRung1_2_1 hO2LRoverDofTerrainRung1_1_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverDofTerrainRung1_2 : List (Term (Var 3)) :=
  hostComps vsRoverDofTerrainRung1 3 (((rover_dof_terrain_rung1_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverDofTerrainRung1_2 : ℕ → List (CutAtomP 3)
  | 0 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverDofTerrainRung1_2 : ℕ → Formula (Var 3)
  | 0 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)
  | 1 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)
  | 2 => hostGuard vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)
  | _ => Formula.tt
noncomputable def cutLRoverDofTerrainRung1_2 : List (CutAtomP 3) := [(hostAtomF vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "1.4")))]

theorem GWRoverDofTerrainRung12_modes_eq : (GWRoverDofTerrainRung1 2).modes =
    [realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 2 0) (mRRoverDofTerrainRung1 0),
     realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 2 1) (mRRoverDofTerrainRung1 1),
     realModeOf vsRoverDofTerrainRung1 3 (mLRoverDofTerrainRung1 2) ((1 : ℚ) / 1) (fRowRoverDofTerrainRung1 2 2) (mRRoverDofTerrainRung1 2)] := rfl

theorem certRoverDofTerrainRung1_2 (hdp_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverDofTerrainRung1 2) gsRoverDofTerrainRung1_2 GdRoverDofTerrainRung1_2 cutLRoverDofTerrainRung1_2 cutRRoverDofTerrainRung1_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverDofTerrainRung1_2] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverDofTerrainRung1) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverDofTerrainRung1_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((1 : ℚ) / 1 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverDofTerrainRung1_2_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverDofTerrainRung1_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverDofTerrainRung1) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverDofTerrainRung1_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverDofTerrainRung1_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverDofTerrainRung1_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverDofTerrainRung1_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverDofTerrainRung1_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverDofTerrainRung1_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverDofTerrainRung1_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverDofTerrainRung1_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDofTerrainRung1, rover_dof_terrain_rung1_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDofTerrainRung1_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverDofTerrainRung12_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_dof_terrain_rung1_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 0)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 1)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (hostGuard vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverDofTerrainRung1_2.length),     z3solve (flowQuery ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDofTerrainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)) (hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2))) (Formula.and (cutF cutLRoverDofTerrainRung1_2) (cutF (cutRRoverDofTerrainRung1_2 2)))) (gsRoverDofTerrainRung1_2.take i)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 0)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 1)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2RoverDofTerrainRung1_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.R (mRRoverDofTerrainRung1 2)⟩) = Verdict.unsat) (hO2LRoverDofTerrainRung1_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverDofTerrainRung1 3 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverDofTerrainRung1 3 Side.L (mLRoverDofTerrainRung1 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsRoverDofTerrainRung1_2 ν → CutSat cutLRoverDofTerrainRung1_2 ν → CutSat (cutRRoverDofTerrainRung1_2 q0) ν →
      Covered (GWRoverDofTerrainRung1 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverDofTerrainRung1 2) GdRoverDofTerrainRung1_2 gsRoverDofTerrainRung1_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverDofTerrainRung1_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2RoverDofTerrainRung1_0_0 hO2RoverDofTerrainRung1_0_1 hO2RoverDofTerrainRung1_1_0 hO2RoverDofTerrainRung1_1_1 hO2RoverDofTerrainRung1_2_0 hO2RoverDofTerrainRung1_2_1 hO2LRoverDofTerrainRung1_2_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 5 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutRoverDofTerrainRung1
end RelCertifier
