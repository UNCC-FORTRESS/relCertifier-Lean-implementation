/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutRefinementLadderRoverRung36to8
open DL Parse

def vsRefinementLadderRoverRung36to8 : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
def dummyRefinementLadderRoverRung36to8 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRefinementLadderRoverRung36to8 (l : ℕ) : Parse.PMode := refinement_ladder_rover_rung3_6to8_IR.L.modes.getD l dummyRefinementLadderRoverRung36to8
def mRRefinementLadderRoverRung36to8 (q : ℕ) : Parse.PMode := refinement_ladder_rover_rung3_6to8_IR.R.modes.getD q dummyRefinementLadderRoverRung36to8
def fRowRefinementLadderRoverRung36to8 (l q : ℕ) : ModeFlagsE :=
  ((refinement_ladder_rover_rung3_6to8_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRefinementLadderRoverRung36to8 (l : ℕ) : SearchGraph (Var 8) :=
  realGraphOf vsRefinementLadderRoverRung36to8 8 refinement_ladder_rover_rung3_6to8_IR (mLRefinementLadderRoverRung36to8 l)
    ((refinement_ladder_rover_rung3_6to8_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((refinement_ladder_rover_rung3_6to8_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => refinement_ladder_rover_rung3_6to8_cover.pruned.contains (a, b))

theorem hsomeRefinementLadderRoverRung36to8_0 :
    (Run.lowerF vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0).guard : Option (IForm 8)).isSome = true := by
  simp [mRRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRefinementLadderRoverRung36to8_1 :
    (Run.lowerF vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1).guard : Option (IForm 8)).isSome = true := by
  simp [mRRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRefinementLadderRoverRung36to8_2 :
    (Run.lowerF vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2).guard : Option (IForm 8)).isSome = true := by
  simp [mRRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsRefinementLadderRoverRung36to8_0 : List (Term (Var 8)) :=
  hostComps vsRefinementLadderRoverRung36to8 8 (((refinement_ladder_rover_rung3_6to8_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRefinementLadderRoverRung36to8_0 : ℕ → List (CutAtomP 8)
  | 0 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRefinementLadderRoverRung36to8_0 : ℕ → Formula (Var 8)
  | 0 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)
  | 1 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)
  | 2 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)
  | _ => Formula.tt
noncomputable def cutLRefinementLadderRoverRung36to8_0 : List (CutAtomP 8) := [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.3")))]

theorem GWRefinementLadderRoverRung36to80_modes_eq : (GWRefinementLadderRoverRung36to8 0).modes =
    [realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 0) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 0 0) (mRRefinementLadderRoverRung36to8 0),
     realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 0) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 0 1) (mRRefinementLadderRoverRung36to8 1),
     realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 0) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 0 2) (mRRefinementLadderRoverRung36to8 2)] := rfl

theorem certRefinementLadderRoverRung36to8_0 (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.3")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWRefinementLadderRoverRung36to8 0) gsRefinementLadderRoverRung36to8_0 GdRefinementLadderRoverRung36to8_0 cutLRefinementLadderRoverRung36to8_0 cutRRefinementLadderRoverRung36to8_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRefinementLadderRoverRung36to8_0] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
    · rw [List.mem_singleton] at ha
      subst ha
      exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.L) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_L_nonstrict _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_L_superlevel _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_L_nonstrict _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_L_superlevel _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_0_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_L_nonstrict _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_L_superlevel _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_0_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRefinementLadderRoverRung36to8_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRefinementLadderRoverRung36to8_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRefinementLadderRoverRung36to8_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRefinementLadderRoverRung36to8_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRefinementLadderRoverRung36to8_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRefinementLadderRoverRung36to8_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung36to80_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem refinement_ladder_rover_rung3_6to8_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 0)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 1)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_0) (cutF (cutRRefinementLadderRoverRung36to8_0 2)))) (gsRefinementLadderRoverRung36to8_0.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.3")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRefinementLadderRoverRung36to8_0 ν → CutSat cutLRefinementLadderRoverRung36to8_0 ν → CutSat (cutRRefinementLadderRoverRung36to8_0 q0) ν →
      Covered (GWRefinementLadderRoverRung36to8 0) ⟨q0, 3, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRefinementLadderRoverRung36to8 0) GdRefinementLadderRoverRung36to8_0 gsRefinementLadderRoverRung36to8_0 ⟨q0, 3, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRefinementLadderRoverRung36to8_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2RefinementLadderRoverRung36to8_0_0 hO2RefinementLadderRoverRung36to8_0_1 hO2RefinementLadderRoverRung36to8_1_0 hO2RefinementLadderRoverRung36to8_1_1 hO2RefinementLadderRoverRung36to8_2_0 hO2RefinementLadderRoverRung36to8_2_1 hO2LRefinementLadderRoverRung36to8_0_0 hO2LRefinementLadderRoverRung36to8_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 13 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRefinementLadderRoverRung36to8_1 : List (Term (Var 8)) :=
  hostComps vsRefinementLadderRoverRung36to8 8 (((refinement_ladder_rover_rung3_6to8_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRefinementLadderRoverRung36to8_1 : ℕ → List (CutAtomP 8)
  | 0 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRefinementLadderRoverRung36to8_1 : ℕ → Formula (Var 8)
  | 0 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)
  | 1 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)
  | 2 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)
  | _ => Formula.tt
noncomputable def cutLRefinementLadderRoverRung36to8_1 : List (CutAtomP 8) := [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.5")))]

theorem GWRefinementLadderRoverRung36to81_modes_eq : (GWRefinementLadderRoverRung36to8 1).modes =
    [realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 1) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 1 0) (mRRefinementLadderRoverRung36to8 0),
     realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 1) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 1 1) (mRRefinementLadderRoverRung36to8 1),
     realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 1) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 1 2) (mRRefinementLadderRoverRung36to8 2)] := rfl

theorem certRefinementLadderRoverRung36to8_1 (hdp_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.5")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWRefinementLadderRoverRung36to8 1) gsRefinementLadderRoverRung36to8_1 GdRefinementLadderRoverRung36to8_1 cutLRefinementLadderRoverRung36to8_1 cutRRefinementLadderRoverRung36to8_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRefinementLadderRoverRung36to8_1] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
    · rw [List.mem_singleton] at ha
      subst ha
      exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.L) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_L_nonstrict _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_L_superlevel _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_L_nonstrict _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_L_superlevel _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_1_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRefinementLadderRoverRung36to8_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRefinementLadderRoverRung36to8_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRefinementLadderRoverRung36to8_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRefinementLadderRoverRung36to8_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRefinementLadderRoverRung36to8_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRefinementLadderRoverRung36to8_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung36to81_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem refinement_ladder_rover_rung3_6to8_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 0)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 1)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_1) (cutF (cutRRefinementLadderRoverRung36to8_1 2)))) (gsRefinementLadderRoverRung36to8_1.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.5")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRefinementLadderRoverRung36to8_1 ν → CutSat cutLRefinementLadderRoverRung36to8_1 ν → CutSat (cutRRefinementLadderRoverRung36to8_1 q0) ν →
      Covered (GWRefinementLadderRoverRung36to8 1) ⟨q0, 3, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRefinementLadderRoverRung36to8 1) GdRefinementLadderRoverRung36to8_1 gsRefinementLadderRoverRung36to8_1 ⟨q0, 3, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRefinementLadderRoverRung36to8_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2RefinementLadderRoverRung36to8_0_0 hO2RefinementLadderRoverRung36to8_0_1 hO2RefinementLadderRoverRung36to8_1_0 hO2RefinementLadderRoverRung36to8_1_1 hO2RefinementLadderRoverRung36to8_2_0 hO2RefinementLadderRoverRung36to8_2_1 hO2LRefinementLadderRoverRung36to8_1_0 hO2LRefinementLadderRoverRung36to8_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 13 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRefinementLadderRoverRung36to8_2 : List (Term (Var 8)) :=
  hostComps vsRefinementLadderRoverRung36to8 8 (((refinement_ladder_rover_rung3_6to8_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRefinementLadderRoverRung36to8_2 : ℕ → List (CutAtomP 8)
  | 0 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRefinementLadderRoverRung36to8_2 : ℕ → Formula (Var 8)
  | 0 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)
  | 1 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)
  | 2 => hostGuard vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)
  | _ => Formula.tt
noncomputable def cutLRefinementLadderRoverRung36to8_2 : List (CutAtomP 8) := [(hostAtomF vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.65")))]

theorem GWRefinementLadderRoverRung36to82_modes_eq : (GWRefinementLadderRoverRung36to8 2).modes =
    [realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 2) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 2 0) (mRRefinementLadderRoverRung36to8 0),
     realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 2) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 2 1) (mRRefinementLadderRoverRung36to8 1),
     realModeOf vsRefinementLadderRoverRung36to8 8 (mLRefinementLadderRoverRung36to8 2) ((9 : ℚ) / 4) (fRowRefinementLadderRoverRung36to8 2 2) (mRRefinementLadderRoverRung36to8 2)] := rfl

theorem certRefinementLadderRoverRung36to8_2 (hdp_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.65")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWRefinementLadderRoverRung36to8 2) gsRefinementLadderRoverRung36to8_2 GdRefinementLadderRoverRung36to8_2 cutLRefinementLadderRoverRung36to8_2 cutRRefinementLadderRoverRung36to8_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRefinementLadderRoverRung36to8_2] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
    · rw [List.mem_singleton] at ha
      subst ha
      exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.L) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung36to8) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_L_nonstrict _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_L_superlevel _ _ _ (Term.const (((9 : ℚ) / 4 : ℚ) : ℝ)) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
            (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((9 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
        · rw [List.mem_singleton] at ha
          subst ha
          exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung36to8) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung36to8_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRefinementLadderRoverRung36to8_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRefinementLadderRoverRung36to8_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRefinementLadderRoverRung36to8_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRefinementLadderRoverRung36to8_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung36to8_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRefinementLadderRoverRung36to8_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRefinementLadderRoverRung36to8_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung36to8, refinement_ladder_rover_rung3_6to8_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung36to8_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung36to82_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem refinement_ladder_rover_rung3_6to8_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 0)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 1)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const (((9 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (hostGuard vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung36to8_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung36to8_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)) (hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2))) (Formula.and (cutF cutLRefinementLadderRoverRung36to8_2) (cutF (cutRRefinementLadderRoverRung36to8_2 2)))) (gsRefinementLadderRoverRung36to8_2.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.R (mRRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung36to8_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung36to8 8 Side.L (.cmp "<=" (.var "v") (.num "0.65")),       hostDyn vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung36to8 8 Side.L (mLRefinementLadderRoverRung36to8 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsRefinementLadderRoverRung36to8_2 ν → CutSat cutLRefinementLadderRoverRung36to8_2 ν → CutSat (cutRRefinementLadderRoverRung36to8_2 q0) ν →
      Covered (GWRefinementLadderRoverRung36to8 2) ⟨q0, 3, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRefinementLadderRoverRung36to8 2) GdRefinementLadderRoverRung36to8_2 gsRefinementLadderRoverRung36to8_2 ⟨q0, 3, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRefinementLadderRoverRung36to8_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2RefinementLadderRoverRung36to8_0_0 hO2RefinementLadderRoverRung36to8_0_1 hO2RefinementLadderRoverRung36to8_1_0 hO2RefinementLadderRoverRung36to8_1_1 hO2RefinementLadderRoverRung36to8_2_0 hO2RefinementLadderRoverRung36to8_2_1 hO2LRefinementLadderRoverRung36to8_2_0 hO2LRefinementLadderRoverRung36to8_2_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 13 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutRefinementLadderRoverRung36to8
end RelCertifier
