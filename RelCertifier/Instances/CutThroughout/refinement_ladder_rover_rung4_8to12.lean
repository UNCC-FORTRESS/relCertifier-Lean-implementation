/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers.refinement_ladder_rover_rung4_8to12
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung4_8to12

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutRefinementLadderRoverRung48to12
open DL Parse

def vsRefinementLadderRoverRung48to12 : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]
def dummyRefinementLadderRoverRung48to12 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRefinementLadderRoverRung48to12 (l : ℕ) : Parse.PMode := refinement_ladder_rover_rung4_8to12_IR.L.modes.getD l dummyRefinementLadderRoverRung48to12
def mRRefinementLadderRoverRung48to12 (q : ℕ) : Parse.PMode := refinement_ladder_rover_rung4_8to12_IR.R.modes.getD q dummyRefinementLadderRoverRung48to12
def fRowRefinementLadderRoverRung48to12 (l q : ℕ) : ModeFlagsE :=
  ((refinement_ladder_rover_rung4_8to12_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false⟩)
noncomputable def GWRefinementLadderRoverRung48to12 (l : ℕ) : SearchGraph (Var 12) :=
  realGraphOf vsRefinementLadderRoverRung48to12 12 refinement_ladder_rover_rung4_8to12_IR (mLRefinementLadderRoverRung48to12 l)
    ((refinement_ladder_rover_rung4_8to12_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((refinement_ladder_rover_rung4_8to12_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => refinement_ladder_rover_rung4_8to12_cover.pruned.contains (a, b))

theorem hsomeRefinementLadderRoverRung48to12_0 :
    (Run.lowerF vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0).guard : Option (IForm 12)).isSome = true := by
  simp [mRRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRefinementLadderRoverRung48to12_1 :
    (Run.lowerF vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1).guard : Option (IForm 12)).isSome = true := by
  simp [mRRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRefinementLadderRoverRung48to12_2 :
    (Run.lowerF vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2).guard : Option (IForm 12)).isSome = true := by
  simp [mRRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsRefinementLadderRoverRung48to12_0 : List (Term (Var 12)) :=
  hostComps vsRefinementLadderRoverRung48to12 12 (((refinement_ladder_rover_rung4_8to12_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRefinementLadderRoverRung48to12_0 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRefinementLadderRoverRung48to12_0 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)
  | 1 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)
  | 2 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)
  | _ => Formula.tt
noncomputable def cutLRefinementLadderRoverRung48to12_0 : List (CutAtomP 12) := [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")))]

theorem GWRefinementLadderRoverRung48to120_modes_eq : (GWRefinementLadderRoverRung48to12 0).modes =
    [realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 0) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 0 0) (mRRefinementLadderRoverRung48to12 0),
     realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 0) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 0 1) (mRRefinementLadderRoverRung48to12 1),
     realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 0) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 0 2) (mRRefinementLadderRoverRung48to12 2)] := rfl

theorem certRefinementLadderRoverRung48to12_0 (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWRefinementLadderRoverRung48to12 0) gsRefinementLadderRoverRung48to12_0 GdRefinementLadderRoverRung48to12_0 cutLRefinementLadderRoverRung48to12_0 cutRRefinementLadderRoverRung48to12_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRefinementLadderRoverRung48to12_0] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung48to12_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung48to12_0_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung48to12_0_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRefinementLadderRoverRung48to12_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRefinementLadderRoverRung48to12_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRefinementLadderRoverRung48to12_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRefinementLadderRoverRung48to12_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRefinementLadderRoverRung48to12_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRefinementLadderRoverRung48to12_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung48to120_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem refinement_ladder_rover_rung4_8to12_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 0)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 1)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_0[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_0) (cutF (cutRRefinementLadderRoverRung48to12_0 2)))) (gsRefinementLadderRoverRung48to12_0.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRefinementLadderRoverRung48to12_0 ν → CutSat cutLRefinementLadderRoverRung48to12_0 ν → CutSat (cutRRefinementLadderRoverRung48to12_0 q0) ν →
      Covered (GWRefinementLadderRoverRung48to12 0) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRefinementLadderRoverRung48to12 0) GdRefinementLadderRoverRung48to12_0 gsRefinementLadderRoverRung48to12_0 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRefinementLadderRoverRung48to12_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2RefinementLadderRoverRung48to12_0_0 hO2RefinementLadderRoverRung48to12_0_1 hO2RefinementLadderRoverRung48to12_1_0 hO2RefinementLadderRoverRung48to12_1_1 hO2RefinementLadderRoverRung48to12_2_0 hO2RefinementLadderRoverRung48to12_2_1 hO2LRefinementLadderRoverRung48to12_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRefinementLadderRoverRung48to12_1 : List (Term (Var 12)) :=
  hostComps vsRefinementLadderRoverRung48to12 12 (((refinement_ladder_rover_rung4_8to12_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRefinementLadderRoverRung48to12_1 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRefinementLadderRoverRung48to12_1 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)
  | 1 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)
  | 2 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)
  | _ => Formula.tt
noncomputable def cutLRefinementLadderRoverRung48to12_1 : List (CutAtomP 12) := [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")))]

theorem GWRefinementLadderRoverRung48to121_modes_eq : (GWRefinementLadderRoverRung48to12 1).modes =
    [realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 1) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 1 0) (mRRefinementLadderRoverRung48to12 0),
     realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 1) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 1 1) (mRRefinementLadderRoverRung48to12 1),
     realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 1) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 1 2) (mRRefinementLadderRoverRung48to12 2)] := rfl

theorem certRefinementLadderRoverRung48to12_1 (hdp_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWRefinementLadderRoverRung48to12 1) gsRefinementLadderRoverRung48to12_1 GdRefinementLadderRoverRung48to12_1 cutLRefinementLadderRoverRung48to12_1 cutRRefinementLadderRoverRung48to12_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRefinementLadderRoverRung48to12_1] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung48to12_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung48to12_1_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRefinementLadderRoverRung48to12_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRefinementLadderRoverRung48to12_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRefinementLadderRoverRung48to12_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRefinementLadderRoverRung48to12_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRefinementLadderRoverRung48to12_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRefinementLadderRoverRung48to12_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung48to121_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem refinement_ladder_rover_rung4_8to12_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 0)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 1)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_1[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_1) (cutF (cutRRefinementLadderRoverRung48to12_1 2)))) (gsRefinementLadderRoverRung48to12_1.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRefinementLadderRoverRung48to12_1 ν → CutSat cutLRefinementLadderRoverRung48to12_1 ν → CutSat (cutRRefinementLadderRoverRung48to12_1 q0) ν →
      Covered (GWRefinementLadderRoverRung48to12 1) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRefinementLadderRoverRung48to12 1) GdRefinementLadderRoverRung48to12_1 gsRefinementLadderRoverRung48to12_1 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRefinementLadderRoverRung48to12_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2RefinementLadderRoverRung48to12_0_0 hO2RefinementLadderRoverRung48to12_0_1 hO2RefinementLadderRoverRung48to12_1_0 hO2RefinementLadderRoverRung48to12_1_1 hO2RefinementLadderRoverRung48to12_2_0 hO2RefinementLadderRoverRung48to12_2_1 hO2LRefinementLadderRoverRung48to12_1_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRefinementLadderRoverRung48to12_2 : List (Term (Var 12)) :=
  hostComps vsRefinementLadderRoverRung48to12 12 (((refinement_ladder_rover_rung4_8to12_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRefinementLadderRoverRung48to12_2 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRefinementLadderRoverRung48to12_2 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)
  | 1 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)
  | 2 => hostGuard vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)
  | _ => Formula.tt
noncomputable def cutLRefinementLadderRoverRung48to12_2 : List (CutAtomP 12) := [(hostAtomF vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")))]

theorem GWRefinementLadderRoverRung48to122_modes_eq : (GWRefinementLadderRoverRung48to12 2).modes =
    [realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 2) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 2 0) (mRRefinementLadderRoverRung48to12 0),
     realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 2) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 2 1) (mRRefinementLadderRoverRung48to12 1),
     realModeOf vsRefinementLadderRoverRung48to12 12 (mLRefinementLadderRoverRung48to12 2) ((17 : ℚ) / 10) (fRowRefinementLadderRoverRung48to12 2 2) (mRRefinementLadderRoverRung48to12 2)] := rfl

theorem certRefinementLadderRoverRung48to12_2 (hdp_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWRefinementLadderRoverRung48to12 2) gsRefinementLadderRoverRung48to12_2 GdRefinementLadderRoverRung48to12_2 cutLRefinementLadderRoverRung48to12_2 cutRRefinementLadderRoverRung48to12_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRefinementLadderRoverRung48to12_2] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRefinementLadderRoverRung48to12) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRefinementLadderRoverRung48to12_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRefinementLadderRoverRung48to12_2_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRefinementLadderRoverRung48to12_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRefinementLadderRoverRung48to12) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RefinementLadderRoverRung48to12_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRefinementLadderRoverRung48to12_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRefinementLadderRoverRung48to12_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRefinementLadderRoverRung48to12_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRefinementLadderRoverRung48to12_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRefinementLadderRoverRung48to12_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRefinementLadderRoverRung48to12_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRefinementLadderRoverRung48to12_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung48to12, refinement_ladder_rover_rung4_8to12_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung48to12_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung48to122_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem refinement_ladder_rover_rung4_8to12_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 0)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 1)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (hostGuard vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung48to12_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung48to12_2[i],       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)) (hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2))) (Formula.and (cutF cutLRefinementLadderRoverRung48to12_2) (cutF (cutRRefinementLadderRoverRung48to12_2 2)))) (gsRefinementLadderRoverRung48to12_2.take i)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 0)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 1)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2RefinementLadderRoverRung48to12_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.R (mRRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) (hO2LRefinementLadderRoverRung48to12_2_0 : z3solve (flowQuery ⟨hostAtomG vsRefinementLadderRoverRung48to12 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRefinementLadderRoverRung48to12 12 Side.L (mLRefinementLadderRoverRung48to12 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsRefinementLadderRoverRung48to12_2 ν → CutSat cutLRefinementLadderRoverRung48to12_2 ν → CutSat (cutRRefinementLadderRoverRung48to12_2 q0) ν →
      Covered (GWRefinementLadderRoverRung48to12 2) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRefinementLadderRoverRung48to12 2) GdRefinementLadderRoverRung48to12_2 gsRefinementLadderRoverRung48to12_2 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRefinementLadderRoverRung48to12_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2RefinementLadderRoverRung48to12_0_0 hO2RefinementLadderRoverRung48to12_0_1 hO2RefinementLadderRoverRung48to12_1_0 hO2RefinementLadderRoverRung48to12_1_1 hO2RefinementLadderRoverRung48to12_2_0 hO2RefinementLadderRoverRung48to12_2_1 hO2LRefinementLadderRoverRung48to12_2_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutRefinementLadderRoverRung48to12
end RelCertifier
