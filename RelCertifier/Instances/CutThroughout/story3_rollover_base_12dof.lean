/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers.story3_rollover_base_12dof
import RelCertifier.Instances.BenchIR.story3_rollover_base_12dof

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutStory3RolloverBase12dof
open DL Parse

def vsStory3RolloverBase12dof : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "e", "r", "phi_r", "omega_phi", "z", "y"]
def dummyStory3RolloverBase12dof : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLStory3RolloverBase12dof (l : ℕ) : Parse.PMode := story3_rollover_base_12dof_IR.L.modes.getD l dummyStory3RolloverBase12dof
def mRStory3RolloverBase12dof (q : ℕ) : Parse.PMode := story3_rollover_base_12dof_IR.R.modes.getD q dummyStory3RolloverBase12dof
def fRowStory3RolloverBase12dof (l q : ℕ) : ModeFlagsE :=
  ((story3_rollover_base_12dof_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWStory3RolloverBase12dof (l : ℕ) : SearchGraph (Var 12) :=
  realGraphOf vsStory3RolloverBase12dof 12 story3_rollover_base_12dof_IR (mLStory3RolloverBase12dof l)
    ((story3_rollover_base_12dof_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((story3_rollover_base_12dof_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => story3_rollover_base_12dof_cover.pruned.contains (a, b))

theorem hsomeStory3RolloverBase12dof_0 :
    (Run.lowerF vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0).guard : Option (IForm 12)).isSome = true := by
  simp [mRStory3RolloverBase12dof, story3_rollover_base_12dof_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeStory3RolloverBase12dof_1 :
    (Run.lowerF vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1).guard : Option (IForm 12)).isSome = true := by
  simp [mRStory3RolloverBase12dof, story3_rollover_base_12dof_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeStory3RolloverBase12dof_2 :
    (Run.lowerF vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2).guard : Option (IForm 12)).isSome = true := by
  simp [mRStory3RolloverBase12dof, story3_rollover_base_12dof_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsStory3RolloverBase12dof_0 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverBase12dof 12 (((story3_rollover_base_12dof_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRStory3RolloverBase12dof_0 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdStory3RolloverBase12dof_0 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)
  | 1 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)
  | 2 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)
  | _ => Formula.tt
noncomputable def cutLStory3RolloverBase12dof_0 : List (CutAtomP 12) := [(hostAtomF vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")))]

theorem GWStory3RolloverBase12dof0_modes_eq : (GWStory3RolloverBase12dof 0).modes =
    [realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 0) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 0 0) (mRStory3RolloverBase12dof 0),
     realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 0) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 0 1) (mRStory3RolloverBase12dof 1),
     realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 0) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 0 2) (mRStory3RolloverBase12dof 2)] := rfl

theorem certStory3RolloverBase12dof_0 (hs_0_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2LStory3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWStory3RolloverBase12dof 0) gsStory3RolloverBase12dof_0 GdStory3RolloverBase12dof_0 cutLStory3RolloverBase12dof_0 cutRStory3RolloverBase12dof_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLStory3RolloverBase12dof_0] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((5 : ℚ) / 4 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverBase12dof_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((5 : ℚ) / 4 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverBase12dof_0_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((5 : ℚ) / 4 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverBase12dof_0_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeStory3RolloverBase12dof_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeStory3RolloverBase12dof_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeStory3RolloverBase12dof_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeStory3RolloverBase12dof_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeStory3RolloverBase12dof_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeStory3RolloverBase12dof_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverBase12dof0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_base_12dof_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 0)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 1)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_0.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_0) (cutF (cutRStory3RolloverBase12dof_0 2)))) (gsStory3RolloverBase12dof_0.take i)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2LStory3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory3RolloverBase12dof_0 ν → CutSat cutLStory3RolloverBase12dof_0 ν → CutSat (cutRStory3RolloverBase12dof_0 q0) ν →
      Covered (GWStory3RolloverBase12dof 0) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWStory3RolloverBase12dof 0) GdStory3RolloverBase12dof_0 gsStory3RolloverBase12dof_0 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certStory3RolloverBase12dof_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2Story3RolloverBase12dof_0_0 hO2Story3RolloverBase12dof_0_1 hO2Story3RolloverBase12dof_1_0 hO2Story3RolloverBase12dof_1_1 hO2Story3RolloverBase12dof_2_0 hO2Story3RolloverBase12dof_2_1 hO2LStory3RolloverBase12dof_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsStory3RolloverBase12dof_1 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverBase12dof 12 (((story3_rollover_base_12dof_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRStory3RolloverBase12dof_1 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdStory3RolloverBase12dof_1 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)
  | 1 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)
  | 2 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)
  | _ => Formula.tt
noncomputable def cutLStory3RolloverBase12dof_1 : List (CutAtomP 12) := [(hostAtomF vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")))]

theorem GWStory3RolloverBase12dof1_modes_eq : (GWStory3RolloverBase12dof 1).modes =
    [realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 1) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 1 0) (mRStory3RolloverBase12dof 0),
     realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 1) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 1 1) (mRStory3RolloverBase12dof 1),
     realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 1) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 1 2) (mRStory3RolloverBase12dof 2)] := rfl

theorem certStory3RolloverBase12dof_1 (hdp_1_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2LStory3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWStory3RolloverBase12dof 1) gsStory3RolloverBase12dof_1 GdStory3RolloverBase12dof_1 cutLStory3RolloverBase12dof_1 cutRStory3RolloverBase12dof_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLStory3RolloverBase12dof_1] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((5 : ℚ) / 4 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverBase12dof_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((5 : ℚ) / 4 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverBase12dof_1_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeStory3RolloverBase12dof_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeStory3RolloverBase12dof_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeStory3RolloverBase12dof_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeStory3RolloverBase12dof_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeStory3RolloverBase12dof_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeStory3RolloverBase12dof_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverBase12dof1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_base_12dof_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 0)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 1)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_1.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_1) (cutF (cutRStory3RolloverBase12dof_1 2)))) (gsStory3RolloverBase12dof_1.take i)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2LStory3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory3RolloverBase12dof_1 ν → CutSat cutLStory3RolloverBase12dof_1 ν → CutSat (cutRStory3RolloverBase12dof_1 q0) ν →
      Covered (GWStory3RolloverBase12dof 1) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWStory3RolloverBase12dof 1) GdStory3RolloverBase12dof_1 gsStory3RolloverBase12dof_1 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certStory3RolloverBase12dof_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2Story3RolloverBase12dof_0_0 hO2Story3RolloverBase12dof_0_1 hO2Story3RolloverBase12dof_1_0 hO2Story3RolloverBase12dof_1_1 hO2Story3RolloverBase12dof_2_0 hO2Story3RolloverBase12dof_2_1 hO2LStory3RolloverBase12dof_1_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsStory3RolloverBase12dof_2 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverBase12dof 12 (((story3_rollover_base_12dof_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRStory3RolloverBase12dof_2 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdStory3RolloverBase12dof_2 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)
  | 1 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)
  | 2 => hostGuard vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)
  | _ => Formula.tt
noncomputable def cutLStory3RolloverBase12dof_2 : List (CutAtomP 12) := [(hostAtomF vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")))]

theorem GWStory3RolloverBase12dof2_modes_eq : (GWStory3RolloverBase12dof 2).modes =
    [realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 2) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 2 0) (mRStory3RolloverBase12dof 0),
     realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 2) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 2 1) (mRStory3RolloverBase12dof 1),
     realModeOf vsStory3RolloverBase12dof 12 (mLStory3RolloverBase12dof 2) ((5 : ℚ) / 4) (fRowStory3RolloverBase12dof 2 2) (mRStory3RolloverBase12dof 2)] := rfl

theorem certStory3RolloverBase12dof_2 (hdp_2_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2LStory3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWStory3RolloverBase12dof 2) gsStory3RolloverBase12dof_2 GdStory3RolloverBase12dof_2 cutLStory3RolloverBase12dof_2 cutRStory3RolloverBase12dof_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLStory3RolloverBase12dof_2] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverBase12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverBase12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((5 : ℚ) / 4 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverBase12dof_2_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((5 : ℚ) / 4 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverBase12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverBase12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverBase12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeStory3RolloverBase12dof_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeStory3RolloverBase12dof_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeStory3RolloverBase12dof_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeStory3RolloverBase12dof_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRStory3RolloverBase12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeStory3RolloverBase12dof_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeStory3RolloverBase12dof_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverBase12dof, story3_rollover_base_12dof_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverBase12dof_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverBase12dof2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_base_12dof_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 0)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 1)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const (((5 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (hostGuard vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsStory3RolloverBase12dof_2.length),     z3solve (flowQuery ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverBase12dof_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)) (hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2))) (Formula.and (cutF cutLStory3RolloverBase12dof_2) (cutF (cutRStory3RolloverBase12dof_2 2)))) (gsStory3RolloverBase12dof_2.take i)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 0)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 1)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2Story3RolloverBase12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.R (mRStory3RolloverBase12dof 2)⟩) = Verdict.unsat) (hO2LStory3RolloverBase12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverBase12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverBase12dof 12 Side.L (mLStory3RolloverBase12dof 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsStory3RolloverBase12dof_2 ν → CutSat cutLStory3RolloverBase12dof_2 ν → CutSat (cutRStory3RolloverBase12dof_2 q0) ν →
      Covered (GWStory3RolloverBase12dof 2) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWStory3RolloverBase12dof 2) GdStory3RolloverBase12dof_2 gsStory3RolloverBase12dof_2 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certStory3RolloverBase12dof_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2Story3RolloverBase12dof_0_0 hO2Story3RolloverBase12dof_0_1 hO2Story3RolloverBase12dof_1_0 hO2Story3RolloverBase12dof_1_1 hO2Story3RolloverBase12dof_2_0 hO2Story3RolloverBase12dof_2_1 hO2LStory3RolloverBase12dof_2_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutStory3RolloverBase12dof
end RelCertifier
