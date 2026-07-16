/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutStory3RolloverLadderRungA
open DL Parse

def vsStory3RolloverLadderRungA : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "e", "r", "phi_r", "omega_phi", "z", "y"]
def dummyStory3RolloverLadderRungA : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLStory3RolloverLadderRungA (l : ℕ) : Parse.PMode := story3_rollover_ladder_rung_a_IR.L.modes.getD l dummyStory3RolloverLadderRungA
def mRStory3RolloverLadderRungA (q : ℕ) : Parse.PMode := story3_rollover_ladder_rung_a_IR.R.modes.getD q dummyStory3RolloverLadderRungA
def fRowStory3RolloverLadderRungA (l q : ℕ) : ModeFlagsE :=
  ((story3_rollover_ladder_rung_a_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWStory3RolloverLadderRungA (l : ℕ) : SearchGraph (Var 12) :=
  realGraphOf vsStory3RolloverLadderRungA 12 story3_rollover_ladder_rung_a_IR (mLStory3RolloverLadderRungA l)
    ((story3_rollover_ladder_rung_a_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((story3_rollover_ladder_rung_a_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => story3_rollover_ladder_rung_a_cover.pruned.contains (a, b))

theorem hsomeStory3RolloverLadderRungA_0 :
    (Run.lowerF vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0).guard : Option (IForm 12)).isSome = true := by
  simp [mRStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeStory3RolloverLadderRungA_1 :
    (Run.lowerF vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1).guard : Option (IForm 12)).isSome = true := by
  simp [mRStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeStory3RolloverLadderRungA_2 :
    (Run.lowerF vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2).guard : Option (IForm 12)).isSome = true := by
  simp [mRStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsStory3RolloverLadderRungA_0 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverLadderRungA 12 (((story3_rollover_ladder_rung_a_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRStory3RolloverLadderRungA_0 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdStory3RolloverLadderRungA_0 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)
  | 1 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)
  | 2 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)
  | _ => Formula.tt
noncomputable def cutLStory3RolloverLadderRungA_0 : List (CutAtomP 12) := [(hostAtomF vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")))]

theorem GWStory3RolloverLadderRungA0_modes_eq : (GWStory3RolloverLadderRungA 0).modes =
    [realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 0) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 0 0) (mRStory3RolloverLadderRungA 0),
     realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 0) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 0 1) (mRStory3RolloverLadderRungA 1),
     realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 0) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 0 2) (mRStory3RolloverLadderRungA 2)] := rfl

theorem certStory3RolloverLadderRungA_0 (hs_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2LStory3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWStory3RolloverLadderRungA 0) gsStory3RolloverLadderRungA_0 GdStory3RolloverLadderRungA_0 cutLStory3RolloverLadderRungA_0 cutRStory3RolloverLadderRungA_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLStory3RolloverLadderRungA_0] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((27 : ℚ) / 20 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverLadderRungA_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((27 : ℚ) / 20 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverLadderRungA_0_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((27 : ℚ) / 20 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverLadderRungA_0_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeStory3RolloverLadderRungA_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeStory3RolloverLadderRungA_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeStory3RolloverLadderRungA_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeStory3RolloverLadderRungA_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeStory3RolloverLadderRungA_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeStory3RolloverLadderRungA_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverLadderRungA0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_ladder_rung_a_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 0)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 1)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_0[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_0) (cutF (cutRStory3RolloverLadderRungA_0 2)))) (gsStory3RolloverLadderRungA_0.take i)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2LStory3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory3RolloverLadderRungA_0 ν → CutSat cutLStory3RolloverLadderRungA_0 ν → CutSat (cutRStory3RolloverLadderRungA_0 q0) ν →
      Covered (GWStory3RolloverLadderRungA 0) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWStory3RolloverLadderRungA 0) GdStory3RolloverLadderRungA_0 gsStory3RolloverLadderRungA_0 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certStory3RolloverLadderRungA_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2Story3RolloverLadderRungA_0_0 hO2Story3RolloverLadderRungA_0_1 hO2Story3RolloverLadderRungA_1_0 hO2Story3RolloverLadderRungA_1_1 hO2Story3RolloverLadderRungA_2_0 hO2Story3RolloverLadderRungA_2_1 hO2LStory3RolloverLadderRungA_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsStory3RolloverLadderRungA_1 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverLadderRungA 12 (((story3_rollover_ladder_rung_a_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRStory3RolloverLadderRungA_1 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdStory3RolloverLadderRungA_1 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)
  | 1 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)
  | 2 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)
  | _ => Formula.tt
noncomputable def cutLStory3RolloverLadderRungA_1 : List (CutAtomP 12) := [(hostAtomF vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")))]

theorem GWStory3RolloverLadderRungA1_modes_eq : (GWStory3RolloverLadderRungA 1).modes =
    [realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 1) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 1 0) (mRStory3RolloverLadderRungA 0),
     realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 1) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 1 1) (mRStory3RolloverLadderRungA 1),
     realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 1) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 1 2) (mRStory3RolloverLadderRungA 2)] := rfl

theorem certStory3RolloverLadderRungA_1 (hdp_1_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2LStory3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWStory3RolloverLadderRungA 1) gsStory3RolloverLadderRungA_1 GdStory3RolloverLadderRungA_1 cutLStory3RolloverLadderRungA_1 cutRStory3RolloverLadderRungA_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLStory3RolloverLadderRungA_1] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((27 : ℚ) / 20 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverLadderRungA_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((27 : ℚ) / 20 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverLadderRungA_1_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeStory3RolloverLadderRungA_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeStory3RolloverLadderRungA_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeStory3RolloverLadderRungA_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeStory3RolloverLadderRungA_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeStory3RolloverLadderRungA_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeStory3RolloverLadderRungA_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverLadderRungA1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_ladder_rung_a_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 0)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 1)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_1[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_1) (cutF (cutRStory3RolloverLadderRungA_1 2)))) (gsStory3RolloverLadderRungA_1.take i)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2LStory3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory3RolloverLadderRungA_1 ν → CutSat cutLStory3RolloverLadderRungA_1 ν → CutSat (cutRStory3RolloverLadderRungA_1 q0) ν →
      Covered (GWStory3RolloverLadderRungA 1) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWStory3RolloverLadderRungA 1) GdStory3RolloverLadderRungA_1 gsStory3RolloverLadderRungA_1 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certStory3RolloverLadderRungA_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2Story3RolloverLadderRungA_0_0 hO2Story3RolloverLadderRungA_0_1 hO2Story3RolloverLadderRungA_1_0 hO2Story3RolloverLadderRungA_1_1 hO2Story3RolloverLadderRungA_2_0 hO2Story3RolloverLadderRungA_2_1 hO2LStory3RolloverLadderRungA_1_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsStory3RolloverLadderRungA_2 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverLadderRungA 12 (((story3_rollover_ladder_rung_a_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRStory3RolloverLadderRungA_2 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdStory3RolloverLadderRungA_2 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)
  | 1 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)
  | 2 => hostGuard vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)
  | _ => Formula.tt
noncomputable def cutLStory3RolloverLadderRungA_2 : List (CutAtomP 12) := [(hostAtomF vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")))]

theorem GWStory3RolloverLadderRungA2_modes_eq : (GWStory3RolloverLadderRungA 2).modes =
    [realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 2) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 2 0) (mRStory3RolloverLadderRungA 0),
     realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 2) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 2 1) (mRStory3RolloverLadderRungA 1),
     realModeOf vsStory3RolloverLadderRungA 12 (mLStory3RolloverLadderRungA 2) ((27 : ℚ) / 20) (fRowStory3RolloverLadderRungA 2 2) (mRStory3RolloverLadderRungA 2)] := rfl

theorem certStory3RolloverLadderRungA_2 (hdp_2_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2LStory3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWStory3RolloverLadderRungA 2) gsStory3RolloverLadderRungA_2 GdStory3RolloverLadderRungA_2 cutLStory3RolloverLadderRungA_2 cutRStory3RolloverLadderRungA_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLStory3RolloverLadderRungA_2] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsStory3RolloverLadderRungA) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLStory3RolloverLadderRungA_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((27 : ℚ) / 20 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LStory3RolloverLadderRungA_2_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((27 : ℚ) / 20 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLStory3RolloverLadderRungA_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsStory3RolloverLadderRungA) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2Story3RolloverLadderRungA_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeStory3RolloverLadderRungA_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeStory3RolloverLadderRungA_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeStory3RolloverLadderRungA_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeStory3RolloverLadderRungA_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRStory3RolloverLadderRungA_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeStory3RolloverLadderRungA_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeStory3RolloverLadderRungA_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungA, story3_rollover_ladder_rung_a_cover])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungA_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverLadderRungA2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_ladder_rung_a_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 0)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 1)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const (((27 : ℚ) / 20 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (hostGuard vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungA_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungA_2[i],       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)) (hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2))) (Formula.and (cutF cutLStory3RolloverLadderRungA_2) (cutF (cutRStory3RolloverLadderRungA_2 2)))) (gsStory3RolloverLadderRungA_2.take i)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 0)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 1)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2Story3RolloverLadderRungA_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.R (mRStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) (hO2LStory3RolloverLadderRungA_2_0 : z3solve (flowQuery ⟨hostAtomG vsStory3RolloverLadderRungA 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsStory3RolloverLadderRungA 12 Side.L (mLStory3RolloverLadderRungA 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsStory3RolloverLadderRungA_2 ν → CutSat cutLStory3RolloverLadderRungA_2 ν → CutSat (cutRStory3RolloverLadderRungA_2 q0) ν →
      Covered (GWStory3RolloverLadderRungA 2) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWStory3RolloverLadderRungA 2) GdStory3RolloverLadderRungA_2 gsStory3RolloverLadderRungA_2 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certStory3RolloverLadderRungA_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2Story3RolloverLadderRungA_0_0 hO2Story3RolloverLadderRungA_0_1 hO2Story3RolloverLadderRungA_1_0 hO2Story3RolloverLadderRungA_1_1 hO2Story3RolloverLadderRungA_2_0 hO2Story3RolloverLadderRungA_2_1 hO2LStory3RolloverLadderRungA_2_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutStory3RolloverLadderRungA
end RelCertifier
