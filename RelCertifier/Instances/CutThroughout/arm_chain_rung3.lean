/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutArmChainRung3
open DL Parse

def vsArmChainRung3 : List String := ["theta", "v"]
def dummyArmChainRung3 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLArmChainRung3 (l : ℕ) : Parse.PMode := arm_chain_rung3_IR.L.modes.getD l dummyArmChainRung3
def mRArmChainRung3 (q : ℕ) : Parse.PMode := arm_chain_rung3_IR.R.modes.getD q dummyArmChainRung3
def fRowArmChainRung3 (l q : ℕ) : ModeFlagsE :=
  ((arm_chain_rung3_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWArmChainRung3 (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsArmChainRung3 2 arm_chain_rung3_IR (mLArmChainRung3 l)
    ((arm_chain_rung3_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((arm_chain_rung3_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => arm_chain_rung3_cover.pruned.contains (a, b))

theorem hsomeArmChainRung3_0 :
    (Run.lowerF vsArmChainRung3 2 Side.R (mRArmChainRung3 0).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmChainRung3, arm_chain_rung3_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeArmChainRung3_1 :
    (Run.lowerF vsArmChainRung3 2 Side.R (mRArmChainRung3 1).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmChainRung3, arm_chain_rung3_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeArmChainRung3_2 :
    (Run.lowerF vsArmChainRung3 2 Side.R (mRArmChainRung3 2).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmChainRung3, arm_chain_rung3_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeArmChainRung3_3 :
    (Run.lowerF vsArmChainRung3 2 Side.R (mRArmChainRung3 3).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmChainRung3, arm_chain_rung3_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsArmChainRung3_0 : List (Term (Var 2)) :=
  hostComps vsArmChainRung3 2 (((arm_chain_rung3_IR.invariants.find? (fun r => r.1 == "Accelerate")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRArmChainRung3_0 : ℕ → List (CutAtomP 2)
  | 0 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")))]
  | 1 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")))]
  | 2 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")))]
  | 3 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")))]
  | _ => []
noncomputable def GdArmChainRung3_0 : ℕ → Formula (Var 2)
  | 0 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 0)
  | 1 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 1)
  | 2 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2)
  | 3 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3)
  | _ => Formula.tt
def cutLArmChainRung3_0 : List (CutAtomP 2) := []

theorem GWArmChainRung30_modes_eq : (GWArmChainRung3 0).modes =
    [realModeOf vsArmChainRung3 2 (mLArmChainRung3 0) ((1 : ℚ) / 1) (fRowArmChainRung3 0 0) (mRArmChainRung3 0),
     realModeOf vsArmChainRung3 2 (mLArmChainRung3 0) ((1 : ℚ) / 1) (fRowArmChainRung3 0 1) (mRArmChainRung3 1),
     realModeOf vsArmChainRung3 2 (mLArmChainRung3 0) ((1 : ℚ) / 1) (fRowArmChainRung3 0 2) (mRArmChainRung3 2),
     realModeOf vsArmChainRung3 2 (mLArmChainRung3 0) ((1 : ℚ) / 1) (fRowArmChainRung3 0 3) (mRArmChainRung3 3)] := rfl

theorem certArmChainRung3_0 (hs_0_0 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hs_0_3 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hr_0_3 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_3 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_3 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_3 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hO2ArmChainRung3_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0)⟩) = Verdict.unsat) (hO2ArmChainRung3_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1)⟩) = Verdict.unsat) (hO2ArmChainRung3_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)⟩) = Verdict.unsat) (hO2ArmChainRung3_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)⟩) = Verdict.unsat) :
    CoverCertMC (GWArmChainRung3 0) gsArmChainRung3_0 GdArmChainRung3_0 cutLArmChainRung3_0 cutRArmChainRung3_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact atomsIff_nil
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) ν
    | 3 =>
        intro a ha ν
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) ν
    | q + 4 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_3_0) hb
    | q + 4, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.0")) (by decide) hsomeArmChainRung3_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.35")) (by decide) hsomeArmChainRung3_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.5")) (by decide) hsomeArmChainRung3_2 ν hg
    | 3 =>
        intro a ha
        simp only [cutRArmChainRung3_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.6")) (by decide) hsomeArmChainRung3_3 ν hg
    | q + 4 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hs_0_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung3_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung3_0 _ (fun g hg => z3_unsat_sound (hr_0_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung3_0 _ (fun g hg => z3_unsat_sound (hr_0_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmChainRung3_0 _ (fun g hg => z3_unsat_sound (hq_0_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmChainRung3_0 _ (fun g hg => z3_unsat_sound (hq_0_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdp_0_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdp_0_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung30_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdq_0_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_0 hdq_0_3
    | q + 4, hm => simp at hm
  · intro m hm
    rw [GWArmChainRung30_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp

theorem arm_chain_rung3_cut_throughout_Accelerate (hs_0_0 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 0)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 1)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 2)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hs_0_3 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hr_0_3 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_3 : ∀ g ∈ gsArmChainRung3_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_3 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hdq_0_3 : ∀ i (hi : i < gsArmChainRung3_0.length),     z3solve (flowQuery ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 0)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_0) (cutF (cutRArmChainRung3_0 3)))) (gsArmChainRung3_0.take i)⟩) = Verdict.unsat) (hO2ArmChainRung3_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0)⟩) = Verdict.unsat) (hO2ArmChainRung3_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1)⟩) = Verdict.unsat) (hO2ArmChainRung3_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)⟩) = Verdict.unsat) (hO2ArmChainRung3_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2, 3], ∀ ν, InvAllHolds gsArmChainRung3_0 ν → CutSat (cutRArmChainRung3_0 q0) ν →
      Covered (GWArmChainRung3 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWArmChainRung3 0) GdArmChainRung3_0 gsArmChainRung3_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcut
  have cert := certArmChainRung3_0 hs_0_0 hdp_0_0 hdq_0_0 hr_0_1 hdp_0_1 hdq_0_1 hr_0_2 hq_0_2 hdp_0_2 hdq_0_2 hs_0_3 hr_0_3 hq_0_3 hdp_0_3 hdq_0_3 hO2ArmChainRung3_0_0 hO2ArmChainRung3_1_0 hO2ArmChainRung3_2_0 hO2ArmChainRung3_3_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 6 _ (by decide) ν hν
      (fun a ha => absurd ha List.not_mem_nil) hcut

noncomputable def gsArmChainRung3_1 : List (Term (Var 2)) :=
  hostComps vsArmChainRung3 2 (((arm_chain_rung3_IR.invariants.find? (fun r => r.1 == "Brake")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRArmChainRung3_1 : ℕ → List (CutAtomP 2)
  | 0 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")))]
  | 1 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")))]
  | 2 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")))]
  | 3 => [(hostAtomF vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")), hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")))]
  | _ => []
noncomputable def GdArmChainRung3_1 : ℕ → Formula (Var 2)
  | 0 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 0)
  | 1 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 1)
  | 2 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2)
  | 3 => hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3)
  | _ => Formula.tt
def cutLArmChainRung3_1 : List (CutAtomP 2) := []

theorem GWArmChainRung31_modes_eq : (GWArmChainRung3 1).modes =
    [realModeOf vsArmChainRung3 2 (mLArmChainRung3 1) ((1 : ℚ) / 1) (fRowArmChainRung3 1 0) (mRArmChainRung3 0),
     realModeOf vsArmChainRung3 2 (mLArmChainRung3 1) ((1 : ℚ) / 1) (fRowArmChainRung3 1 1) (mRArmChainRung3 1),
     realModeOf vsArmChainRung3 2 (mLArmChainRung3 1) ((1 : ℚ) / 1) (fRowArmChainRung3 1 2) (mRArmChainRung3 2),
     realModeOf vsArmChainRung3 2 (mLArmChainRung3 1) ((1 : ℚ) / 1) (fRowArmChainRung3 1 3) (mRArmChainRung3 3)] := rfl

theorem certArmChainRung3_1 (hs_1_0 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hs_1_3 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hr_1_3 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_3 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_3 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_3 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hO2ArmChainRung3_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0)⟩) = Verdict.unsat) (hO2ArmChainRung3_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1)⟩) = Verdict.unsat) (hO2ArmChainRung3_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)⟩) = Verdict.unsat) (hO2ArmChainRung3_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)⟩) = Verdict.unsat) :
    CoverCertMC (GWArmChainRung3 1) gsArmChainRung3_1 GdArmChainRung3_1 cutLArmChainRung3_1 cutRArmChainRung3_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact atomsIff_nil
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) ν
    | 3 =>
        intro a ha ν
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmChainRung3) (side := Side.R) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) ν
    | q + 4 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmChainRung3_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmChainRung3) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmChainRung3_3_0) hb
    | q + 4, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.0")) (by decide) hsomeArmChainRung3_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.35")) (by decide) hsomeArmChainRung3_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.5")) (by decide) hsomeArmChainRung3_2 ν hg
    | 3 =>
        intro a ha
        simp only [cutRArmChainRung3_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.6")) (by decide) hsomeArmChainRung3_3 ν hg
    | q + 4 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hs_1_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung3_1 _ (fun g hg => z3_unsat_sound (hr_1_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung3_1 _ (fun g hg => z3_unsat_sound (hr_1_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung3, arm_chain_rung3_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmChainRung3_1 _ (fun g hg => z3_unsat_sound (hq_1_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmChainRung3_1 _ (fun g hg => z3_unsat_sound (hq_1_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdp_1_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdp_1_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung31_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdq_1_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung3_1 hdq_1_3
    | q + 4, hm => simp at hm
  · intro m hm
    rw [GWArmChainRung31_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp

theorem arm_chain_rung3_cut_throughout_Brake (hs_1_0 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 0)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 1)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 2)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 2)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hs_1_3 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       hostDyn vsArmChainRung3 2 Side.L (mLArmChainRung3 1), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hr_1_3 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_3 : ∀ g ∈ gsArmChainRung3_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung3 2 Side.R (mRArmChainRung3 3)) (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_3 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (hostGuard vsArmChainRung3 2 Side.L (mLArmChainRung3 1))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hdq_1_3 : ∀ i (hi : i < gsArmChainRung3_1.length),     z3solve (flowQuery ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung3_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung3 2 Side.L (mLArmChainRung3 1)) (hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3))) (Formula.and (cutF cutLArmChainRung3_1) (cutF (cutRArmChainRung3_1 3)))) (gsArmChainRung3_1.take i)⟩) = Verdict.unsat) (hO2ArmChainRung3_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 0), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 0)⟩) = Verdict.unsat) (hO2ArmChainRung3_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 1), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 1)⟩) = Verdict.unsat) (hO2ArmChainRung3_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 2), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 2)⟩) = Verdict.unsat) (hO2ArmChainRung3_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmChainRung3 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmChainRung3 2 Side.R (mRArmChainRung3 3), Term.const 1,       hostEvolve vsArmChainRung3 2 Side.R (mRArmChainRung3 3)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2, 3], ∀ ν, InvAllHolds gsArmChainRung3_1 ν → CutSat (cutRArmChainRung3_1 q0) ν →
      Covered (GWArmChainRung3 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWArmChainRung3 1) GdArmChainRung3_1 gsArmChainRung3_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcut
  have cert := certArmChainRung3_1 hs_1_0 hdp_1_0 hdq_1_0 hdp_1_1 hdq_1_1 hr_1_2 hq_1_2 hdp_1_2 hdq_1_2 hs_1_3 hr_1_3 hq_1_3 hdp_1_3 hdq_1_3 hO2ArmChainRung3_0_0 hO2ArmChainRung3_1_0 hO2ArmChainRung3_2_0 hO2ArmChainRung3_3_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 6 _ (by decide) ν hν
      (fun a ha => absurd ha List.not_mem_nil) hcut

end CutThroughoutArmChainRung3
end RelCertifier
