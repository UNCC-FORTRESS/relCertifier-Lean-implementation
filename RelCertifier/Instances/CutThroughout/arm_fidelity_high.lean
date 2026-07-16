/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutArmFidelityHigh
open DL Parse

def vsArmFidelityHigh : List String := ["theta", "v"]
def dummyArmFidelityHigh : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLArmFidelityHigh (l : ℕ) : Parse.PMode := arm_fidelity_high_IR.L.modes.getD l dummyArmFidelityHigh
def mRArmFidelityHigh (q : ℕ) : Parse.PMode := arm_fidelity_high_IR.R.modes.getD q dummyArmFidelityHigh
def fRowArmFidelityHigh (l q : ℕ) : ModeFlagsE :=
  ((arm_fidelity_high_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWArmFidelityHigh (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsArmFidelityHigh 2 arm_fidelity_high_IR (mLArmFidelityHigh l)
    ((arm_fidelity_high_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((arm_fidelity_high_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => arm_fidelity_high_cover.pruned.contains (a, b))

theorem hsomeArmFidelityHigh_0 :
    (Run.lowerF vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmFidelityHigh, arm_fidelity_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeArmFidelityHigh_1 :
    (Run.lowerF vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmFidelityHigh, arm_fidelity_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeArmFidelityHigh_2 :
    (Run.lowerF vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmFidelityHigh, arm_fidelity_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeArmFidelityHigh_3 :
    (Run.lowerF vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3).guard : Option (IForm 2)).isSome = true := by
  simp [mRArmFidelityHigh, arm_fidelity_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsArmFidelityHigh_0 : List (Term (Var 2)) :=
  hostComps vsArmFidelityHigh 2 (((arm_fidelity_high_IR.invariants.find? (fun r => r.1 == "Accelerate")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRArmFidelityHigh_0 : ℕ → List (CutAtomP 2)
  | 0 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")))]
  | 1 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")))]
  | 2 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")))]
  | 3 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")))]
  | _ => []
noncomputable def GdArmFidelityHigh_0 : ℕ → Formula (Var 2)
  | 0 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0)
  | 1 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)
  | 2 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)
  | 3 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)
  | _ => Formula.tt
def cutLArmFidelityHigh_0 : List (CutAtomP 2) := []

theorem GWArmFidelityHigh0_modes_eq : (GWArmFidelityHigh 0).modes =
    [realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 0) ((1 : ℚ) / 1) (fRowArmFidelityHigh 0 0) (mRArmFidelityHigh 0),
     realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 0) ((1 : ℚ) / 1) (fRowArmFidelityHigh 0 1) (mRArmFidelityHigh 1),
     realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 0) ((1 : ℚ) / 1) (fRowArmFidelityHigh 0 2) (mRArmFidelityHigh 2),
     realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 0) ((1 : ℚ) / 1) (fRowArmFidelityHigh 0 3) (mRArmFidelityHigh 3)] := rfl

theorem certArmFidelityHigh_0 (hs_0_0 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hs_0_3 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hr_0_3 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_3 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_3 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_3 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)⟩) = Verdict.unsat) :
    CoverCertMC (GWArmFidelityHigh 0) gsArmFidelityHigh_0 GdArmFidelityHigh_0 cutLArmFidelityHigh_0 cutRArmFidelityHigh_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact atomsIff_nil
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) ν
    | 3 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) ν
    | q + 4 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.0")) (by decide) hsomeArmFidelityHigh_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.35")) (by decide) hsomeArmFidelityHigh_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.5")) (by decide) hsomeArmFidelityHigh_2 ν hg
    | 3 =>
        intro a ha
        simp only [cutRArmFidelityHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.6")) (by decide) hsomeArmFidelityHigh_3 ν hg
    | q + 4 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hs_0_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmFidelityHigh_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmFidelityHigh_0 _ (fun g hg => z3_unsat_sound (hr_0_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmFidelityHigh_0 _ (fun g hg => z3_unsat_sound (hr_0_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmFidelityHigh_0 _ (fun g hg => z3_unsat_sound (hq_0_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmFidelityHigh_0 _ (fun g hg => z3_unsat_sound (hq_0_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdp_0_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdp_0_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdq_0_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_0 hdq_0_3
    | q + 4, hm => simp at hm
  · intro m hm
    rw [GWArmFidelityHigh0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp

theorem arm_fidelity_high_cut_throughout_Accelerate (hs_0_0 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 0)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 1)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 2)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hs_0_3 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hr_0_3 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_3 : ∀ g ∈ gsArmFidelityHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_3 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_3 : ∀ i (hi : i < gsArmFidelityHigh_0.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 0)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_0) (cutF (cutRArmFidelityHigh_0 3)))) (gsArmFidelityHigh_0.take i)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2, 3], ∀ ν, InvAllHolds gsArmFidelityHigh_0 ν → CutSat (cutRArmFidelityHigh_0 q0) ν →
      Covered (GWArmFidelityHigh 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWArmFidelityHigh 0) GdArmFidelityHigh_0 gsArmFidelityHigh_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcut
  have cert := certArmFidelityHigh_0 hs_0_0 hdp_0_0 hdq_0_0 hr_0_1 hdp_0_1 hdq_0_1 hr_0_2 hq_0_2 hdp_0_2 hdq_0_2 hs_0_3 hr_0_3 hq_0_3 hdp_0_3 hdq_0_3 hO2ArmFidelityHigh_0_0 hO2ArmFidelityHigh_1_0 hO2ArmFidelityHigh_2_0 hO2ArmFidelityHigh_3_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 6 _ (by decide) ν hν
      (fun a ha => absurd ha List.not_mem_nil) hcut

noncomputable def gsArmFidelityHigh_1 : List (Term (Var 2)) :=
  hostComps vsArmFidelityHigh 2 (((arm_fidelity_high_IR.invariants.find? (fun r => r.1 == "Brake")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRArmFidelityHigh_1 : ℕ → List (CutAtomP 2)
  | 0 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")))]
  | 1 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")))]
  | 2 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")))]
  | 3 => [(hostAtomF vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")), hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")))]
  | _ => []
noncomputable def GdArmFidelityHigh_1 : ℕ → Formula (Var 2)
  | 0 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0)
  | 1 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)
  | 2 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)
  | 3 => hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)
  | _ => Formula.tt
def cutLArmFidelityHigh_1 : List (CutAtomP 2) := []

theorem GWArmFidelityHigh1_modes_eq : (GWArmFidelityHigh 1).modes =
    [realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 1) ((1 : ℚ) / 1) (fRowArmFidelityHigh 1 0) (mRArmFidelityHigh 0),
     realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 1) ((1 : ℚ) / 1) (fRowArmFidelityHigh 1 1) (mRArmFidelityHigh 1),
     realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 1) ((1 : ℚ) / 1) (fRowArmFidelityHigh 1 2) (mRArmFidelityHigh 2),
     realModeOf vsArmFidelityHigh 2 (mLArmFidelityHigh 1) ((1 : ℚ) / 1) (fRowArmFidelityHigh 1 3) (mRArmFidelityHigh 3)] := rfl

theorem certArmFidelityHigh_1 (hs_1_0 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hs_1_3 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hr_1_3 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_3 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_3 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_3 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)⟩) = Verdict.unsat) :
    CoverCertMC (GWArmFidelityHigh 1) gsArmFidelityHigh_1 GdArmFidelityHigh_1 cutLArmFidelityHigh_1 cutRArmFidelityHigh_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact atomsIff_nil
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) ν
    | 3 =>
        intro a ha ν
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsArmFidelityHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) ν
    | q + 4 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2ArmFidelityHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsArmFidelityHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2ArmFidelityHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.0")) (by decide) hsomeArmFidelityHigh_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.35")) (by decide) hsomeArmFidelityHigh_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.5")) (by decide) hsomeArmFidelityHigh_2 ν hg
    | 3 =>
        intro a ha
        simp only [cutRArmFidelityHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.6")) (by decide) hsomeArmFidelityHigh_3 ν hg
    | q + 4 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hs_1_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmFidelityHigh_1 _ (fun g hg => z3_unsat_sound (hr_1_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmFidelityHigh_1 _ (fun g hg => z3_unsat_sound (hr_1_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityHigh, arm_fidelity_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmFidelityHigh_1 _ (fun g hg => z3_unsat_sound (hq_1_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmFidelityHigh_1 _ (fun g hg => z3_unsat_sound (hq_1_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdp_1_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdp_1_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdq_1_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityHigh_1 hdq_1_3
    | q + 4, hm => simp at hm
  · intro m hm
    rw [GWArmFidelityHigh1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp

theorem arm_fidelity_high_cut_throughout_Brake (hs_1_0 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 0)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 1)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 2)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hs_1_3 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       hostDyn vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hr_1_3 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_3 : ∀ g ∈ gsArmFidelityHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)) (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_3 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (hostGuard vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_3 : ∀ i (hi : i < gsArmFidelityHigh_1.length),     z3solve (flowQuery ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityHigh_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityHigh 2 Side.L (mLArmFidelityHigh 1)) (hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3))) (Formula.and (cutF cutLArmFidelityHigh_1) (cutF (cutRArmFidelityHigh_1 3)))) (gsArmFidelityHigh_1.take i)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 0)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 1)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 2)⟩) = Verdict.unsat) (hO2ArmFidelityHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsArmFidelityHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3), Term.const 1,       hostEvolve vsArmFidelityHigh 2 Side.R (mRArmFidelityHigh 3)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2, 3], ∀ ν, InvAllHolds gsArmFidelityHigh_1 ν → CutSat (cutRArmFidelityHigh_1 q0) ν →
      Covered (GWArmFidelityHigh 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWArmFidelityHigh 1) GdArmFidelityHigh_1 gsArmFidelityHigh_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcut
  have cert := certArmFidelityHigh_1 hs_1_0 hdp_1_0 hdq_1_0 hdp_1_1 hdq_1_1 hr_1_2 hq_1_2 hdp_1_2 hdq_1_2 hs_1_3 hr_1_3 hq_1_3 hdp_1_3 hdq_1_3 hO2ArmFidelityHigh_0_0 hO2ArmFidelityHigh_1_0 hO2ArmFidelityHigh_2_0 hO2ArmFidelityHigh_3_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 6 _ (by decide) ν hν
      (fun a ha => absurd ha List.not_mem_nil) hcut

end CutThroughoutArmFidelityHigh
end RelCertifier
