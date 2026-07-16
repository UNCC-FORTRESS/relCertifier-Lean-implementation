/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutPlantFanHigh
open DL Parse

def vsPlantFanHigh : List String := ["theta", "v"]
def dummyPlantFanHigh : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLPlantFanHigh (l : ℕ) : Parse.PMode := plant_fan_high_IR.L.modes.getD l dummyPlantFanHigh
def mRPlantFanHigh (q : ℕ) : Parse.PMode := plant_fan_high_IR.R.modes.getD q dummyPlantFanHigh
def fRowPlantFanHigh (l q : ℕ) : ModeFlagsE :=
  ((plant_fan_high_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWPlantFanHigh (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsPlantFanHigh 2 plant_fan_high_IR (mLPlantFanHigh l)
    ((plant_fan_high_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((plant_fan_high_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => plant_fan_high_cover.pruned.contains (a, b))

theorem hsomePlantFanHigh_0 :
    (Run.lowerF vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0).guard : Option (IForm 2)).isSome = true := by
  simp [mRPlantFanHigh, plant_fan_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomePlantFanHigh_1 :
    (Run.lowerF vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1).guard : Option (IForm 2)).isSome = true := by
  simp [mRPlantFanHigh, plant_fan_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomePlantFanHigh_2 :
    (Run.lowerF vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2).guard : Option (IForm 2)).isSome = true := by
  simp [mRPlantFanHigh, plant_fan_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomePlantFanHigh_3 :
    (Run.lowerF vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3).guard : Option (IForm 2)).isSome = true := by
  simp [mRPlantFanHigh, plant_fan_high_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsPlantFanHigh_0 : List (Term (Var 2)) :=
  hostComps vsPlantFanHigh 2 (((plant_fan_high_IR.invariants.find? (fun r => r.1 == "Accelerate")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRPlantFanHigh_0 : ℕ → List (CutAtomP 2)
  | 0 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")))]
  | 1 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")))]
  | 2 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")))]
  | 3 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")))]
  | _ => []
noncomputable def GdPlantFanHigh_0 : ℕ → Formula (Var 2)
  | 0 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0)
  | 1 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)
  | 2 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)
  | 3 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)
  | _ => Formula.tt
def cutLPlantFanHigh_0 : List (CutAtomP 2) := []

theorem GWPlantFanHigh0_modes_eq : (GWPlantFanHigh 0).modes =
    [realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 0) ((1 : ℚ) / 1) (fRowPlantFanHigh 0 0) (mRPlantFanHigh 0),
     realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 0) ((1 : ℚ) / 1) (fRowPlantFanHigh 0 1) (mRPlantFanHigh 1),
     realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 0) ((1 : ℚ) / 1) (fRowPlantFanHigh 0 2) (mRPlantFanHigh 2),
     realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 0) ((1 : ℚ) / 1) (fRowPlantFanHigh 0 3) (mRPlantFanHigh 3)] := rfl

theorem certPlantFanHigh_0 (hs_0_0 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hs_0_3 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hr_0_3 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_3 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_3 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_3 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hO2PlantFanHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0)⟩) = Verdict.unsat) (hO2PlantFanHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)⟩) = Verdict.unsat) (hO2PlantFanHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)⟩) = Verdict.unsat) (hO2PlantFanHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)⟩) = Verdict.unsat) :
    CoverCertMC (GWPlantFanHigh 0) gsPlantFanHigh_0 GdPlantFanHigh_0 cutLPlantFanHigh_0 cutRPlantFanHigh_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact atomsIff_nil
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) ν
    | 3 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) ν
    | q + 4 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.0")) (by decide) hsomePlantFanHigh_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.35")) (by decide) hsomePlantFanHigh_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.5")) (by decide) hsomePlantFanHigh_2 ν hg
    | 3 =>
        intro a ha
        simp only [cutRPlantFanHigh_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.6")) (by decide) hsomePlantFanHigh_3 ν hg
    | q + 4 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hs_0_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanHigh_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanHigh_0 _ (fun g hg => z3_unsat_sound (hr_0_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanHigh_0 _ (fun g hg => z3_unsat_sound (hr_0_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanHigh_0 _ (fun g hg => z3_unsat_sound (hq_0_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanHigh_0 _ (fun g hg => z3_unsat_sound (hq_0_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdp_0_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdp_0_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdq_0_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_0 hdq_0_3
    | q + 4, hm => simp at hm
  · intro m hm
    rw [GWPlantFanHigh0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp

theorem plant_fan_high_cut_throughout_Accelerate (hs_0_0 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 0)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 1)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 2)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hs_0_3 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hr_0_3 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_3 : ∀ g ∈ gsPlantFanHigh_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_3 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hdq_0_3 : ∀ i (hi : i < gsPlantFanHigh_0.length),     z3solve (flowQuery ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 0)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_0) (cutF (cutRPlantFanHigh_0 3)))) (gsPlantFanHigh_0.take i)⟩) = Verdict.unsat) (hO2PlantFanHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0)⟩) = Verdict.unsat) (hO2PlantFanHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)⟩) = Verdict.unsat) (hO2PlantFanHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)⟩) = Verdict.unsat) (hO2PlantFanHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2, 3], ∀ ν, InvAllHolds gsPlantFanHigh_0 ν → CutSat (cutRPlantFanHigh_0 q0) ν →
      Covered (GWPlantFanHigh 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWPlantFanHigh 0) GdPlantFanHigh_0 gsPlantFanHigh_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcut
  have cert := certPlantFanHigh_0 hs_0_0 hdp_0_0 hdq_0_0 hr_0_1 hdp_0_1 hdq_0_1 hr_0_2 hq_0_2 hdp_0_2 hdq_0_2 hs_0_3 hr_0_3 hq_0_3 hdp_0_3 hdq_0_3 hO2PlantFanHigh_0_0 hO2PlantFanHigh_1_0 hO2PlantFanHigh_2_0 hO2PlantFanHigh_3_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 6 _ (by decide) ν hν
      (fun a ha => absurd ha List.not_mem_nil) hcut

noncomputable def gsPlantFanHigh_1 : List (Term (Var 2)) :=
  hostComps vsPlantFanHigh 2 (((plant_fan_high_IR.invariants.find? (fun r => r.1 == "Brake")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRPlantFanHigh_1 : ℕ → List (CutAtomP 2)
  | 0 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")))]
  | 1 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")))]
  | 2 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")))]
  | 3 => [(hostAtomF vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")), hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")))]
  | _ => []
noncomputable def GdPlantFanHigh_1 : ℕ → Formula (Var 2)
  | 0 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0)
  | 1 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)
  | 2 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)
  | 3 => hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)
  | _ => Formula.tt
def cutLPlantFanHigh_1 : List (CutAtomP 2) := []

theorem GWPlantFanHigh1_modes_eq : (GWPlantFanHigh 1).modes =
    [realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 1) ((1 : ℚ) / 1) (fRowPlantFanHigh 1 0) (mRPlantFanHigh 0),
     realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 1) ((1 : ℚ) / 1) (fRowPlantFanHigh 1 1) (mRPlantFanHigh 1),
     realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 1) ((1 : ℚ) / 1) (fRowPlantFanHigh 1 2) (mRPlantFanHigh 2),
     realModeOf vsPlantFanHigh 2 (mLPlantFanHigh 1) ((1 : ℚ) / 1) (fRowPlantFanHigh 1 3) (mRPlantFanHigh 3)] := rfl

theorem certPlantFanHigh_1 (hs_1_0 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hs_1_3 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hr_1_3 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_3 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_3 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_3 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hO2PlantFanHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0)⟩) = Verdict.unsat) (hO2PlantFanHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)⟩) = Verdict.unsat) (hO2PlantFanHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)⟩) = Verdict.unsat) (hO2PlantFanHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)⟩) = Verdict.unsat) :
    CoverCertMC (GWPlantFanHigh 1) gsPlantFanHigh_1 GdPlantFanHigh_1 cutLPlantFanHigh_1 cutRPlantFanHigh_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact atomsIff_nil
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) ν
    | 3 =>
        intro a ha ν
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostAtom_iff (vars := vsPlantFanHigh) (side := Side.R) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) ν
    | q + 4 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (((1 : ℚ) / 1 : ℚ) : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.1.2) (z3_unsat_sound hO2PlantFanHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    exact atomsStay_nil _ _
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.35")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_strict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.5")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_2_0) hb
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsPlantFanHigh) (x := (.var "theta")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
          (by intro x h; exact h.2) (z3_unsat_sound hO2PlantFanHigh_3_0) hb
    | q + 4, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.0")) (by decide) hsomePlantFanHigh_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.35")) (by decide) hsomePlantFanHigh_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.5")) (by decide) hsomePlantFanHigh_2 ν hg
    | 3 =>
        intro a ha
        simp only [cutRPlantFanHigh_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "theta") (.num "0.6")) (by decide) hsomePlantFanHigh_3 ν hg
    | q + 4 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hs_1_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanHigh_1 _ (fun g hg => z3_unsat_sound (hr_1_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanHigh_1 _ (fun g hg => z3_unsat_sound (hr_1_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanHigh, plant_fan_high_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanHigh_1 _ (fun g hg => z3_unsat_sound (hq_1_2 g hg))
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanHigh_1 _ (fun g hg => z3_unsat_sound (hq_1_3 g hg))
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdp_1_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdp_1_3
    | q + 4, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdq_1_2
    | 3, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanHigh_1 hdq_1_3
    | q + 4, hm => simp at hm
  · intro m hm
    rw [GWPlantFanHigh1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp

theorem plant_fan_high_cut_throughout_Brake (hs_1_0 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 0)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 1)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 2)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hs_1_3 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       hostDyn vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hr_1_3 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_3 : ∀ g ∈ gsPlantFanHigh_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)) (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_3 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (hostGuard vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hdq_1_3 : ∀ i (hi : i < gsPlantFanHigh_1.length),     z3solve (flowQuery ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanHigh_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanHigh 2 Side.L (mLPlantFanHigh 1)) (hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3))) (Formula.and (cutF cutLPlantFanHigh_1) (cutF (cutRPlantFanHigh_1 3)))) (gsPlantFanHigh_1.take i)⟩) = Verdict.unsat) (hO2PlantFanHigh_0_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 0)⟩) = Verdict.unsat) (hO2PlantFanHigh_1_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.35")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 1)⟩) = Verdict.unsat) (hO2PlantFanHigh_2_0 : z3solve (flowQueryStrict ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 2)⟩) = Verdict.unsat) (hO2PlantFanHigh_3_0 : z3solve (flowQuery ⟨hostAtomG vsPlantFanHigh 2 Side.R (.cmp ">=" (.var "theta") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3), Term.const 1,       hostEvolve vsPlantFanHigh 2 Side.R (mRPlantFanHigh 3)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2, 3], ∀ ν, InvAllHolds gsPlantFanHigh_1 ν → CutSat (cutRPlantFanHigh_1 q0) ν →
      Covered (GWPlantFanHigh 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWPlantFanHigh 1) GdPlantFanHigh_1 gsPlantFanHigh_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcut
  have cert := certPlantFanHigh_1 hs_1_0 hdp_1_0 hdq_1_0 hdp_1_1 hdq_1_1 hr_1_2 hq_1_2 hdp_1_2 hdq_1_2 hs_1_3 hr_1_3 hq_1_3 hdp_1_3 hdq_1_3 hO2PlantFanHigh_0_0 hO2PlantFanHigh_1_0 hO2PlantFanHigh_2_0 hO2PlantFanHigh_3_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 6 _ (by decide) ν hν
      (fun a ha => absurd ha List.not_mem_nil) hcut

end CutThroughoutPlantFanHigh
end RelCertifier
