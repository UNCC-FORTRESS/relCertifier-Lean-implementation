/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Soundness.CutCoverDischarge
import RelCertifier.Instances.BenchCovers.rover_attitude_cone_12dof
import RelCertifier.Instances.BenchIR.rover_attitude_cone_12dof

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace CutThroughoutRoverAttitudeCone12dof
open DL Parse

def vsRoverAttitudeCone12dof : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "y", "e_lat", "omega_y"]
def dummyRoverAttitudeCone12dof : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRoverAttitudeCone12dof (l : ℕ) : Parse.PMode := rover_attitude_cone_12dof_IR.L.modes.getD l dummyRoverAttitudeCone12dof
def mRRoverAttitudeCone12dof (q : ℕ) : Parse.PMode := rover_attitude_cone_12dof_IR.R.modes.getD q dummyRoverAttitudeCone12dof
def fRowRoverAttitudeCone12dof (l q : ℕ) : ModeFlagsE :=
  ((rover_attitude_cone_12dof_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false⟩)
noncomputable def GWRoverAttitudeCone12dof (l : ℕ) : SearchGraph (Var 12) :=
  realGraphOf vsRoverAttitudeCone12dof 12 rover_attitude_cone_12dof_IR (mLRoverAttitudeCone12dof l)
    ((rover_attitude_cone_12dof_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover_attitude_cone_12dof_cover.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover_attitude_cone_12dof_cover.pruned.contains (a, b))

theorem hsomeRoverAttitudeCone12dof_0 :
    (Run.lowerF vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0).guard : Option (IForm 12)).isSome = true := by
  simp [mRRoverAttitudeCone12dof, rover_attitude_cone_12dof_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverAttitudeCone12dof_1 :
    (Run.lowerF vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1).guard : Option (IForm 12)).isSome = true := by
  simp [mRRoverAttitudeCone12dof, rover_attitude_cone_12dof_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

theorem hsomeRoverAttitudeCone12dof_2 :
    (Run.lowerF vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2).guard : Option (IForm 12)).isSome = true := by
  simp [mRRoverAttitudeCone12dof, rover_attitude_cone_12dof_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat, List.findIdx?, List.findIdx?.go]
  decide

noncomputable def gsRoverAttitudeCone12dof_0 : List (Term (Var 12)) :=
  hostComps vsRoverAttitudeCone12dof 12 (((rover_attitude_cone_12dof_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverAttitudeCone12dof_0 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverAttitudeCone12dof_0 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)
  | 1 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)
  | 2 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)
  | _ => Formula.tt
noncomputable def cutLRoverAttitudeCone12dof_0 : List (CutAtomP 12) := [(hostAtomF vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")))]

theorem GWRoverAttitudeCone12dof0_modes_eq : (GWRoverAttitudeCone12dof 0).modes =
    [realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 0) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 0 0) (mRRoverAttitudeCone12dof 0),
     realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 0) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 0 1) (mRRoverAttitudeCone12dof 1),
     realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 0) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 0 2) (mRRoverAttitudeCone12dof 2)] := rfl

theorem certRoverAttitudeCone12dof_0 (hs_0_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2LRoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverAttitudeCone12dof 0) gsRoverAttitudeCone12dof_0 GdRoverAttitudeCone12dof_0 cutLRoverAttitudeCone12dof_0 cutRRoverAttitudeCone12dof_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverAttitudeCone12dof_0] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.L) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverAttitudeCone12dof_0_0) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverAttitudeCone12dof_0_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverAttitudeCone12dof_0_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_0] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverAttitudeCone12dof_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverAttitudeCone12dof_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverAttitudeCone12dof_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverAttitudeCone12dof_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_0] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverAttitudeCone12dof_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverAttitudeCone12dof_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hdp_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_0 hdq_0_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverAttitudeCone12dof0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_attitude_cone_12dof_cut_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 0)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 1)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdp_0_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hdq_0_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_0.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_0[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_0) (cutF (cutRRoverAttitudeCone12dof_0 2)))) (gsRoverAttitudeCone12dof_0.take i)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2LRoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.0")),       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverAttitudeCone12dof_0 ν → CutSat cutLRoverAttitudeCone12dof_0 ν → CutSat (cutRRoverAttitudeCone12dof_0 q0) ν →
      Covered (GWRoverAttitudeCone12dof 0) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverAttitudeCone12dof 0) GdRoverAttitudeCone12dof_0 gsRoverAttitudeCone12dof_0 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverAttitudeCone12dof_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1 hs_0_2 hdp_0_2 hdq_0_2 hO2RoverAttitudeCone12dof_0_0 hO2RoverAttitudeCone12dof_0_1 hO2RoverAttitudeCone12dof_1_0 hO2RoverAttitudeCone12dof_1_1 hO2RoverAttitudeCone12dof_2_0 hO2RoverAttitudeCone12dof_2_1 hO2LRoverAttitudeCone12dof_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverAttitudeCone12dof_1 : List (Term (Var 12)) :=
  hostComps vsRoverAttitudeCone12dof 12 (((rover_attitude_cone_12dof_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverAttitudeCone12dof_1 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverAttitudeCone12dof_1 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)
  | 1 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)
  | 2 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)
  | _ => Formula.tt
noncomputable def cutLRoverAttitudeCone12dof_1 : List (CutAtomP 12) := [(hostAtomF vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")))]

theorem GWRoverAttitudeCone12dof1_modes_eq : (GWRoverAttitudeCone12dof 1).modes =
    [realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 1) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 1 0) (mRRoverAttitudeCone12dof 0),
     realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 1) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 1 1) (mRRoverAttitudeCone12dof 1),
     realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 1) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 1 2) (mRRoverAttitudeCone12dof 2)] := rfl

theorem certRoverAttitudeCone12dof_1 (hdp_1_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2LRoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverAttitudeCone12dof 1) gsRoverAttitudeCone12dof_1 GdRoverAttitudeCone12dof_1 cutLRoverAttitudeCone12dof_1 cutRRoverAttitudeCone12dof_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverAttitudeCone12dof_1] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.L) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverAttitudeCone12dof_1_0) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverAttitudeCone12dof_1_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_1] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverAttitudeCone12dof_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverAttitudeCone12dof_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverAttitudeCone12dof_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverAttitudeCone12dof_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverAttitudeCone12dof_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverAttitudeCone12dof_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hdp_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_1 hdq_1_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverAttitudeCone12dof1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_attitude_cone_12dof_cut_throughout_MODER (hdp_1_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 0)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 1)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdp_1_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hdq_1_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_1.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_1[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_1) (cutF (cutRRoverAttitudeCone12dof_1 2)))) (gsRoverAttitudeCone12dof_1.take i)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2LRoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "0.6")),       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRoverAttitudeCone12dof_1 ν → CutSat cutLRoverAttitudeCone12dof_1 ν → CutSat (cutRRoverAttitudeCone12dof_1 q0) ν →
      Covered (GWRoverAttitudeCone12dof 1) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverAttitudeCone12dof 1) GdRoverAttitudeCone12dof_1 gsRoverAttitudeCone12dof_1 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverAttitudeCone12dof_1 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1 hs_1_2 hdp_1_2 hdq_1_2 hO2RoverAttitudeCone12dof_0_0 hO2RoverAttitudeCone12dof_0_1 hO2RoverAttitudeCone12dof_1_0 hO2RoverAttitudeCone12dof_1_1 hO2RoverAttitudeCone12dof_2_0 hO2RoverAttitudeCone12dof_2_1 hO2LRoverAttitudeCone12dof_1_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

noncomputable def gsRoverAttitudeCone12dof_2 : List (Term (Var 12)) :=
  hostComps vsRoverAttitudeCone12dof 12 (((rover_attitude_cone_12dof_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

noncomputable def cutRRoverAttitudeCone12dof_2 : ℕ → List (CutAtomP 12)
  | 0 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")))]
  | 1 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")))]
  | 2 => [(hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4"))), (hostAtomF vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")), hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")))]
  | _ => []
noncomputable def GdRoverAttitudeCone12dof_2 : ℕ → Formula (Var 12)
  | 0 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)
  | 1 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)
  | 2 => hostGuard vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)
  | _ => Formula.tt
noncomputable def cutLRoverAttitudeCone12dof_2 : List (CutAtomP 12) := [(hostAtomF vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")), hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")))]

theorem GWRoverAttitudeCone12dof2_modes_eq : (GWRoverAttitudeCone12dof 2).modes =
    [realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 2) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 2 0) (mRRoverAttitudeCone12dof 0),
     realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 2) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 2 1) (mRRoverAttitudeCone12dof 1),
     realModeOf vsRoverAttitudeCone12dof 12 (mLRoverAttitudeCone12dof 2) ((17 : ℚ) / 10) (fRowRoverAttitudeCone12dof 2 2) (mRRoverAttitudeCone12dof 2)] := rfl

theorem certRoverAttitudeCone12dof_2 (hdp_2_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2LRoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) :
    CoverCertMC (GWRoverAttitudeCone12dof 2) gsRoverAttitudeCone12dof_2 GdRoverAttitudeCone12dof_2 cutLRoverAttitudeCone12dof_2 cutRRoverAttitudeCone12dof_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha ν
    simp only [cutLRoverAttitudeCone12dof_2] at ha
    rw [List.mem_singleton] at ha
    subst ha
    exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.L) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
  · intro q
    match q with
    | 0 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) ν
    | 1 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) ν
    | 2 =>
        intro a ha ν
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) ν
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostAtom_iff (vars := vsRoverAttitudeCone12dof) (side := Side.R) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) ν
    | q + 3 =>
        intro a ha ν
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutLRoverAttitudeCone12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact atom_boxle_L_nonstrict _ _ _ (Term.const (((17 : ℚ) / 10 : ℚ) : ℝ)) _ _
          (fun i h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv]))
          (by intro x h; exact h.1) (z3_unsat_sound hO2LRoverAttitudeCone12dof_2_0) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_sys, realModeOf_dom]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (((17 : ℚ) / 10 : ℚ) : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPre]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.1.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        refine atomsStay_L_frozen_dyn _ _ _ ?_
        intro a ha i
        simp only [cutLRoverAttitudeCone12dof_2] at ha
        rw [List.mem_singleton] at ha
        subst ha
        exact fun h => absurd (hostAtomG_fv_side (resolvesTo_L vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Rv])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.0")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.3")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_0_1) hb
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "0.6")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.5")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_1_1) hb
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        simp only [realModeOf_dynSys, realModeOf_dynDomPost]
        intro a ha ν hb
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact atom_boxle_R_nonstrict _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "s")) (y := (.num "1.4")) (Or.inr rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_0) hb
        · rw [List.mem_singleton] at ha
          subst ha
          exact atom_boxle_R_superlevel _ _ _ (1 : ℝ) (by norm_num) _ _
            (fun i h => absurd (hostAtomG_fv_side (resolvesTo_R vsRoverAttitudeCone12dof) (x := (.var "v")) (y := (.num "0.65")) (Or.inl rfl) (by first | decide | simp [Parse.PExpr.namesFree]) (by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [Lv]))
            (by intro x h; exact h.2) (z3_unsat_sound hO2RoverAttitudeCone12dof_2_1) hb
    | q + 3, hm => simp at hm
  · intro q ν hg
    match q with
    | 0 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.0")) (by decide) hsomeRoverAttitudeCone12dof_0 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.3")) (by decide) hsomeRoverAttitudeCone12dof_0 ν hg
    | 1 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "0.6")) (by decide) hsomeRoverAttitudeCone12dof_1 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.5")) (by decide) hsomeRoverAttitudeCone12dof_1 ν hg
    | 2 =>
        intro a ha
        simp only [cutRRoverAttitudeCone12dof_2] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hostGuard_cutAtoms_sat (a := .cmp ">=" (.var "s") (.num "1.4")) (by decide) hsomeRoverAttitudeCone12dof_2 ν hg
        · rw [List.mem_singleton] at ha
          subst ha
          exact hostGuard_cutAtoms_sat (a := .cmp "<=" (.var "v") (.num "0.65")) (by decide) hsomeRoverAttitudeCone12dof_2 ν hg
    | q + 3 =>
        intro a ha
        exact absurd ha List.not_mem_nil
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverAttitudeCone12dof, rover_attitude_cone_12dof_cover])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_2 hdp_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverAttitudeCone12dof_2 hdq_2_2
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRoverAttitudeCone12dof2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem rover_attitude_cone_12dof_cut_throughout_FLAT (hdp_2_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 0)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 1)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const (((17 : ℚ) / 10 : ℚ) : ℝ),       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdp_2_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (hostGuard vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hdq_2_2 : ∀ i (hi : i < gsRoverAttitudeCone12dof_2.length),     z3solve (flowQuery ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverAttitudeCone12dof_2[i],       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)) (hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2))) (Formula.and (cutF cutLRoverAttitudeCone12dof_2) (cutF (cutRRoverAttitudeCone12dof_2 2)))) (gsRoverAttitudeCone12dof_2.take i)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.0")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_0_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.3")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 0)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "0.6")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_1_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.5")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 1)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp ">=" (.var "s") (.num "1.4")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2RoverAttitudeCone12dof_2_1 : z3solve (flowQuerySuperlevel ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.R (.cmp "<=" (.var "v") (.num "0.65")),       (fun _ => Term.const 0), hostDyn vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.R (mRRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) (hO2LRoverAttitudeCone12dof_2_0 : z3solve (flowQuery ⟨hostAtomG vsRoverAttitudeCone12dof 12 Side.L (.cmp ">=" (.var "s") (.num "1.4")),       hostDyn vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2), (fun _ => Term.const 0), Term.const 1,       hostEvolve vsRoverAttitudeCone12dof 12 Side.L (mLRoverAttitudeCone12dof 2)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [1, 2], ∀ ν, InvAllHolds gsRoverAttitudeCone12dof_2 ν → CutSat cutLRoverAttitudeCone12dof_2 ν → CutSat (cutRRoverAttitudeCone12dof_2 q0) ν →
      Covered (GWRoverAttitudeCone12dof 2) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughoutG (GWRoverAttitudeCone12dof 2) GdRoverAttitudeCone12dof_2 gsRoverAttitudeCone12dof_2 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν hcutL hcut
  have cert := certRoverAttitudeCone12dof_2 hdp_2_0 hdq_2_0 hdp_2_1 hdq_2_1 hs_2_2 hdp_2_2 hdq_2_2 hO2RoverAttitudeCone12dof_0_0 hO2RoverAttitudeCone12dof_0_1 hO2RoverAttitudeCone12dof_1_0 hO2RoverAttitudeCone12dof_1_1 hO2RoverAttitudeCone12dof_2_0 hO2RoverAttitudeCone12dof_2_1 hO2LRoverAttitudeCone12dof_2_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi_cut _ _ _ _ _ cert 9 _ (by decide) ν hν
      hcutL hcut

end CutThroughoutRoverAttitudeCone12dof
end RelCertifier
