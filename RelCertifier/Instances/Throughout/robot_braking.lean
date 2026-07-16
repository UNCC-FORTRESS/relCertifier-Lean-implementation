/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRobotBraking
open DL Parse

def vsRobotBraking : List String := ["v"]
def dummyRobotBraking : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRobotBraking (l : ℕ) : Parse.PMode := robot_braking_IR.L.modes.getD l dummyRobotBraking
def mRRobotBraking (q : ℕ) : Parse.PMode := robot_braking_IR.R.modes.getD q dummyRobotBraking
def fRowRobotBraking (l q : ℕ) : ModeFlagsE :=
  ((robot_braking_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRobotBraking (l : ℕ) : SearchGraph (Var 1) :=
  realGraphOf vsRobotBraking 1 robot_braking_IR (mLRobotBraking l)
    ((robot_braking_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((robot_braking_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => robot_braking_coverNC.pruned.contains (a, b))

noncomputable def gsRobotBraking_0 : List (Term (Var 1)) :=
  hostComps vsRobotBraking 1 (((robot_braking_IR.invariants.find? (fun r => r.1 == "CRUISE")).getD ("", Parse.PForm.tt)).2)

theorem GWRobotBraking0_modes_eq : (GWRobotBraking 0).modes =
    [realModeOf vsRobotBraking 1 (mLRobotBraking 0) ((1 : ℚ) / 1) (fRowRobotBraking 0 0) (mRRobotBraking 0),
     realModeOf vsRobotBraking 1 (mLRobotBraking 0) ((1 : ℚ) / 1) (fRowRobotBraking 0 1) (mRRobotBraking 1),
     realModeOf vsRobotBraking 1 (mLRobotBraking 0) ((1 : ℚ) / 1) (fRowRobotBraking 0 2) (mRRobotBraking 2)] := rfl

theorem certRobotBraking_0 (hr_0_0 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 0))) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 0)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_0 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 0)) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 0)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 1))) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 1)) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRobotBraking_0.length),     z3solve (flowQuery ⟨gsRobotBraking_0[i],       hostDyn vsRobotBraking 1 Side.L (mLRobotBraking 0), hostDyn vsRobotBraking 1 Side.R (mRRobotBraking 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 2))) (gsRobotBraking_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRobotBraking_0[i],       hostDyn vsRobotBraking 1 Side.L (mLRobotBraking 0), hostDyn vsRobotBraking 1 Side.R (mRRobotBraking 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 2))) (gsRobotBraking_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRobotBraking_0[i],       hostDyn vsRobotBraking 1 Side.L (mLRobotBraking 0), hostDyn vsRobotBraking 1 Side.R (mRRobotBraking 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 2))) (gsRobotBraking_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRobotBraking 0) gsRobotBraking_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GWRobotBraking0_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_region]; exact regionInvAll_of_unsat' gsRobotBraking_0 _ (fun g hg => z3_unsat_sound (hr_0_0 g hg)))
           | (rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsRobotBraking_0 _ (fun g hg => z3_unsat_sound (hq_0_0 g hg)))
           | exact absurd hflag (by simp [fRowRobotBraking, robot_braking_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_region]; exact regionInvAll_of_unsat' gsRobotBraking_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg)))
           | (rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsRobotBraking_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg)))
           | exact absurd hflag (by simp [fRowRobotBraking, robot_braking_coverNC])
       | 2, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRobotBraking_0 hs_0_2)
           | exact absurd hflag (by simp [fRowRobotBraking, robot_braking_coverNC])
       | q + 3, hm => simp at hm)
    | (intro m hm
       rw [GWRobotBraking0_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl | rfl <;> simp)

theorem robot_braking_throughout_CRUISE (hr_0_0 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 0))) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 0)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_0 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 0)) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 0)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 1))) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsRobotBraking_0, z3solve (Formula.and (Formula.and (hostGuard vsRobotBraking 1 Side.R (mRRobotBraking 1)) (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRobotBraking_0.length),     z3solve (flowQuery ⟨gsRobotBraking_0[i],       hostDyn vsRobotBraking 1 Side.L (mLRobotBraking 0), hostDyn vsRobotBraking 1 Side.R (mRRobotBraking 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 2))) (gsRobotBraking_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRobotBraking_0[i],       hostDyn vsRobotBraking 1 Side.L (mLRobotBraking 0), hostDyn vsRobotBraking 1 Side.R (mRRobotBraking 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 2))) (gsRobotBraking_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRobotBraking_0[i],       hostDyn vsRobotBraking 1 Side.L (mLRobotBraking 0), hostDyn vsRobotBraking 1 Side.R (mRRobotBraking 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRobotBraking 1 Side.L (mLRobotBraking 0)) (hostEvolve vsRobotBraking 1 Side.R (mRRobotBraking 2))) (gsRobotBraking_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRobotBraking_0 ν →
      Covered (GWRobotBraking 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRobotBraking 0) gsRobotBraking_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRobotBraking_0 hr_0_0 hq_0_0 hr_0_1 hq_0_1 hs_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

end ThroughoutRobotBraking
end RelCertifier
