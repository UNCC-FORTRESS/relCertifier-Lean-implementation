/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRover3tierM1
open DL Parse

def vsRover3tierM1 : List String := ["v", "s"]
def dummyRover3tierM1 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRover3tierM1 (l : ℕ) : Parse.PMode := rover3tier_M1_IR.L.modes.getD l dummyRover3tierM1
def mRRover3tierM1 (q : ℕ) : Parse.PMode := rover3tier_M1_IR.R.modes.getD q dummyRover3tierM1
def fRowRover3tierM1 (l q : ℕ) : ModeFlagsE :=
  ((rover3tier_M1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRover3tierM1 (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsRover3tierM1 2 rover3tier_M1_IR (mLRover3tierM1 l)
    ((rover3tier_M1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover3tier_M1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover3tier_M1_coverNC.pruned.contains (a, b))

noncomputable def gsRover3tierM1_0 : List (Term (Var 2)) :=
  hostComps vsRover3tierM1 2 (((rover3tier_M1_IR.invariants.find? (fun r => r.1 == "ACCEL")).getD ("", Parse.PForm.tt)).2)

theorem GWRover3tierM10_modes_eq : (GWRover3tierM1 0).modes =
    [realModeOf vsRover3tierM1 2 (mLRover3tierM1 0) ((1 : ℚ) / 1) (fRowRover3tierM1 0 0) (mRRover3tierM1 0),
     realModeOf vsRover3tierM1 2 (mLRover3tierM1 0) ((1 : ℚ) / 1) (fRowRover3tierM1 0 1) (mRRover3tierM1 1)] := rfl

theorem certRover3tierM1_0 (hs_0_0 : ∀ i (hi : i < gsRover3tierM1_0.length),     z3solve (flowQuery ⟨gsRover3tierM1_0[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 0), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierM1_0[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 0), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierM1_0[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 0), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsRover3tierM1_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsRover3tierM1_0, z3solve (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1)) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWRover3tierM1 0) gsRover3tierM1_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GWRover3tierM10_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierM1_0 hs_0_0)
           | exact absurd hflag (by simp [fRowRover3tierM1, rover3tier_M1_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_region]; exact regionInvAll_of_unsat' gsRover3tierM1_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg)))
           | (rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsRover3tierM1_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg)))
           | exact absurd hflag (by simp [fRowRover3tierM1, rover3tier_M1_coverNC])
       | q + 2, hm => simp at hm)
    | (intro m hm
       rw [GWRover3tierM10_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl <;> simp)

theorem rover3tier_M1_throughout_ACCEL (hs_0_0 : ∀ i (hi : i < gsRover3tierM1_0.length),     z3solve (flowQuery ⟨gsRover3tierM1_0[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 0), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierM1_0[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 0), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierM1_0[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 0), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsRover3tierM1_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsRover3tierM1_0, z3solve (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1)) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 0)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsRover3tierM1_0 ν →
      Covered (GWRover3tierM1 0) ⟨q0, 4, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRover3tierM1 0) gsRover3tierM1_0 ⟨q0, 4, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRover3tierM1_0 hs_0_0 hr_0_1 hq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 13 _ (by decide) ν hν

noncomputable def gsRover3tierM1_1 : List (Term (Var 2)) :=
  hostComps vsRover3tierM1 2 (((rover3tier_M1_IR.invariants.find? (fun r => r.1 == "COAST")).getD ("", Parse.PForm.tt)).2)

theorem GWRover3tierM11_modes_eq : (GWRover3tierM1 1).modes =
    [realModeOf vsRover3tierM1 2 (mLRover3tierM1 1) ((1 : ℚ) / 1) (fRowRover3tierM1 1 0) (mRRover3tierM1 0),
     realModeOf vsRover3tierM1 2 (mLRover3tierM1 1) ((1 : ℚ) / 1) (fRowRover3tierM1 1 1) (mRRover3tierM1 1)] := rfl

theorem certRover3tierM1_1 (hs_1_0 : ∀ i (hi : i < gsRover3tierM1_1.length),     z3solve (flowQuery ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRover3tierM1_1.length),     z3solve (flowQuery ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsRover3tierM1_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsRover3tierM1_1, z3solve (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1)) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWRover3tierM1 1) gsRover3tierM1_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GWRover3tierM11_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierM1_1 hs_1_0)
           | exact absurd hflag (by simp [fRowRover3tierM1, rover3tier_M1_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierM1_1 hs_1_1)
           | (rw [realModeOf_region]; exact regionInvAll_of_unsat' gsRover3tierM1_1 _ (fun g hg => z3_unsat_sound (hr_1_1 g hg)))
           | (rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsRover3tierM1_1 _ (fun g hg => z3_unsat_sound (hq_1_1 g hg)))
           | exact absurd hflag (by simp [fRowRover3tierM1, rover3tier_M1_coverNC])
       | q + 2, hm => simp at hm)
    | (intro m hm
       rw [GWRover3tierM11_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl <;> simp)

theorem rover3tier_M1_throughout_COAST (hs_1_0 : ∀ i (hi : i < gsRover3tierM1_1.length),     z3solve (flowQuery ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 0))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRover3tierM1_1.length),     z3solve (flowQuery ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierM1_1[i],       hostDyn vsRover3tierM1 2 Side.L (mLRover3tierM1 1), hostDyn vsRover3tierM1 2 Side.R (mRRover3tierM1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (gsRover3tierM1_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsRover3tierM1_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1))) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsRover3tierM1_1, z3solve (Formula.and (Formula.and (hostGuard vsRover3tierM1 2 Side.R (mRRover3tierM1 1)) (Formula.and (hostEvolve vsRover3tierM1 2 Side.L (mLRover3tierM1 1)) (hostEvolve vsRover3tierM1 2 Side.R (mRRover3tierM1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsRover3tierM1_1 ν →
      Covered (GWRover3tierM1 1) ⟨q0, 4, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRover3tierM1 1) gsRover3tierM1_1 ⟨q0, 4, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRover3tierM1_1 hs_1_0 hs_1_1 hr_1_1 hq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 13 _ (by decide) ν hν

end ThroughoutRover3tierM1
end RelCertifier
