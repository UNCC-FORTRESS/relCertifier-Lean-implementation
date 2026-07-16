/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutArmChainRung1
open DL Parse

def vsArmChainRung1 : List String := ["theta"]
def dummyArmChainRung1 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLArmChainRung1 (l : ℕ) : Parse.PMode := arm_chain_rung1_IR.L.modes.getD l dummyArmChainRung1
def mRArmChainRung1 (q : ℕ) : Parse.PMode := arm_chain_rung1_IR.R.modes.getD q dummyArmChainRung1
def fRowArmChainRung1 (l q : ℕ) : ModeFlagsE :=
  ((arm_chain_rung1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWArmChainRung1 (l : ℕ) : SearchGraph (Var 1) :=
  realGraphOf vsArmChainRung1 1 arm_chain_rung1_IR (mLArmChainRung1 l)
    ((arm_chain_rung1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((arm_chain_rung1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => arm_chain_rung1_coverNC.pruned.contains (a, b))

noncomputable def gsArmChainRung1_0 : List (Term (Var 1)) :=
  hostComps vsArmChainRung1 1 (((arm_chain_rung1_IR.invariants.find? (fun r => r.1 == "ApproachFast")).getD ("", Parse.PForm.tt)).2)

theorem GWArmChainRung10_modes_eq : (GWArmChainRung1 0).modes =
    [realModeOf vsArmChainRung1 1 (mLArmChainRung1 0) ((5 : ℚ) / 2) (fRowArmChainRung1 0 0) (mRArmChainRung1 0),
     realModeOf vsArmChainRung1 1 (mLArmChainRung1 0) ((5 : ℚ) / 2) (fRowArmChainRung1 0 1) (mRArmChainRung1 1)] := rfl

theorem certArmChainRung1_0 (hs_0_0 : ∀ i (hi : i < gsArmChainRung1_0.length),     z3solve (flowQuery ⟨gsArmChainRung1_0[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((5 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_0[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((5 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_0[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((5 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat) (hr_0_0 : ∀ g ∈ gsArmChainRung1_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmChainRung1_0.length),     z3solve (flowQuery ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmChainRung1_0.length),     z3solve (flowQuery ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmChainRung1_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsArmChainRung1_0, z3solve (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1)) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWArmChainRung1 0) gsArmChainRung1_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung1_0 _ (fun g hg => z3_unsat_sound (hr_0_0 g hg))
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung1_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmChainRung1_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWArmChainRung10_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem arm_chain_rung1_throughout_ApproachFast (hs_0_0 : ∀ i (hi : i < gsArmChainRung1_0.length),     z3solve (flowQuery ⟨gsArmChainRung1_0[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((5 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_0[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((5 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_0[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((5 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat) (hr_0_0 : ∀ g ∈ gsArmChainRung1_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmChainRung1_0.length),     z3solve (flowQuery ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmChainRung1_0.length),     z3solve (flowQuery ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_0[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmChainRung1_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsArmChainRung1_0, z3solve (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1)) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 0)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsArmChainRung1_0 ν →
      Covered (GWArmChainRung1 0) ⟨q0, 3, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWArmChainRung1 0) gsArmChainRung1_0 ⟨q0, 3, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certArmChainRung1_0 hs_0_0 hr_0_0 hdp_0_0 hdq_0_0 hr_0_1 hq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 10 _ (by decide) ν hν

noncomputable def gsArmChainRung1_1 : List (Term (Var 1)) :=
  hostComps vsArmChainRung1 1 (((arm_chain_rung1_IR.invariants.find? (fun r => r.1 == "ApproachSlow")).getD ("", Parse.PForm.tt)).2)

theorem GWArmChainRung11_modes_eq : (GWArmChainRung1 1).modes =
    [realModeOf vsArmChainRung1 1 (mLArmChainRung1 1) ((3 : ℚ) / 2) (fRowArmChainRung1 1 0) (mRArmChainRung1 0),
     realModeOf vsArmChainRung1 1 (mLArmChainRung1 1) ((3 : ℚ) / 2) (fRowArmChainRung1 1 1) (mRArmChainRung1 1)] := rfl

theorem certArmChainRung1_1 (hs_1_0 : ∀ i (hi : i < gsArmChainRung1_1.length),     z3solve (flowQuery ⟨gsArmChainRung1_1[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 1), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((3 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_1[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 1), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((3 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_1[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 1), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((3 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmChainRung1_1.length),     z3solve (flowQuery ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmChainRung1_1.length),     z3solve (flowQuery ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsArmChainRung1_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsArmChainRung1_1, z3solve (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1)) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWArmChainRung1 1) gsArmChainRung1_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung1_1 _ (fun g hg => z3_unsat_sound (hr_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmChainRung1_1 _ (fun g hg => z3_unsat_sound (hq_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung11_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWArmChainRung11_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem arm_chain_rung1_throughout_ApproachSlow (hs_1_0 : ∀ i (hi : i < gsArmChainRung1_1.length),     z3solve (flowQuery ⟨gsArmChainRung1_1[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 1), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((3 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_1[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 1), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((3 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_1[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 1), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((3 : ℚ) / 2 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmChainRung1_1.length),     z3solve (flowQuery ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmChainRung1_1.length),     z3solve (flowQuery ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_1[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsArmChainRung1_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsArmChainRung1_1, z3solve (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1)) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 1)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsArmChainRung1_1 ν →
      Covered (GWArmChainRung1 1) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWArmChainRung1 1) gsArmChainRung1_1 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certArmChainRung1_1 hs_1_0 hdp_1_0 hdq_1_0 hr_1_1 hq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 7 _ (by decide) ν hν

noncomputable def gsArmChainRung1_2 : List (Term (Var 1)) :=
  hostComps vsArmChainRung1 1 (((arm_chain_rung1_IR.invariants.find? (fun r => r.1 == "Return")).getD ("", Parse.PForm.tt)).2)

theorem GWArmChainRung12_modes_eq : (GWArmChainRung1 2).modes =
    [realModeOf vsArmChainRung1 1 (mLArmChainRung1 2) ((1 : ℚ) / 1) (fRowArmChainRung1 2 0) (mRArmChainRung1 0),
     realModeOf vsArmChainRung1 1 (mLArmChainRung1 2) ((1 : ℚ) / 1) (fRowArmChainRung1 2 1) (mRArmChainRung1 1)] := rfl

theorem certArmChainRung1_2 (hs_2_0 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hdp_2_0 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hr_2_1 : ∀ g ∈ gsArmChainRung1_2, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_2_1 : ∀ g ∈ gsArmChainRung1_2, z3solve (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1)) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWArmChainRung1 2) gsArmChainRung1_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_2 hs_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_2 hs_2_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmChainRung1_2 _ (fun g hg => z3_unsat_sound (hr_2_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmChainRung1_2 _ (fun g hg => z3_unsat_sound (hq_2_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_2 hdp_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmChainRung12_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmChainRung1_2 hdq_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmChainRung1, arm_chain_rung1_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWArmChainRung12_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem arm_chain_rung1_throughout_Return (hs_2_0 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hdp_2_0 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hdq_2_0 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       (fun _ => Term.const 0), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 0))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsArmChainRung1_2.length),     z3solve (flowQuery ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmChainRung1_2[i],       hostDyn vsArmChainRung1 1 Side.L (mLArmChainRung1 2), hostDyn vsArmChainRung1 1 Side.R (mRArmChainRung1 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (gsArmChainRung1_2.take i)⟩) = Verdict.unsat) (hr_2_1 : ∀ g ∈ gsArmChainRung1_2, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1))) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_2_1 : ∀ g ∈ gsArmChainRung1_2, z3solve (Formula.and (Formula.and (hostGuard vsArmChainRung1 1 Side.R (mRArmChainRung1 1)) (Formula.and (hostEvolve vsArmChainRung1 1 Side.L (mLArmChainRung1 2)) (hostEvolve vsArmChainRung1 1 Side.R (mRArmChainRung1 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsArmChainRung1_2 ν →
      Covered (GWArmChainRung1 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWArmChainRung1 2) gsArmChainRung1_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certArmChainRung1_2 hs_2_0 hdp_2_0 hdq_2_0 hs_2_1 hr_2_1 hq_2_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 4 _ (by decide) ν hν

end ThroughoutArmChainRung1
end RelCertifier
