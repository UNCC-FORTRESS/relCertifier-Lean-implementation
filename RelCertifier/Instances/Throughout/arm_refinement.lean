/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutArmRefinement
open DL Parse

def vsArmRefinement : List String := ["theta", "v"]
def dummyArmRefinement : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLArmRefinement (l : ℕ) : Parse.PMode := arm_refinement_IR.L.modes.getD l dummyArmRefinement
def mRArmRefinement (q : ℕ) : Parse.PMode := arm_refinement_IR.R.modes.getD q dummyArmRefinement
def fRowArmRefinement (l q : ℕ) : ModeFlagsE :=
  ((arm_refinement_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWArmRefinement (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsArmRefinement 2 arm_refinement_IR (mLArmRefinement l)
    ((arm_refinement_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((arm_refinement_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => arm_refinement_coverNC.pruned.contains (a, b))

noncomputable def gsArmRefinement_0 : List (Term (Var 2)) :=
  hostComps vsArmRefinement 2 (((arm_refinement_IR.invariants.find? (fun r => r.1 == "Accelerate")).getD ("", Parse.PForm.tt)).2)

theorem GWArmRefinement0_modes_eq : (GWArmRefinement 0).modes =
    [realModeOf vsArmRefinement 2 (mLArmRefinement 0) ((5 : ℚ) / 1) (fRowArmRefinement 0 0) (mRArmRefinement 0),
     realModeOf vsArmRefinement 2 (mLArmRefinement 0) ((5 : ℚ) / 1) (fRowArmRefinement 0 1) (mRArmRefinement 1)] := rfl

theorem certArmRefinement_0 (hs_0_0 : ∀ i (hi : i < gsArmRefinement_0.length),     z3solve (flowQuery ⟨gsArmRefinement_0[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_0[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_0[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmRefinement_0.length),     z3solve (flowQuery ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmRefinement_0.length),     z3solve (flowQuery ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmRefinement_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1))) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsArmRefinement_0, z3solve (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1)) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWArmRefinement 0) gsArmRefinement_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmRefinement_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmRefinement_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmRefinement_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmRefinement_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmRefinement_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWArmRefinement0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem arm_refinement_throughout_Accelerate (hs_0_0 : ∀ i (hi : i < gsArmRefinement_0.length),     z3solve (flowQuery ⟨gsArmRefinement_0[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_0[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_0[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmRefinement_0.length),     z3solve (flowQuery ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmRefinement_0.length),     z3solve (flowQuery ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_0[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmRefinement_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1))) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsArmRefinement_0, z3solve (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1)) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 0)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsArmRefinement_0 ν →
      Covered (GWArmRefinement 0) ⟨q0, 5, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWArmRefinement 0) gsArmRefinement_0 ⟨q0, 5, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certArmRefinement_0 hs_0_0 hdp_0_0 hdq_0_0 hr_0_1 hq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 16 _ (by decide) ν hν

noncomputable def gsArmRefinement_1 : List (Term (Var 2)) :=
  hostComps vsArmRefinement 2 (((arm_refinement_IR.invariants.find? (fun r => r.1 == "Brake")).getD ("", Parse.PForm.tt)).2)

theorem GWArmRefinement1_modes_eq : (GWArmRefinement 1).modes =
    [realModeOf vsArmRefinement 2 (mLArmRefinement 1) ((5 : ℚ) / 1) (fRowArmRefinement 1 0) (mRArmRefinement 0),
     realModeOf vsArmRefinement 2 (mLArmRefinement 1) ((5 : ℚ) / 1) (fRowArmRefinement 1 1) (mRArmRefinement 1)] := rfl

theorem certArmRefinement_1 (hs_1_0 : ∀ i (hi : i < gsArmRefinement_1.length),     z3solve (flowQuery ⟨gsArmRefinement_1[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 1), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_1[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 1), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_1[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 1), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmRefinement_1.length),     z3solve (flowQuery ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmRefinement_1.length),     z3solve (flowQuery ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsArmRefinement_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1))) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsArmRefinement_1, z3solve (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1)) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWArmRefinement 1) gsArmRefinement_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmRefinement_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmRefinement_1 _ (fun g hg => z3_unsat_sound (hr_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmRefinement_1 _ (fun g hg => z3_unsat_sound (hq_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmRefinement_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmRefinement1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmRefinement_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmRefinement, arm_refinement_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWArmRefinement1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem arm_refinement_throughout_Brake (hs_1_0 : ∀ i (hi : i < gsArmRefinement_1.length),     z3solve (flowQuery ⟨gsArmRefinement_1[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 1), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_1[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 1), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_1[i],       hostDyn vsArmRefinement 2 Side.L (mLArmRefinement 1), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmRefinement_1.length),     z3solve (flowQuery ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmRefinement_1.length),     z3solve (flowQuery ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmRefinement_1[i],       (fun _ => Term.const 0), hostDyn vsArmRefinement 2 Side.R (mRArmRefinement 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 0))) (gsArmRefinement_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsArmRefinement_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1))) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsArmRefinement_1, z3solve (Formula.and (Formula.and (hostGuard vsArmRefinement 2 Side.R (mRArmRefinement 1)) (Formula.and (hostEvolve vsArmRefinement 2 Side.L (mLArmRefinement 1)) (hostEvolve vsArmRefinement 2 Side.R (mRArmRefinement 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsArmRefinement_1 ν →
      Covered (GWArmRefinement 1) ⟨q0, 5, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWArmRefinement 1) gsArmRefinement_1 ⟨q0, 5, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certArmRefinement_1 hs_1_0 hdp_1_0 hdq_1_0 hr_1_1 hq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 16 _ (by decide) ν hν

end ThroughoutArmRefinement
end RelCertifier
