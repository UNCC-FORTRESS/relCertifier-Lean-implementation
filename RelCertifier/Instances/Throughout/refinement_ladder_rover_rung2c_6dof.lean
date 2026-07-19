/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.refinement_ladder_rover_rung2c_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2c_6dof

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRefinementLadderRoverRung2c6dof
open DL Parse

def vsRefinementLadderRoverRung2c6dof : List String := ["v", "s", "psi", "theta_p", "z", "phi_r"]
def dummyRefinementLadderRoverRung2c6dof : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRefinementLadderRoverRung2c6dof (l : ℕ) : Parse.PMode := refinement_ladder_rover_rung2c_6dof_IR.L.modes.getD l dummyRefinementLadderRoverRung2c6dof
def mRRefinementLadderRoverRung2c6dof (q : ℕ) : Parse.PMode := refinement_ladder_rover_rung2c_6dof_IR.R.modes.getD q dummyRefinementLadderRoverRung2c6dof
def fRowRefinementLadderRoverRung2c6dof (l q : ℕ) : ModeFlagsE :=
  ((refinement_ladder_rover_rung2c_6dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRefinementLadderRoverRung2c6dof (l : ℕ) : SearchGraph (Var 6) :=
  realGraphOf vsRefinementLadderRoverRung2c6dof 6 refinement_ladder_rover_rung2c_6dof_IR (mLRefinementLadderRoverRung2c6dof l)
    ((refinement_ladder_rover_rung2c_6dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((refinement_ladder_rover_rung2c_6dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => refinement_ladder_rover_rung2c_6dof_coverNC.pruned.contains (a, b))

noncomputable def gsRefinementLadderRoverRung2c6dof_0 : List (Term (Var 6)) :=
  hostComps vsRefinementLadderRoverRung2c6dof 6 (((refinement_ladder_rover_rung2c_6dof_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

theorem GWRefinementLadderRoverRung2c6dof0_modes_eq : (GWRefinementLadderRoverRung2c6dof 0).modes =
    [realModeOf vsRefinementLadderRoverRung2c6dof 6 (mLRefinementLadderRoverRung2c6dof 0) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung2c6dof 0 0) (mRRefinementLadderRoverRung2c6dof 0)] := rfl

theorem certRefinementLadderRoverRung2c6dof_0 (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung2c6dof_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung2c6dof_0[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0))) (gsRefinementLadderRoverRung2c6dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung2c6dof_0[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0))) (gsRefinementLadderRoverRung2c6dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung2c6dof_0[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0))) (gsRefinementLadderRoverRung2c6dof_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRefinementLadderRoverRung2c6dof 0) gsRefinementLadderRoverRung2c6dof_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung2c6dof_0 hs_0_0
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung2c6dof0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl <;> simp

theorem refinement_ladder_rover_rung2c_6dof_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung2c6dof_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung2c6dof_0[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0))) (gsRefinementLadderRoverRung2c6dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung2c6dof_0[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0))) (gsRefinementLadderRoverRung2c6dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung2c6dof_0[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 0)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 0))) (gsRefinementLadderRoverRung2c6dof_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0], ∀ ν, InvAllHolds gsRefinementLadderRoverRung2c6dof_0 ν →
      Covered (GWRefinementLadderRoverRung2c6dof 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRefinementLadderRoverRung2c6dof 0) gsRefinementLadderRoverRung2c6dof_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRefinementLadderRoverRung2c6dof_0 hs_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 3 _ (by decide) ν hν

noncomputable def gsRefinementLadderRoverRung2c6dof_1 : List (Term (Var 6)) :=
  hostComps vsRefinementLadderRoverRung2c6dof 6 (((refinement_ladder_rover_rung2c_6dof_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

theorem GWRefinementLadderRoverRung2c6dof1_modes_eq : (GWRefinementLadderRoverRung2c6dof 1).modes =
    [realModeOf vsRefinementLadderRoverRung2c6dof 6 (mLRefinementLadderRoverRung2c6dof 1) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung2c6dof 1 1) (mRRefinementLadderRoverRung2c6dof 1)] := rfl

theorem certRefinementLadderRoverRung2c6dof_1 (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung2c6dof_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung2c6dof_1[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1))) (gsRefinementLadderRoverRung2c6dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung2c6dof_1[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1))) (gsRefinementLadderRoverRung2c6dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung2c6dof_1[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1))) (gsRefinementLadderRoverRung2c6dof_1.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRefinementLadderRoverRung2c6dof 1) gsRefinementLadderRoverRung2c6dof_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung2c6dof_1 hs_1_1
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung2c6dof1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl <;> simp

theorem refinement_ladder_rover_rung2c_6dof_throughout_MODER (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung2c6dof_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung2c6dof_1[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1))) (gsRefinementLadderRoverRung2c6dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung2c6dof_1[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1))) (gsRefinementLadderRoverRung2c6dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung2c6dof_1[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 1)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 1))) (gsRefinementLadderRoverRung2c6dof_1.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0], ∀ ν, InvAllHolds gsRefinementLadderRoverRung2c6dof_1 ν →
      Covered (GWRefinementLadderRoverRung2c6dof 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRefinementLadderRoverRung2c6dof 1) gsRefinementLadderRoverRung2c6dof_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRefinementLadderRoverRung2c6dof_1 hs_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 3 _ (by decide) ν hν

noncomputable def gsRefinementLadderRoverRung2c6dof_2 : List (Term (Var 6)) :=
  hostComps vsRefinementLadderRoverRung2c6dof 6 (((refinement_ladder_rover_rung2c_6dof_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

theorem GWRefinementLadderRoverRung2c6dof2_modes_eq : (GWRefinementLadderRoverRung2c6dof 2).modes =
    [realModeOf vsRefinementLadderRoverRung2c6dof 6 (mLRefinementLadderRoverRung2c6dof 2) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung2c6dof 2 2) (mRRefinementLadderRoverRung2c6dof 2)] := rfl

theorem certRefinementLadderRoverRung2c6dof_2 (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung2c6dof_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung2c6dof_2[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2))) (gsRefinementLadderRoverRung2c6dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung2c6dof_2[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2))) (gsRefinementLadderRoverRung2c6dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung2c6dof_2[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2))) (gsRefinementLadderRoverRung2c6dof_2.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRefinementLadderRoverRung2c6dof 2) gsRefinementLadderRoverRung2c6dof_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung2c6dof_2 hs_2_2
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung2c6dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung2c6dof, refinement_ladder_rover_rung2c_6dof_coverNC])
    | q + 1, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung2c6dof2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl <;> simp

theorem refinement_ladder_rover_rung2c_6dof_throughout_FLAT (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung2c6dof_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung2c6dof_2[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2))) (gsRefinementLadderRoverRung2c6dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung2c6dof_2[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2))) (gsRefinementLadderRoverRung2c6dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung2c6dof_2[i],       hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2), hostDyn vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.L (mLRefinementLadderRoverRung2c6dof 2)) (hostEvolve vsRefinementLadderRoverRung2c6dof 6 Side.R (mRRefinementLadderRoverRung2c6dof 2))) (gsRefinementLadderRoverRung2c6dof_2.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0], ∀ ν, InvAllHolds gsRefinementLadderRoverRung2c6dof_2 ν →
      Covered (GWRefinementLadderRoverRung2c6dof 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRefinementLadderRoverRung2c6dof 2) gsRefinementLadderRoverRung2c6dof_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRefinementLadderRoverRung2c6dof_2 hs_2_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 3 _ (by decide) ν hν

end ThroughoutRefinementLadderRoverRung2c6dof
end RelCertifier
