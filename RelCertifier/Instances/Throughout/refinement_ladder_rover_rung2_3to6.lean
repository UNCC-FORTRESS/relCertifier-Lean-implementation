/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.refinement_ladder_rover_rung2_3to6
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2_3to6

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRefinementLadderRoverRung23to6
open DL Parse

def vsRefinementLadderRoverRung23to6 : List String := ["v", "s", "psi", "theta_p", "z", "phi_r"]
def dummyRefinementLadderRoverRung23to6 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRefinementLadderRoverRung23to6 (l : ℕ) : Parse.PMode := refinement_ladder_rover_rung2_3to6_IR.L.modes.getD l dummyRefinementLadderRoverRung23to6
def mRRefinementLadderRoverRung23to6 (q : ℕ) : Parse.PMode := refinement_ladder_rover_rung2_3to6_IR.R.modes.getD q dummyRefinementLadderRoverRung23to6
def fRowRefinementLadderRoverRung23to6 (l q : ℕ) : ModeFlagsE :=
  ((refinement_ladder_rover_rung2_3to6_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRefinementLadderRoverRung23to6 (l : ℕ) : SearchGraph (Var 6) :=
  realGraphOf vsRefinementLadderRoverRung23to6 6 refinement_ladder_rover_rung2_3to6_IR (mLRefinementLadderRoverRung23to6 l)
    ((refinement_ladder_rover_rung2_3to6_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((refinement_ladder_rover_rung2_3to6_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => refinement_ladder_rover_rung2_3to6_coverNC.pruned.contains (a, b))

noncomputable def gsRefinementLadderRoverRung23to6_0 : List (Term (Var 6)) :=
  hostComps vsRefinementLadderRoverRung23to6 6 (((refinement_ladder_rover_rung2_3to6_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

theorem GWRefinementLadderRoverRung23to60_modes_eq : (GWRefinementLadderRoverRung23to6 0).modes =
    [realModeOf vsRefinementLadderRoverRung23to6 6 (mLRefinementLadderRoverRung23to6 0) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung23to6 0 0) (mRRefinementLadderRoverRung23to6 0),
     realModeOf vsRefinementLadderRoverRung23to6 6 (mLRefinementLadderRoverRung23to6 0) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung23to6 0 1) (mRRefinementLadderRoverRung23to6 1),
     realModeOf vsRefinementLadderRoverRung23to6 6 (mLRefinementLadderRoverRung23to6 0) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung23to6 0 2) (mRRefinementLadderRoverRung23to6 2)] := rfl

theorem certRefinementLadderRoverRung23to6_0 (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRefinementLadderRoverRung23to6 0) gsRefinementLadderRoverRung23to6_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to60_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung23to6_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung23to6_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung23to6_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to60_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to60_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to60_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to60_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung23to60_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem refinement_ladder_rover_rung2_3to6_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 0))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_0.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_0[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 0)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsRefinementLadderRoverRung23to6_0 ν →
      Covered (GWRefinementLadderRoverRung23to6 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRefinementLadderRoverRung23to6 0) gsRefinementLadderRoverRung23to6_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRefinementLadderRoverRung23to6_0 hs_0_0 hs_0_1 hs_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

noncomputable def gsRefinementLadderRoverRung23to6_1 : List (Term (Var 6)) :=
  hostComps vsRefinementLadderRoverRung23to6 6 (((refinement_ladder_rover_rung2_3to6_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

theorem GWRefinementLadderRoverRung23to61_modes_eq : (GWRefinementLadderRoverRung23to6 1).modes =
    [realModeOf vsRefinementLadderRoverRung23to6 6 (mLRefinementLadderRoverRung23to6 1) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung23to6 1 1) (mRRefinementLadderRoverRung23to6 1),
     realModeOf vsRefinementLadderRoverRung23to6 6 (mLRefinementLadderRoverRung23to6 1) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung23to6 1 2) (mRRefinementLadderRoverRung23to6 2)] := rfl

theorem certRefinementLadderRoverRung23to6_1 (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRefinementLadderRoverRung23to6 1) gsRefinementLadderRoverRung23to6_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to61_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung23to6_1 hs_1_1
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung23to6_1 hs_1_2
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to61_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to61_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to61_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to61_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung23to61_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem refinement_ladder_rover_rung2_3to6_throughout_MODER (hs_1_1 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 1))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_1.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_1[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 1)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_1.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsRefinementLadderRoverRung23to6_1 ν →
      Covered (GWRefinementLadderRoverRung23to6 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRefinementLadderRoverRung23to6 1) gsRefinementLadderRoverRung23to6_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRefinementLadderRoverRung23to6_1 hs_1_1 hs_1_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 4 _ (by decide) ν hν

noncomputable def gsRefinementLadderRoverRung23to6_2 : List (Term (Var 6)) :=
  hostComps vsRefinementLadderRoverRung23to6 6 (((refinement_ladder_rover_rung2_3to6_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

theorem GWRefinementLadderRoverRung23to62_modes_eq : (GWRefinementLadderRoverRung23to6 2).modes =
    [realModeOf vsRefinementLadderRoverRung23to6 6 (mLRefinementLadderRoverRung23to6 2) ((1 : ℚ) / 1) (fRowRefinementLadderRoverRung23to6 2 2) (mRRefinementLadderRoverRung23to6 2)] := rfl

theorem certRefinementLadderRoverRung23to6_2 (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_2[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_2[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_2[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_2.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRefinementLadderRoverRung23to6 2) gsRefinementLadderRoverRung23to6_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to62_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRefinementLadderRoverRung23to6_2 hs_2_2
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to62_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to62_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to62_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRefinementLadderRoverRung23to62_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRefinementLadderRoverRung23to6, refinement_ladder_rover_rung2_3to6_coverNC])
    | q + 1, hm => simp at hm
  · intro m hm
    rw [GWRefinementLadderRoverRung23to62_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl <;> simp

theorem refinement_ladder_rover_rung2_3to6_throughout_FLAT (hs_2_2 : ∀ i (hi : i < gsRefinementLadderRoverRung23to6_2.length),     z3solve (flowQuery ⟨gsRefinementLadderRoverRung23to6_2[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRefinementLadderRoverRung23to6_2[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRefinementLadderRoverRung23to6_2[i],       hostDyn vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2), hostDyn vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.L (mLRefinementLadderRoverRung23to6 2)) (hostEvolve vsRefinementLadderRoverRung23to6 6 Side.R (mRRefinementLadderRoverRung23to6 2))) (gsRefinementLadderRoverRung23to6_2.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0], ∀ ν, InvAllHolds gsRefinementLadderRoverRung23to6_2 ν →
      Covered (GWRefinementLadderRoverRung23to6 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRefinementLadderRoverRung23to6 2) gsRefinementLadderRoverRung23to6_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRefinementLadderRoverRung23to6_2 hs_2_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 3 _ (by decide) ν hν

end ThroughoutRefinementLadderRoverRung23to6
end RelCertifier
