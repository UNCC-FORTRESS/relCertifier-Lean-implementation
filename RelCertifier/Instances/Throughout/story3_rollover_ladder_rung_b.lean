/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.story3_rollover_ladder_rung_b
import RelCertifier.Instances.BenchIR.story3_rollover_ladder_rung_b

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutStory3RolloverLadderRungB
open DL Parse

def vsStory3RolloverLadderRungB : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "e", "r", "phi_r", "omega_phi", "z", "y"]
def dummyStory3RolloverLadderRungB : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLStory3RolloverLadderRungB (l : ℕ) : Parse.PMode := story3_rollover_ladder_rung_b_IR.L.modes.getD l dummyStory3RolloverLadderRungB
def mRStory3RolloverLadderRungB (q : ℕ) : Parse.PMode := story3_rollover_ladder_rung_b_IR.R.modes.getD q dummyStory3RolloverLadderRungB
def fRowStory3RolloverLadderRungB (l q : ℕ) : ModeFlagsE :=
  ((story3_rollover_ladder_rung_b_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWStory3RolloverLadderRungB (l : ℕ) : SearchGraph (Var 12) :=
  realGraphOf vsStory3RolloverLadderRungB 12 story3_rollover_ladder_rung_b_IR (mLStory3RolloverLadderRungB l)
    ((story3_rollover_ladder_rung_b_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((story3_rollover_ladder_rung_b_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => story3_rollover_ladder_rung_b_coverNC.pruned.contains (a, b))

noncomputable def gsStory3RolloverLadderRungB_0 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverLadderRungB 12 (((story3_rollover_ladder_rung_b_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

theorem GWStory3RolloverLadderRungB0_modes_eq : (GWStory3RolloverLadderRungB 0).modes =
    [realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 0) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 0 0) (mRStory3RolloverLadderRungB 0),
     realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 0) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 0 1) (mRStory3RolloverLadderRungB 1),
     realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 0) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 0 2) (mRStory3RolloverLadderRungB 2)] := rfl

theorem certStory3RolloverLadderRungB_0 (hs_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungB_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungB_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungB_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory3RolloverLadderRungB 0) gsStory3RolloverLadderRungB_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverLadderRungB0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_ladder_rung_b_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsStory3RolloverLadderRungB_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory3RolloverLadderRungB_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory3RolloverLadderRungB_0.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_0[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 0)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory3RolloverLadderRungB_0 ν →
      Covered (GWStory3RolloverLadderRungB 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory3RolloverLadderRungB 0) gsStory3RolloverLadderRungB_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory3RolloverLadderRungB_0 hs_0_0 hs_0_1 hs_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

noncomputable def gsStory3RolloverLadderRungB_1 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverLadderRungB 12 (((story3_rollover_ladder_rung_b_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

theorem GWStory3RolloverLadderRungB1_modes_eq : (GWStory3RolloverLadderRungB 1).modes =
    [realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 1) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 1 0) (mRStory3RolloverLadderRungB 0),
     realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 1) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 1 1) (mRStory3RolloverLadderRungB 1),
     realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 1) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 1 2) (mRStory3RolloverLadderRungB 2)] := rfl

theorem certStory3RolloverLadderRungB_1 (hs_1_0 : ∀ i (hi : i < gsStory3RolloverLadderRungB_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungB_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungB_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory3RolloverLadderRungB 1) gsStory3RolloverLadderRungB_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverLadderRungB1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_ladder_rung_b_throughout_MODER (hs_1_0 : ∀ i (hi : i < gsStory3RolloverLadderRungB_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory3RolloverLadderRungB_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory3RolloverLadderRungB_1.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_1[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 1)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_1.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory3RolloverLadderRungB_1 ν →
      Covered (GWStory3RolloverLadderRungB 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory3RolloverLadderRungB 1) gsStory3RolloverLadderRungB_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory3RolloverLadderRungB_1 hs_1_0 hs_1_1 hs_1_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

noncomputable def gsStory3RolloverLadderRungB_2 : List (Term (Var 12)) :=
  hostComps vsStory3RolloverLadderRungB 12 (((story3_rollover_ladder_rung_b_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

theorem GWStory3RolloverLadderRungB2_modes_eq : (GWStory3RolloverLadderRungB 2).modes =
    [realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 2) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 2 0) (mRStory3RolloverLadderRungB 0),
     realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 2) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 2 1) (mRStory3RolloverLadderRungB 1),
     realModeOf vsStory3RolloverLadderRungB 12 (mLStory3RolloverLadderRungB 2) ((1 : ℚ) / 1) (fRowStory3RolloverLadderRungB 2 2) (mRStory3RolloverLadderRungB 2)] := rfl

theorem certStory3RolloverLadderRungB_2 (hs_2_0 : ∀ i (hi : i < gsStory3RolloverLadderRungB_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsStory3RolloverLadderRungB_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungB_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory3RolloverLadderRungB 2) gsStory3RolloverLadderRungB_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_2 hs_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_2 hs_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory3RolloverLadderRungB_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory3RolloverLadderRungB2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory3RolloverLadderRungB, story3_rollover_ladder_rung_b_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory3RolloverLadderRungB2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story3_rollover_ladder_rung_b_throughout_FLAT (hs_2_0 : ∀ i (hi : i < gsStory3RolloverLadderRungB_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 0))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsStory3RolloverLadderRungB_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 1))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory3RolloverLadderRungB_2.length),     z3solve (flowQuery ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory3RolloverLadderRungB_2[i],       hostDyn vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2), hostDyn vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory3RolloverLadderRungB 12 Side.L (mLStory3RolloverLadderRungB 2)) (hostEvolve vsStory3RolloverLadderRungB 12 Side.R (mRStory3RolloverLadderRungB 2))) (gsStory3RolloverLadderRungB_2.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory3RolloverLadderRungB_2 ν →
      Covered (GWStory3RolloverLadderRungB 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory3RolloverLadderRungB 2) gsStory3RolloverLadderRungB_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory3RolloverLadderRungB_2 hs_2_0 hs_2_1 hs_2_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

end ThroughoutStory3RolloverLadderRungB
end RelCertifier
