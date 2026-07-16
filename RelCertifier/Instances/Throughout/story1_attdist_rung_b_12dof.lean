/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutStory1AttdistRungB12dof
open DL Parse

def vsStory1AttdistRungB12dof : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]
def dummyStory1AttdistRungB12dof : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLStory1AttdistRungB12dof (l : ℕ) : Parse.PMode := story1_attdist_rung_b_12dof_IR.L.modes.getD l dummyStory1AttdistRungB12dof
def mRStory1AttdistRungB12dof (q : ℕ) : Parse.PMode := story1_attdist_rung_b_12dof_IR.R.modes.getD q dummyStory1AttdistRungB12dof
def fRowStory1AttdistRungB12dof (l q : ℕ) : ModeFlagsE :=
  ((story1_attdist_rung_b_12dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWStory1AttdistRungB12dof (l : ℕ) : SearchGraph (Var 12) :=
  realGraphOf vsStory1AttdistRungB12dof 12 story1_attdist_rung_b_12dof_IR (mLStory1AttdistRungB12dof l)
    ((story1_attdist_rung_b_12dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((story1_attdist_rung_b_12dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => story1_attdist_rung_b_12dof_coverNC.pruned.contains (a, b))

noncomputable def gsStory1AttdistRungB12dof_0 : List (Term (Var 12)) :=
  hostComps vsStory1AttdistRungB12dof 12 (((story1_attdist_rung_b_12dof_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

theorem GWStory1AttdistRungB12dof0_modes_eq : (GWStory1AttdistRungB12dof 0).modes =
    [realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 0) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 0 0) (mRStory1AttdistRungB12dof 0),
     realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 0) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 0 1) (mRStory1AttdistRungB12dof 1),
     realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 0) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 0 2) (mRStory1AttdistRungB12dof 2)] := rfl

theorem certStory1AttdistRungB12dof_0 (hs_0_0 : ∀ i (hi : i < gsStory1AttdistRungB12dof_0.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory1AttdistRungB12dof_0.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory1AttdistRungB12dof_0.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory1AttdistRungB12dof 0) gsStory1AttdistRungB12dof_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory1AttdistRungB12dof0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story1_attdist_rung_b_12dof_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsStory1AttdistRungB12dof_0.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory1AttdistRungB12dof_0.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory1AttdistRungB12dof_0.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_0[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 0)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory1AttdistRungB12dof_0 ν →
      Covered (GWStory1AttdistRungB12dof 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory1AttdistRungB12dof 0) gsStory1AttdistRungB12dof_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory1AttdistRungB12dof_0 hs_0_0 hs_0_1 hs_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

noncomputable def gsStory1AttdistRungB12dof_1 : List (Term (Var 12)) :=
  hostComps vsStory1AttdistRungB12dof 12 (((story1_attdist_rung_b_12dof_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

theorem GWStory1AttdistRungB12dof1_modes_eq : (GWStory1AttdistRungB12dof 1).modes =
    [realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 1) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 1 0) (mRStory1AttdistRungB12dof 0),
     realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 1) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 1 1) (mRStory1AttdistRungB12dof 1),
     realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 1) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 1 2) (mRStory1AttdistRungB12dof 2)] := rfl

theorem certStory1AttdistRungB12dof_1 (hs_1_0 : ∀ i (hi : i < gsStory1AttdistRungB12dof_1.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory1AttdistRungB12dof_1.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory1AttdistRungB12dof_1.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory1AttdistRungB12dof 1) gsStory1AttdistRungB12dof_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory1AttdistRungB12dof1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story1_attdist_rung_b_12dof_throughout_MODER (hs_1_0 : ∀ i (hi : i < gsStory1AttdistRungB12dof_1.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsStory1AttdistRungB12dof_1.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory1AttdistRungB12dof_1.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_1[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 1)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_1.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory1AttdistRungB12dof_1 ν →
      Covered (GWStory1AttdistRungB12dof 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory1AttdistRungB12dof 1) gsStory1AttdistRungB12dof_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory1AttdistRungB12dof_1 hs_1_0 hs_1_1 hs_1_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

noncomputable def gsStory1AttdistRungB12dof_2 : List (Term (Var 12)) :=
  hostComps vsStory1AttdistRungB12dof 12 (((story1_attdist_rung_b_12dof_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

theorem GWStory1AttdistRungB12dof2_modes_eq : (GWStory1AttdistRungB12dof 2).modes =
    [realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 2) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 2 0) (mRStory1AttdistRungB12dof 0),
     realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 2) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 2 1) (mRStory1AttdistRungB12dof 1),
     realModeOf vsStory1AttdistRungB12dof 12 (mLStory1AttdistRungB12dof 2) ((1 : ℚ) / 1) (fRowStory1AttdistRungB12dof 2 2) (mRStory1AttdistRungB12dof 2)] := rfl

theorem certStory1AttdistRungB12dof_2 (hs_2_0 : ∀ i (hi : i < gsStory1AttdistRungB12dof_2.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsStory1AttdistRungB12dof_2.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory1AttdistRungB12dof_2.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory1AttdistRungB12dof 2) gsStory1AttdistRungB12dof_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_2 hs_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_2 hs_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory1AttdistRungB12dof_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWStory1AttdistRungB12dof2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowStory1AttdistRungB12dof, story1_attdist_rung_b_12dof_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWStory1AttdistRungB12dof2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem story1_attdist_rung_b_12dof_throughout_FLAT (hs_2_0 : ∀ i (hi : i < gsStory1AttdistRungB12dof_2.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 0))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsStory1AttdistRungB12dof_2.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 1))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsStory1AttdistRungB12dof_2.length),     z3solve (flowQuery ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory1AttdistRungB12dof_2[i],       hostDyn vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2), hostDyn vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory1AttdistRungB12dof 12 Side.L (mLStory1AttdistRungB12dof 2)) (hostEvolve vsStory1AttdistRungB12dof 12 Side.R (mRStory1AttdistRungB12dof 2))) (gsStory1AttdistRungB12dof_2.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory1AttdistRungB12dof_2 ν →
      Covered (GWStory1AttdistRungB12dof 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory1AttdistRungB12dof 2) gsStory1AttdistRungB12dof_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory1AttdistRungB12dof_2 hs_2_0 hs_2_1 hs_2_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

end ThroughoutStory1AttdistRungB12dof
end RelCertifier
