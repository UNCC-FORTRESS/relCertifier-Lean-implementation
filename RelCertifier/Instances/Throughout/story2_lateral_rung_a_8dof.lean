/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutStory2LateralRungA8dof
open DL Parse

def vsStory2LateralRungA8dof : List String := ["v", "s", "psi", "theta_p", "y", "z", "phi_r", "w"]
def dummyStory2LateralRungA8dof : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLStory2LateralRungA8dof (l : ℕ) : Parse.PMode := story2_lateral_rung_a_8dof_IR.L.modes.getD l dummyStory2LateralRungA8dof
def mRStory2LateralRungA8dof (q : ℕ) : Parse.PMode := story2_lateral_rung_a_8dof_IR.R.modes.getD q dummyStory2LateralRungA8dof
def fRowStory2LateralRungA8dof (l q : ℕ) : ModeFlagsE :=
  ((story2_lateral_rung_a_8dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWStory2LateralRungA8dof (l : ℕ) : SearchGraph (Var 8) :=
  realGraphOf vsStory2LateralRungA8dof 8 story2_lateral_rung_a_8dof_IR (mLStory2LateralRungA8dof l)
    ((story2_lateral_rung_a_8dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((story2_lateral_rung_a_8dof_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => story2_lateral_rung_a_8dof_coverNC.pruned.contains (a, b))

noncomputable def gsStory2LateralRungA8dof_0 : List (Term (Var 8)) :=
  hostComps vsStory2LateralRungA8dof 8 (((story2_lateral_rung_a_8dof_IR.invariants.find? (fun r => r.1 == "STEEP")).getD ("", Parse.PForm.tt)).2)

theorem GWStory2LateralRungA8dof0_modes_eq : (GWStory2LateralRungA8dof 0).modes =
    [realModeOf vsStory2LateralRungA8dof 8 (mLStory2LateralRungA8dof 0) ((1 : ℚ) / 1) (fRowStory2LateralRungA8dof 0 0) (mRStory2LateralRungA8dof 0),
     realModeOf vsStory2LateralRungA8dof 8 (mLStory2LateralRungA8dof 0) ((1 : ℚ) / 1) (fRowStory2LateralRungA8dof 0 1) (mRStory2LateralRungA8dof 1),
     realModeOf vsStory2LateralRungA8dof 8 (mLStory2LateralRungA8dof 0) ((1 : ℚ) / 1) (fRowStory2LateralRungA8dof 0 2) (mRStory2LateralRungA8dof 2)] := rfl

theorem certStory2LateralRungA8dof_0 (hs_0_0 : ∀ i (hi : i < gsStory2LateralRungA8dof_0.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory2LateralRungA8dof_0.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory2LateralRungA8dof_0.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory2LateralRungA8dof 0) gsStory2LateralRungA8dof_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GWStory2LateralRungA8dof0_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory2LateralRungA8dof_0 hs_0_0)
           | exact absurd hflag (by simp [fRowStory2LateralRungA8dof, story2_lateral_rung_a_8dof_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory2LateralRungA8dof_0 hs_0_1)
           | exact absurd hflag (by simp [fRowStory2LateralRungA8dof, story2_lateral_rung_a_8dof_coverNC])
       | 2, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory2LateralRungA8dof_0 hs_0_2)
           | exact absurd hflag (by simp [fRowStory2LateralRungA8dof, story2_lateral_rung_a_8dof_coverNC])
       | q + 3, hm => simp at hm)
    | (intro m hm
       rw [GWStory2LateralRungA8dof0_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl | rfl <;> simp)

theorem story2_lateral_rung_a_8dof_throughout_STEEP (hs_0_0 : ∀ i (hi : i < gsStory2LateralRungA8dof_0.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 0))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsStory2LateralRungA8dof_0.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsStory2LateralRungA8dof_0.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_0[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 0)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsStory2LateralRungA8dof_0 ν →
      Covered (GWStory2LateralRungA8dof 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory2LateralRungA8dof 0) gsStory2LateralRungA8dof_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory2LateralRungA8dof_0 hs_0_0 hs_0_1 hs_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

noncomputable def gsStory2LateralRungA8dof_1 : List (Term (Var 8)) :=
  hostComps vsStory2LateralRungA8dof 8 (((story2_lateral_rung_a_8dof_IR.invariants.find? (fun r => r.1 == "MODER")).getD ("", Parse.PForm.tt)).2)

theorem GWStory2LateralRungA8dof1_modes_eq : (GWStory2LateralRungA8dof 1).modes =
    [realModeOf vsStory2LateralRungA8dof 8 (mLStory2LateralRungA8dof 1) ((1 : ℚ) / 1) (fRowStory2LateralRungA8dof 1 1) (mRStory2LateralRungA8dof 1),
     realModeOf vsStory2LateralRungA8dof 8 (mLStory2LateralRungA8dof 1) ((1 : ℚ) / 1) (fRowStory2LateralRungA8dof 1 2) (mRStory2LateralRungA8dof 2)] := rfl

theorem certStory2LateralRungA8dof_1 (hs_1_1 : ∀ i (hi : i < gsStory2LateralRungA8dof_1.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory2LateralRungA8dof_1.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory2LateralRungA8dof 1) gsStory2LateralRungA8dof_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GWStory2LateralRungA8dof1_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory2LateralRungA8dof_1 hs_1_1)
           | exact absurd hflag (by simp [fRowStory2LateralRungA8dof, story2_lateral_rung_a_8dof_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory2LateralRungA8dof_1 hs_1_2)
           | exact absurd hflag (by simp [fRowStory2LateralRungA8dof, story2_lateral_rung_a_8dof_coverNC])
       | q + 2, hm => simp at hm)
    | (intro m hm
       rw [GWStory2LateralRungA8dof1_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl <;> simp)

theorem story2_lateral_rung_a_8dof_throughout_MODER (hs_1_1 : ∀ i (hi : i < gsStory2LateralRungA8dof_1.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 1))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsStory2LateralRungA8dof_1.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_1[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 1)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_1.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsStory2LateralRungA8dof_1 ν →
      Covered (GWStory2LateralRungA8dof 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory2LateralRungA8dof 1) gsStory2LateralRungA8dof_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory2LateralRungA8dof_1 hs_1_1 hs_1_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 4 _ (by decide) ν hν

noncomputable def gsStory2LateralRungA8dof_2 : List (Term (Var 8)) :=
  hostComps vsStory2LateralRungA8dof 8 (((story2_lateral_rung_a_8dof_IR.invariants.find? (fun r => r.1 == "FLAT")).getD ("", Parse.PForm.tt)).2)

theorem GWStory2LateralRungA8dof2_modes_eq : (GWStory2LateralRungA8dof 2).modes =
    [realModeOf vsStory2LateralRungA8dof 8 (mLStory2LateralRungA8dof 2) ((1 : ℚ) / 1) (fRowStory2LateralRungA8dof 2 2) (mRStory2LateralRungA8dof 2)] := rfl

theorem certStory2LateralRungA8dof_2 (hs_2_2 : ∀ i (hi : i < gsStory2LateralRungA8dof_2.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_2[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_2[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_2[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_2.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWStory2LateralRungA8dof 2) gsStory2LateralRungA8dof_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GWStory2LateralRungA8dof2_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsStory2LateralRungA8dof_2 hs_2_2)
           | exact absurd hflag (by simp [fRowStory2LateralRungA8dof, story2_lateral_rung_a_8dof_coverNC])
       | q + 1, hm => simp at hm)
    | (intro m hm
       rw [GWStory2LateralRungA8dof2_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl <;> simp)

theorem story2_lateral_rung_a_8dof_throughout_FLAT (hs_2_2 : ∀ i (hi : i < gsStory2LateralRungA8dof_2.length),     z3solve (flowQuery ⟨gsStory2LateralRungA8dof_2[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsStory2LateralRungA8dof_2[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsStory2LateralRungA8dof_2[i],       hostDyn vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2), hostDyn vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsStory2LateralRungA8dof 8 Side.L (mLStory2LateralRungA8dof 2)) (hostEvolve vsStory2LateralRungA8dof 8 Side.R (mRStory2LateralRungA8dof 2))) (gsStory2LateralRungA8dof_2.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0], ∀ ν, InvAllHolds gsStory2LateralRungA8dof_2 ν →
      Covered (GWStory2LateralRungA8dof 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWStory2LateralRungA8dof 2) gsStory2LateralRungA8dof_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certStory2LateralRungA8dof_2 hs_2_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 3 _ (by decide) ν hν

end ThroughoutStory2LateralRungA8dof
end RelCertifier
