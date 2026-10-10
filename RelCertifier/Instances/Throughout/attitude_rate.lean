/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.attitude_rate
import RelCertifier.Instances.BenchIR.attitude_rate

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutAttitudeRate
open DL Parse

def vsAttitudeRate : List String := ["phi", "p", "theta", "q", "psi", "r"]
def dummyAttitudeRate : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLAttitudeRate (l : ℕ) : Parse.PMode := attitude_rate_IR.L.modes.getD l dummyAttitudeRate
def mRAttitudeRate (q : ℕ) : Parse.PMode := attitude_rate_IR.R.modes.getD q dummyAttitudeRate
def fRowAttitudeRate (l q : ℕ) : ModeFlagsE :=
  ((attitude_rate_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false⟩)
noncomputable def GWAttitudeRate (l : ℕ) : SearchGraph (Var 6) :=
  realGraphOf vsAttitudeRate 6 attitude_rate_IR (mLAttitudeRate l)
    ((attitude_rate_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((attitude_rate_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => attitude_rate_coverNC.pruned.contains (a, b))

noncomputable def gsAttitudeRate_0 : List (Term (Var 6)) :=
  hostComps vsAttitudeRate 6 (((attitude_rate_IR.invariants.find? (fun r => r.1 == "CRUISE")).getD ("", Parse.PForm.tt)).2)

theorem GWAttitudeRate0_modes_eq : (GWAttitudeRate 0).modes =
    [realModeOf vsAttitudeRate 6 (mLAttitudeRate 0) ((2 : ℚ) / 1) (fRowAttitudeRate 0 0) (mRAttitudeRate 0),
     realModeOf vsAttitudeRate 6 (mLAttitudeRate 0) ((2 : ℚ) / 1) (fRowAttitudeRate 0 1) (mRAttitudeRate 1)] := rfl

theorem certAttitudeRate_0 (hs_0_0 : ∀ i (hi : i < gsAttitudeRate_0.length),     z3solve (flowQuery ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 0))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 0))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 0))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsAttitudeRate_0.length),     z3solve (flowQuery ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 1))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 1))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 1))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWAttitudeRate 0) gsAttitudeRate_0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWAttitudeRate0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsAttitudeRate_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsAttitudeRate_0 hs_0_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWAttitudeRate0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowAttitudeRate, attitude_rate_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowAttitudeRate, attitude_rate_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWAttitudeRate0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowAttitudeRate, attitude_rate_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowAttitudeRate, attitude_rate_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWAttitudeRate0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem attitude_rate_throughout_CRUISE (hs_0_0 : ∀ i (hi : i < gsAttitudeRate_0.length),     z3solve (flowQuery ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 0))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 0))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 0))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsAttitudeRate_0.length),     z3solve (flowQuery ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 1))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 1))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsAttitudeRate_0[i],       hostDyn vsAttitudeRate 6 Side.L (mLAttitudeRate 0), hostDyn vsAttitudeRate 6 Side.R (mRAttitudeRate 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsAttitudeRate 6 Side.L (mLAttitudeRate 0)) (hostEvolve vsAttitudeRate 6 Side.R (mRAttitudeRate 1))) (gsAttitudeRate_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsAttitudeRate_0 ν →
      Covered (GWAttitudeRate 0) ⟨q0, 2, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWAttitudeRate 0) gsAttitudeRate_0 ⟨q0, 2, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certAttitudeRate_0 hs_0_0 hs_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 7 _ (by decide) ν hν

end ThroughoutAttitudeRate
end RelCertifier
