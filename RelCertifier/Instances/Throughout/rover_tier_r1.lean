/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRoverTierR1
open DL Parse

def vsRoverTierR1 : List String := ["s", "v", "a"]
def dummyRoverTierR1 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRoverTierR1 (l : ℕ) : Parse.PMode := rover_tier_r1_IR.L.modes.getD l dummyRoverTierR1
def mRRoverTierR1 (q : ℕ) : Parse.PMode := rover_tier_r1_IR.R.modes.getD q dummyRoverTierR1
def fRowRoverTierR1 (l q : ℕ) : ModeFlagsE :=
  ((rover_tier_r1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRoverTierR1 (l : ℕ) : SearchGraph (Var 3) :=
  realGraphOf vsRoverTierR1 3 rover_tier_r1_IR (mLRoverTierR1 l)
    ((rover_tier_r1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover_tier_r1_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover_tier_r1_coverNC.pruned.contains (a, b))

noncomputable def gsRoverTierR1_0 : List (Term (Var 3)) :=
  hostComps vsRoverTierR1 3 (((rover_tier_r1_IR.invariants.find? (fun r => r.1 == "Cruise")).getD ("", Parse.PForm.tt)).2)

theorem GWRoverTierR10_modes_eq : (GWRoverTierR1 0).modes =
    [realModeOf vsRoverTierR1 3 (mLRoverTierR1 0) ((23 : ℚ) / 4) (fRowRoverTierR1 0 0) (mRRoverTierR1 0)] := rfl

theorem certRoverTierR1_0 (hs_0_0 : ∀ i (hi : i < gsRoverTierR1_0.length),     z3solve (flowQuery ⟨gsRoverTierR1_0[i],       hostDyn vsRoverTierR1 3 Side.L (mLRoverTierR1 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const (((23 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverTierR1_0[i],       hostDyn vsRoverTierR1 3 Side.L (mLRoverTierR1 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const (((23 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverTierR1_0[i],       hostDyn vsRoverTierR1 3 Side.L (mLRoverTierR1 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const (((23 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverTierR1_0.length),     z3solve (flowQuery ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (hostGuard vsRoverTierR1 3 Side.L (mLRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (hostGuard vsRoverTierR1 3 Side.L (mLRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (hostGuard vsRoverTierR1 3 Side.L (mLRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverTierR1_0.length),     z3solve (flowQuery ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRoverTierR1 0) gsRoverTierR1_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverTierR10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverTierR1_0 hs_0_0
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverTierR10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverTierR1, rover_tier_r1_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverTierR10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverTierR1, rover_tier_r1_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverTierR10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverTierR1_0 hdp_0_0
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverTierR10_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverTierR1_0 hdq_0_0
    | q + 1, hm => simp at hm
  · intro m hm
    rw [GWRoverTierR10_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl <;> simp

theorem rover_tier_r1_throughout_Cruise (hs_0_0 : ∀ i (hi : i < gsRoverTierR1_0.length),     z3solve (flowQuery ⟨gsRoverTierR1_0[i],       hostDyn vsRoverTierR1 3 Side.L (mLRoverTierR1 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const (((23 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverTierR1_0[i],       hostDyn vsRoverTierR1 3 Side.L (mLRoverTierR1 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const (((23 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverTierR1_0[i],       hostDyn vsRoverTierR1 3 Side.L (mLRoverTierR1 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const (((23 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRoverTierR1_0.length),     z3solve (flowQuery ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (hostGuard vsRoverTierR1 3 Side.L (mLRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (hostGuard vsRoverTierR1 3 Side.L (mLRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (hostGuard vsRoverTierR1 3 Side.L (mLRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRoverTierR1_0.length),     z3solve (flowQuery ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverTierR1_0[i],       (fun _ => Term.const 0), hostDyn vsRoverTierR1 3 Side.R (mRRoverTierR1 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRoverTierR1 3 Side.L (mLRoverTierR1 0)) (hostEvolve vsRoverTierR1 3 Side.R (mRRoverTierR1 0))) (gsRoverTierR1_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0], ∀ ν, InvAllHolds gsRoverTierR1_0 ν →
      Covered (GWRoverTierR1 0) ⟨q0, 6, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRoverTierR1 0) gsRoverTierR1_0 ⟨q0, 6, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRoverTierR1_0 hs_0_0 hdp_0_0 hdq_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 13 _ (by decide) ν hν

end ThroughoutRoverTierR1
end RelCertifier
