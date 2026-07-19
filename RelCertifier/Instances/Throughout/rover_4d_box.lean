/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.rover_4d_box
import RelCertifier.Instances.BenchIR.rover_4d_box

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRover4dBox
open DL Parse

def vsRover4dBox : List String := ["px", "py", "vx", "vy"]
def dummyRover4dBox : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRover4dBox (l : ℕ) : Parse.PMode := rover_4d_box_IR.L.modes.getD l dummyRover4dBox
def mRRover4dBox (q : ℕ) : Parse.PMode := rover_4d_box_IR.R.modes.getD q dummyRover4dBox
def fRowRover4dBox (l q : ℕ) : ModeFlagsE :=
  ((rover_4d_box_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRover4dBox (l : ℕ) : SearchGraph (Var 4) :=
  realGraphOf vsRover4dBox 4 rover_4d_box_IR (mLRover4dBox l)
    ((rover_4d_box_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover_4d_box_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover_4d_box_coverNC.pruned.contains (a, b))

noncomputable def gsRover4dBox_0 : List (Term (Var 4)) :=
  hostComps vsRover4dBox 4 (((rover_4d_box_IR.invariants.find? (fun r => r.1 == "HOLD")).getD ("", Parse.PForm.tt)).2)

theorem GWRover4dBox0_modes_eq : (GWRover4dBox 0).modes =
    [realModeOf vsRover4dBox 4 (mLRover4dBox 0) ((1 : ℚ) / 1) (fRowRover4dBox 0 0) (mRRover4dBox 0),
     realModeOf vsRover4dBox 4 (mLRover4dBox 0) ((1 : ℚ) / 1) (fRowRover4dBox 0 1) (mRRover4dBox 1)] := rfl

theorem certRover4dBox_0 (hs_0_0 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRover4dBox 0) gsRover4dBox_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover4dBox0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover4dBox_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover4dBox_0 hs_0_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover4dBox0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover4dBox, rover_4d_box_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover4dBox, rover_4d_box_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover4dBox0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover4dBox, rover_4d_box_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover4dBox, rover_4d_box_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover4dBox0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover4dBox_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover4dBox_0 hdp_0_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover4dBox0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover4dBox_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover4dBox_0 hdq_0_1
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWRover4dBox0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem rover_4d_box_throughout_HOLD (hs_0_0 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       hostDyn vsRover4dBox 4 Side.L (mLRover4dBox 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (hostGuard vsRover4dBox 4 Side.L (mLRover4dBox 0))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRover4dBox_0.length),     z3solve (flowQuery ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover4dBox_0[i],       (fun _ => Term.const 0), hostDyn vsRover4dBox 4 Side.R (mRRover4dBox 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover4dBox 4 Side.L (mLRover4dBox 0)) (hostEvolve vsRover4dBox 4 Side.R (mRRover4dBox 1))) (gsRover4dBox_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsRover4dBox_0 ν →
      Covered (GWRover4dBox 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRover4dBox 0) gsRover4dBox_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRover4dBox_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hdp_0_1 hdq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 4 _ (by decide) ν hν

end ThroughoutRover4dBox
end RelCertifier
