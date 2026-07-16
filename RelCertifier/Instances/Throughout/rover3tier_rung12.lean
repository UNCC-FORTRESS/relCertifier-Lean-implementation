/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRover3tierRung12
open DL Parse

def vsRover3tierRung12 : List String := ["v", "s", "a"]
def dummyRover3tierRung12 : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRover3tierRung12 (l : ℕ) : Parse.PMode := rover3tier_rung12_IR.L.modes.getD l dummyRover3tierRung12
def mRRover3tierRung12 (q : ℕ) : Parse.PMode := rover3tier_rung12_IR.R.modes.getD q dummyRover3tierRung12
def fRowRover3tierRung12 (l q : ℕ) : ModeFlagsE :=
  ((rover3tier_rung12_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRover3tierRung12 (l : ℕ) : SearchGraph (Var 3) :=
  realGraphOf vsRover3tierRung12 3 rover3tier_rung12_IR (mLRover3tierRung12 l)
    ((rover3tier_rung12_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover3tier_rung12_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover3tier_rung12_coverNC.pruned.contains (a, b))

noncomputable def gsRover3tierRung12_0 : List (Term (Var 3)) :=
  hostComps vsRover3tierRung12 3 (((rover3tier_rung12_IR.invariants.find? (fun r => r.1 == "ACCEL")).getD ("", Parse.PForm.tt)).2)

theorem GWRover3tierRung120_modes_eq : (GWRover3tierRung12 0).modes =
    [realModeOf vsRover3tierRung12 3 (mLRover3tierRung12 0) ((2 : ℚ) / 1) (fRowRover3tierRung12 0 0) (mRRover3tierRung12 0),
     realModeOf vsRover3tierRung12 3 (mLRover3tierRung12 0) ((2 : ℚ) / 1) (fRowRover3tierRung12 0 1) (mRRover3tierRung12 1)] := rfl

theorem certRover3tierRung12_0 (hs_0_0 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsRover3tierRung12_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostGuard vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRover3tierRung12 0) gsRover3tierRung12_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_0 hs_0_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover3tierRung12, rover3tier_rung12_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsRover3tierRung12_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover3tierRung12, rover3tier_rung12_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover3tierRung12, rover3tier_rung12_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_0 hdp_0_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung120_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_0 hdq_0_1
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWRover3tierRung120_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem rover3tier_rung12_throughout_ACCEL (hs_0_0 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((2 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsRover3tierRung12_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostGuard vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsRover3tierRung12_0.length),     z3solve (flowQuery ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_0[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 0)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsRover3tierRung12_0 ν →
      Covered (GWRover3tierRung12 0) ⟨q0, 7, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRover3tierRung12 0) gsRover3tierRung12_0 ⟨q0, 7, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRover3tierRung12_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hr_0_1 hdp_0_1 hdq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 22 _ (by decide) ν hν

noncomputable def gsRover3tierRung12_1 : List (Term (Var 3)) :=
  hostComps vsRover3tierRung12 3 (((rover3tier_rung12_IR.invariants.find? (fun r => r.1 == "COAST")).getD ("", Parse.PForm.tt)).2)

theorem GWRover3tierRung121_modes_eq : (GWRover3tierRung12 1).modes =
    [realModeOf vsRover3tierRung12 3 (mLRover3tierRung12 1) ((1 : ℚ) / 1) (fRowRover3tierRung12 1 0) (mRRover3tierRung12 0),
     realModeOf vsRover3tierRung12 3 (mLRover3tierRung12 1) ((1 : ℚ) / 1) (fRowRover3tierRung12 1 1) (mRRover3tierRung12 1)] := rfl

theorem certRover3tierRung12_1 (hs_1_0 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRover3tierRung12 1) gsRover3tierRung12_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_1 hs_1_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover3tierRung12, rover3tier_rung12_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover3tierRung12, rover3tier_rung12_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover3tierRung12, rover3tier_rung12_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRover3tierRung12, rover3tier_rung12_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_1 hdp_1_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRover3tierRung121_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRover3tierRung12_1 hdq_1_1
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWRover3tierRung121_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem rover3tier_rung12_throughout_COAST (hs_1_0 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 0))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       hostDyn vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (hostGuard vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsRover3tierRung12_1.length),     z3solve (flowQuery ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRover3tierRung12_1[i],       (fun _ => Term.const 0), hostDyn vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsRover3tierRung12 3 Side.L (mLRover3tierRung12 1)) (hostEvolve vsRover3tierRung12 3 Side.R (mRRover3tierRung12 1))) (gsRover3tierRung12_1.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsRover3tierRung12_1 ν →
      Covered (GWRover3tierRung12 1) ⟨q0, 4, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRover3tierRung12 1) gsRover3tierRung12_1 ⟨q0, 4, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRover3tierRung12_1 hs_1_0 hdp_1_0 hdq_1_0 hs_1_1 hdp_1_1 hdq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 13 _ (by decide) ν hν

end ThroughoutRover3tierRung12
end RelCertifier
