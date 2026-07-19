/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.watertank
import RelCertifier.Instances.BenchIR.watertank

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutWatertank
open DL Parse

def vsWatertank : List String := ["x"]
def dummyWatertank : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLWatertank (l : ℕ) : Parse.PMode := watertank_IR.L.modes.getD l dummyWatertank
def mRWatertank (q : ℕ) : Parse.PMode := watertank_IR.R.modes.getD q dummyWatertank
def fRowWatertank (l q : ℕ) : ModeFlagsE :=
  ((watertank_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWWatertank (l : ℕ) : SearchGraph (Var 1) :=
  realGraphOf vsWatertank 1 watertank_IR (mLWatertank l)
    ((watertank_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((watertank_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => watertank_coverNC.pruned.contains (a, b))

noncomputable def gsWatertank_0 : List (Term (Var 1)) :=
  hostComps vsWatertank 1 (((watertank_IR.invariants.find? (fun r => r.1 == "Low")).getD ("", Parse.PForm.tt)).2)

theorem GWWatertank0_modes_eq : (GWWatertank 0).modes =
    [realModeOf vsWatertank 1 (mLWatertank 0) ((1 : ℚ) / 1) (fRowWatertank 0 0) (mRWatertank 0),
     realModeOf vsWatertank 1 (mLWatertank 0) ((1 : ℚ) / 1) (fRowWatertank 0 1) (mRWatertank 1),
     realModeOf vsWatertank 1 (mLWatertank 0) ((1 : ℚ) / 1) (fRowWatertank 0 2) (mRWatertank 2)] := rfl

theorem certWatertank_0 (hs_0_0 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsWatertank_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsWatertank 1 Side.L (mLWatertank 0)) (hostGuard vsWatertank 1 Side.R (mRWatertank 1))) (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsWatertank_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsWatertank 1 Side.L (mLWatertank 0)) (hostGuard vsWatertank 1 Side.R (mRWatertank 2))) (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWWatertank 0) gsWatertank_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsWatertank_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsWatertank_0 _ (fun g hg => z3_unsat_sound (hr_0_2 g hg))
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWWatertank0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem watertank_throughout_Low (hs_0_0 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsWatertank_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsWatertank 1 Side.L (mLWatertank 0)) (hostGuard vsWatertank 1 Side.R (mRWatertank 1))) (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 0))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsWatertank_0.length),     z3solve (flowQuery ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_0[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsWatertank_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsWatertank 1 Side.L (mLWatertank 0)) (hostGuard vsWatertank 1 Side.R (mRWatertank 2))) (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 0)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsWatertank_0 ν →
      Covered (GWWatertank 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWWatertank 0) gsWatertank_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certWatertank_0 hs_0_0 hs_0_1 hr_0_1 hdp_0_1 hdq_0_1 hr_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

noncomputable def gsWatertank_1 : List (Term (Var 1)) :=
  hostComps vsWatertank 1 (((watertank_IR.invariants.find? (fun r => r.1 == "Mid")).getD ("", Parse.PForm.tt)).2)

theorem GWWatertank1_modes_eq : (GWWatertank 1).modes =
    [realModeOf vsWatertank 1 (mLWatertank 1) ((1 : ℚ) / 1) (fRowWatertank 1 1) (mRWatertank 1),
     realModeOf vsWatertank 1 (mLWatertank 1) ((1 : ℚ) / 1) (fRowWatertank 1 2) (mRWatertank 2)] := rfl

theorem certWatertank_1 (hs_1_1 : ∀ i (hi : i < gsWatertank_1.length),     z3solve (flowQuery ⟨gsWatertank_1[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 1), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_1[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 1), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_1[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 1), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsWatertank_1.length),     z3solve (flowQuery ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsWatertank_1.length),     z3solve (flowQuery ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsWatertank_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsWatertank 1 Side.L (mLWatertank 1)) (hostGuard vsWatertank 1 Side.R (mRWatertank 2))) (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWWatertank 1) gsWatertank_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_1 hs_1_1
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsWatertank_1 _ (fun g hg => z3_unsat_sound (hr_1_2 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_1 hdp_1_1
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_1 hdq_1_1
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWWatertank1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem watertank_throughout_Mid (hs_1_1 : ∀ i (hi : i < gsWatertank_1.length),     z3solve (flowQuery ⟨gsWatertank_1[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 1), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_1[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 1), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_1[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 1), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsWatertank_1.length),     z3solve (flowQuery ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsWatertank_1.length),     z3solve (flowQuery ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_1[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsWatertank_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsWatertank 1 Side.L (mLWatertank 1)) (hostGuard vsWatertank 1 Side.R (mRWatertank 2))) (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 1)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsWatertank_1 ν →
      Covered (GWWatertank 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWWatertank 1) gsWatertank_1 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certWatertank_1 hs_1_1 hdp_1_1 hdq_1_1 hr_1_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 4 _ (by decide) ν hν

noncomputable def gsWatertank_2 : List (Term (Var 1)) :=
  hostComps vsWatertank 1 (((watertank_IR.invariants.find? (fun r => r.1 == "High")).getD ("", Parse.PForm.tt)).2)

theorem GWWatertank2_modes_eq : (GWWatertank 2).modes =
    [realModeOf vsWatertank 1 (mLWatertank 2) ((1 : ℚ) / 1) (fRowWatertank 2 0) (mRWatertank 0),
     realModeOf vsWatertank 1 (mLWatertank 2) ((1 : ℚ) / 1) (fRowWatertank 2 1) (mRWatertank 1),
     realModeOf vsWatertank 1 (mLWatertank 2) ((1 : ℚ) / 1) (fRowWatertank 2 2) (mRWatertank 2)] := rfl

theorem certWatertank_2 (hs_2_0 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWWatertank 2) gsWatertank_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_2 hs_2_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_2 hs_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_2 hs_2_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_2 hdp_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWWatertank2_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsWatertank_2 hdq_2_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowWatertank, watertank_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWWatertank2_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem watertank_throughout_High (hs_2_0 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 0))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hs_2_1 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hdp_2_1 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (hostGuard vsWatertank 1 Side.L (mLWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hdq_2_1 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       (fun _ => Term.const 0), hostDyn vsWatertank 1 Side.R (mRWatertank 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 1))) (gsWatertank_2.take i)⟩) = Verdict.unsat) (hs_2_2 : ∀ i (hi : i < gsWatertank_2.length),     z3solve (flowQuery ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsWatertank_2[i],       hostDyn vsWatertank 1 Side.L (mLWatertank 2), hostDyn vsWatertank 1 Side.R (mRWatertank 2), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsWatertank 1 Side.L (mLWatertank 2)) (hostEvolve vsWatertank 1 Side.R (mRWatertank 2))) (gsWatertank_2.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [2], ∀ ν, InvAllHolds gsWatertank_2 ν →
      Covered (GWWatertank 2) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWWatertank 2) gsWatertank_2 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certWatertank_2 hs_2_0 hs_2_1 hdp_2_1 hdq_2_1 hs_2_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

end ThroughoutWatertank
end RelCertifier
