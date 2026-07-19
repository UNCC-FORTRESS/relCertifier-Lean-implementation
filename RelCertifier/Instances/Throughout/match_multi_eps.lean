/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.match_multi_eps
import RelCertifier.Instances.BenchIR.match_multi_eps

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutMatchMultiEps
open DL Parse

def vsMatchMultiEps : List String := ["v", "s"]
def dummyMatchMultiEps : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLMatchMultiEps (l : ℕ) : Parse.PMode := match_multi_eps_IR.L.modes.getD l dummyMatchMultiEps
def mRMatchMultiEps (q : ℕ) : Parse.PMode := match_multi_eps_IR.R.modes.getD q dummyMatchMultiEps
def fRowMatchMultiEps (l q : ℕ) : ModeFlagsE :=
  ((match_multi_eps_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWMatchMultiEps (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsMatchMultiEps 2 match_multi_eps_IR (mLMatchMultiEps l)
    ((match_multi_eps_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((match_multi_eps_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => match_multi_eps_coverNC.pruned.contains (a, b))

noncomputable def gsMatchMultiEps_0 : List (Term (Var 2)) :=
  hostComps vsMatchMultiEps 2 (((match_multi_eps_IR.invariants.find? (fun r => r.1 == "ACCEL")).getD ("", Parse.PForm.tt)).2)

theorem GWMatchMultiEps0_modes_eq : (GWMatchMultiEps 0).modes =
    [realModeOf vsMatchMultiEps 2 (mLMatchMultiEps 0) ((1 : ℚ) / 1) (fRowMatchMultiEps 0 0) (mRMatchMultiEps 0),
     realModeOf vsMatchMultiEps 2 (mLMatchMultiEps 0) ((1 : ℚ) / 1) (fRowMatchMultiEps 0 1) (mRMatchMultiEps 1)] := rfl

theorem certMatchMultiEps_0 (hs_0_0 : ∀ i (hi : i < gsMatchMultiEps_0.length),     z3solve (flowQuery ⟨gsMatchMultiEps_0[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsMatchMultiEps_0[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsMatchMultiEps_0[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsMatchMultiEps_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsMatchMultiEps_0, z3solve (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWMatchMultiEps 0) gsMatchMultiEps_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsMatchMultiEps_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsMatchMultiEps_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsMatchMultiEps_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWMatchMultiEps0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem match_multi_eps_throughout_ACCEL (hs_0_0 : ∀ i (hi : i < gsMatchMultiEps_0.length),     z3solve (flowQuery ⟨gsMatchMultiEps_0[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsMatchMultiEps_0[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsMatchMultiEps_0[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsMatchMultiEps_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsMatchMultiEps_0, z3solve (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 0)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsMatchMultiEps_0 ν →
      Covered (GWMatchMultiEps 0) ⟨q0, 4, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWMatchMultiEps 0) gsMatchMultiEps_0 ⟨q0, 4, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certMatchMultiEps_0 hs_0_0 hr_0_1 hq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 13 _ (by decide) ν hν

noncomputable def gsMatchMultiEps_1 : List (Term (Var 2)) :=
  hostComps vsMatchMultiEps 2 (((match_multi_eps_IR.invariants.find? (fun r => r.1 == "COAST")).getD ("", Parse.PForm.tt)).2)

theorem GWMatchMultiEps1_modes_eq : (GWMatchMultiEps 1).modes =
    [realModeOf vsMatchMultiEps 2 (mLMatchMultiEps 1) ((1 : ℚ) / 1) (fRowMatchMultiEps 1 0) (mRMatchMultiEps 0),
     realModeOf vsMatchMultiEps 2 (mLMatchMultiEps 1) ((1 : ℚ) / 1) (fRowMatchMultiEps 1 1) (mRMatchMultiEps 1)] := rfl

theorem certMatchMultiEps_1 (hs_1_0 : ∀ i (hi : i < gsMatchMultiEps_1.length),     z3solve (flowQuery ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsMatchMultiEps_1.length),     z3solve (flowQuery ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsMatchMultiEps_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsMatchMultiEps_1, z3solve (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWMatchMultiEps 1) gsMatchMultiEps_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsMatchMultiEps_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsMatchMultiEps_1 hs_1_1
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsMatchMultiEps_1 _ (fun g hg => z3_unsat_sound (hr_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsMatchMultiEps_1 _ (fun g hg => z3_unsat_sound (hq_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWMatchMultiEps1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowMatchMultiEps, match_multi_eps_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWMatchMultiEps1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem match_multi_eps_throughout_COAST (hs_1_0 : ∀ i (hi : i < gsMatchMultiEps_1.length),     z3solve (flowQuery ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 0))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsMatchMultiEps_1.length),     z3solve (flowQuery ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsMatchMultiEps_1[i],       hostDyn vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1), hostDyn vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (gsMatchMultiEps_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsMatchMultiEps_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1))) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsMatchMultiEps_1, z3solve (Formula.and (Formula.and (hostGuard vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)) (Formula.and (hostEvolve vsMatchMultiEps 2 Side.L (mLMatchMultiEps 1)) (hostEvolve vsMatchMultiEps 2 Side.R (mRMatchMultiEps 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsMatchMultiEps_1 ν →
      Covered (GWMatchMultiEps 1) ⟨q0, 4, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWMatchMultiEps 1) gsMatchMultiEps_1 ⟨q0, 4, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certMatchMultiEps_1 hs_1_0 hs_1_1 hr_1_1 hq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 13 _ (by decide) ν hν

end ThroughoutMatchMultiEps
end RelCertifier
