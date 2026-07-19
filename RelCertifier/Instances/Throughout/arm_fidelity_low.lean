/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.arm_fidelity_low
import RelCertifier.Instances.BenchIR.arm_fidelity_low

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutArmFidelityLow
open DL Parse

def vsArmFidelityLow : List String := ["theta", "v"]
def dummyArmFidelityLow : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLArmFidelityLow (l : ℕ) : Parse.PMode := arm_fidelity_low_IR.L.modes.getD l dummyArmFidelityLow
def mRArmFidelityLow (q : ℕ) : Parse.PMode := arm_fidelity_low_IR.R.modes.getD q dummyArmFidelityLow
def fRowArmFidelityLow (l q : ℕ) : ModeFlagsE :=
  ((arm_fidelity_low_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWArmFidelityLow (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsArmFidelityLow 2 arm_fidelity_low_IR (mLArmFidelityLow l)
    ((arm_fidelity_low_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((arm_fidelity_low_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => arm_fidelity_low_coverNC.pruned.contains (a, b))

noncomputable def gsArmFidelityLow_0 : List (Term (Var 2)) :=
  hostComps vsArmFidelityLow 2 (((arm_fidelity_low_IR.invariants.find? (fun r => r.1 == "Accelerate")).getD ("", Parse.PForm.tt)).2)

theorem GWArmFidelityLow0_modes_eq : (GWArmFidelityLow 0).modes =
    [realModeOf vsArmFidelityLow 2 (mLArmFidelityLow 0) ((5 : ℚ) / 1) (fRowArmFidelityLow 0 0) (mRArmFidelityLow 0),
     realModeOf vsArmFidelityLow 2 (mLArmFidelityLow 0) ((5 : ℚ) / 1) (fRowArmFidelityLow 0 1) (mRArmFidelityLow 1)] := rfl

theorem certArmFidelityLow_0 (hs_0_0 : ∀ i (hi : i < gsArmFidelityLow_0.length),     z3solve (flowQuery ⟨gsArmFidelityLow_0[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_0[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_0[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmFidelityLow_0.length),     z3solve (flowQuery ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmFidelityLow_0.length),     z3solve (flowQuery ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmFidelityLow_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1))) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsArmFidelityLow_0, z3solve (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWArmFidelityLow 0) gsArmFidelityLow_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityLow_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmFidelityLow_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmFidelityLow_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityLow_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityLow_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWArmFidelityLow0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem arm_fidelity_low_throughout_Accelerate (hs_0_0 : ∀ i (hi : i < gsArmFidelityLow_0.length),     z3solve (flowQuery ⟨gsArmFidelityLow_0[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_0[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_0[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsArmFidelityLow_0.length),     z3solve (flowQuery ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsArmFidelityLow_0.length),     z3solve (flowQuery ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_0[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsArmFidelityLow_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1))) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsArmFidelityLow_0, z3solve (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 0)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsArmFidelityLow_0 ν →
      Covered (GWArmFidelityLow 0) ⟨q0, 5, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWArmFidelityLow 0) gsArmFidelityLow_0 ⟨q0, 5, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certArmFidelityLow_0 hs_0_0 hdp_0_0 hdq_0_0 hr_0_1 hq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 16 _ (by decide) ν hν

noncomputable def gsArmFidelityLow_1 : List (Term (Var 2)) :=
  hostComps vsArmFidelityLow 2 (((arm_fidelity_low_IR.invariants.find? (fun r => r.1 == "Brake")).getD ("", Parse.PForm.tt)).2)

theorem GWArmFidelityLow1_modes_eq : (GWArmFidelityLow 1).modes =
    [realModeOf vsArmFidelityLow 2 (mLArmFidelityLow 1) ((5 : ℚ) / 1) (fRowArmFidelityLow 1 0) (mRArmFidelityLow 0),
     realModeOf vsArmFidelityLow 2 (mLArmFidelityLow 1) ((5 : ℚ) / 1) (fRowArmFidelityLow 1 1) (mRArmFidelityLow 1)] := rfl

theorem certArmFidelityLow_1 (hs_1_0 : ∀ i (hi : i < gsArmFidelityLow_1.length),     z3solve (flowQuery ⟨gsArmFidelityLow_1[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_1[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_1[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmFidelityLow_1.length),     z3solve (flowQuery ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmFidelityLow_1.length),     z3solve (flowQuery ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsArmFidelityLow_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1))) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsArmFidelityLow_1, z3solve (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWArmFidelityLow 1) gsArmFidelityLow_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityLow_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsArmFidelityLow_1 _ (fun g hg => z3_unsat_sound (hr_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsArmFidelityLow_1 _ (fun g hg => z3_unsat_sound (hq_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityLow_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWArmFidelityLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsArmFidelityLow_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowArmFidelityLow, arm_fidelity_low_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWArmFidelityLow1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem arm_fidelity_low_throughout_Brake (hs_1_0 : ∀ i (hi : i < gsArmFidelityLow_1.length),     z3solve (flowQuery ⟨gsArmFidelityLow_1[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_1[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_1[i],       hostDyn vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsArmFidelityLow_1.length),     z3solve (flowQuery ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsArmFidelityLow_1.length),     z3solve (flowQuery ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsArmFidelityLow_1[i],       (fun _ => Term.const 0), hostDyn vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 0))) (gsArmFidelityLow_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsArmFidelityLow_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1))) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsArmFidelityLow_1, z3solve (Formula.and (Formula.and (hostGuard vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)) (Formula.and (hostEvolve vsArmFidelityLow 2 Side.L (mLArmFidelityLow 1)) (hostEvolve vsArmFidelityLow 2 Side.R (mRArmFidelityLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsArmFidelityLow_1 ν →
      Covered (GWArmFidelityLow 1) ⟨q0, 5, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWArmFidelityLow 1) gsArmFidelityLow_1 ⟨q0, 5, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certArmFidelityLow_1 hs_1_0 hdp_1_0 hdq_1_0 hr_1_1 hq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 16 _ (by decide) ν hν

end ThroughoutArmFidelityLow
end RelCertifier
