/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutPlantFanLow
open DL Parse

def vsPlantFanLow : List String := ["theta", "v"]
def dummyPlantFanLow : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLPlantFanLow (l : ℕ) : Parse.PMode := plant_fan_low_IR.L.modes.getD l dummyPlantFanLow
def mRPlantFanLow (q : ℕ) : Parse.PMode := plant_fan_low_IR.R.modes.getD q dummyPlantFanLow
def fRowPlantFanLow (l q : ℕ) : ModeFlagsE :=
  ((plant_fan_low_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWPlantFanLow (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsPlantFanLow 2 plant_fan_low_IR (mLPlantFanLow l)
    ((plant_fan_low_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((plant_fan_low_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => plant_fan_low_coverNC.pruned.contains (a, b))

noncomputable def gsPlantFanLow_0 : List (Term (Var 2)) :=
  hostComps vsPlantFanLow 2 (((plant_fan_low_IR.invariants.find? (fun r => r.1 == "Accelerate")).getD ("", Parse.PForm.tt)).2)

theorem GWPlantFanLow0_modes_eq : (GWPlantFanLow 0).modes =
    [realModeOf vsPlantFanLow 2 (mLPlantFanLow 0) ((5 : ℚ) / 1) (fRowPlantFanLow 0 0) (mRPlantFanLow 0),
     realModeOf vsPlantFanLow 2 (mLPlantFanLow 0) ((5 : ℚ) / 1) (fRowPlantFanLow 0 1) (mRPlantFanLow 1)] := rfl

theorem certPlantFanLow_0 (hs_0_0 : ∀ i (hi : i < gsPlantFanLow_0.length),     z3solve (flowQuery ⟨gsPlantFanLow_0[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_0[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_0[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsPlantFanLow_0.length),     z3solve (flowQuery ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsPlantFanLow_0.length),     z3solve (flowQuery ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsPlantFanLow_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1))) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsPlantFanLow_0, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1)) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWPlantFanLow 0) gsPlantFanLow_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanLow_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanLow_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanLow_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanLow_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanLow_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWPlantFanLow0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem plant_fan_low_throughout_Accelerate (hs_0_0 : ∀ i (hi : i < gsPlantFanLow_0.length),     z3solve (flowQuery ⟨gsPlantFanLow_0[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_0[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_0[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsPlantFanLow_0.length),     z3solve (flowQuery ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsPlantFanLow_0.length),     z3solve (flowQuery ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsPlantFanLow_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1))) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsPlantFanLow_0, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1)) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 0)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsPlantFanLow_0 ν →
      Covered (GWPlantFanLow 0) ⟨q0, 5, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWPlantFanLow 0) gsPlantFanLow_0 ⟨q0, 5, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certPlantFanLow_0 hs_0_0 hdp_0_0 hdq_0_0 hr_0_1 hq_0_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 16 _ (by decide) ν hν

noncomputable def gsPlantFanLow_1 : List (Term (Var 2)) :=
  hostComps vsPlantFanLow 2 (((plant_fan_low_IR.invariants.find? (fun r => r.1 == "Brake")).getD ("", Parse.PForm.tt)).2)

theorem GWPlantFanLow1_modes_eq : (GWPlantFanLow 1).modes =
    [realModeOf vsPlantFanLow 2 (mLPlantFanLow 1) ((5 : ℚ) / 1) (fRowPlantFanLow 1 0) (mRPlantFanLow 0),
     realModeOf vsPlantFanLow 2 (mLPlantFanLow 1) ((5 : ℚ) / 1) (fRowPlantFanLow 1 1) (mRPlantFanLow 1)] := rfl

theorem certPlantFanLow_1 (hs_1_0 : ∀ i (hi : i < gsPlantFanLow_1.length),     z3solve (flowQuery ⟨gsPlantFanLow_1[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 1), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_1[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 1), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_1[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 1), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsPlantFanLow_1.length),     z3solve (flowQuery ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsPlantFanLow_1.length),     z3solve (flowQuery ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsPlantFanLow_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1))) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsPlantFanLow_1, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1)) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWPlantFanLow 1) gsPlantFanLow_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanLow_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanLow_1 _ (fun g hg => z3_unsat_sound (hr_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanLow_1 _ (fun g hg => z3_unsat_sound (hq_1_1 g hg))
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanLow_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | q + 2, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanLow1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanLow_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanLow, plant_fan_low_coverNC])
    | q + 2, hm => simp at hm
  · intro m hm
    rw [GWPlantFanLow1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem plant_fan_low_throughout_Brake (hs_1_0 : ∀ i (hi : i < gsPlantFanLow_1.length),     z3solve (flowQuery ⟨gsPlantFanLow_1[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 1), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_1[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 1), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_1[i],       hostDyn vsPlantFanLow 2 Side.L (mLPlantFanLow 1), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const (((5 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsPlantFanLow_1.length),     z3solve (flowQuery ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsPlantFanLow_1.length),     z3solve (flowQuery ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanLow_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanLow 2 Side.R (mRPlantFanLow 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 0))) (gsPlantFanLow_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsPlantFanLow_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1))) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsPlantFanLow_1, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanLow 2 Side.R (mRPlantFanLow 1)) (Formula.and (hostEvolve vsPlantFanLow 2 Side.L (mLPlantFanLow 1)) (hostEvolve vsPlantFanLow 2 Side.R (mRPlantFanLow 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsPlantFanLow_1 ν →
      Covered (GWPlantFanLow 1) ⟨q0, 5, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWPlantFanLow 1) gsPlantFanLow_1 ⟨q0, 5, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certPlantFanLow_1 hs_1_0 hdp_1_0 hdq_1_0 hr_1_1 hq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl <;>
    exact check_sound_multi _ _ cert 16 _ (by decide) ν hν

end ThroughoutPlantFanLow
end RelCertifier
