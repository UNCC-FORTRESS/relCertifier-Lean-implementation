/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutPlantFanMid
open DL Parse

def vsPlantFanMid : List String := ["theta", "v"]
def dummyPlantFanMid : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLPlantFanMid (l : ℕ) : Parse.PMode := plant_fan_mid_IR.L.modes.getD l dummyPlantFanMid
def mRPlantFanMid (q : ℕ) : Parse.PMode := plant_fan_mid_IR.R.modes.getD q dummyPlantFanMid
def fRowPlantFanMid (l q : ℕ) : ModeFlagsE :=
  ((plant_fan_mid_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWPlantFanMid (l : ℕ) : SearchGraph (Var 2) :=
  realGraphOf vsPlantFanMid 2 plant_fan_mid_IR (mLPlantFanMid l)
    ((plant_fan_mid_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((plant_fan_mid_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => plant_fan_mid_coverNC.pruned.contains (a, b))

noncomputable def gsPlantFanMid_0 : List (Term (Var 2)) :=
  hostComps vsPlantFanMid 2 (((plant_fan_mid_IR.invariants.find? (fun r => r.1 == "Accelerate")).getD ("", Parse.PForm.tt)).2)

theorem GWPlantFanMid0_modes_eq : (GWPlantFanMid 0).modes =
    [realModeOf vsPlantFanMid 2 (mLPlantFanMid 0) ((15 : ℚ) / 4) (fRowPlantFanMid 0 0) (mRPlantFanMid 0),
     realModeOf vsPlantFanMid 2 (mLPlantFanMid 0) ((15 : ℚ) / 4) (fRowPlantFanMid 0 1) (mRPlantFanMid 1),
     realModeOf vsPlantFanMid 2 (mLPlantFanMid 0) ((15 : ℚ) / 4) (fRowPlantFanMid 0 2) (mRPlantFanMid 2)] := rfl

theorem certPlantFanMid_0 (hs_0_0 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWPlantFanMid 0) gsPlantFanMid_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_0 hs_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_0 hs_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_0 hs_0_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanMid_0 _ (fun g hg => z3_unsat_sound (hr_0_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanMid_0 _ (fun g hg => z3_unsat_sound (hr_0_2 g hg))
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanMid_0 _ (fun g hg => z3_unsat_sound (hq_0_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanMid_0 _ (fun g hg => z3_unsat_sound (hq_0_2 g hg))
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_0 hdp_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_0 hdp_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_0 hdq_0_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_0 hdq_0_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWPlantFanMid0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem plant_fan_mid_throughout_Accelerate (hs_0_0 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hdp_0_0 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hdq_0_0 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hs_0_1 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hr_0_1 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_1 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_0_1 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hdq_0_1 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hs_0_2 : ∀ i (hi : i < gsPlantFanMid_0.length),     z3solve (flowQuery ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_0[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_0.take i)⟩) = Verdict.unsat) (hr_0_2 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_0_2 : ∀ g ∈ gsPlantFanMid_0, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 0)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsPlantFanMid_0 ν →
      Covered (GWPlantFanMid 0) ⟨q0, 4, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWPlantFanMid 0) gsPlantFanMid_0 ⟨q0, 4, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certPlantFanMid_0 hs_0_0 hdp_0_0 hdq_0_0 hs_0_1 hr_0_1 hq_0_1 hdp_0_1 hdq_0_1 hs_0_2 hr_0_2 hq_0_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 17 _ (by decide) ν hν

noncomputable def gsPlantFanMid_1 : List (Term (Var 2)) :=
  hostComps vsPlantFanMid 2 (((plant_fan_mid_IR.invariants.find? (fun r => r.1 == "Brake")).getD ("", Parse.PForm.tt)).2)

theorem GWPlantFanMid1_modes_eq : (GWPlantFanMid 1).modes =
    [realModeOf vsPlantFanMid 2 (mLPlantFanMid 1) ((15 : ℚ) / 4) (fRowPlantFanMid 1 0) (mRPlantFanMid 0),
     realModeOf vsPlantFanMid 2 (mLPlantFanMid 1) ((15 : ℚ) / 4) (fRowPlantFanMid 1 1) (mRPlantFanMid 1),
     realModeOf vsPlantFanMid 2 (mLPlantFanMid 1) ((15 : ℚ) / 4) (fRowPlantFanMid 1 2) (mRPlantFanMid 2)] := rfl

theorem certPlantFanMid_1 (hs_1_0 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    CoverCertM (GWPlantFanMid 1) gsPlantFanMid_1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_1 hs_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_1 hs_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_1 hs_1_2
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanMid_1 _ (fun g hg => z3_unsat_sound (hr_1_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_region]; exact regionInvAll_of_unsat' gsPlantFanMid_1 _ (fun g hg => z3_unsat_sound (hr_1_2 g hg))
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanMid_1 _ (fun g hg => z3_unsat_sound (hq_1_1 g hg))
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' gsPlantFanMid_1 _ (fun g hg => z3_unsat_sound (hq_1_2 g hg))
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_1 hdp_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_1 hdp_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | q + 3, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWPlantFanMid1_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_1 hdq_1_0
    | 1, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsPlantFanMid_1 hdq_1_1
    | 2, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowPlantFanMid, plant_fan_mid_coverNC])
    | q + 3, hm => simp at hm
  · intro m hm
    rw [GWPlantFanMid1_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

theorem plant_fan_mid_throughout_Brake (hs_1_0 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hdp_1_0 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hdq_1_0 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 0), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 0))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hs_1_1 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hr_1_1 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_1 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 1)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hdp_1_1 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hdq_1_1 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       (fun _ => Term.const 0), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 1), Term.const 1,       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 1))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hs_1_2 : ∀ i (hi : i < gsPlantFanMid_1.length),     z3solve (flowQuery ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsPlantFanMid_1[i],       hostDyn vsPlantFanMid 2 Side.L (mLPlantFanMid 1), hostDyn vsPlantFanMid 2 Side.R (mRPlantFanMid 2), Term.const (((15 : ℚ) / 4 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (gsPlantFanMid_1.take i)⟩) = Verdict.unsat) (hr_1_2 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2))) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) (hq_1_2 : ∀ g ∈ gsPlantFanMid_1, z3solve (Formula.and (Formula.and (hostGuard vsPlantFanMid 2 Side.R (mRPlantFanMid 2)) (Formula.and (hostEvolve vsPlantFanMid 2 Side.L (mLPlantFanMid 1)) (hostEvolve vsPlantFanMid 2 Side.R (mRPlantFanMid 2)))) (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsPlantFanMid_1 ν →
      Covered (GWPlantFanMid 1) ⟨q0, 4, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWPlantFanMid 1) gsPlantFanMid_1 ⟨q0, 4, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certPlantFanMid_1 hs_1_0 hdp_1_0 hdq_1_0 hs_1_1 hr_1_1 hq_1_1 hdp_1_1 hdq_1_1 hs_1_2 hr_1_2 hq_1_2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl <;>
    exact check_sound_multi _ _ cert 17 _ (by decide) ν hν

end ThroughoutPlantFanMid
end RelCertifier
