/- GENERATED (scripts/gen_throughout.py) — do not edit. -/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.rover_drag
import RelCertifier.Instances.BenchIR.rover_drag

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

namespace RelCertifier
namespace ThroughoutRoverDrag
open DL Parse

def vsRoverDrag : List String := ["vx"]
def dummyRoverDrag : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLRoverDrag (l : ℕ) : Parse.PMode := rover_drag_IR.L.modes.getD l dummyRoverDrag
def mRRoverDrag (q : ℕ) : Parse.PMode := rover_drag_IR.R.modes.getD q dummyRoverDrag
def fRowRoverDrag (l q : ℕ) : ModeFlagsE :=
  ((rover_drag_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)
noncomputable def GWRoverDrag (l : ℕ) : SearchGraph (Var 1) :=
  realGraphOf vsRoverDrag 1 rover_drag_IR (mLRoverDrag l)
    ((rover_drag_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).lamQ)
    ((rover_drag_coverNC.covers.getD l ⟨"", 1, 1, [], [], []⟩).flags)
    (fun a b => rover_drag_coverNC.pruned.contains (a, b))

noncomputable def gsRoverDrag_0 : List (Term (Var 1)) :=
  hostComps vsRoverDrag 1 (((rover_drag_IR.invariants.find? (fun r => r.1 == "Cruise")).getD ("", Parse.PForm.tt)).2)

theorem GWRoverDrag0_modes_eq : (GWRoverDrag 0).modes =
    [realModeOf vsRoverDrag 1 (mLRoverDrag 0) ((1 : ℚ) / 1) (fRowRoverDrag 0 0) (mRRoverDrag 0)] := rfl

theorem certRoverDrag_0 (hs_0_0 : ∀ i (hi : i < gsRoverDrag_0.length),     z3solve (flowQuery ⟨gsRoverDrag_0[i],       hostDyn vsRoverDrag 1 Side.L (mLRoverDrag 0), hostDyn vsRoverDrag 1 Side.R (mRRoverDrag 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverDrag 1 Side.L (mLRoverDrag 0)) (hostEvolve vsRoverDrag 1 Side.R (mRRoverDrag 0))) (gsRoverDrag_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDrag_0[i],       hostDyn vsRoverDrag 1 Side.L (mLRoverDrag 0), hostDyn vsRoverDrag 1 Side.R (mRRoverDrag 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverDrag 1 Side.L (mLRoverDrag 0)) (hostEvolve vsRoverDrag 1 Side.R (mRRoverDrag 0))) (gsRoverDrag_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDrag_0[i],       hostDyn vsRoverDrag 1 Side.L (mLRoverDrag 0), hostDyn vsRoverDrag 1 Side.R (mRRoverDrag 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverDrag 1 Side.L (mLRoverDrag 0)) (hostEvolve vsRoverDrag 1 Side.R (mRRoverDrag 0))) (gsRoverDrag_0.take i)⟩) = Verdict.unsat) :
    CoverCertM (GWRoverDrag 0) gsRoverDrag_0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDrag0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ gsRoverDrag_0 hs_0_0
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDrag0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDrag, rover_drag_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDrag0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDrag, rover_drag_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDrag0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDrag, rover_drag_coverNC])
    | q + 1, hm => simp at hm
  · intro q m hm hflag
    unfold SearchGraph.modeAt at hm
    rw [GWRoverDrag0_modes_eq] at hm
    match q, hm with
    | 0, hm =>
        replace hm := Option.some.inj hm
        subst hm
        exact absurd hflag (by simp [fRowRoverDrag, rover_drag_coverNC])
    | q + 1, hm => simp at hm
  · intro m hm
    rw [GWRoverDrag0_modes_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl <;> simp

theorem rover_drag_throughout_Cruise (hs_0_0 : ∀ i (hi : i < gsRoverDrag_0.length),     z3solve (flowQuery ⟨gsRoverDrag_0[i],       hostDyn vsRoverDrag 1 Side.L (mLRoverDrag 0), hostDyn vsRoverDrag 1 Side.R (mRRoverDrag 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverDrag 1 Side.L (mLRoverDrag 0)) (hostEvolve vsRoverDrag 1 Side.R (mRRoverDrag 0))) (gsRoverDrag_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQueryStrict ⟨gsRoverDrag_0[i],       hostDyn vsRoverDrag 1 Side.L (mLRoverDrag 0), hostDyn vsRoverDrag 1 Side.R (mRRoverDrag 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverDrag 1 Side.L (mLRoverDrag 0)) (hostEvolve vsRoverDrag 1 Side.R (mRRoverDrag 0))) (gsRoverDrag_0.take i)⟩) = Verdict.unsat     ∨ z3solve (flowQuerySuperlevel ⟨gsRoverDrag_0[i],       hostDyn vsRoverDrag 1 Side.L (mLRoverDrag 0), hostDyn vsRoverDrag 1 Side.R (mRRoverDrag 0), Term.const (((1 : ℚ) / 1 : ℚ) : ℝ),       strataDomHost (Formula.and (hostEvolve vsRoverDrag 1 Side.L (mLRoverDrag 0)) (hostEvolve vsRoverDrag 1 Side.R (mRRoverDrag 0))) (gsRoverDrag_0.take i)⟩) = Verdict.unsat) :
    ∀ q0 ∈ [0], ∀ ν, InvAllHolds gsRoverDrag_0 ν →
      Covered (GWRoverDrag 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GWRoverDrag 0) gsRoverDrag_0 ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := certRoverDrag_0 hs_0_0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl <;>
    exact check_sound_multi _ _ cert 3 _ (by decide) ν hν

end ThroughoutRoverDrag
end RelCertifier
