/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Watertank, conjunction throughout — the multi-node template (R5)

The second validated template for the generated battery: THREE windows (one per left
mode), multi-node real graphs (the Mid window drops the uncertified `Low` row), and all
three certificate kinds — joint segments (`segPresAll_from_strata_verdicts'`), static
pre-j repositions (`regionInvAll_of_unsat'`), and σ-matched dynamic repositions
(frozen-left `segPresAll'`). Residuals: the named Z3 verdicts, exactly the tool's
emitted cut-free queries. Axioms: the standard three + `z3_unsat_sound`.
-/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC
import RelCertifier.Instances.BenchIR

namespace RelCertifier
namespace WatertankThroughout

open DL Parse

def vsW : List String := ["x"]
def dummyMode : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

/-- IR modes (left and right share names; records differ). -/
def mL (ℓ : ℕ) : Parse.PMode := watertank_IR.L.modes.getD ℓ dummyMode
def mR (q : ℕ) : Parse.PMode := watertank_IR.R.modes.getD q dummyMode

/-- The one invariant component (`L_x − (R_x + 3)`), shared by all windows. -/
noncomputable def gsW : List (Term (Var 1)) :=
  hostComps vsW 1 ((watertank_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)

/-- Emitted flag rows, per window. -/
def fRow (ℓ q : ℕ) : ModeFlagsE :=
  ((watertank_coverNC.covers.getD ℓ ⟨"", 1, 1, [], [], []⟩).flags.getD q
    ⟨"", false, false, false, false, false⟩)

/-- The real graph of window `ℓ`. -/
noncomputable def GW (ℓ : ℕ) : SearchGraph (Var 1) :=
  realGraphOf vsW 1 watertank_IR (mL ℓ) 1
    (watertank_coverNC.covers.getD ℓ ⟨"", 1, 1, [], [], []⟩).flags
    (fun a b => watertank_coverNC.pruned.contains (a, b))

/-! ## Node lists, evaluated (kernel defeq through the emitted literals) -/

theorem GW0_modes_eq : (GW 0).modes =
    [realModeOf vsW 1 (mL 0) 1 (fRow 0 0) (mR 0),
     realModeOf vsW 1 (mL 0) 1 (fRow 0 1) (mR 1),
     realModeOf vsW 1 (mL 0) 1 (fRow 0 2) (mR 2)] := rfl

theorem GW1_modes_eq : (GW 1).modes =
    [realModeOf vsW 1 (mL 1) 1 (fRow 1 1) (mR 1),
     realModeOf vsW 1 (mL 1) 1 (fRow 1 2) (mR 2)] := rfl

theorem GW2_modes_eq : (GW 2).modes =
    [realModeOf vsW 1 (mL 2) 1 (fRow 2 0) (mR 0),
     realModeOf vsW 1 (mL 2) 1 (fRow 2 1) (mR 1),
     realModeOf vsW 1 (mL 2) 1 (fRow 2 2) (mR 2)] := rfl

/-! ## The verdict bundles (per window, per certificate kind — tool query shapes) -/

/-- Joint-segment strata verdicts for pair `(ℓ, q)` at λ = 1. -/
def SegHyp (ℓ q : ℕ) : Prop :=
  ∀ i (hi : i < gsW.length),
    z3solve (flowQuery ⟨gsW[i],
      hostDyn vsW 1 Side.L (mL ℓ), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ))
        (hostEvolve vsW 1 Side.R (mR q))) (gsW.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨gsW[i],
      hostDyn vsW 1 Side.L (mL ℓ), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ))
        (hostEvolve vsW 1 Side.R (mR q))) (gsW.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨gsW[i],
      hostDyn vsW 1 Side.L (mL ℓ), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ))
        (hostEvolve vsW 1 Side.R (mR q))) (gsW.take i)⟩) = Verdict.unsat

/-- Static pre-j region verdicts for pair `(ℓ, q)` (tool order: `region ∧ g > 0`). -/
def RegHyp (ℓ q : ℕ) : Prop :=
  ∀ g ∈ gsW, z3solve (Formula.and
    (Formula.and (Formula.and (hostGuard vsW 1 Side.L (mL ℓ)) (hostGuard vsW 1 Side.R (mR q)))
      (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q))))
    (Formula.cmp .gt g (Term.const 0))) = Verdict.unsat

/-- Dynamic-reposition strata verdicts (frozen left, λ = 1), σ = pre-j. -/
def DynPreHyp (ℓ q : ℕ) : Prop :=
  ∀ i (hi : i < gsW.length),
    z3solve (flowQuery ⟨gsW[i],
      (fun _ => Term.const 0), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and
        (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q)))
        (hostGuard vsW 1 Side.L (mL ℓ))) (gsW.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨gsW[i],
      (fun _ => Term.const 0), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and
        (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q)))
        (hostGuard vsW 1 Side.L (mL ℓ))) (gsW.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨gsW[i],
      (fun _ => Term.const 0), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and
        (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q)))
        (hostGuard vsW 1 Side.L (mL ℓ))) (gsW.take i)⟩) = Verdict.unsat

/-- Dynamic-reposition strata verdicts, σ = post-j (no guardL). -/
def DynPostHyp (ℓ q : ℕ) : Prop :=
  ∀ i (hi : i < gsW.length),
    z3solve (flowQuery ⟨gsW[i],
      (fun _ => Term.const 0), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ))
        (hostEvolve vsW 1 Side.R (mR q))) (gsW.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨gsW[i],
      (fun _ => Term.const 0), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ))
        (hostEvolve vsW 1 Side.R (mR q))) (gsW.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨gsW[i],
      (fun _ => Term.const 0), hostDyn vsW 1 Side.R (mR q), Term.const 1,
      strataDomHost (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ))
        (hostEvolve vsW 1 Side.R (mR q))) (gsW.take i)⟩) = Verdict.unsat

/-! ## Discharge helpers -/

theorem segPres_of (ℓ q : ℕ) (h : SegHyp ℓ q) :
    SegPreservesAllOn gsW
      (jointSys (hostDyn vsW 1 Side.L (mL ℓ)) (hostDyn vsW 1 Side.R (mR q))
        (Term.const 1))
      (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q))) :=
  segPresAll_from_strata_verdicts' _ _ _ _ gsW h

theorem regPres_of (ℓ q : ℕ) (h : RegHyp ℓ q) :
    RegionInvAllOn gsW (Formula.and
      (Formula.and (hostGuard vsW 1 Side.L (mL ℓ)) (hostGuard vsW 1 Side.R (mR q)))
      (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q)))) :=
  regionInvAll_of_unsat' gsW _ (fun g hg => z3_unsat_sound (h g hg))

theorem dynPre_of (ℓ q : ℕ) (h : DynPreHyp ℓ q) :
    SegPreservesAllOn gsW
      (jointSys (fun _ => Term.const 0) (hostDyn vsW 1 Side.R (mR q)) (Term.const 1))
      (Formula.and
        (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q)))
        (hostGuard vsW 1 Side.L (mL ℓ))) :=
  segPresAll_from_strata_verdicts' _ _ _ _ gsW h

theorem dynPost_of (ℓ q : ℕ) (h : DynPostHyp ℓ q) :
    SegPreservesAllOn gsW
      (jointSys (fun _ => Term.const 0) (hostDyn vsW 1 Side.R (mR q)) (Term.const 1))
      (Formula.and (hostEvolve vsW 1 Side.L (mL ℓ)) (hostEvolve vsW 1 Side.R (mR q))) :=
  segPresAll_from_strata_verdicts' _ _ _ _ gsW h

/-! ## Window 0 (`Low`): nodes Low(joint), Mid(joint+repoPre+dyn), High(repoPre) -/

theorem cert0 (hs0 : SegHyp 0 0) (hs1 : SegHyp 0 1)
    (hr1 : RegHyp 0 1) (hr2 : RegHyp 0 2)
    (hdp1 : DynPreHyp 0 1) (hdq1 : DynPostHyp 0 1) :
    CoverCertM (GW 0) gsW := by
  have hlam : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GW0_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom, hlam]; exact segPres_of 0 0 hs0)
           | (rw [realModeOf_region]; exact absurd hflag (by simp [fRow, watertank_coverNC]))
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom, hlam]; exact segPres_of 0 1 hs1)
           | (rw [realModeOf_region]; exact regPres_of 0 1 hr1)
           | (rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact dynPre_of 0 1 hdp1)
           | (rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact dynPost_of 0 1 hdq1)
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | 2, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_region]; exact regPres_of 0 2 hr2)
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | q + 3, hm => simp at hm)
    | (intro m hm
       rw [GW0_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl | rfl <;> simp)

/-! ## Window 1 (`Mid`): nodes Mid(joint+dyn), High(repoPre) -/

theorem cert1 (hs1 : SegHyp 1 1) (hr2 : RegHyp 1 2)
    (hdp1 : DynPreHyp 1 1) (hdq1 : DynPostHyp 1 1) :
    CoverCertM (GW 1) gsW := by
  have hlam : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GW1_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom, hlam]; exact segPres_of 1 1 hs1)
           | (rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact dynPre_of 1 1 hdp1)
           | (rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact dynPost_of 1 1 hdq1)
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_region]; exact regPres_of 1 2 hr2)
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | q + 2, hm => simp at hm)
    | (intro m hm
       rw [GW1_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl <;> simp)

/-! ## Window 2 (`High`): nodes Low, Mid, High (all joint; Mid also dyn) -/

theorem cert2 (hs0 : SegHyp 2 0) (hs1 : SegHyp 2 1) (hs2 : SegHyp 2 2)
    (hdp1 : DynPreHyp 2 1) (hdq1 : DynPostHyp 2 1) :
    CoverCertM (GW 2) gsW := by
  have hlam : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro q m hm hflag
       unfold SearchGraph.modeAt at hm
       rw [GW2_modes_eq] at hm
       match q, hm with
       | 0, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom, hlam]; exact segPres_of 2 0 hs0)
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | 1, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom, hlam]; exact segPres_of 2 1 hs1)
           | (rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact dynPre_of 2 1 hdp1)
           | (rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact dynPost_of 2 1 hdq1)
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | 2, hm =>
           replace hm := Option.some.inj hm
           subst hm
           first
           | (rw [realModeOf_sys, realModeOf_dom, hlam]; exact segPres_of 2 2 hs2)
           | exact absurd hflag (by simp [fRow, watertank_coverNC])
       | q + 3, hm => simp at hm)
    | (intro m hm
       rw [GW2_modes_eq] at hm
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
       rcases hm with rfl | rfl | rfl <;> simp)

/-! ## The window theorems: gate re-decided in kernel + throughout -/

/-- Window `Low`, all three admissible starts. -/
theorem watertank_throughout_Low (hs0 : SegHyp 0 0) (hs1 : SegHyp 0 1)
    (hr1 : RegHyp 0 1) (hr2 : RegHyp 0 2)
    (hdp1 : DynPreHyp 0 1) (hdq1 : DynPostHyp 0 1) :
    ∀ q0 ∈ [0, 1, 2], ∀ ν, InvAllHolds gsW ν →
      Covered (GW 0) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GW 0) gsW ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := cert0 hs0 hs1 hr1 hr2 hdp1 hdq1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl | rfl
  · exact check_sound_multi _ _ cert 5 _ (by decide) ν hν
  · exact check_sound_multi _ _ cert 5 _ (by decide) ν hν
  · exact check_sound_multi _ _ cert 5 _ (by decide) ν hν

/-- Window `Mid`, admissible starts Mid (node 0) and High (node 1). -/
theorem watertank_throughout_Mid (hs1 : SegHyp 1 1) (hr2 : RegHyp 1 2)
    (hdp1 : DynPreHyp 1 1) (hdq1 : DynPostHyp 1 1) :
    ∀ q0 ∈ [0, 1], ∀ ν, InvAllHolds gsW ν →
      Covered (GW 1) ⟨q0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GW 1) gsW ⟨q0, 1, SrcSetting.preJ⟩ ν := by
  intro q0 hq0 ν hν
  have cert := cert1 hs1 hr2 hdp1 hdq1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0
  rcases hq0 with rfl | rfl
  · exact check_sound_multi _ _ cert 4 _ (by decide) ν hν
  · exact check_sound_multi _ _ cert 4 _ (by decide) ν hν

/-- Window `High`, admissible start High (node 2). -/
theorem watertank_throughout_High (hs0 : SegHyp 2 0) (hs1 : SegHyp 2 1)
    (hs2 : SegHyp 2 2) (hdp1 : DynPreHyp 2 1) (hdq1 : DynPostHyp 2 1) :
    ∀ ν, InvAllHolds gsW ν →
      Covered (GW 2) ⟨2, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout (GW 2) gsW ⟨2, 1, SrcSetting.preJ⟩ ν := by
  intro ν hν
  exact check_sound_multi _ _ (cert2 hs0 hs1 hs2 hdp1 hdq1) 5 _ (by decide) ν hν

end WatertankThroughout
end RelCertifier
