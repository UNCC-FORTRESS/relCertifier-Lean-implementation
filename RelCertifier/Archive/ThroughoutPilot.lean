/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_drag` throughout pilot (ARCHIVED 2026-07-30 — template, superseded by the generated battery)

**ARCHIVED.** The hand-built template that `scripts/gen_throughout.py` was modelled on.
The generated battery shipped: `Instances/Throughout/rover_drag.lean`
(`ThroughoutRoverDrag.rover_drag_throughout_Cruise`) is the live instance, and this file
has no other referents. Kept compiled as the readable reference version of the shape.

The generated battery's shape, validated by hand on the simplest benchmark: the REAL
cover graph from the IR at the emitted cut-free cover (`rover_drag_coverNC`), the
lowered component list, `CoverCertM` from the fold-shaped strata verdicts (the tool's
exact queries), the checker gate re-decided in kernel, and `check_sound_multi`'s
conclusion — every invariant component holds throughout every assembled right response.

Residual: the strata verdicts (`hz3`, item 1 of the frozen contract). Axioms: the
standard three + `z3_unsat_sound`.
-/
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Instances.BenchCoversNC.rover_drag
import RelCertifier.Instances.BenchIR.rover_drag

namespace RelCertifier
namespace RoverDragThroughout

open DL Parse

def vsT : List String := ["vx"]

/-- Dummy mode (never hit: indices are in range). -/
def dummyMode : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

/-- The lowered invariant components (one: `R_vx − L_vx − 0.05`). -/
noncomputable def gsT : List (Term (Var 1)) :=
  hostComps vsT 1 ((rover_drag_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)

/-- The emitted window cover (single left mode `Cruise`). -/
def lcT : LeftCoverE := rover_drag_coverNC.covers.getD 0
  ⟨"", 1, 1, [], [], []⟩

/-- The real cover graph at the emitted flags (λ = 1). -/
noncomputable def GT : SearchGraph (Var 1) :=
  realGraphOf vsT 1 rover_drag_IR (rover_drag_IR.L.modes.getD 0 dummyMode) 1
    lcT.flags (fun a b => rover_drag_coverNC.pruned.contains (a, b))

/-- The node list, evaluated (kernel defeq through the emitted literal). -/
theorem GT_modes_eq : GT.modes =
    [realModeOf vsT 1 (rover_drag_IR.L.modes.getD 0 dummyMode) 1
      ⟨"Track", true, false, false⟩
      (rover_drag_IR.R.modes.getD 0 dummyMode)] := rfl

/-- Graph inversion (single node). -/
theorem GT_modeAt {q : ℕ} {m : RMode (Var 1)} (hm : GT.modeAt q = some m) :
    q = 0 ∧ m = realModeOf vsT 1 (rover_drag_IR.L.modes.getD 0 dummyMode) 1
      ⟨"Track", true, false, false⟩
      (rover_drag_IR.R.modes.getD 0 dummyMode) := by
  unfold SearchGraph.modeAt at hm
  rw [GT_modes_eq] at hm
  match q with
  | 0 =>
      refine ⟨rfl, ?_⟩
      simpa using hm.symm
  | q + 1 => simp at hm

/-- The certificate bundle from the strata verdicts (single pair, identity order). -/
theorem certT
    (hz3 : ∀ i (hi : i < gsT.length),
      z3solve (flowQuery ⟨gsT[i],
        hostDyn vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode),
        hostDyn vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode),
        Term.const 1,
        strataDomHost (Formula.and
          (hostEvolve vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
          (hostEvolve vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode)))
          (gsT.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQueryStrict ⟨gsT[i],
        hostDyn vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode),
        hostDyn vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode),
        Term.const 1,
        strataDomHost (Formula.and
          (hostEvolve vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
          (hostEvolve vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode)))
          (gsT.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQuerySuperlevel ⟨gsT[i],
        hostDyn vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode),
        hostDyn vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode),
        Term.const 1,
        strataDomHost (Formula.and
          (hostEvolve vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
          (hostEvolve vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode)))
          (gsT.take i)⟩) = Verdict.unsat) :
    CoverCertM GT gsT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q m hm hjOK
    obtain ⟨rfl, rfl⟩ := GT_modeAt hm
    rw [realModeOf_sys, realModeOf_dom]
    have hlam : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
    rw [hlam]
    exact segPresAll_from_strata_verdicts'
      (hostDyn vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
      (hostDyn vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode))
      (Term.const 1)
      (Formula.and
        (hostEvolve vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
        (hostEvolve vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode)))
      gsT hz3
  · intro q m hm hflag
    obtain ⟨rfl, rfl⟩ := GT_modeAt hm
    simp [realModeOf] at hflag
  · intro q m hm hflag
    obtain ⟨rfl, rfl⟩ := GT_modeAt hm
    simp [realModeOf] at hflag
  · intro m hm
    rw [GT_modes_eq, List.mem_singleton] at hm
    subst hm
    norm_num [realModeOf]

/-- **`rover_drag`, throughout, end to end**: the checker gate re-decided in kernel on
the REAL graph, and — under the strata verdicts — every invariant component preserved
throughout every assembled right response from every jointly-invariant entry. -/
theorem rover_drag_throughout
    (hz3 : ∀ i (hi : i < gsT.length),
      z3solve (flowQuery ⟨gsT[i],
        hostDyn vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode),
        hostDyn vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode),
        Term.const 1,
        strataDomHost (Formula.and
          (hostEvolve vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
          (hostEvolve vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode)))
          (gsT.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQueryStrict ⟨gsT[i],
        hostDyn vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode),
        hostDyn vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode),
        Term.const 1,
        strataDomHost (Formula.and
          (hostEvolve vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
          (hostEvolve vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode)))
          (gsT.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQuerySuperlevel ⟨gsT[i],
        hostDyn vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode),
        hostDyn vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode),
        Term.const 1,
        strataDomHost (Formula.and
          (hostEvolve vsT 1 Side.L (rover_drag_IR.L.modes.getD 0 dummyMode))
          (hostEvolve vsT 1 Side.R (rover_drag_IR.R.modes.getD 0 dummyMode)))
          (gsT.take i)⟩) = Verdict.unsat) :
    ∀ ν, InvAllHolds gsT ν →
      Covered GT ⟨0, 1, SrcSetting.preJ⟩
      ∧ CoexecInvAllThroughout GT gsT ⟨0, 1, SrcSetting.preJ⟩ ν := by
  intro ν hν
  exact check_sound_multi GT gsT (certT hz3) 2 ⟨0, 1, SrcSetting.preJ⟩ (by decide) ν hν

end RoverDragThroughout
end RelCertifier
