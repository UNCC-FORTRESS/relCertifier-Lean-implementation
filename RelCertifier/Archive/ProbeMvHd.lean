import RelCertifier.Archive.GapThreeRoverDemo
import RelCertifier.Archive.GapThreeTask3

namespace RelCertifier
open DL DLCalTiming

/-- A minimal right search graph: one mode (the rover right block) + one self-edge. -/
noncomputable def probeGr : SearchGraph (Var 3) :=
  { modes := [{ sys := rightBlock roverFR (Term.const 1), dom := Formula.tt, weight := 1 }],
    edges := [{ src := 0, tgt := 0, guard := Formula.tt, pruned := false }] }

/-- `mv = Lv 2` (what `MvFrozen` forces) IS bound by the left block — hence in `Program.vars`
of the left program. -/
theorem probe_mv_in_left :
    (Lv (2 : Fin 3)) ∈ Program.vars (Program.ode (leftBlock roverFL) Formula.tt) := by
  right
  show (Lv (2 : Fin 3)) ∈ (leftBlock roverFL).boundSet
  simp only [ODESystem.boundSet, leftBlock, ODESystem.bound, List.map_map, Set.mem_setOf_eq,
    List.mem_map, Function.comp]
  exact ⟨2, List.mem_finRange 2, rfl⟩

/-- `mv = Lv 2` also occurs in the right automaton body (the `modeStep` assigns `mv`), hence in
`Program.vars` of the right program. -/
theorem probe_mv_in_right :
    (Lv (2 : Fin 3)) ∈ Program.vars (rightAutomatonBody probeGr (Lv 2)) := by
  right
  -- rightAutomatonBody = bigChoiceP [modeStep probeGr mv 0 m]; modeStep assigns mv
  have hbody : rightAutomatonBody probeGr (Lv 2)
      = bigChoiceP [modeStep probeGr (Lv 2) 0
          { sys := rightBlock roverFR (Term.const 1), dom := Formula.tt, weight := 1 }] := rfl
  rw [hbody]
  -- descend into the assign mv node: bv(assign mv _) = {mv}
  simp only [bigChoiceP, modeStep, SearchGraph.edgesFrom, probeGr, List.filter, decide_true,
    List.map_cons, List.map_nil, Program.bv, Set.mem_union, Set.mem_singleton_iff]
  tauto

/-- **The vacuity, sealed.** With `mv = Lv 2` (which `MvFrozen` forces), the left program's variables
and the right automaton's variables SHARE `mv`, so `tooling_sound`'s disjointness hypothesis
`Disjoint (vars left) (vars right)` is **false**. Hence any `MvFrozen`-based concrete instantiation
of `tooling_sound` rests on a false `hd` — it is vacuous. The mode variable must live OUTSIDE the left
block (an `Aux` coordinate), not frozen inside it. -/
theorem probe_hd_false :
    ¬ Disjoint (Program.vars (Program.ode (leftBlock roverFL) Formula.tt))
               (Program.vars (rightAutomatonBody probeGr (Lv 2))) := by
  intro hdisj
  exact Set.disjoint_left.mp hdisj probe_mv_in_left probe_mv_in_right

end RelCertifier
