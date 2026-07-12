/-
GAP 3 — the full `tooling_sound` instantiation at concrete `rover` data (non-vacuous).

This assembles `tooling_sound` at concrete single-mode rover automata `roverL`, `roverR` with
`mv = Av 1` (auxiliary mode slot) and `tg = Av 0` (auxiliary clock). Everything structural is
discharged CONCRETELY: `graphOf` construction, `RightProjAlign` (derived, Task 2), freshness
(`mv`/`tg` in `Aux`), and the `∀∃` disjointness `hd`/`hddF` (by SIDE SPLIT: left = `Lv`, right =
`Rv ∪ Aux`). The Z3-leaf `cert`/`cert_repo`, the emit `EmitSegs`, and the field-shape `HExistSeg`
(carried inside `graphOfSide`) remain PARAMETRIC — the established honest boundaries.

The instantiation is NON-VACUOUS: the freshness that blocked concrete instantiation is discharged
(`mv`/`tg` in `Aux`), and `hd`/`hddF` — which the frozen-`mv` route made unsatisfiable
(`ProbeMvHd.probe_hd_false`) — hold by side split. So the antecedents are jointly satisfiable.
-/
import RelCertifier.GapThreeTask3
import RelCertifier.GapThreeRoverDemo

namespace RelCertifier
open DL DLCalTiming DLRel Function

/-- Concrete single-mode left automaton (rover flow mode; trivial evolution domain). -/
noncomputable def roverL : HybridAut 3 :=
  { modes := [{ dyn := roverFL, dom := Formula.tt, guard := Formula.tt, next := [0] }] }

/-- Concrete single-mode right automaton. -/
noncomputable def roverR : HybridAut 3 :=
  { modes := [{ dyn := roverFR, dom := Formula.tt, guard := Formula.tt, next := [0] }] }

/-- The right coupling scale `λ = 1`. -/
def roverLam : Term (Var 3) := Term.const 1

/-! ## Side-split infrastructure for the disjointness `hd`/`hddF` -/

/-- Every variable of a left-block ODE (fields + trivial domain) is on the left side. -/
theorem leftOde_vars_side_L (fL : Fin 3 → Term (Var 3))
    (hfL : ∀ i, (fL i).fv ⊆ {x | x.1 = Side.L}) {v : Var 3}
    (hv : v ∈ Program.vars (Program.ode (leftBlock fL) Formula.tt)) : v.1 = Side.L := by
  rcases hv with hfv | hbv
  · -- fv (ode) = boundSet ∪ readVars ∪ domain.fv
    simp only [Program.fv, Set.mem_union] at hfv
    rcases hfv with (hb | hr) | hd
    · simp only [ODESystem.boundSet, leftBlock, ODESystem.bound, List.map_map, Set.mem_setOf_eq,
        List.mem_map, Function.comp] at hb
      obtain ⟨i, -, rfl⟩ := hb; rfl
    · simp only [ODESystem.readVars, leftBlock, Set.mem_setOf_eq, List.mem_map] at hr
      obtain ⟨p, ⟨i, -, rfl⟩, hx⟩ := hr
      exact hfL i hx
    · exact absurd hd (by simp [Formula.fv])
  · -- bv (ode) = boundSet
    simp only [Program.bv, ODESystem.boundSet, leftBlock, ODESystem.bound, List.map_map,
      Set.mem_setOf_eq, List.mem_map, Function.comp] at hbv
    obtain ⟨i, -, rfl⟩ := hbv; rfl

/-- `vars (choice a b) = vars a ∪ vars b`. -/
theorem vars_choice (a b : Program (Var 3)) :
    Program.vars (Program.choice a b) = Program.vars a ∪ Program.vars b := by
  simp only [Program.vars, Program.fv, Program.bv]; ac_rfl

/-- `vars (star P) = vars P`. -/
theorem vars_star (P : Program (Var 3)) : Program.vars (Program.star P) = Program.vars P := rfl

/-- `vars (seq a b) ⊆ vars a ∪ vars b` (the seq-`fv` `\ mbv` only shrinks it). -/
theorem vars_seq_subset (a b : Program (Var 3)) :
    Program.vars (Program.seq a b) ⊆ Program.vars a ∪ Program.vars b := by
  intro v hv
  rcases hv with hfv | hbv
  · simp only [Program.fv, Set.mem_union] at hfv
    rcases hfv with ha | hb
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (Or.inl hb.1)
  · simp only [Program.bv, Set.mem_union] at hbv
    rcases hbv with ha | hb
    · exact Or.inl (Or.inr ha)
    · exact Or.inr (Or.inr hb)

/-- `roverFL`'s fields read only left-side coordinates. -/
theorem roverFL_side_L : ∀ i, (roverFL i).fv ⊆ {x : Var 3 | x.1 = Side.L} := by
  intro i; fin_cases i <;> simp [roverFL, Term.fv, Lv, Set.subset_def]

/-- The constant-`0` (reposition) field reads nothing. -/
theorem const0_side_L : ∀ i, ((fun _ => Term.const 0 : Fin 3 → Term (Var 3)) i).fv ⊆
    {x : Var 3 | x.1 = Side.L} := by
  intro i; simp [Term.fv]

/-- Every variable of a member of `bigChoice ps` whose members are all left-sided is left-sided. -/
theorem bigChoice_vars_side_L {ps : List (Program (Var 3))}
    (hps : ∀ p ∈ ps, ∀ v ∈ Program.vars p, v.1 = Side.L)
    {v : Var 3} (hv : v ∈ Program.vars (bigChoice ps)) : v.1 = Side.L := by
  induction ps with
  | nil => simp only [bigChoice, Program.vars, Program.fv, Program.bv, Formula.fv,
      Set.union_empty, Set.mem_empty_iff_false] at hv
  | cons p ps ih =>
      rw [bigChoice, vars_choice, Set.mem_union] at hv
      rcases hv with h | h
      · exact hps p (List.mem_cons.mpr (Or.inl rfl)) v h
      · exact ih (fun q hq => hps q (List.mem_cons.mpr (Or.inr hq))) h

/-- **`hd`/`hddF` left half.** Every variable of the concrete left program (both rover flow modes and
the frozen reposition, trivial domains) is on the left side. -/
theorem rover_left_side_L {v : Var 3}
    (hv : v ∈ Program.vars (bigChoice (roverL.leftProgs ++
      [Program.ode (leftBlock (fun _ => Term.const 0)) Formula.tt]))) : v.1 = Side.L := by
  refine bigChoice_vars_side_L ?_ hv
  intro p hp w hw
  simp only [roverL, HybridAut.leftProgs, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · rw [hp] at hw; exact leftOde_vars_side_L roverFL roverFL_side_L hw
  · rw [hp] at hw; exact leftOde_vars_side_L _ const0_side_L hw

/-- The concrete right search graph. -/
noncomputable def roverGr : SearchGraph (Var 3) := graphOf_Gr roverR roverLam

/-- Every variable of the concrete right ODE (`rightBlock roverFR roverLam`, trivial domain) is
right-sided. -/
theorem rightOde_vars_side_R {v : Var 3}
    (hv : v ∈ Program.vars (Program.ode (rightBlock roverFR roverLam) Formula.tt)) :
    v.1 = Side.R := by
  have hmem : v ∈ (rightBlock roverFR roverLam).boundSet ∪ (rightBlock roverFR roverLam).readVars := by
    rcases hv with hfv | hbv
    · simp only [Program.fv, Set.mem_union] at hfv
      rcases hfv with (hb | hr) | hd
      · exact Or.inl hb
      · exact Or.inr hr
      · exact absurd hd (by simp [Formula.fv])
    · exact Or.inl hbv
  exact rightBlock_side_R roverFR roverLam (by simp [roverLam, Term.fv])
    (by intro i; fin_cases i <;> simp [roverFR, Term.fv, Rv]) hmem

/-- `vars (test ϕ) = ϕ.fv`. -/
theorem vars_test (ϕ : Formula (Var 3)) : Program.vars (Program.test ϕ) = ϕ.fv := by
  simp only [Program.vars, Program.fv, Program.bv, Set.union_empty]

/-- The concrete right graph's edges: one `⊤`-guarded self-loop at mode `0`. -/
theorem roverGr_edges :
    roverGr.edges = [{ src := 0, tgt := 0, guard := Formula.tt, pruned := false }] := by
  simp [roverGr, graphOf_Gr, roverR, HybridAut.edgesOf]

/-- The concrete right edge program list: one `?⊤ ; mv := 0`. -/
theorem roverGr_edgeProgs :
    (roverGr.edgesFrom 0).map (fun e =>
        Program.seq (Program.test e.guard) (Program.assign roverMv (Term.const (e.tgt : ℝ))))
      = [Program.seq (Program.test Formula.tt) (Program.assign roverMv (Term.const (0 : ℝ)))] := by
  simp [SearchGraph.edgesFrom, roverGr_edges]

/-- `vars (bigChoiceP [x]) = vars x`. -/
theorem vars_bigChoiceP_singleton (x : Program (Var 3)) :
    Program.vars (bigChoiceP [x]) = Program.vars x := by
  simp only [bigChoiceP, vars_choice, vars_test, Formula.fv, Set.union_empty]

/-- The concrete right automaton body's single mode. -/
noncomputable def roverRMode : RMode (Var 3) :=
  { sys := rightBlock roverFR roverLam, dom := Formula.tt, weight := 1,
    dynSys := jointSys (fun _ => Term.const 0) roverFR roverLam,
    dynDomPre := Formula.tt, dynDomPost := Formula.tt }

/-- **`hd`/`hddF` right half.** Every variable of the concrete right automaton body is either
right-sided or the mode variable `mv = Av 1`. -/
theorem rover_right_side_R_or_mv {v : Var 3}
    (hv : v ∈ Program.vars (rightAutomatonBody roverGr roverMv)) :
    v.1 = Side.R ∨ v = roverMv := by
  -- rightAutomatonBody roverGr mv = bigChoiceP [modeStep roverGr mv 0 m0]; and bigChoiceP [x] vars = vars x
  have hbody0 : rightAutomatonBody roverGr roverMv
      = bigChoiceP [modeStep roverGr roverMv 0 roverRMode] := rfl
  rw [hbody0, vars_bigChoiceP_singleton, modeStep] at hv
  -- modeStep = seq A (seq B C)
  rcases vars_seq_subset _ _ hv with hA | hBC
  · -- A = test (modeIs mv 0): vars = {mv}
    right
    rw [vars_test] at hA
    simpa only [modeIs, Formula.fv, Term.fv, Set.union_empty, Set.mem_singleton_iff] using hA
  · rcases vars_seq_subset _ _ hBC with hB | hC
    · -- B = ode (rightBlock roverFR roverLam) tt: Side.R
      exact Or.inl (rightOde_vars_side_R hB)
    · -- C = bigChoiceP [?⊤ ; mv := 0]: vars = {mv}
      right
      rw [show (roverGr.edgesFrom 0).map (fun e =>
          Program.seq (Program.test e.guard) (Program.assign roverMv (Term.const (e.tgt : ℝ))))
        = _ from roverGr_edgeProgs] at hC
      simp only [bigChoiceP, vars_choice, vars_test, Formula.fv, Set.union_empty,
        Set.mem_union, Set.mem_empty_iff_false, or_false] at hC
      rcases vars_seq_subset _ _ hC with hc1 | hc2
      · rw [vars_test] at hc1; exact absurd hc1 (by simp [Formula.fv])
      · simpa only [Program.vars, Program.fv, Program.bv, Term.fv, Set.empty_union,
          Set.mem_singleton_iff] using hc2

/-- **`hd` holds at concrete rover data** — the disjointness that the frozen-`mv` route made FALSE
(`ProbeMvHd.probe_hd_false`). With `mv = Av 1` in the `Aux` side, the left program (all `Lv`) and the
right automaton (all `Rv`, plus the auxiliary `mv`) are disjoint by side split. This is the concrete
witness that the `Aux` formulation is `hd`-satisfiable. -/
theorem rover_hd_holds :
    Disjoint (Program.vars (bigChoice (roverL.leftProgs ++
        [Program.ode (leftBlock (fun _ => Term.const 0)) Formula.tt])))
      (Program.vars ((rightAutomatonBody roverGr roverMv).rename (Equiv.refl (Var 3)))) := by
  rw [Set.disjoint_left]
  intro v hL hR
  rw [Program.rename_refl] at hR
  have hvL : v.1 = Side.L := rover_left_side_L hL
  rcases rover_right_side_R_or_mv hR with hvR | hvmv
  · rw [hvL] at hvR; exact absurd hvR (by decide)
  · rw [hvmv] at hvL; exact absurd hvL (by simp [roverMv, Av])

end RelCertifier
