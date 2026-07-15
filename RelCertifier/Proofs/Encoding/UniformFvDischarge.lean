/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Footprint dischargers for the uniform multi-flow chain

`theorem3_uniform_multiflow` carries two variable-hygiene hypotheses (`hd`, `hddF`) and a
handful of freshness facts (`hfresh`, `htgRight`, per-window `tg`/`mv` facts). This file
discharges all of them from THREE side-split residuals per benchmark:

* every left field/domain reads only `Lv`s,
* every right mode's system/domain touches only `Rv`s,
* the invariant's projections split as `varsL ⊆ Lv` / `varsR ⊆ Rv`,

with `mv = (Aux, a)`, `tg = (Aux, b)`, `a ≠ b` — the same recipe as `FvDischarge`'s
`hdis_aux`/`hddF_aux` for the cadenced chain, retargeted at `windowSeg` lefts and the
un-cadenced `rightAutomatonBody`. The wrapper `uniform_multiflow_end_to_end` is
`theorem3_uniform_multiflow` with every bookkeeping hypothesis replaced by the side-splits;
what remains per benchmark: the side-splits, the encoding identity, and the load-bearing
cover data (`CoverCert` + `RightProjAlignV` + `EmitWindows`).
-/
import RelCertifier.Proofs.Encoding.UniformMultiflow
import RelCertifier.Proofs.Encoding.FvDischarge

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## Side helpers -/

theorem aux_ne_Lv (a i : Fin n) : (Side.Aux, a) ≠ Lv i := by
  simp [Lv, Prod.ext_iff]

theorem aux_notin_range_Lv (a : Fin n) : ((Side.Aux, a) : Var n) ∉ range Lv :=
  fun ⟨i, hi⟩ => aux_ne_Lv a i hi.symm

theorem aux_notin_range_Rv (a : Fin n) : ((Side.Aux, a) : Var n) ∉ range Rv :=
  fun ⟨i, hi⟩ => aux_ne_Rv a i hi.symm

/-- Every `Lv i` is bound by the left block. -/
theorem Lv_mem_leftBlock_boundSet (fL : Fin n → Term (Var n)) (i : Fin n) :
    Lv i ∈ (leftBlock fL).boundSet := by
  simp only [leftBlock, ODESystem.boundSet, ODESystem.bound, List.map_map,
    Set.mem_setOf_eq, List.mem_map, List.mem_finRange]
  exact ⟨i, trivial, rfl⟩

/-- List-membership form of `leftBlock_boundSet_sub`. -/
theorem leftBlock_bound_sub (fL : Fin n → Term (Var n)) :
    ∀ x ∈ (leftBlock fL).bound, ∃ i, x = Lv i := by
  intro x hx
  simp only [leftBlock, ODESystem.bound, List.map_map, List.mem_map,
    List.mem_finRange] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ⟨i, rfl⟩

/-- Every `Rv i` is bound by the right block. -/
theorem Rv_mem_rightBlock_boundSet (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (i : Fin n) : Rv i ∈ (rightBlock fR lam).boundSet := by
  simp only [rightBlock, ODESystem.boundSet, ODESystem.bound, List.map_map,
    Set.mem_setOf_eq, List.mem_map, List.mem_finRange]
  exact ⟨i, trivial, rfl⟩

/-- Set form of `rightBlock_bound_sub`. -/
theorem rightBlock_boundSet_sub (fR : Fin n → Term (Var n)) (lam : Term (Var n)) :
    (rightBlock fR lam).boundSet ⊆ range Rv := by
  intro x hx
  obtain ⟨i, hi⟩ := rightBlock_bound_sub fR lam x
    (by simpa [ODESystem.boundSet] using hx)
  exact hi ▸ mem_range_self i

/-- The right block reads only `Rv`s (given the side-split of the fields; the stretch
factor's variables must also be right-side — constants qualify vacuously). -/
theorem rightBlock_readVars_sub (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv) :
    (rightBlock fR lam).readVars ⊆ range Rv := by
  intro x hx
  simp only [rightBlock, ODESystem.readVars, Set.mem_setOf_eq, List.mem_map,
    List.mem_finRange] at hx
  obtain ⟨p, ⟨i, -, rfl⟩, hxp⟩ := hx
  simp only [Term.fv] at hxp
  rcases hxp with hxp | hxp
  · exact hlam hxp
  · exact hfR i hxp

/-- Side-split left/right blocks have disjoint footprints. -/
theorem LR_blocks_disjoint (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (hlam : lam.fv ⊆ range Rv) :
    Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars) := by
  rw [Set.disjoint_left]
  intro x hxL hxR
  have hL : x ∈ range Lv := by
    rcases hxL with hx | hx
    · exact leftBlock_boundSet_sub fL hx
    · exact leftBlock_readVars_sub fL hfL hx
  have hR : x ∈ range Rv := by
    rcases hxR with hx | hx
    · exact rightBlock_boundSet_sub fR lam hx
    · exact rightBlock_readVars_sub fR lam hfR hlam hx
  obtain ⟨i, rfl⟩ := hL
  obtain ⟨j, hj⟩ := hR
  exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-! ## `Program.vars` bounds: `bigSeq`, `windowSeg`, `bigChoice`, `rightAutomatonBody` -/

theorem vars_bigSeq_sub (ps : List (Program (Var n))) (S : Set (Var n))
    (h : ∀ p ∈ ps, Program.vars p ⊆ S) : Program.vars (bigSeq ps) ⊆ S := by
  induction ps with
  | nil =>
      intro x hx
      simp [bigSeq, Program.vars, Program.fv, Program.bv, Formula.fv] at hx
  | cons p ps ih =>
      intro x hx
      rcases vars_seq_sub _ _ hx with hx | hx
      · exact h p (List.mem_cons_self ..) hx
      · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hx

theorem vars_bigChoice_sub (ps : List (Program (Var n))) (S : Set (Var n))
    (h : ∀ p ∈ ps, Program.vars p ⊆ S) : Program.vars (bigChoice ps) ⊆ S := by
  induction ps with
  | nil =>
      simp [bigChoice, Program.vars, Program.fv, Program.bv, Formula.fv]
  | cons p ps ih =>
      intro x hx
      rcases vars_choice_sub _ _ hx with hx | hx
      · exact h p (List.mem_cons_self ..) hx
      · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hx

/-- A `k`-piece window's variables: the clocked segment's, `k`-independently. -/
theorem vars_windowSeg_sub (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ) :
    Program.vars (windowSeg leftSys domL tg dt k)
      ⊆ {tg} ∪ leftSys.boundSet ∪ leftSys.readVars ∪ domL.fv := by
  refine vars_bigSeq_sub _ _ ?_
  intro p hp
  rw [List.eq_of_mem_replicate hp]
  exact vars_clockedSeg_sub leftSys domL tg dt

/-- Side-split window: touches only its clock and `Lv`s. -/
theorem vars_windowSegL_sub (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (b : Fin n) (dt : ℝ) (k : ℕ) (hfL : ∀ i, (fL i).fv ⊆ range Lv)
    (hdomL : domL.fv ⊆ range Lv) :
    Program.vars (windowSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) dt k)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv := by
  intro x hx
  rcases vars_windowSeg_sub _ _ _ _ _ hx with ((hx | hx) | hx) | hx
  · exact Or.inl hx
  · exact Or.inr (leftBlock_boundSet_sub fL hx)
  · exact Or.inr (leftBlock_readVars_sub fL hfL hx)
  · exact Or.inr (hdomL hx)

/-- The uniform (un-cadenced) mode step touches only `mv` and the mode's own footprint,
provided every outgoing declared guard is `⊤`. -/
theorem vars_modeStepU_sub (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (m : RMode (Var n))
    (htt : ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt) :
    Program.vars (modeStep G mv q m)
      ⊆ {mv} ∪ (m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv) := by
  intro x hx
  rcases vars_seq_sub _ _ hx with hx | hx
  · rw [vars_test_eq] at hx
    simp only [modeIs, Formula.fv, Term.fv] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact absurd hx (by simp)
  · rcases vars_seq_sub _ _ hx with hx | hx
    · exact Or.inr (vars_ode_sub _ _ hx)
    · refine vars_bigChoiceP_sub _ _ ?_ hx
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨e, hef, rfl⟩ := hp
      intro y hy
      rcases vars_seq_sub _ _ hy with hy | hy
      · rw [vars_test_eq, htt e hef] at hy
        exact absurd hy (by simp [Formula.fv])
      · rcases vars_assign_sub mv _ hy with hy | hy
        · exact Or.inl hy
        · exact absurd hy (by simp [Term.fv])

/-- The uniform right automaton touches only `mv` and `Rv`s, given ⊤-guards and the
per-mode right-side split. -/
theorem vars_bodyU_sub (G : SearchGraph (Var n)) (mv : Var n)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    Program.vars (rightAutomatonBody G mv) ⊆ {mv} ∪ range Rv := by
  refine vars_bigChoiceP_sub _ _ ?_
  intro p hp
  simp only [List.mem_filterMap, List.mem_range] at hp
  obtain ⟨q, -, hq⟩ := hp
  rcases hm : G.modeAt q with _ | m
  · rw [hm] at hq; simp at hq
  · rw [hm] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    intro x hx
    rcases vars_modeStepU_sub G mv q m (htt q) hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hRv q m hm hx)

/-! ## The postcondition's projections -/

/-- `(ϕinv ∧ mvValidR)`'s left variables are exactly the invariant's. -/
theorem ψmulti_varsL (mv : Var n) (len : ℕ) (ϕinv : RFormula (Var n)) :
    (RFormula.and ϕinv (mvValidR mv len)).varsL = ϕinv.varsL := by
  simp only [RFormula.varsL, mvValidR, Set.union_empty]

/-- `(ϕinv ∧ mvValidR)`'s right variables: the invariant's plus `mv`. -/
theorem ψmulti_varsR_sub (mv : Var n) (len : ℕ) (ϕinv : RFormula (Var n)) :
    (RFormula.and ϕinv (mvValidR mv len)).varsR ⊆ ϕinv.varsR ∪ {mv} := by
  simp only [RFormula.varsR, mvValidR]
  refine Set.union_subset Set.subset_union_left ?_
  exact fun v hv => Or.inr (mvValid_fv_sub mv len hv)

/-! ## The `hd`/`hddF` dischargers -/

/-- **The `hd` discharger** for the multi-window left choice vs. the uniform automaton. -/
theorem hdis_multi (Gr : SearchGraph (Var n)) (a b : Fin n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (hab : a ≠ b)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv) :
    Disjoint (Program.vars (bigChoice (leftData.map (fun d =>
        windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
      (Program.vars ((rightAutomatonBody Gr ((Side.Aux, a) : Var n)).rename
        (Equiv.refl (Var n)))) := by
  refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
  · refine vars_bigChoice_sub _ _ ?_
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    exact vars_windowSegL_sub d.1 d.2.1 b dt d.2.2 (hL d hd).1 (hL d hd).2
  · intro x hx
    rw [Program.rename_refl] at hx
    rcases vars_bodyU_sub Gr _ htt hRv hx with hx | hx
    · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
    · exact Or.inr hx

/-- **The `hddF` discharger** for the multi-window shape. -/
theorem hddF_multi (Gr : SearchGraph (Var n)) (a b : Fin n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (ϕinv : RFormula (Var n)) (hab : a ≠ b)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv) :
    Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and ϕinv (mvValidR ((Side.Aux, a) : Var n) Gr.modes.length))).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and ϕinv (mvValidR ((Side.Aux, a) : Var n) Gr.modes.length))).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
  · rw [faShape_varsL', pvars_star', ψmulti_varsL]
    refine Set.union_subset ?_ (fun v hv => Or.inr (hinvL hv))
    refine vars_bigChoice_sub _ _ ?_
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    exact vars_windowSegL_sub d.1 d.2.1 b dt d.2.2 (hL d hd).1 (hL d hd).2
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyU_sub Gr _ htt hRv hv with hv | hv
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv
    · intro v hv
      rcases ψmulti_varsR_sub _ Gr.modes.length ϕinv hv with hv | hv
      · exact Or.inr (hinvR hv)
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))

/-! ## The discharged wrapper -/

/-- **`theorem3_uniform_multiflow`, bookkeeping-free.** All variable-hygiene and freshness
hypotheses discharged from the side-splits. Per-benchmark residuals: the side-splits
themselves, the invariant's encoding/splits, the graph shape facts (`htt`/`hlt`), and the
load-bearing cover data — per left window a `CoverCert` (Z3 leaf), the projection alignment
(carrying `HExistSeg`), and the emitted response sequences. -/
theorem uniform_multiflow_end_to_end (Gr : SearchGraph (Var n)) (g : Term (Var n))
    (a b : Fin n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (ϕinv : RFormula (Var n)) (hab : a ≠ b)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hgLR : g.fv ⊆ range Lv ∪ range Rv)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hcov : ∀ d ∈ leftData,
      (∃ Gj : SearchGraph (Var n), CoverCert Gj g
        ∧ RightProjAlignV Gj Gr g d.1 d.2.1)
      ∧ EmitWindows Gr g ((Side.Aux, a) : Var n) d.1 d.2.1
          ((Side.Aux, b) : Var n) dt d.2.2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftData.map (fun d => windowSeg (leftBlock d.1) d.2.1
        ((Side.Aux, b) : Var n) dt d.2.2)))
      (rightAutomatonBody Gr ((Side.Aux, a) : Var n))
      (RFormula.and ϕinv (mvValidR ((Side.Aux, a) : Var n) Gr.modes.length))) := by
  have haux : ∀ (c : Fin n) x, x ∈ range Lv ∪ range Rv → ((Side.Aux, c) : Var n) ≠ x := by
    rintro c x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact aux_ne_Lv c i
    · exact fun h => aux_ne_Rv c i h
  refine theorem3_uniform_multiflow Gr g ((Side.Aux, a) : Var n) ((Side.Aux, b) : Var n)
    dt leftData ϕinv
    (fun hmem => haux a _ (hgLR hmem) rfl)
    (fun hmem => haux b _ (hgLR hmem) rfl)
    (by simpa [Prod.ext_iff] using hab) hψ ?_ htt hlt ?_ ?_
    (hdis_multi Gr a b dt leftData hab htt hRv hL)
    (hddF_multi Gr a b dt leftData ϕinv hab htt hRv hL hinvL hinvR)
  · -- hfresh: mv is Aux, the mode programs live on Rv
    intro q m hm hmv
    exact aux_notin_range_Rv a (hRv q m hm (vars_ode_sub _ _ (Or.inl hmv)))
  · -- htgRight: tg is Aux, the mode data lives on Rv
    intro q m hm
    have hsub := hRv q m hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact aux_notin_range_Rv b (hsub (Or.inl (Or.inl (by
        simpa [ODESystem.boundSet, Set.mem_setOf_eq] using h))))
    · exact fun h => aux_notin_range_Rv b (hsub (Or.inl (Or.inr h)))
    · exact fun h => aux_notin_range_Rv b (hsub (Or.inl (Or.inl h)))
    · exact fun h => aux_notin_range_Rv b (hsub (Or.inr h))
  · -- per-window facts from the side-splits + the load-bearing cover data
    intro d hd
    obtain ⟨hfL, hdomL⟩ := hL d hd
    obtain ⟨hGj, hemit⟩ := hcov d hd
    refine ⟨?_, ?_, ?_, ?_, ?_, hGj, hemit⟩
    · intro h
      obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
      exact aux_ne_Lv a i hi
    · intro v hv
      obtain ⟨i, hi⟩ := hdomL hv
      exact Or.inl (hi ▸ Lv_mem_leftBlock_boundSet d.1 i)
    · intro h
      obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
      exact aux_ne_Lv b i hi
    · exact fun h => aux_notin_range_Lv b (leftBlock_readVars_sub d.1 hfL h)
    · exact fun h => aux_notin_range_Lv b (hdomL h)

end RelCertifier
