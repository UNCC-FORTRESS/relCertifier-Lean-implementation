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
import RelCertifier.Archive.GapThreeTask3
import RelCertifier.Archive.GapThreeRoverDemo

namespace RelCertifier
open DL DLCalTiming DLRel Function

/-- The single left mode (rover flow mode; trivial evolution domain, `⊤`-guarded self-loop). -/
noncomputable def roverLm : HybridMode 3 :=
  { dyn := roverFL, dom := Formula.tt, guard := Formula.tt, next := [0] }

/-- The single right mode. -/
noncomputable def roverRm : HybridMode 3 :=
  { dyn := roverFR, dom := Formula.tt, guard := Formula.tt, next := [0] }

/-- Concrete single-mode left automaton. -/
noncomputable def roverL : HybridAut 3 := { modes := [roverLm] }

/-- Concrete single-mode right automaton. -/
noncomputable def roverR : HybridAut 3 := { modes := [roverRm] }

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
  simp [roverGr, graphOf_Gr, roverR, roverRm, HybridAut.edgesOf]

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

/-! ## The relational invariant `ϕinv` -/

/-- The rel-formula invariant: `⌊px_L⌋_L + ⌊px_R⌋_R ≤ 0`. Encodes (`ρ = id`) to `invLe roverG`, with
`varsL = {Lv 0}` (left-sided) and `varsR = {Rv 0}` (right-sided). -/
def roverInv : RFormula (Var 3) :=
  RFormula.cmp CompOp.le
    (RTerm.binop AOp.add (RTerm.proj DLRel.Side.L (Term.var (Lv 0)))
      (RTerm.proj DLRel.Side.R (Term.var (Rv 0))))
    (RTerm.proj DLRel.Side.L (Term.const 0))

/-- `roverInv` encodes to `invLe roverG` (the `hψ` obligation). -/
theorem rover_hψ : encode (Equiv.refl (Var 3)) roverInv = invLe roverG := rfl

/-- `roverInv`'s left variables are `{Lv 0}` — left-sided. -/
theorem roverInv_varsL_side_L {v : Var 3} (hv : v ∈ roverInv.varsL) : v.1 = Side.L := by
  simp only [roverInv, RFormula.varsL, RTerm.varsL, Term.fv, Set.union_empty, Set.mem_union,
    Set.mem_empty_iff_false, or_false, Set.mem_singleton_iff] at hv
  subst hv; rfl

/-- `roverInv`'s right variables are `{Rv 0}` — right-sided. -/
theorem roverInv_varsR_side_R {v : Var 3} (hv : v ∈ roverInv.varsR) : v.1 = Side.R := by
  simp only [roverInv, RFormula.varsR, RTerm.varsR, Term.fv, Set.empty_union, Set.union_empty,
    Set.mem_union, Set.mem_empty_iff_false, false_or, Set.mem_singleton_iff] at hv
  subst hv; rfl

/-! ## The `∀∃` disjointness `hddF` (twin of `hd`, over `faShape`) -/

/-- `varsL (faShape α β ψ) = pvars α ∪ ψ.varsL`. -/
theorem faShape_varsL (α β : Program (Var 3)) (ψ : RFormula (Var 3)) :
    (faShape α β ψ).varsL = pvars α ∪ ψ.varsL := by
  simp only [faShape, RFormula.rdiamond, RFormula.varsL, RProgram.varsL, pvars, Program.fv,
    Program.bv, Formula.fv, Set.union_empty, Set.empty_union]

/-- `varsR (faShape α β ψ) = pvars β ∪ ψ.varsR`. -/
theorem faShape_varsR (α β : Program (Var 3)) (ψ : RFormula (Var 3)) :
    (faShape α β ψ).varsR = pvars β ∪ ψ.varsR := by
  simp only [faShape, RFormula.rdiamond, RFormula.varsR, RProgram.varsR, pvars, Program.fv,
    Program.bv, Formula.fv, Set.union_empty, Set.empty_union]

/-- `pvars (star P) = Program.vars P`. -/
theorem pvars_star (P : Program (Var 3)) : pvars (Program.star P) = Program.vars P := rfl

/-- `mvValidR`'s left variables are empty (it is a right projection). -/
theorem mvValidR_varsL (mv : Var 3) (k : ℕ) : (mvValidR mv k).varsL = (∅ : Set (Var 3)) := rfl

/-- `bigOr`'s free variables are bounded by any set bounding each disjunct's. -/
theorem bigOr_fv_subset {fs : List (Formula (Var 3))} {S : Set (Var 3)}
    (h : ∀ f ∈ fs, f.fv ⊆ S) : (bigOr fs).fv ⊆ S := by
  induction fs with
  | nil => intro v hv; exact absurd hv (by simp [bigOr, Formula.fv])
  | cons a as ih =>
      intro v hv
      simp only [bigOr, Formula.fv, Set.mem_union] at hv
      rcases hv with ha | hrest
      · exact h a (List.mem_cons.mpr (Or.inl rfl)) ha
      · exact ih (fun f hf => h f (List.mem_cons.mpr (Or.inr hf))) hrest

/-- `mvValid mv k` reads only `mv`. -/
theorem mvValid_fv (mv : Var 3) (k : ℕ) : (mvValid mv k).fv ⊆ {mv} := by
  refine bigOr_fv_subset ?_
  intro f hf
  simp only [List.mem_map, List.mem_range] at hf
  obtain ⟨q, -, rfl⟩ := hf
  intro v hv
  simpa only [modeIs, Formula.fv, Term.fv, Set.union_empty] using hv

/-- **`hddF` holds at concrete rover data.** The `faShape` left variables (all `Lv`) are disjoint from
its right variables (all `Rv`, plus the auxiliary mode variable `mv`) — the same side split as `hd`. -/
theorem rover_hddF :
    Disjoint (faShape (Program.star (bigChoice (roverL.leftProgs ++
          [Program.ode (leftBlock (fun _ => Term.const 0)) Formula.tt])))
        (Program.star (rightAutomatonBody roverGr roverMv))
        (RFormula.and roverInv (mvValidR roverMv roverGr.modes.length))).varsL
      ((Equiv.refl (Var 3)) '' (faShape (Program.star (bigChoice (roverL.leftProgs ++
          [Program.ode (leftBlock (fun _ => Term.const 0)) Formula.tt])))
        (Program.star (rightAutomatonBody roverGr roverMv))
        (RFormula.and roverInv (mvValidR roverMv roverGr.modes.length))).varsR) := by
  rw [Equiv.coe_refl, Set.image_id, Set.disjoint_left]
  intro v hL hR
  -- left side: v is Side.L
  rw [faShape_varsL, pvars_star, RFormula.varsL, mvValidR_varsL, Set.union_empty] at hL
  have hvL : v.1 = Side.L := by
    rcases hL with hα | hψ
    · exact rover_left_side_L hα
    · exact roverInv_varsL_side_L hψ
  -- right side: v is Side.R or v = mv
  rw [faShape_varsR, pvars_star, RFormula.varsR] at hR
  rcases hR with hβ | hψR
  · rcases rover_right_side_R_or_mv hβ with h | h
    · rw [hvL] at h; exact absurd h (by decide)
    · rw [h] at hvL; exact absurd hvL (by simp [roverMv, Av])
  · rcases hψR with hinv | hmvR
    · rw [roverInv_varsR_side_R hinv] at hvL; exact absurd hvL (by decide)
    · -- v ∈ (mvValidR roverMv k).varsR = (mvValid roverMv k).fv ⊆ {roverMv}
      have hvmv : v = roverMv := by
        have : v ∈ (mvValid roverMv roverGr.modes.length).fv := hmvR
        simpa only [Set.mem_singleton_iff] using mvValid_fv roverMv _ this
      rw [hvmv] at hvL; exact absurd hvL (by simp [roverMv, Av])

/-! ## Remaining concrete side-conditions -/

/-- Any auxiliary coordinate is outside any left block's bound set (all `Side.L`). -/
theorem av_notin_leftBlock_bound (f : Fin 3 → Term (Var 3)) (i : Fin 3) :
    (Av i) ∉ (leftBlock f).bound := by
  intro hv
  have hL : (Av i).1 = Side.L := by
    simp only [leftBlock, ODESystem.bound, List.map_map, List.mem_map, Function.comp] at hv
    obtain ⟨j, -, hj⟩ := hv; rw [← hj]
  exact absurd hL (by simp [Av])

/-- An auxiliary coordinate is outside any left block's read set, when the fields are left-sided. -/
theorem av_notin_leftBlock_readVars (f : Fin 3 → Term (Var 3))
    (hf : ∀ i, (f i).fv ⊆ {x : Var 3 | x.1 = Side.L}) (i : Fin 3) :
    (Av i) ∉ (leftBlock f).readVars := by
  intro hv
  simp only [ODESystem.readVars, leftBlock, Set.mem_setOf_eq, List.mem_map] at hv
  obtain ⟨p, ⟨j, -, rfl⟩, hx⟩ := hv
  exact absurd (hf j hx) (by simp [Av])

/-- Every variable read/written by a left block (left-sided fields) is on the left side. -/
theorem leftBlock_side_L (f : Fin 3 → Term (Var 3))
    (hf : ∀ i, (f i).fv ⊆ {x : Var 3 | x.1 = Side.L})
    {v : Var 3} (hv : v ∈ (leftBlock f).boundSet ∪ (leftBlock f).readVars) : v.1 = Side.L := by
  rcases hv with hb | hr
  · simp only [ODESystem.boundSet, leftBlock, ODESystem.bound, List.map_map, Set.mem_setOf_eq,
      List.mem_map, Function.comp] at hb
    obtain ⟨i, -, rfl⟩ := hb; rfl
  · simp only [ODESystem.readVars, leftBlock, Set.mem_setOf_eq, List.mem_map] at hr
    obtain ⟨p, ⟨i, -, rfl⟩, hx⟩ := hr
    exact hf i hx

/-- Any auxiliary coordinate is outside any right block's read/write set (all `Side.R`). -/
theorem av_notin_rightBlock (f : Fin 3 → Term (Var 3))
    (hf : ∀ i, (f i).fv ⊆ {x : Var 3 | x.1 = Side.R}) (i : Fin 3) :
    (Av i) ∉ (rightBlock f roverLam).boundSet ∪ (rightBlock f roverLam).readVars := by
  intro hv
  exact absurd (rightBlock_side_R f roverLam (by simp [roverLam, Term.fv]) hf hv) (by simp [Av])

/-- `roverFR`'s fields read only right-side coordinates. -/
theorem roverFR_side_R : ∀ i, (roverFR i).fv ⊆ {x : Var 3 | x.1 = Side.R} := by
  intro i; fin_cases i <;> simp [roverFR, Term.fv, Rv, Set.subset_def]

/-- Left/right footprint disjointness (the CSF `hdisj`). -/
theorem rover_LR_disjoint :
    Disjoint ((leftBlock roverFL).boundSet ∪ (leftBlock roverFL).readVars)
             ((rightBlock roverFR roverLam).boundSet ∪ (rightBlock roverFR roverLam).readVars) := by
  rw [Set.disjoint_left]
  intro v hL hR
  have h1 := leftBlock_side_L roverFL roverFL_side_L hL
  have h2 := rightBlock_side_R roverFR roverLam (by simp [roverLam, Term.fv]) roverFR_side_R hR
  rw [h1] at h2; exact absurd h2 (by decide)

/-- The right mode's `tg`-freshness bundle (`tg = Av i` outside the right block and trivial domain). -/
theorem av_notin_rightMode (i : Fin 3) :
    (Av i) ∉ (rightBlock roverFR roverLam).bound ∧
    (Av i) ∉ (rightBlock roverFR roverLam).readVars ∧
    (Av i) ∉ (rightBlock roverFR roverLam).boundSet ∧
    (Av i) ∉ (Formula.tt : Formula (Var 3)).fv := by
  have hb := av_notin_rightBlock roverFR roverFR_side_R i
  exact ⟨fun h => hb (Or.inl h), fun h => hb (Or.inr h), fun h => hb (Or.inl h), by simp [Formula.fv]⟩

/-! ## `HExistSeg` discharged via global existence (trivial `domR`, affine right field) -/

/-- The explicit right witness for the affine rover field, started at `base = ΦL s`: the `Rv`
coordinates follow the affine solution (`px` quadratic, `vx` linear, mode constant), every other
coordinate frozen to `base`. This is the global solution of `rightBlock roverFR roverLam` — no bounded
region to escape (`domR = ⊤`), so it discharges `HExistSeg` for EVERY `ν` (the field shape only needs
to be globally solvable; the banked region lemmas `hExist_from_rover` are for bounded `domR`). -/
noncomputable def roverΦR (base : State (Var 3)) (t : ℝ) : State (Var 3) :=
  fun x => if x = Rv 0 then base (Rv 0) + base (Rv 1) * t + (2 / 10) * t ^ 2
           else if x = Rv 1 then base (Rv 1) + (4 / 10) * t
           else base x

@[simp] theorem roverΦR_Rv0 (base : State (Var 3)) (t : ℝ) :
    roverΦR base t (Rv 0) = base (Rv 0) + base (Rv 1) * t + (2 / 10) * t ^ 2 := rfl

@[simp] theorem roverΦR_Rv1 (base : State (Var 3)) (t : ℝ) :
    roverΦR base t (Rv 1) = base (Rv 1) + (4 / 10) * t := by
  show (if (Rv 1 : Var 3) = Rv 0 then _ else if (Rv 1 : Var 3) = Rv 1 then _ else _) = _
  rw [if_neg (by decide), if_pos rfl]

@[simp] theorem roverΦR_other (base : State (Var 3)) (t : ℝ) {x : Var 3}
    (h0 : x ≠ Rv 0) (h1 : x ≠ Rv 1) : roverΦR base t x = base x := by
  simp only [roverΦR]; rw [if_neg h0, if_neg h1]

/-- **`∀ν HExistSeg` discharged for the affine rover field at trivial `domR`.** The global polynomial
solution `roverΦR` witnesses the right run for every `ν` — removing `HExistSeg` from the carried
boundary (it holds because `domR = ⊤` has no region to escape; contrast the bounded-`domR` case where
`∀ν HExistSeg` is false). -/
theorem hExistSeg_affine_tt (ν : State (Var 3)) :
    HExistSeg roverFL roverFR roverLam Formula.tt Formula.tt ν := by
  intro s ΦL hs0 hΦL0 _ hmaskL _
  refine ⟨roverΦR (ΦL s), ?_, ?_, ?_, fun t _ => by trivial⟩
  · -- ΦR 0 = ΦL s
    funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp
    · by_cases h1 : x = Rv 1
      · subst h1; simp
      · rw [roverΦR_other _ _ h0 h1]
  · -- right derivatives
    intro t _ p hp
    have hlist : rightBlock roverFR roverLam
        = [(Rv 0, Term.binop AOp.mul roverLam (Term.var (Rv 1))),
           (Rv 1, Term.binop AOp.mul roverLam (Term.const (4 / 10))),
           (Rv 2, Term.binop AOp.mul roverLam (Term.const 0))] := rfl
    rw [hlist, List.mem_cons, List.mem_cons, List.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · -- Rv 0: px' = vx  (deriv of the quadratic = vx(t))
      have hval : (Term.binop AOp.mul roverLam (Term.var (Rv 1))).eval (roverΦR (ΦL s) t)
          = ΦL s (Rv 1) + (4 / 10) * t := by simp [roverLam, Term.eval, AOp.interp]
      have hfun : (fun u => roverΦR (ΦL s) u (Rv 0, Term.binop AOp.mul roverLam (Term.var (Rv 1))).1)
          = fun u => ΦL s (Rv 0) + ΦL s (Rv 1) * u + (2 / 10) * u ^ 2 := by funext u; simp
      rw [hfun, hval]
      exact ((((hasDerivAt_const t (ΦL s (Rv 0))).add
        ((hasDerivAt_id t).const_mul (ΦL s (Rv 1)))).add
        ((hasDerivAt_pow 2 t).const_mul (2 / 10))).congr_deriv (by push_cast; ring)).hasDerivWithinAt
    · -- Rv 1: vx' = 0.4
      have hval : (Term.binop AOp.mul roverLam (Term.const (4 / 10))).eval (roverΦR (ΦL s) t)
          = 4 / 10 := by simp [roverLam, Term.eval, AOp.interp]
      have hfun : (fun u => roverΦR (ΦL s) u (Rv 1, Term.binop AOp.mul roverLam (Term.const (4/10))).1)
          = fun u => ΦL s (Rv 1) + (4 / 10) * u := by funext u; simp
      rw [hfun, hval]
      exact (((hasDerivAt_const t (ΦL s (Rv 1))).add
        ((hasDerivAt_id t).const_mul (4 / 10))).congr_deriv (by ring)).hasDerivWithinAt
    · -- Rv 2: mode' = 0
      have hval : (Term.binop AOp.mul roverLam (Term.const 0)).eval (roverΦR (ΦL s) t) = 0 := by
        simp [roverLam, Term.eval, AOp.interp]
      have hfun : (fun u => roverΦR (ΦL s) u (Rv 2, Term.binop AOp.mul roverLam (Term.const 0)).1)
          = fun _ => ΦL s (Rv 2) := by
        funext u; exact roverΦR_other _ _ (by decide) (by decide)
      rw [hfun, hval]
      exact (hasDerivAt_const t (ΦL s (Rv 2))).hasDerivWithinAt
  · -- right mask: coords outside the right block are frozen to ΦL s
    intro t _ x hx
    have h0 : x ≠ Rv 0 := by rintro rfl; exact hx (by simp [rightBlock, ODESystem.bound, Rv])
    have h1 : x ≠ Rv 1 := by rintro rfl; exact hx (by simp [rightBlock, ODESystem.bound, Rv])
    exact roverΦR_other _ _ h0 h1

/-- **The full `tooling_sound` instantiation at concrete rover data — non-vacuous.** Everything
structural is discharged concretely: `graphOf`, `RightProjAlign` (derived, Task 2), the freshness
(`mv = Av 1`, `tg = Av 0`, both `Aux`), and the `∀∃` disjointness `hd`/`hddF` (side split). The Z3-leaf
`cert`/`cert_repo`, the emit `EmitSegs` (`hemit`/`hemit'`), the field-shape `HExistSeg` (`hHExist`,
carried), and the reposition `Gj_repo`/`hRPA_dyn` remain PARAMETRIC — the established honest boundaries.
The antecedents are jointly satisfiable (freshness discharged, `hd` holds — contrast
`ProbeMvHd.probe_hd_false`), so this is a genuine, non-vacuous certification of the end-to-end theorem
at real benchmark-shaped data. `#print axioms = [propext, Classical.choice, Quot.sound]`. -/
theorem rover_tooling_sound (dt : ℝ) (hdt : 0 ≤ dt)
    (cert : CoverCert (graphOf_Gj roverL roverR roverLam roverLm) roverG)
    (hHExist : ∀ ν, HExistSeg roverFL roverFR roverLam Formula.tt Formula.tt ν)
    (hemit : EmitSegs roverGr roverG roverMv roverFL Formula.tt roverTg dt)
    (Gj_repo : SearchGraph (Var 3)) (cert_repo : CoverCert Gj_repo roverG)
    (hRPA_dyn : RightProjAlign_dyn Gj_repo roverGr roverG roverMv Formula.tt roverLam)
    (hemit' : EmitSegs roverGr roverG roverMv (fun _ => Term.const 0) Formula.tt roverTg dt) :
    RFormula.rvalid (theorem3Form
      (bigChoice (roverL.leftProgs ++ [Program.ode (leftBlock (fun _ => Term.const 0)) Formula.tt]))
      (rightAutomatonBody roverGr roverMv)
      (RFormula.and roverInv (mvValidR roverMv roverGr.modes.length))) := by
  have hg : roverMv ∉ roverG.fv := rover_mv_fresh_satisfiable.2.1
  -- the per-mode CSF side-conditions (structural + carried HExistSeg)
  have hside : graphOfSide roverL roverR roverLam roverLm := by
    intro q mR hmR
    rcases q with _ | q
    · -- q = 0: mR = roverRm
      simp only [roverR, List.getElem?_cons_zero, Option.some.injEq] at hmR
      subst hmR
      refine ⟨rover_LR_disjoint, by simp [roverRm, Formula.fv], hHExist, by simp [roverRm], ?_⟩
      intro tgt htgt
      simp only [roverRm, List.mem_singleton] at htgt; subst htgt; simp [roverR]
    · simp [roverR] at hmR
  -- freshness (mv, tg in Aux; trivial domain)
  have hfr : graphOfFresh roverMv roverTg roverLm := by
    refine ⟨av_notin_leftBlock_bound roverFL 1, by simp [roverLm, Formula.fv],
      av_notin_leftBlock_bound roverFL 0, av_notin_leftBlock_readVars roverFL roverFL_side_L 0,
      by simp [roverLm, Formula.fv]⟩
  -- assemble the single flow mode, apply the family theorem via tooling_sound
  refine tooling_sound roverL roverR roverG roverMv roverLam roverTg dt roverInv hdt hg rover_hψ
    [graphOfFlowMode roverL roverR roverG roverMv roverLam roverTg dt roverLm cert hg hside hfr hemit]
    rfl Gj_repo cert_repo Formula.tt
    (av_notin_leftBlock_bound _ 1) (by simp [Formula.fv])
    (av_notin_leftBlock_bound _ 0) (av_notin_leftBlock_readVars _ const0_side_L 0)
    (by simp [Formula.fv]) hRPA_dyn hemit'
    rover_tg_fresh_satisfiable.2.2 ?_ ?_ ?_ ?_ rover_hd_holds rover_hddF
  · -- htgRight : tg = Av 0 outside every right mode's block/domain
    intro q m hm
    rcases q with _ | q
    · simp only [SearchGraph.modeAt, roverGr, graphOf_Gr, roverR, List.map_cons, List.map_nil,
        List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm; exact av_notin_rightMode 0
    · simp [SearchGraph.modeAt, roverGr, graphOf_Gr, roverR] at hm
  · -- hfresh : mv = Av 1 not read by any right mode ODE
    intro q m hm
    rcases q with _ | q
    · simp only [SearchGraph.modeAt, roverGr, graphOf_Gr, roverR, List.map_cons, List.map_nil,
        List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      intro hv
      simp only [roverRm, Program.fv, Formula.fv, Set.union_empty, Set.mem_union] at hv
      exact (av_notin_rightBlock roverFR roverFR_side_R 1) hv
    · simp [SearchGraph.modeAt, roverGr, graphOf_Gr, roverR] at hm
  · -- htt : every declared edge is ⊤-guarded
    intro q e he
    rw [SearchGraph.edgesFrom, show (graphOf_Gr roverR roverLam).edges = _ from roverGr_edges,
      List.mem_filter] at he
    obtain ⟨hmem, -⟩ := he
    rw [List.mem_singleton] at hmem; subst hmem; rfl
  · -- hlt : every edge target is in range
    intro q e he
    rw [SearchGraph.edgesFrom, show (graphOf_Gr roverR roverLam).edges = _ from roverGr_edges,
      List.mem_filter] at he
    obtain ⟨hmem, -⟩ := he
    rw [List.mem_singleton] at hmem; subst hmem
    simp [roverGr, graphOf_Gr, roverR]

/-- **The fuller representative — `tooling_sound` with `HExistSeg` ALSO discharged.** Same concrete
rover instantiation as `rover_tooling_sound`, but the field-shape side-condition `HExistSeg` is
discharged concretely (`hExistSeg_affine_tt`, global existence at trivial `domR`) instead of carried.
So this instantiation carries ONLY the two irreducible boundaries — the Z3 leaf (`cert`/`cert_repo`,
`z3_unsat_sound` at construction) and the emit `EmitSegs` — plus the reposition cover; freshness,
disjointness, `graphOf`, `RightProjAlign`, AND `HExistSeg` are all concrete. The cleanest non-vacuous
certification of the end-to-end theorem at rover data. `#print axioms` picks up `z3_unsat_sound` only
through the supplied `cert`s. -/
theorem rover_tooling_sound_full (dt : ℝ) (hdt : 0 ≤ dt)
    (cert : CoverCert (graphOf_Gj roverL roverR roverLam roverLm) roverG)
    (hemit : EmitSegs roverGr roverG roverMv roverFL Formula.tt roverTg dt)
    (Gj_repo : SearchGraph (Var 3)) (cert_repo : CoverCert Gj_repo roverG)
    (hRPA_dyn : RightProjAlign_dyn Gj_repo roverGr roverG roverMv Formula.tt roverLam)
    (hemit' : EmitSegs roverGr roverG roverMv (fun _ => Term.const 0) Formula.tt roverTg dt) :
    RFormula.rvalid (theorem3Form
      (bigChoice (roverL.leftProgs ++ [Program.ode (leftBlock (fun _ => Term.const 0)) Formula.tt]))
      (rightAutomatonBody roverGr roverMv)
      (RFormula.and roverInv (mvValidR roverMv roverGr.modes.length))) :=
  rover_tooling_sound dt hdt cert hExistSeg_affine_tt hemit Gj_repo cert_repo hRPA_dyn hemit'

end RelCertifier
