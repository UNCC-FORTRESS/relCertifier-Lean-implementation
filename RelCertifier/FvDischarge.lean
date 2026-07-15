/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Freshness discharge (the phase-A′ `fv ⊆ Rv` helpers, finally built)

Every formula the checker builds — `envF`, `bandDom`, `GdOf` — mentions only right-side
coordinates `Rv i`. Hence any AUX-side choice of the mode variable `mv` and the clock `tg`
is automatically fresh, and the whole freshness block of `WellFormedSound` discharges
generically: `wellformed_sound_aux` below consumes ONLY the checker certificate, the
invariant-term side split (`g` mentions no Aux coordinates), and the Z3 certificates.
-/
import RelCertifier.WellFormedChecker
import RelCertifier.ClockedTop

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

/-! ## `fv ⊆ Rv` for the checker's formulas -/

theorem Band.formula_fv_sub (i : Fin n) (b : Band) :
    (Band.formula i b).fv ⊆ range Rv := by
  unfold Band.formula
  rcases b.lo with _ | l <;> rcases b.hi with _ | h <;>
    simp [Formula.fv, Term.fv] <;>
    intro x hx <;>
    first
      | (rcases hx with hx | hx) <;> simp_all [mem_range]
      | simp_all [mem_range]

theorem envF_fv_sub (M : SettlingModel n) : M.envF.fv ⊆ range Rv := by
  unfold SettlingModel.envF
  induction (List.finRange n) with
  | nil => simp [Formula.fv]
  | cons a t ih =>
      simp only [List.foldr_cons, Formula.fv]
      exact union_subset (Band.formula_fv_sub a (M.env a)) ih

theorem bandDom_fv_sub (j : Fin n) (lo hi : ℝ) : (bandDom j lo hi).fv ⊆ range Rv := by
  unfold bandDom
  simp only [Formula.fv, Term.fv]
  intro x hx
  rcases hx with (hx | hx) | (hx | hx) <;> simp_all [mem_range]

theorem GdOf_fv_sub (M : SettlingModel n) (q : ℕ) : (M.GdOf q).fv ⊆ range Rv := by
  unfold SettlingModel.GdOf
  rcases M.modes[q]? with _ | m
  · simp [Formula.fv]
  · exact union_subset (envF_fv_sub M) (bandDom_fv_sub m.gcoord _ _)

/-! ## Aux-side freshness -/

/-- An Aux coordinate is never an `Rv`. -/
theorem aux_ne_Rv (a i : Fin n) : (Side.Aux, a) ≠ Rv i := by
  intro h
  exact absurd (congrArg Prod.fst h) (by simp)

theorem aux_notin_GdOf (M : SettlingModel n) (a : Fin n) (q : ℕ) :
    ((Side.Aux, a) : Var n) ∉ (M.GdOf q).fv := by
  intro hmem
  obtain ⟨i, hi⟩ := GdOf_fv_sub M q hmem
  exact aux_ne_Rv a i hi.symm

/-- The clocked left block binds only `Lv`s and the clock. -/
theorem clk_leftBlock_bound (tg : Var n) (fL : Fin n → Term (Var n)) :
    ∀ x ∈ (DLCalTiming.clk tg (leftBlock fL)).bound, x = tg ∨ ∃ i, x = Lv i := by
  intro x hx
  simp only [DLCalTiming.clk, ODESystem.bound, leftBlock, List.map_append, List.map_map,
    List.mem_append, List.mem_map, List.mem_finRange] at hx
  rcases hx with ⟨i, -, rfl⟩ | hx
  · exact Or.inr ⟨i, rfl⟩
  · obtain ⟨p, hp, hpx⟩ := hx
    rw [List.mem_singleton] at hp
    subst hp
    exact Or.inl hpx.symm

theorem aux_notin_clk_bound {a : Fin n} {b : Fin n} (fL : Fin n → Term (Var n))
    (hab : a ≠ b) :
    ((Side.Aux, a) : Var n) ∉ (DLCalTiming.clk ((Side.Aux, b) : Var n)
      (leftBlock fL)).bound := by
  intro hmem
  rcases clk_leftBlock_bound _ fL _ hmem with h | ⟨i, h⟩
  · exact hab (by injection h)
  · exact absurd (congrArg Prod.fst h) (by simp)

theorem Rv_notin_clk_bound {b : Fin n} (fL : Fin n → Term (Var n)) (i : Fin n) :
    (Rv i : Var n) ∉ (DLCalTiming.clk ((Side.Aux, b) : Var n) (leftBlock fL)).bound := by
  intro hmem
  rcases clk_leftBlock_bound _ fL _ hmem with h | ⟨j, h⟩
  · exact absurd (congrArg Prod.fst h) (by simp)
  · exact absurd (congrArg Prod.fst h) (by simp)

/-! ## The bookkeeping-free reduction theorem -/

/-- **`wellformed_sound`, Aux-instantiated**: with `mv := (Aux, a)`, `tg := (Aux, b)`,
`a ≠ b`, every freshness hypothesis discharges generically. What remains is the checker
certificate, `dt ≥ 0`, the invariant term's side split (no Aux reads), and the Z3
certificates — the pipeline's designed residuals. -/
theorem wellformed_sound_aux (M : SettlingModel n) (a b : Fin n) (hab : a ≠ b)
    (g : Term (Var n)) (fL : Fin n → Term (Var n))
    (hwf : decideWellFormed M = true)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ))
    (hgAux : ∀ i : Fin n, ((Side.Aux, i) : Var n) ∉ g.fv)
    (hcert : ∀ q m, M.graph.modeAt q = some m → ∀ ν, Formula.sat (M.GdOf q) ν →
        BoxLe (Program.ode m.sys M.envF) (fun ω => Term.eval g ω) ν) :
    GuardSettlingH M.graph M.GdOf ((Side.Aux, a) : Var n) g (Term.const 1)
      ((Side.Aux, b) : Var n) (M.dt : ℝ) fL M.envF := by
  refine wellformed_sound M _ _ g fL hwf hdt (hgAux a) (aux_notin_clk_bound fL hab)
    (by intro h; exact hab (by injection h)) (fun q' => aux_notin_GdOf M a q')
    (fun q' => aux_notin_GdOf M b q') ?_ hcert
  intro q' x hx
  obtain ⟨i, hi⟩ := GdOf_fv_sub M q' hx
  rw [← hi]
  exact Rv_notin_clk_bound fL i

/-! ## Field terms read only `Rv`s (per shape) -/

/-- The damper fold of `drivenDamp` reads only `Rv`s. -/
theorem dampFold_fv_sub (dampers : List (Fin n × ℤ × ℤ)) :
    (dampers.foldr (fun d acc =>
        Term.binop AOp.sub acc
          (Term.binop AOp.mul (Term.const ((d.2.1 : ℝ) / (d.2.2 : ℝ)))
            (Term.binop AOp.mul (Term.var (Rv d.1)) (Term.var (Rv d.1)))))
      (Term.const 1) : Term (Var n)).fv ⊆ range Rv := by
  induction dampers with
  | nil => simp [Term.fv]
  | cons d tl ih =>
      simp only [List.foldr_cons, Term.fv]
      refine union_subset ih ?_
      intro x hx
      rcases hx with hx | (hx | hx) <;> simp_all [mem_range]

/-- Every shape's field term reads only right-side coordinates. -/
theorem field_fv_sub (i : Fin n) (sh : CoordShape n) :
    (CoordShape.field i sh).fv ⊆ range Rv := by
  cases sh with
  | drivenDamp j dampers =>
      simp only [CoordShape.field, Term.fv]
      refine union_subset ?_ (dampFold_fv_sub dampers)
      intro x hx; simp_all [mem_range]
  | _ =>
      simp only [CoordShape.field, Term.fv] <;>
      intro x hx <;>
      first
        | exact absurd hx (Set.not_mem_empty x)
        | ((repeat' (rcases hx with hx | hx)) <;>
           first
             | exact absurd hx (Set.not_mem_empty x)
             | simp_all [mem_range])

theorem rightBlock_bound_sub (fR : Fin n → Term (Var n)) (lam : Term (Var n)) :
    ∀ x ∈ (rightBlock fR lam).bound, ∃ i, x = Rv i := by
  intro x hx
  simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map,
    List.mem_finRange] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ⟨i, rfl⟩

/-- `rightBlock` is injective in the fields (needed because the cadenced theorem's
`tg`-hygiene hypothesis quantifies over every `fR` presenting the mode's system). -/
theorem rightBlock_inj {fR fR' : Fin n → Term (Var n)} {lam : Term (Var n)}
    (h : rightBlock fR lam = rightBlock fR' lam) : fR = fR' := by
  funext i
  have hmem : ((Rv i : Var n), Term.binop AOp.mul lam (fR i)) ∈ rightBlock fR lam := by
    simp only [rightBlock, List.mem_map, List.mem_finRange]
    exact ⟨i, trivial, rfl⟩
  rw [h] at hmem
  simp only [rightBlock, List.mem_map, List.mem_finRange] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  have hji : j = i := by
    have h1 := congrArg Prod.fst hj
    simp only [Rv, Prod.mk.injEq] at h1
    exact h1.2
  subst hji
  have h2 := congrArg Prod.snd hj
  simp only at h2
  injection h2 with _ h3 h4
  first
    | exact h4
    | exact h4.symm

/-- An Aux clock is fresh for every checker mode's system: the bound and the field terms
live on the `Rv` side. -/
theorem aux_tgS (M : SettlingModel n) (b : Fin n) :
    ∀ q m, M.graph.modeAt q = some m → ∀ fR, m.sys = rightBlock fR (Term.const 1) →
      ((Side.Aux, b) : Var n) ∉ (rightBlock fR (Term.const 1)).bound ∧
      (∀ p ∈ rightBlock fR (Term.const 1),
        ((Side.Aux, b) : Var n) ∉ (p.2 : Term (Var n)).fv) := by
  intro q m hm fR hsys
  rw [graph_modeAt] at hm
  obtain ⟨SM, hSM, rfl⟩ := Option.map_eq_some_iff.mp hm
  have hfr : fR = SM.fieldOf := by
    refine rightBlock_inj (lam := Term.const 1) ?_
    have h0 : (SM.toRMode M).sys = rightBlock SM.fieldOf (Term.const 1) := rfl
    rw [← hsys, h0]
  subst hfr
  constructor
  · intro hmem
    obtain ⟨i, hi⟩ := rightBlock_bound_sub SM.fieldOf (Term.const 1) _ hmem
    exact aux_ne_Rv b i hi
  · intro p hp hmem
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    simp only [Term.fv, Set.empty_union] at hmem
    obtain ⟨j, hj⟩ := field_fv_sub i (SM.shapes i) (by
      simpa [SettlingMode.fieldOf] using hmem)
    exact aux_ne_Rv b j hj.symm

theorem aux_notin_envF (M : SettlingModel n) (b : Fin n) :
    ((Side.Aux, b) : Var n) ∉ M.envF.fv := by
  intro hmem
  obtain ⟨i, hi⟩ := envF_fv_sub M hmem
  exact aux_ne_Rv b i hi.symm

/-- **The generic Aux-instantiated end-to-end theorem** (any checker model, `mv = (Aux, a)`,
`tg = (Aux, b)`, `a ≠ b`): checker certificate → the ε-cadenced ∀∃ refinement claim, with
every freshness and clock-hygiene hypothesis discharged. Residuals: the invariant
encoding, the invariant's Aux-freshness, the two variable-hygiene facts, and the Z3
certificates. -/
theorem settling_end_to_end_aux (M : SettlingModel n) (a b c : Fin n) (hab : a ≠ b)
    (g : Term (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (ϕinv : RFormula (Var n))
    (hwf : decideWellFormed M = true)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hgAux : ∀ i : Fin n, ((Side.Aux, i) : Var n) ∉ g.fv)
    (hdis : Disjoint (Program.vars (clockedSeg (leftBlock fL) domL
          ((Side.Aux, b) : Var n) (M.dt : ℝ)))
        (Program.vars ((Program.star (rightAutomatonBodyC M.graph
          ((Side.Aux, a) : Var n) ((Side.Aux, c) : Var n) (M.dt : ℝ))).rename
          (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (clockedSeg (leftBlock fL) domL
            ((Side.Aux, b) : Var n) (M.dt : ℝ)))
          (Program.star (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n)
            ((Side.Aux, c) : Var n) (M.dt : ℝ)))
          (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL
            ((Side.Aux, b) : Var n) (M.dt : ℝ)))
          (Program.star (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n)
            ((Side.Aux, c) : Var n) (M.dt : ℝ)))
          (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)).varsR))
    (hcert : ∀ q m, M.graph.modeAt q = some m → ∀ ν, Formula.sat (M.GdOf q) ν →
        BoxLe (Program.ode m.sys M.envF) (fun ω => Term.eval g ω) ν) :
    RFormula.rvalid (theorem3Form
      (clockedSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) (M.dt : ℝ))
      (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n) ((Side.Aux, c) : Var n)
        (M.dt : ℝ))
      (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)) := by
  have hH := wellformed_sound_aux M a b hab g fL hwf hdt hgAux hcert
  exact theorem3_faithful_settling_cadenced' M.graph M.GdOf _ g fL domL M.envF _
    ((Side.Aux, c) : Var n) (M.dt : ℝ) (Term.const 1) ϕinv hψ hH (hgAux c)
    (aux_tgS M c) (aux_notin_envF M c) (fun q' => aux_notin_GdOf M c q') hdis hddF

/-! ## `Program.vars` bounds and the `hdis` discharger -/

theorem vars_bigChoiceP_sub (ps : List (Program (Var n))) (S : Set (Var n))
    (h : ∀ p ∈ ps, Program.vars p ⊆ S) : Program.vars (bigChoiceP ps) ⊆ S := by
  induction ps with
  | nil =>
      simp [bigChoiceP, Program.vars, Program.fv, Program.bv, Formula.fv]
  | cons p ps ih =>
      have hp := h p (List.mem_cons_self ..)
      have hps := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [bigChoiceP, Program.vars, Program.fv, Program.bv] at hp hps ⊢
      intro x hx
      rcases hx with (hx | hx) | (hx | hx)
      · exact hp (Or.inl hx)
      · exact hps (Or.inl hx)
      · exact hp (Or.inr hx)
      · exact hps (Or.inr hx)

/-- Compositional over-approximations of `Program.vars` (the `seq` minus-terms only
shrink, so the plain unions bound them). -/
theorem vars_seq_sub (α β : Program (Var n)) :
    Program.vars (Program.seq α β) ⊆ Program.vars α ∪ Program.vars β := by
  simp only [Program.vars, Program.fv, Program.bv]
  intro x hx
  rcases hx with hx | hx
  · rcases hx with hx | ⟨hx, -⟩
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
  · rcases hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)

theorem vars_choice_sub (α β : Program (Var n)) :
    Program.vars (Program.choice α β) ⊆ Program.vars α ∪ Program.vars β := by
  simp only [Program.vars, Program.fv, Program.bv]
  intro x hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
  · rcases hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)

theorem vars_star_eq (α : Program (Var n)) :
    Program.vars (Program.star α) = Program.vars α := rfl

theorem vars_test_eq (φ : Formula (Var n)) : Program.vars (Program.test φ) = φ.fv := by
  simp [Program.vars, Program.fv, Program.bv]

theorem vars_assign_sub (x : Var n) (e : Term (Var n)) :
    Program.vars (Program.assign x e) ⊆ {x} ∪ e.fv := by
  simp only [Program.vars, Program.fv, Program.bv]
  intro y hy
  rcases hy with hy | hy
  · exact Or.inr hy
  · exact Or.inl hy

theorem vars_ode_sub (sys : ODESystem (Var n)) (dom : Formula (Var n)) :
    Program.vars (Program.ode sys dom) ⊆ sys.boundSet ∪ sys.readVars ∪ dom.fv := by
  simp only [Program.vars, Program.fv, Program.bv]
  intro x hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  · exact Or.inl (Or.inl hx)

theorem clk_boundSet_sub (tg : Var n) (sys : ODESystem (Var n)) :
    (DLCalTiming.clk tg sys).boundSet ⊆ sys.boundSet ∪ {tg} := by
  intro y hy
  simp only [DLCalTiming.clk, ODESystem.boundSet, ODESystem.bound, List.map_append,
    List.mem_append, Set.mem_setOf_eq, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hy
  rcases hy with hy | hy
  · exact Or.inl hy
  · exact Or.inr hy

theorem clk_readVars_sub (tg : Var n) (sys : ODESystem (Var n)) :
    (DLCalTiming.clk tg sys).readVars ⊆ sys.readVars := by
  intro y hy
  simp only [DLCalTiming.clk, ODESystem.readVars, Set.mem_setOf_eq, List.mem_append,
    List.mem_singleton] at hy ⊢
  obtain ⟨p, hp, hyp⟩ := hy
  rcases hp with hp | hp
  · exact ⟨p, hp, hyp⟩
  · subst hp
    exact absurd hyp (by simp [Term.fv])

theorem vars_clockedSeg_sub (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) :
    Program.vars (clockedSeg leftSys domL tg dt)
      ⊆ {tg} ∪ leftSys.boundSet ∪ leftSys.readVars ∪ domL.fv := by
  intro x hx
  rcases vars_seq_sub _ _ hx with hx | hx
  · rcases vars_assign_sub tg (Term.const 0) hx with hx | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact absurd hx (by simp [Term.fv])
  · rcases vars_seq_sub _ _ hx with hx | hx
    · rcases vars_ode_sub _ _ hx with (hx | hx) | hx
      · rcases clk_boundSet_sub tg leftSys hx with hx | hx
        · exact Or.inl (Or.inl (Or.inr hx))
        · exact Or.inl (Or.inl (Or.inl hx))
      · exact Or.inl (Or.inr (clk_readVars_sub tg leftSys hx))
      · exact Or.inr hx
    · rw [vars_test_eq] at hx
      simp only [clkGuard, Formula.fv, Term.fv] at hx
      rcases hx with hx | hx
      · exact Or.inl (Or.inl (Or.inl hx))
      · exact absurd hx (by simp)

/-- Left block binds only `Lv`s. -/
theorem leftBlock_boundSet_sub (fL : Fin n → Term (Var n)) :
    (leftBlock fL).boundSet ⊆ range Lv := by
  intro x hx
  simp only [leftBlock, ODESystem.boundSet, ODESystem.bound, List.map_map,
    Set.mem_setOf_eq, List.mem_map, List.mem_finRange] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ⟨i, rfl⟩

theorem leftBlock_readVars_sub (fL : Fin n → Term (Var n))
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) : (leftBlock fL).readVars ⊆ range Lv := by
  intro x hx
  simp only [leftBlock, ODESystem.readVars, Set.mem_setOf_eq, List.mem_map,
    List.mem_finRange] at hx
  obtain ⟨p, ⟨i, -, rfl⟩, hxp⟩ := hx
  exact hfL i hxp

/-- One cadenced mode step of a checker model touches only `mv`, its clock, and `Rv`s. -/
theorem vars_modeStepC_sub (M : SettlingModel n) (mv tr : Var n) (dt : ℝ) (q : ℕ)
    (SM : SettlingMode n) (hq : M.graph.modeAt q = some (SM.toRMode M)) :
    Program.vars (modeStepC M.graph mv tr dt q (SM.toRMode M))
      ⊆ {mv, tr} ∪ range Rv := by
  intro x hx
  rcases vars_seq_sub _ _ hx with hx | hx
  · rw [vars_test_eq] at hx
    simp only [modeIs, Formula.fv, Term.fv] at hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact absurd hx (by simp)
  · rcases vars_seq_sub _ _ hx with hx | hx
    · rcases vars_clockedSeg_sub _ _ _ _ hx with ((hx | hx) | hx) | hx
      · exact Or.inl (Or.inr hx)
      · -- bound of the mode system
        obtain ⟨i, hi⟩ := rightBlock_bound_sub SM.fieldOf (Term.const 1) x
          (by simpa [SettlingMode.toRMode, ODESystem.boundSet] using hx)
        exact Or.inr (hi ▸ mem_range_self i)
      · -- reads of the mode system
        simp only [SettlingMode.toRMode, ODESystem.readVars, rightBlock,
          Set.mem_setOf_eq, List.mem_map, List.mem_finRange] at hx
        obtain ⟨p, ⟨i, -, rfl⟩, hxp⟩ := hx
        simp only [Term.fv, Set.empty_union] at hxp
        obtain ⟨j, hj⟩ := field_fv_sub i (SM.shapes i)
          (by simpa [SettlingMode.fieldOf] using hxp)
        exact Or.inr (hj ▸ ⟨j, rfl⟩)
      · -- the domain: the shared envelope
        exact Or.inr (envF_fv_sub M (by simpa [SettlingMode.toRMode] using hx))
    · -- the jumps: guards are ⊤, assigns write `mv`
      refine vars_bigChoiceP_sub _ _ ?_ hx
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨e, hef, rfl⟩ := hp
      have hguard : e.guard = Formula.tt := by
        have hmem : e ∈ M.graph.edges := List.mem_of_mem_filter hef
        exact (graph_edges_shape M hmem).1
      intro y hy
      rcases vars_seq_sub _ _ hy with hy | hy
      · rw [vars_test_eq, hguard] at hy
        exact absurd hy (by simp [Formula.fv])
      · rcases vars_assign_sub mv _ hy with hy | hy
        · exact Or.inl (Or.inl hy)
        · exact absurd hy (by simp [Term.fv])

/-- The cadenced right automaton of a checker model touches only `mv`, its clock, and
`Rv`s. -/
theorem vars_bodyC_sub (M : SettlingModel n) (mv tr : Var n) (dt : ℝ) :
    Program.vars (rightAutomatonBodyC M.graph mv tr dt) ⊆ {mv, tr} ∪ range Rv := by
  refine vars_bigChoiceP_sub _ _ ?_
  intro p hp
  simp only [rightAutomatonBodyC, List.mem_filterMap, List.mem_range] at hp
  obtain ⟨q, -, hq⟩ := hp
  rcases hm : M.graph.modeAt q with _ | m
  · rw [hm] at hq; simp at hq
  · rw [hm] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    have hm' := hm
    rw [graph_modeAt] at hm'
    obtain ⟨SM, hSM, hEq⟩ := Option.map_eq_some_iff.mp hm'
    rw [← hEq] at hm ⊢
    exact vars_modeStepC_sub M mv tr dt q SM hm

/-- **The `hdis` discharger**: for a checker model with Aux mode variable, Aux clocks,
side-split left fields and left domain, the loop rule's disjointness holds. -/
theorem hdis_aux (M : SettlingModel n) (a b c : Fin n)
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (dt : ℝ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hba : b ≠ a) (hbc : b ≠ c) :
    Disjoint
      (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) dt))
      (Program.vars ((Program.star (rightAutomatonBodyC M.graph
        ((Side.Aux, a) : Var n) ((Side.Aux, c) : Var n) dt)).rename
        (Equiv.refl (Var n)))) := by
  rw [Set.disjoint_left]
  intro x hxL hxR
  have hL := vars_clockedSeg_sub (leftBlock fL) domL ((Side.Aux, b) : Var n) dt hxL
  have hR : x ∈ ({((Side.Aux, a) : Var n), ((Side.Aux, c) : Var n)} : Set (Var n))
      ∪ range Rv := by
    refine vars_bodyC_sub M _ _ dt ?_
    rwa [Program.rename_refl, vars_star_eq] at hxR
  -- the left side is {Aux b} ∪ Lv-image; the right side {Aux a, Aux c} ∪ Rv-image
  have hLside : x = ((Side.Aux, b) : Var n) ∨ ∃ i, x = Lv i := by
    rcases hL with ((hx | hx) | hx) | hx
    · exact Or.inl hx
    · rcases leftBlock_boundSet_sub fL hx with ⟨i, hi⟩
      exact Or.inr ⟨i, hi.symm⟩
    · rcases leftBlock_readVars_sub fL hfL hx with ⟨i, hi⟩
      exact Or.inr ⟨i, hi.symm⟩
    · rcases hdomL hx with ⟨i, hi⟩
      exact Or.inr ⟨i, hi.symm⟩
  rcases hLside with rfl | ⟨i, rfl⟩
  · rcases hR with hx | ⟨j, hj⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨-, h⟩ | ⟨-, h⟩
      · exact hba h
      · exact hbc h
    · exact aux_ne_Rv b j hj.symm
  · rcases hR with hx | ⟨j, hj⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Lv, Prod.mk.injEq] at hx
      rcases hx with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by simp)
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-! ## The `hddF` discharger: shape disjointness from side-splits -/

/-- Side separation: a set inside `{Aux b} ∪ Lv`-side is disjoint from a set inside
`{Aux a, Aux c} ∪ Rv`-side whenever `b ∉ {a, c}`. -/
theorem sides_disjoint {S T : Set (Var n)} (a b c : Fin n) (hba : b ≠ a) (hbc : b ≠ c)
    (hS : S ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hT : T ⊆ ({((Side.Aux, a) : Var n), ((Side.Aux, c) : Var n)} : Set (Var n))
      ∪ range Rv) : Disjoint S T := by
  rw [Set.disjoint_left]
  intro x hxS hxT
  rcases hS hxS with hx | ⟨i, rfl⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rcases hT hxT with hx | ⟨j, hj⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨-, h⟩ | ⟨-, h⟩
      · exact hba h
      · exact hbc h
    · exact aux_ne_Rv b j hj.symm
  · rcases hT hxT with hx | ⟨j, hj⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Lv, Prod.mk.injEq] at hx
      rcases hx with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by simp)
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- The clocked left segment touches only its clock and `Lv`s (given side-split data). -/
theorem vars_clockedSegL_sub (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (b : Fin n) (dt : ℝ) (hfL : ∀ i, (fL i).fv ⊆ range Lv)
    (hdomL : domL.fv ⊆ range Lv) :
    Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) dt)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv := by
  intro x hx
  rcases vars_clockedSeg_sub _ _ _ _ hx with ((hx | hx) | hx) | hx
  · exact Or.inl hx
  · exact Or.inr (leftBlock_boundSet_sub fL hx)
  · exact Or.inr (leftBlock_readVars_sub fL hfL hx)
  · exact Or.inr (hdomL hx)

/-- `faShape`'s left variables: the left program's plus the postcondition's. -/
theorem faShape_varsL' (α β : Program (Var n)) (ψ : RFormula (Var n)) :
    (faShape α β ψ).varsL = pvars α ∪ ψ.varsL := by
  simp only [faShape, RFormula.rdiamond, RFormula.varsL, RProgram.varsL, pvars, Program.fv,
    Program.bv, Formula.fv, Set.union_empty, Set.empty_union]

/-- `faShape`'s right variables: the right program's plus the postcondition's. -/
theorem faShape_varsR' (α β : Program (Var n)) (ψ : RFormula (Var n)) :
    (faShape α β ψ).varsR = pvars β ∪ ψ.varsR := by
  simp only [faShape, RFormula.rdiamond, RFormula.varsR, RProgram.varsR, pvars, Program.fv,
    Program.bv, Formula.fv, Set.union_empty, Set.empty_union]

/-- `pvars (star P) = Program.vars P`. -/
theorem pvars_star' (P : Program (Var n)) : pvars (Program.star P) = Program.vars P := rfl

/-- `bigOr`'s free variables are bounded by any set bounding each disjunct's. -/
theorem bigOr_fv_sub {fs : List (Formula (Var n))} {S : Set (Var n)}
    (h : ∀ f ∈ fs, f.fv ⊆ S) : (bigOr fs).fv ⊆ S := by
  induction fs with
  | nil => intro v hv; exact absurd hv (by simp [bigOr, Formula.fv])
  | cons a as ih =>
      intro v hv
      simp only [bigOr, Formula.fv, Set.mem_union] at hv
      rcases hv with ha | hrest
      · exact h a (List.mem_cons.mpr (Or.inl rfl)) ha
      · exact ih (fun f hf => h f (List.mem_cons.mpr (Or.inr hf))) hrest

/-- `mvValid` reads only `mv`. -/
theorem mvValid_fv_sub (mv : Var n) (k : ℕ) : (mvValid mv k).fv ⊆ {mv} := by
  refine bigOr_fv_sub ?_
  intro f hf
  simp only [List.mem_map, List.mem_range] at hf
  obtain ⟨q, -, rfl⟩ := hf
  intro v hv
  simpa only [modeIs, Formula.fv, Term.fv, Set.union_empty] using hv

/-- `inModeGuardF` of a checker model reads only `mv` and `Rv`s. -/
theorem inModeGuardF_fv_sub (M : SettlingModel n) (mv : Var n) :
    (inModeGuardF M.graph M.GdOf mv).fv ⊆ {mv} ∪ range Rv := by
  refine bigOr_fv_sub ?_
  intro f hf
  simp only [List.mem_filterMap, List.mem_range] at hf
  obtain ⟨q, -, hq⟩ := hf
  rcases hm : M.graph.modeAt q with _ | m
  · rw [hm] at hq; simp at hq
  · rw [hm] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    intro v hv
    simp only [Formula.fv, modeIs, Term.fv, Set.union_empty, Set.mem_union] at hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (GdOf_fv_sub M q hv)

/-- `ψpostG`'s left variables are exactly the invariant's. -/
theorem ψpostG_varsL (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (ϕinv : RFormula (Var n)) :
    (ψpostG G Gd mv ϕinv).varsL = ϕinv.varsL := by
  simp only [ψpostG, mvValidR, inModeGuardR, RFormula.varsL, Set.union_empty]

/-- `ψpostG`'s right variables: the invariant's, `mv`, and (for a checker model) `Rv`s. -/
theorem ψpostG_varsR_sub (M : SettlingModel n) (mv : Var n) (ϕinv : RFormula (Var n)) :
    (ψpostG M.graph M.GdOf mv ϕinv).varsR ⊆ ϕinv.varsR ∪ ({mv} ∪ range Rv) := by
  simp only [ψpostG, mvValidR, inModeGuardR, RFormula.varsR]
  refine Set.union_subset (Set.subset_union_left) (Set.union_subset ?_ ?_)
  · exact fun v hv =>
      Or.inr (Or.inl (mvValid_fv_sub mv M.graph.modes.length hv))
  · exact fun v hv => Or.inr (inModeGuardF_fv_sub M mv hv)

/-- **The `hddF` discharger**: the shape disjointness of `settling_end_to_end_aux` from
side-split data on the left field/domain and the invariant. -/
theorem hddF_aux (M : SettlingModel n) (a b c : Fin n)
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (dt : ℝ)
    (ϕinv : RFormula (Var n))
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hba : b ≠ a) (hbc : b ≠ c) :
    Disjoint (faShape (Program.star (clockedSeg (leftBlock fL) domL
          ((Side.Aux, b) : Var n) dt))
        (Program.star (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n)
          ((Side.Aux, c) : Var n) dt))
        (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL
          ((Side.Aux, b) : Var n) dt))
        (Program.star (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n)
          ((Side.Aux, c) : Var n) dt))
        (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by
    intro S; simp]
  refine sides_disjoint a b c hba hbc ?_ ?_
  · rw [faShape_varsL', pvars_star', ψpostG_varsL]
    exact Set.union_subset (vars_clockedSegL_sub fL domL b dt hfL hdomL)
      (fun v hv => Or.inr (hinvL hv))
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      exact vars_bodyC_sub M _ _ dt hv
    · intro v hv
      rcases ψpostG_varsR_sub M _ ϕinv hv with hv | hv | hv
      · exact Or.inr (hinvR hv)
      · exact Or.inl (Or.inl hv)
      · exact Or.inr hv

/-- **Discharged end-to-end**: `settling_end_to_end_aux` with both disjointness
hypotheses replaced by their side-split dischargers. What remains is per-benchmark
data: well-formedness, the encoding identity, side-splits, and the Z3-certified
`BoxLe` facts. -/
theorem settling_end_to_end (M : SettlingModel n) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c)
    (g : Term (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (ϕinv : RFormula (Var n))
    (hwf : decideWellFormed M = true)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hgAux : ∀ i : Fin n, ((Side.Aux, i) : Var n) ∉ g.fv)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hcert : ∀ q m, M.graph.modeAt q = some m → ∀ ν, Formula.sat (M.GdOf q) ν →
        BoxLe (Program.ode m.sys M.envF) (fun ω => Term.eval g ω) ν) :
    RFormula.rvalid (theorem3Form
      (clockedSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) (M.dt : ℝ))
      (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n) ((Side.Aux, c) : Var n)
        (M.dt : ℝ))
      (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)) :=
  settling_end_to_end_aux M a b c hab g fL domL ϕinv hwf hdt hψ hgAux
    (hdis_aux M a b c fL domL (M.dt : ℝ) hfL hdomL hab.symm hbc)
    (hddF_aux M a b c fL domL (M.dt : ℝ) ϕinv hfL hdomL hinvL hinvR hab.symm hbc)
    hcert

end RelCertifier
