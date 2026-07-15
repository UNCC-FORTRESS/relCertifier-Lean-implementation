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
theorem settling_end_to_end_aux (M : SettlingModel n) (a b : Fin n) (hab : a ≠ b)
    (g : Term (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (ϕinv : RFormula (Var n))
    (hwf : decideWellFormed M = true)
    (hdt : (0 : ℝ) ≤ (M.dt : ℝ))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hgAux : ∀ i : Fin n, ((Side.Aux, i) : Var n) ∉ g.fv)
    (hdis : Disjoint (Program.vars (clockedSeg (leftBlock fL) domL
          ((Side.Aux, b) : Var n) (M.dt : ℝ)))
        (Program.vars ((Program.star (rightAutomatonBodyC M.graph
          ((Side.Aux, a) : Var n) ((Side.Aux, b) : Var n) (M.dt : ℝ))).rename
          (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (clockedSeg (leftBlock fL) domL
            ((Side.Aux, b) : Var n) (M.dt : ℝ)))
          (Program.star (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n)
            ((Side.Aux, b) : Var n) (M.dt : ℝ)))
          (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL
            ((Side.Aux, b) : Var n) (M.dt : ℝ)))
          (Program.star (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n)
            ((Side.Aux, b) : Var n) (M.dt : ℝ)))
          (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)).varsR))
    (hcert : ∀ q m, M.graph.modeAt q = some m → ∀ ν, Formula.sat (M.GdOf q) ν →
        BoxLe (Program.ode m.sys M.envF) (fun ω => Term.eval g ω) ν) :
    RFormula.rvalid (theorem3Form
      (clockedSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) (M.dt : ℝ))
      (rightAutomatonBodyC M.graph ((Side.Aux, a) : Var n) ((Side.Aux, b) : Var n)
        (M.dt : ℝ))
      (ψpostG M.graph M.GdOf ((Side.Aux, a) : Var n) ϕinv)) := by
  have hH := wellformed_sound_aux M a b hab g fL hwf hdt hgAux hcert
  exact theorem3_faithful_settling_cadenced' M.graph M.GdOf _ g fL domL M.envF _
    (M.dt : ℝ) (Term.const 1) ϕinv hψ hH (hgAux b) (aux_tgS M b) (aux_notin_envF M b)
    hdis hddF

end RelCertifier
