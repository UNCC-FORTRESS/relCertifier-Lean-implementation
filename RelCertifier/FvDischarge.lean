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

namespace RelCertifier
open DL DLCalTiming Set

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

end RelCertifier
