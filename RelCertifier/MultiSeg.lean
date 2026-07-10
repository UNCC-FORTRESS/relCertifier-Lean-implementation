/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# B>1 — the multi-segment ∀∃ witness composition (clock-free)

The non-trivial ∀∃ case: the right switches modes mid-residence to respond to the left. Per
Gate 0, this is **clock-free** — no `tg` coordinate, no `ExtVar`. The composition `multiseg`
assembles `B` per-segment couplings (`pair_faModal`, proven) into a `B`-fold lockstep `faModal`,
via the proven `faModal_seq` (both-sides sequential) + `faModal_MR` (rule of consequence),
by induction on `B`. Each step peels one right segment coupled with one left `piter` factor.

Remaining after this file (the one analytic piece): `ode` **self-concatenation**
`sem (ode sys ϕ ; ode sys ϕ) = sem (ode sys ϕ)` — so `piter leftOde B ≡ leftOde` and the
`B`-fold left collapses to the single left residence. It mirrors `plantT_glue`'s junction
differentiability, minus the clock. Then `faModal_loopN` lifts the right to `star`, and
`faModal_MULTI` (proven) closes the loop.
-/
import RelCertifier.ToolLevel

namespace RelCertifier

open DL DLCalTiming DLRel

variable {n : ℕ}

/-- `piter` does not introduce variables beyond its body. -/
theorem vars_piter_subset (Q : Program (Var n)) :
    ∀ B, Program.vars (piter Q B) ⊆ Program.vars Q := by
  intro B
  induction B with
  | zero =>
      intro x hx
      simp [piter, Program.vars, Program.fv, Program.bv, Formula.fv] at hx
  | succ B ih =>
      have hfv : (piter Q B).fv ⊆ Program.vars Q := Set.subset_union_left.trans ih
      have hbv : (piter Q B).bv ⊆ Program.vars Q := Set.subset_union_right.trans ih
      simp only [piter, Program.vars, Program.fv, Program.bv]
      refine Set.union_subset (Set.union_subset ?_ ?_) (Set.union_subset ?_ ?_)
      · exact Set.subset_union_left
      · exact Set.diff_subset.trans hfv
      · exact Set.subset_union_right
      · exact hbv

/-- **The multi-segment lockstep composition (clock-free).** Given a per-segment coupling
`hcouple` (one left factor ↔ one right segment, preserving the invariant `φinv` — discharged by
`pair_faModal`) and left/right variable disjointness, the `B`-fold lockstep `faModal` over
`piter leftOde B` (left) and `piter rightStep B` (right) preserves `φinv`. By induction on `B`
via `faModal_seq` (both-sides sequential) + `faModal_MR` (consequence). `ρ = id`. -/
theorem multiseg (leftOde rightStep : Program (Var n)) (φinv : Formula (Var n))
    (hdis : Disjoint (Program.vars (rightStep.rename (Equiv.refl (Var n))))
                     (Program.vars leftOde))
    (hcouple : ∀ σ, Formula.sat φinv σ →
        Formula.sat (faModal (Equiv.refl (Var n)) leftOde rightStep φinv) σ) :
    ∀ (B : ℕ) (ω : State (Var n)), Formula.sat φinv ω →
      Formula.sat (faModal (Equiv.refl (Var n)) (piter leftOde B) (piter rightStep B) φinv) ω := by
  intro B
  induction B with
  | zero =>
      intro ω hω
      simp only [piter]
      rw [faModal_sat]
      intro ν hν
      rw [sem_test] at hν
      obtain ⟨rfl, _⟩ := hν
      exact ⟨ω, by rw [rename_test, sem_test]; exact ⟨rfl, trivial⟩, hω⟩
  | succ B ih =>
      intro ω hω
      simp only [piter]
      refine faModal_seq (Equiv.refl (Var n)) leftOde (piter leftOde B) rightStep
        (piter rightStep B) φinv ω ?_ ?_
      · exact Set.disjoint_of_subset_right (vars_piter_subset leftOde B) hdis
      · refine faModal_MR (Equiv.refl (Var n)) leftOde rightStep φinv _ ω (hcouple ω hω) ?_
        intro μ hμ
        exact ih μ hμ

end RelCertifier
