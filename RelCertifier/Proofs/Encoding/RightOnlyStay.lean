/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Superlevel invariance along a right-only flow

The `CutLiftX` O2 lemmas (`boxle_R_of_super` and the `super_*` shapes) state the invariance of
a right atom along the JOINT system. A guarded response also needs it along the right's OWN
flow (the reference's run inside a response, read off the run), e.g. to show that the run
stays in the guard of the mode it runs in, so that its closing self-loop is legal. The Lie
derivative of a right term along `rightBlock fR λ` is its one-sided Lie derivative scaled by
`λ` (`lie_rightBlock`), so every `super_*` shape lemma applies unchanged
(`boxle_Ronly_of_super`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Soundness.CutLiftX

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

theorem rightBlock_wellFormed (fR : Fin n → Term (Var n)) (lam : Term (Var n)) :
    (rightBlock fR lam).WellFormed := by
  have h := jointSys_wellFormed (fun _ => Term.const 0) fR lam
  unfold ODESystem.WellFormed at h ⊢
  rw [jointSys_split, List.map_append] at h
  exact (List.nodup_append.mp h).2.1

/-- Along the right block, a term's Lie derivative is the joint one with a zero left field. -/
theorem lie_rightBlock (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (g : State (Var n) → ℝ) (x : State (Var n)) :
    Lie (rightBlock fR lam) g x = Lie (jointSys (fun _ => Term.const 0) fR lam) g x := by
  unfold Lie
  rw [jointSys_split, List.map_append, List.sum_append]
  have h0 : ((leftBlock (fun _ => Term.const (0:ℝ)) : ODESystem (Var n)).map
      (fun p => fderiv ℝ g x (Pi.single p.1 1) * Term.eval p.2 x)).sum = 0 := by
    unfold leftBlock
    rw [List.map_map]
    refine List.sum_eq_zero (fun a ha => ?_)
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    show fderiv ℝ g x (Pi.single (Lv i) 1) * Term.eval (Term.const 0) x = 0
    rw [show Term.eval (Term.const (0:ℝ)) x = 0 from rfl, mul_zero]
  rw [h0, zero_add]

/-- **Superlevel O2 along the right's own flow** (the right-only counterpart of
`boxle_R_of_super`). -/
theorem boxle_Ronly_of_super (g : Term (Var n)) (fR : Fin n → Term (Var n)) (c : ℝ)
    (hc : 0 ≤ c) (dom D : Formula (Var n)) (hfv : ∀ i : Fin n, Lv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat D x)
    (hsup : ∀ z, Formula.sat D z → 0 ≤ Term.eval g z → Term.eval (lie1R g fR) z ≤ 0)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (rightBlock fR (Term.const c)) dom) (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_superlevel (rightBlock_wellFormed fR (Term.const c))
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [lie_rightBlock, ← lieDeriv_correct, lieDeriv_one_sided_R g _ fR c hfv]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hsup x (hdomImp x hx) hge)

end RelCertifier
