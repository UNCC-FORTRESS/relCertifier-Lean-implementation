/-
STEP 4 — one WORKED discharge of the carried well-formedness H (`WellFormedFlowB`), demonstrating H is
genuinely dischargeable (not just "checkable in principle").

The benchmark class where H holds cleanly: STABILIZING (decay) modes. Field `v' = −v` (a stabilizing field,
`robot_braking`/`match_multi_eps` shape), evolve `v ∈ [0,1]`. From ANY admissible initial condition
`v₀ ∈ [0,1]`, the explicit solution `v(t) = v₀·exp(−t)` stays in `[0, v₀] ⊆ [0,1]` for ALL `t ≥ 0` — the flow
moves INWARD.

`decay_stays` MECHANIZES the crux: the domain-staying clause of `WellFormedFlowB` for this field, `∀ base`,
all `t ≥ 0`. This is EXACTLY the clause that FAILS for growing-bounded modes (`WellFormedFlowB_rover_boundary
_false`: the boundary base exits). So the discriminating content of H — "does a `≤dt` execution stay in
evolve" — is discharged here by the field shape + analytic staying, `∀base`, no reachability, for any initial
condition. (The remaining `WellFormedFlowB` clauses — the flow EXISTS with the field's derivatives — are
standard Picard/ODE-existence for the smooth field `v'=−v`; the `decayΦR` witness realizes them, its Rv0
derivative being `−v` by `Real.hasDerivAt_exp`. The staying, mechanized here, is the part that separates
stabilizing (H holds) from growing-bounded (H fails).)
-/
import RelCertifier.MultisegLanding

namespace RelCertifier
open DL DLCalTiming Function Set

/-- The stabilizing (decay) field on `Rv 0` (`v' = −v`), other coordinates frozen. -/
noncomputable def decayFR : Fin 3 → Term (Var 3)
  | 0 => Term.binop AOp.mul (Term.const (-1)) (Term.var (Rv 0))
  | _ => Term.const 0

/-- Evolve domain `0 ≤ v ≤ 1` (`v = Rv 0`). -/
noncomputable def decayDom : Formula (Var 3) :=
  Formula.and (Formula.cmp CompOp.le (Term.const 0) (Term.var (Rv 0)))
              (Formula.cmp CompOp.le (Term.var (Rv 0)) (Term.const 1))

/-- The explicit decay solution `v(t) = v₀·exp(−t)`, other coordinates frozen. Its `Rv 0` derivative is
`−v` (`Real.hasDerivAt_exp` composed with negation) — so it is a genuine right-flow of `decayFR`. -/
noncomputable def decayΦR (base : State (Var 3)) (t : ℝ) : State (Var 3) :=
  fun x => if x = Rv 0 then base (Rv 0) * Real.exp (-t) else base x

@[simp] theorem decayΦR_Rv0 (base : State (Var 3)) (t : ℝ) :
    decayΦR base t (Rv 0) = base (Rv 0) * Real.exp (-t) := rfl

/-- The decay solution's `Rv 0` coordinate has derivative `−v` — confirming it solves `v' = −v`. -/
theorem decayΦR_hasDeriv (base : State (Var 3)) (t : ℝ) :
    HasDerivAt (fun u => decayΦR base u (Rv 0)) (-(decayΦR base t (Rv 0))) t := by
  have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
    have h := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    simp only [Function.comp_def, mul_neg, mul_one] at h; exact h
  simp only [decayΦR_Rv0]
  rw [show -(base (Rv 0) * Real.exp (-t)) = base (Rv 0) * (-Real.exp (-t)) from by ring]
  exact h1.const_mul _

/-- **WORKED DISCHARGE (the crux, mechanized): the domain-staying clause of `WellFormedFlowB` holds for the
stabilizing decay mode, `∀base`.** From ANY admissible base `∈ decayDom` (any initial condition `v₀∈[0,1]`),
the decay flow stays in `[0,1]` for ALL `t ≥ 0` — the flow moves inward (`v(t) = v₀·exp(−t) ∈ [0,v₀]`). This
is EXACTLY the clause that fails for growing-bounded modes (`WellFormedFlowB_rover_boundary_false`). So H's
discriminating content is discharged here by field-shape + analytic staying — no reachability, any initial
condition. -/
theorem decay_stays (base : State (Var 3)) (hb : Formula.sat decayDom base) (t : ℝ) (ht : 0 ≤ t) :
    Formula.sat decayDom (decayΦR base t) := by
  simp only [decayDom, Formula.sat, CompOp.interp, Term.eval] at hb ⊢
  have hv0 : (0 : ℝ) ≤ base (Rv 0) := hb.1
  have hv1 : base (Rv 0) ≤ 1 := hb.2
  have hexp1 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  rw [decayΦR_Rv0]
  refine ⟨by positivity, ?_⟩
  calc base (Rv 0) * Real.exp (-t) ≤ base (Rv 0) * 1 := mul_le_mul_of_nonneg_left hexp1 hv0
    _ = base (Rv 0) := by ring
    _ ≤ 1 := hv1

end RelCertifier
