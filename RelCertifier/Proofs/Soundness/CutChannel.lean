/-
# The checked-cut channel — the Lean tie

The certifier (`OracleAPI.checkedCut`) narrows a mode's flow-query domains by a CUT `S` only
after re-deriving, per atomic conjunct, (O1) entry — the mode's guard implies it — and (O2)
invariance — it is flow-invariant along the mode's own field (DI routes B/A, or the tangent-
capable contract shape whose Lean backing is `contract_stays`/`WellFormedFlowB_contract`).
The MODEL is never modified: every mode's ODE domain stays the literal shared envelope, so
the uniform-evol proof structure (`UniformEvol.lean`, `GuardThreaded.lean`) is untouched.

This file proves the semantic step that connects a CUT-DOMAIN certificate back to the
UNIFORM-DOMAIN obligations those proofs consume:

* `sem_ode_and_of_stays` — run inclusion: an `ode(D)`-run whose trace satisfies `S`
  throughout IS an `ode(D ∧ S)`-run (definitional: the ODE semantics asks for the domain
  formula pointwise along the flow, and the trace satisfies both conjuncts).
* `boxLe_cut_lift` — the lift: if `g ≤ 0` is certified over the CUT domain (`BoxLe` for
  `ode(D ∧ S)` — what the narrowed Z3 query establishes, via the same `flow_cert_sound`
  leaves as always) and every `ode(D)`-run from `ν` stays in `S` (what O2-invariance
  guarantees from an O1-entry state — for the settling shapes, exactly
  `contract_stays`/`staying_from_margin`), then `g ≤ 0` holds at every `ode(D)`-endpoint
  from `ν` — the uniform-domain `BoxLe` the `GuardSettlingH` chain consumes at guard bases.

So: checked cut ⟹ (run inclusion + staying) ⟹ uniform-domain certificate — no per-mode
domain ever enters the model, and the trust boundary is unchanged (the same `z3_unsat_sound`
leaf at both the O2 queries and the narrowed g-queries; the kernel for this file).
-/
import RelCertifier.Proofs.Soundness.GuardThreaded

namespace RelCertifier
open DL Function Set

variable {n : ℕ}

/-- **Run inclusion.** An `ode(D)`-run whose trace satisfies `S` at every time is an
`ode(D ∧ S)`-run: the ODE semantics requires the domain formula pointwise along the flow,
and the trace satisfies both conjuncts. -/
theorem sem_ode_and_of_stays (sys : ODESystem (Var n)) (D S : Formula (Var n))
    {ω ν : State (Var n)} (h : Program.sem (Program.ode sys D) ω ν)
    (hstay : ∀ (r : ℝ) (Φ : ℝ → State (Var n)), 0 ≤ r → Φ 0 = ω → Φ r = ν →
      (∀ t ∈ Icc (0 : ℝ) r, ∀ p ∈ sys,
          HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0 : ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = ω x) →
      (∀ t ∈ Icc (0 : ℝ) r, Formula.sat D (Φ t)) →
      ∀ t ∈ Icc (0 : ℝ) r, Formula.sat S (Φ t)) :
    Program.sem (Program.ode sys (Formula.and D S)) ω ν := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  exact ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, fun t ht =>
    ⟨hdom t ht, hstay r Φ hr hΦ0 hΦr hder hmask hdom t ht⟩⟩

/-- **The cut lift.** A certificate over the CUT domain (`BoxLe` for `ode(D ∧ S)` — the
narrowed flow query) plus flow-invariance of the cut from `ν` (O2, from an O1-entry state)
give the UNIFORM-domain certificate `BoxLe` for `ode(D)` at `ν` — the hypothesis shape the
`GuardSettlingH`/landing chain consumes at guard bases. -/
theorem boxLe_cut_lift (sys : ODESystem (Var n)) (D S : Formula (Var n)) (g : Term (Var n))
    (ν : State (Var n))
    (hcut : BoxLe (Program.ode sys (Formula.and D S)) (fun ω => Term.eval g ω) ν)
    (hstay : ∀ (r : ℝ) (Φ : ℝ → State (Var n)), 0 ≤ r → Φ 0 = ν →
      (∀ t ∈ Icc (0 : ℝ) r, ∀ p ∈ sys,
          HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0 : ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = ν x) →
      (∀ t ∈ Icc (0 : ℝ) r, Formula.sat D (Φ t)) →
      ∀ t ∈ Icc (0 : ℝ) r, Formula.sat S (Φ t)) :
    BoxLe (Program.ode sys D) (fun ω => Term.eval g ω) ν := by
  intro μ' hsem
  exact hcut μ' (sem_ode_and_of_stays sys D S hsem
    (fun r Φ hr hΦ0 _ hder hmask hdom => hstay r Φ hr hΦ0 hder hmask hdom))

end RelCertifier
