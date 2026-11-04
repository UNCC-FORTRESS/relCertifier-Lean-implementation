/-
# Mode facts narrow flow queries: the semantic step

The certifier (`OracleAPI.checkedCut`) narrows a mode's flow-query domains by a mode fact `S`
(Definition 2) only after checking, per atomic conjunct, (O1) entry: the mode's guard implies
it, and (O2) invariance: it is preserved along the mode's own flow (DI routes B/A, or the
contraction shape whose Lean backing is `contract_stays`/`WellFormedFlowB_contract`). The
model is never modified: every mode's ODE domain stays the system's single evolution domain
(Appendix B.2), so the uniform-domain proofs (`UniformEvol.lean`, `GuardThreaded.lean`) apply
unchanged.

This file proves the semantic step that connects a certificate over the narrowed domain back
to the uniform-domain obligations those proofs consume:

* `sem_ode_and_of_stays` — run inclusion: an `ode(D)`-run whose trace satisfies `S`
  throughout IS an `ode(D ∧ S)`-run (definitional: the ODE semantics asks for the domain
  formula pointwise along the flow, and the trace satisfies both conjuncts).
* `boxLe_cut_lift` — the lift: if `g ≤ 0` is certified over the narrowed domain (`BoxLe` for
  `ode(D ∧ S)`, what the narrowed Z3 query establishes through `flow_cert_sound`) and every
  `ode(D)`-run from `ν` stays in `S` (what O2 guarantees from an O1-entry state; for the
  settling shapes, `contract_stays`/`staying_from_margin`), then `g ≤ 0` holds at every
  `ode(D)`-endpoint from `ν`, the uniform-domain `BoxLe` the `GuardSettlingH` chain consumes
  at guard bases.

So a mode fact, by run inclusion and staying, yields the uniform-domain certificate: no
per-mode domain enters the model, and the trust base is unchanged (the same `z3_unsat_sound`
axiom for the O2 queries and the narrowed `g`-queries).
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

/-- **The mode-fact lift.** `BoxLe` for `ode(D ∧ S)` at `ν` (the narrowed flow query) plus
staying in `S` along every `ode(D)`-run from `ν` give `BoxLe` for `ode(D)` at `ν`, the
hypothesis shape the `GuardSettlingH`/landing chain consumes at guard bases. -/
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
