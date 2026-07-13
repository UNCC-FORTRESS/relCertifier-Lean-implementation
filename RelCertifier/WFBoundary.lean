/-
`WFBoundary` — the named well-formedness hypothesis that discharges `HExistSeg` at a fold junction.

This is a COMPLETENESS condition (witness-existence), NOT a soundness fix: soundness is independently
done (`cover_sound` checks invariant-preservation on the real dynamics; the ⊤-automaton ∃ is the sound
over-approximation). `HExistSeg` is the ∃-witness-existence side-condition; it discharges freely for
shared/widening domains, and for narrowing it is true-but-unmechanized because the ⊤-model strips the
edge guard the fold would need at the junction. `WFBoundary` states that missing piece as a named,
honest, checkable well-formedness assumption.

Two clauses:
* `coherence` (STATIC, checkable per edge, `decide`/Z3): source domain ∧ successor guard ⟹ successor
  domain. True per benchmark (for rover Recover→Drive: `vx∈[0,1] ∧ vx≥0.3 ⟹ vx∈[0.3,1]`). This is
  exactly `WellFormedGuards` (banked, `GuardLegality.lean`).
* `guardHolds` (the ASSUMED bridge): the successor guard holds at the junction state `ν`. True for a
  well-formed automaton (a fold boundary IS a real in-domain switch) — but it is the part the ⊤-model
  does not mechanize (it strips the guard to `⊤`), so it is stated as the honest assumption.
`inCur` (the junction is in the source domain) comes for free from the coupling (the prior segment's
right run ends in its own domain).

`coherence ∧ inCur ∧ guardHolds ⟹ ν ∈ domR_succ`, then the banked `WellFormedFlow` existence discharges
`HExistSeg`. Uniform across all switch shapes — for shared/widening `coherence` is guard-free (the guard
is irrelevant), for narrowing it uses the guard; both are static checks, one proof structure.
-/
import RelCertifier.WellFormedFlow

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- **The named boundary well-formedness hypothesis.** At a fold junction `ν` entering a segment of
mode `succ` (domain `domR`) from a source mode (domain `domCur`) across an edge with guard `guardSucc`:
the static per-edge coherence, the (free) source-membership, and the assumed guard-at-boundary. -/
structure WFBoundary (domCur domR guardSucc : Formula (Var n)) (ν : State (Var n)) : Prop where
  /-- clause 1 — STATIC, checkable per edge (`decide`/Z3): `domCur ∧ guardSucc ⟹ domR`. -/
  coherence : ∀ μ, Formula.sat domCur μ → Formula.sat guardSucc μ → Formula.sat domR μ
  /-- free from the coupling: the junction lies in the source mode's domain. -/
  inCur : Formula.sat domCur ν
  /-- clause 2 — the ASSUMED bridge: the successor guard holds at the junction (fold boundary is a real
  in-domain switch). True for well-formed automata; the part the ⊤-model leaves unmechanized. -/
  guardHolds : Formula.sat guardSucc ν

/-- The junction is in the successor's domain — clause 1 applied to the source-membership + assumed
guard. This is the `sat domR ν` the `HExistSeg` consumer needs. -/
theorem WFBoundary.entryDom {domCur domR guardSucc : Formula (Var n)} {ν : State (Var n)}
    (h : WFBoundary domCur domR guardSucc ν) : Formula.sat domR ν :=
  h.coherence ν h.inCur h.guardHolds

/-- **`HExistSeg` discharged at the junction from `WFBoundary` + `WellFormedFlow`.** The per-mode flow
well-formedness (existence, banked) supplies the domain-staying right run from any in-domain start;
`WFBoundary` supplies that the junction IS in-domain (via coherence + assumed guard). Uniform for
shared/widening and narrowing — the only difference is whether `coherence` needs the guard, a static
check, not a proof-structure split. -/
theorem hExistSeg_of_WFBoundary (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domCur domR guardSucc : Formula (Var n)) (ν : State (Var n))
    (hwff : WellFormedFlow fR lam domR)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hb : WFBoundary domCur domR guardSucc ν) :
    HExistSeg fL fR lam domL domR ν :=
  hExistSeg_of_wellFormedFlow fL fR lam domL domR ν hwff hfrz hb.entryDom

/-! ## Non-vacuity — clause 1 is TRUE (not the false `invariant ⟹ domain` trap) -/

/-- The velocity coordinate. -/
private abbrev vx : Var 3 := Rv 1

/-- **Clause 1 for the NARROWING edge is true and provable** — rover Recover→Drive shape:
`domCur = vx∈[0,1]`, `guardSucc = vx≥0.3`, `domR = vx∈[0.3,1]`, and `vx∈[0,1] ∧ vx≥0.3 ⟹ vx∈[0.3,1]`.
A static real-arithmetic per-edge implication — non-vacuous (`vx=0.5` satisfies all), NOT the false
universal `invLe g ⟹ domR`. This is exactly the shape `decide`/Z3 checks per benchmark edge. -/
theorem narrowing_coherence_true :
    ∀ μ : State (Var 3),
      Formula.sat (Formula.and (Formula.cmp CompOp.le (Term.const 0) (Term.var vx))
                               (Formula.cmp CompOp.le (Term.var vx) (Term.const 1))) μ →
      Formula.sat (Formula.cmp CompOp.le (Term.const (3/10)) (Term.var vx)) μ →
      Formula.sat (Formula.and (Formula.cmp CompOp.le (Term.const (3/10)) (Term.var vx))
                               (Formula.cmp CompOp.le (Term.var vx) (Term.const 1))) μ := by
  intro μ hcur hguard
  simp only [Formula.sat, CompOp.interp, Term.eval] at *
  exact ⟨hguard, hcur.2⟩

/-- **`WFBoundary` is inhabited at a genuine landing state** (`vx=0.3`, satisfying source domain,
guard, and successor domain) — so the hypothesis is satisfiable, non-vacuous. The three clauses hold
together at a real switch state; `WFBoundary` is not a `False`-antecedent trap. -/
theorem WFBoundary_narrowing_satisfiable (ν : State (Var 3)) (hν : ν vx = 3/10) :
    WFBoundary (Formula.and (Formula.cmp CompOp.le (Term.const 0) (Term.var vx))
                            (Formula.cmp CompOp.le (Term.var vx) (Term.const 1)))
      (Formula.and (Formula.cmp CompOp.le (Term.const (3/10)) (Term.var vx))
                   (Formula.cmp CompOp.le (Term.var vx) (Term.const 1)))
      (Formula.cmp CompOp.le (Term.const (3/10)) (Term.var vx)) ν where
  coherence := narrowing_coherence_true
  inCur := by
    simp only [Formula.sat, CompOp.interp, Term.eval, hν]; constructor <;> norm_num
  guardHolds := by simp only [Formula.sat, CompOp.interp, Term.eval, hν]; norm_num

end RelCertifier
