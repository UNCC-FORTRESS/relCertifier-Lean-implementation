/-
`WFBoundary`: a boundary well-formedness hypothesis that discharges `HExistSeg` (existence of a
domain-staying right run for a segment) at the junction between two segments of a multi-flow run.

No theorem of the paper route (Appendix B.1) consumes the declarations below. The landing
construction of `Proofs/Flow/MultisegLanding.lean` selects the landing mode by its guard, so the
guard clause `guardHolds` holds there by construction; `MultisegLanding` imports this file only to
state that it does not need it. Assumption 1 (`WellFormedRIn`) is the well-formedness hypothesis the
paper's theorems use.

`HExistSeg` is a witness-existence side condition, not a soundness condition: invariant preservation
is checked separately on the dynamics. It holds directly when the successor's domain contains the
source's (shared or widening domains); for a narrowing domain it needs the junction to satisfy the
edge guard, which `WFBoundary` names.

Clauses:
* `coherence` (static, checkable per edge): source domain ∧ successor guard ⟹ successor domain
  (for the rover Recover→Drive edge: `vx∈[0,1] ∧ vx≥0.3 ⟹ vx∈[0.3,1]`).
* `inCur`: the junction lies in the source domain, which the previous segment's right run provides.
* `guardHolds`: the successor guard holds at the junction state `ν`.

Together they give `ν ∈ domR`, and `WellFormedFlow` then discharges `HExistSeg`
(`hExistSeg_of_WFBoundary`).
-/
import RelCertifier.Proofs.Flow.WellFormedFlow

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- **The boundary well-formedness hypothesis** at a junction state `ν` entering a segment of a
successor mode (domain `domR`) from a source mode (domain `domCur`) across an edge with guard
`guardSucc`: per-edge coherence `domCur ∧ guardSucc ⟹ domR`, `ν ∈ domCur`, and `ν ⊨ guardSucc`. -/
structure WFBoundary (domCur domR guardSucc : Formula (Var n)) (ν : State (Var n)) : Prop where
  /-- Static per-edge coherence: every state of `domCur` satisfying `guardSucc` satisfies `domR`. -/
  coherence : ∀ μ, Formula.sat domCur μ → Formula.sat guardSucc μ → Formula.sat domR μ
  /-- The junction lies in the source mode's domain. -/
  inCur : Formula.sat domCur ν
  /-- The successor guard holds at the junction. -/
  guardHolds : Formula.sat guardSucc ν

/-- The junction is in the successor's domain: `coherence` applied to `inCur` and `guardHolds`. -/
theorem WFBoundary.entryDom {domCur domR guardSucc : Formula (Var n)} {ν : State (Var n)}
    (h : WFBoundary domCur domR guardSucc ν) : Formula.sat domR ν :=
  h.coherence ν h.inCur h.guardHolds

/-- **`HExistSeg` at the junction from `WFBoundary` and `WellFormedFlow`.** If the right flow is
well formed on `domR` (`WellFormedFlow`), `domR` reads no coordinate the left block evolves, and
`WFBoundary domCur domR guardSucc ν` holds, then `HExistSeg fL fR lam domL domR ν`. -/
theorem hExistSeg_of_WFBoundary (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domCur domR guardSucc : Formula (Var n)) (ν : State (Var n))
    (hwff : WellFormedFlow fR lam domR)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hb : WFBoundary domCur domR guardSucc ν) :
    HExistSeg fL fR lam domL domR ν :=
  hExistSeg_of_wellFormedFlow fL fR lam domL domR ν hwff hfrz hb.entryDom

/-! ## Non-vacuity: the coherence clause holds on a narrowing edge -/

/-- The velocity coordinate. -/
private abbrev vx : Var 3 := Rv 1

/-- **The coherence clause on a narrowing edge** (rover Recover→Drive shape): with
`domCur = vx∈[0,1]`, `guardSucc = vx≥0.3`, `domR = vx∈[0.3,1]`, every state with
`vx∈[0,1] ∧ vx≥0.3` satisfies `vx∈[0.3,1]`. A static real-arithmetic per-edge implication. -/
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

/-- **`WFBoundary` is satisfiable**: on the narrowing edge above it holds at every state with
`vx = 0.3`, which lies in the source domain, the guard and the successor domain. -/
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
