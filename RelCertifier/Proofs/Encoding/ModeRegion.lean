/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L4 — mode-region conditioning (the `rung2c` vacuity device)

`refinement_ladder_rover_rung2c_6dof`'s right graph is the one-way chain
`STEEP → MODER → FLAT`: three (window, start) pairs have no declared path to a
joint-certified mode, and those pairs are exactly the non-admissible ones
(`guardL ∧ guardR ∧ inv` UNSAT — the invariant is an exact lockstep bisimulation).
They discharge by VACUITY once the loop invariant carries the right mode's
PRESERVED region: the guard's lower bound `s_r ≥ b(q)`, forward-invariant because
`s` is non-decreasing on the envelope (`s' = v·((1 − ψ²/2) − 0.3θ²)`, `v ≥ 0`,
bracket ≥ 0.8 — measured P1 unsat).

This file provides the preservation lemma: the lower bound as the face term
`b − s_r`, preserved along any `(sys, dom)` run by the standard `SegPreservesOn`
certificate — the SAME `BoxLe` shape the cover already emits (one Z3 leaf per mode,
`flow_cert_sound` on `b − s_r`). The instance-side threading (the `modeRegion`
conjunct through the loop invariant, restoration at hops from the measured P2
verdicts, vacuity of the bad pairs from the measured P3 verdicts) happens in the
`rung2c` instance; the suite-wide caveat stands: only 95 of 129 right-mode guard
lower bounds are forward-invariant, so this device is PER-INSTANCE, not a shared
template ingredient.

New leaf; no upstream edits.
-/
import RelCertifier.Checker.Cover

namespace RelCertifier
open DL

variable {n : ℕ}

/-- The preserved lower-bound face: `s_r ≥ b` as `b − s_r ≤ 0`. -/
def lowFace (b : ℝ) (sr : Var n) : Term (Var n) :=
  Term.binop AOp.sub (Term.const b) (Term.var sr)

theorem eval_lowFace (b : ℝ) (sr : Var n) (ν : State (Var n)) :
    Term.eval (lowFace b sr) ν = b - ν sr := by
  simp [lowFace, Term.eval, AOp.interp]

/-- **Lower-bound preservation** from the standard segment certificate: wherever
`s_r ≥ b` holds at a run's start, it holds at its end. One `flow_cert_sound` Z3
leaf per (mode, bound) — the cover's existing query shape on the face term. -/
theorem lowR_preserved (b : ℝ) (sr : Var n) (sys : ODESystem (Var n))
    (dom : Formula (Var n))
    (hcert : SegPreservesOn (lowFace b sr) sys dom) :
    ∀ ν ω, Program.sem (Program.ode sys dom) ν ω → b ≤ ν sr → b ≤ ω sr := by
  intro ν ω hsem hb
  have hinv : InvHolds (lowFace b sr) ν := by
    rw [InvHolds, eval_lowFace]
    linarith
  have := hcert ν hinv ω hsem
  simp only [eval_lowFace] at this
  linarith

end RelCertifier
