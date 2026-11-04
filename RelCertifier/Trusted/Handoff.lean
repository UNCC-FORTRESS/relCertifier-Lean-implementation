/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The handoff query (leaf)

A benchmark may declare a mode-dependent invariant, one row `φ_inv(m)` per left mode
(paper Eq. (9)). The cover certifies each left mode's cycle against that mode's own row,
but a run of the full left program also changes mode: at a declared left mode change
`m → m'` the state is unchanged and only the stored left mode changes, so the mode-keyed
invariant `⋀_m (u_L = m → φ_inv(m))` survives the change when the handoff condition of
paper Theorem 2, Eq. (13), holds:

    φ_inv(m) ∧ evolve_m(x_L) ∧ guard_{m'}(x_L) ∧ evolve_R(x_R)  →  φ_inv(m')

This file defines that query at the SMT-IR level, once, so that the runner
(`Verdicts/RunHandoff.lean`) sends Z3 exactly the formula whose host denotation the
composition theorem (`Proofs/Encoding/ModeHandoff.lean`) consumes, as for the flow
queries. The query is the negation,

    UNSAT( φ_inv(m) ∧ evolve_m(x_L) ∧ guard_{m'}(x_L) ∧ evolve_R(x_R) ∧ ¬φ_inv(m') )

over the joint variables: the left state ends a cycle of `m`, so it satisfies `m`'s
domain, and it satisfies the guard of `m'`; the right state satisfies the right domain.
The invariant rows lower through `invComponents` (the certifier's own lowering), the
guard and the domains through `lowerF` on their side (the same encoding `admissible` and
the flow queries use). `evolve_R` is the right system's evolution domain, one for all its
modes (paper Appendix B.2, Domains), which is what the mechanized `hostEvolve … (mR 0)`
relies on; the runner checks that every right mode declares the same domain and reports a
benchmark that violates it as a failure rather than picking a mode. The composition
theorem's handoff hypothesis takes exactly these facts at the switch state
(`ModeHandoff.hstep_modeKeyed`: `env = domL ∧ domR` rides the loop invariant and the
guard is the edge's test).

For a mode-independent invariant (every row syntactically identical) every handoff
query is trivially unsat; the runner still issues and counts them, reporting the
benchmark as vacuous rather than skipping it, so no handoff passes without its query.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.InvComponents

namespace RelCertifier.Handoff

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- `base ∧ ⋀_{g ∈ comps} g ≤ 0` — the lowered invariant conjunction, folded exactly as
`OracleAPI.admissible` folds it. -/
def iinvConj {n : ℕ} (comps : List (ITerm n)) (base : IForm n) : IForm n :=
  comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) base

/-- The handoff query (paper Eq. (13), negated) for rows `invSrc` (source left mode) and
`invTgt` (target left mode): `(⋀ src ≤ 0 ∧ ((evolve_src ∧ guard_tgt) ∧ evolve_R)) ∧
¬(⋀ tgt ≤ 0)`, with `evolve_src` and `guard_tgt` lowered on the left and `evolveR` on the
right. `none` if any part fails to lower — the caller reports it, never treats it as
passed. -/
def ihandoffQuery (vars : List String) (n : ℕ)
    (invSrc evolveSrc guardTgt evolveR invTgt : PForm) : Option (IForm n) := do
  let cs ← Oracle.invComponents vars n invSrc
  let eL ← lowerF vars n Side.L evolveSrc
  let gT ← lowerF vars n Side.L guardTgt
  let eR ← lowerF vars n Side.R evolveR
  let ct ← Oracle.invComponents vars n invTgt
  pure (IForm.and (iinvConj cs (IForm.and (IForm.and eL gT) eR))
    (IForm.neg (iinvConj ct IForm.tt)))

/-- Index of a left mode by name. -/
def leftModeIndex (p : PProblem) (name : String) : Option ℕ :=
  p.L.modes.findIdx? (fun m => m.name == name)

/-- The invariant row of a left mode, by name — strict, no fallback (the same lookup
`certifyWithData` performs). -/
def invRowOf (p : PProblem) (m : PMode) : Option PForm :=
  (p.invariants.find? (fun kv => kv.1 == m.name)).map Prod.snd

/-- Every declared left mode change `(m, m')` as a pair of mode indices, in declaration
order, self-loops included. A `next` entry that does not resolve is dropped here and
surfaces as a count mismatch against `declaredTransitions` in the runner. -/
def transitions (p : PProblem) : List (ℕ × ℕ) :=
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  (List.range p.L.modes.length).flatMap (fun m' =>
    ((p.L.modes.getD m' dm).next.filterMap (leftModeIndex p)).map (fun t => (m', t)))

/-- How many left mode changes the file declares (the sum of the `next` list lengths). -/
def declaredTransitions (p : PProblem) : ℕ :=
  (p.L.modes.map (fun m => m.next.length)).sum

/-- Every right mode declares the same evolution domain (one domain per system, paper
Appendix B.2), so the right state's domain at a switch is one formula. -/
def uniformEvolveR (p : PProblem) : Bool :=
  match p.R.modes with
  | [] => true
  | m :: rest => rest.all (fun m' => m'.evolve == m.evolve)

/-- The right side's (uniform) evolve domain: the first right mode's. -/
def evolveR (p : PProblem) : PForm :=
  ((p.R.modes.head?).map (·.evolve)).getD PForm.tt

/-- The handoff query of one declared left mode change, built from the problem's own
rows: the source mode's own domain, the target's guard, the right system's domain. -/
def queryOf (p : PProblem) (n : ℕ) (tr : ℕ × ℕ) : Option (IForm n) := do
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mSrc := p.L.modes.getD tr.1 dm
  let mTgt := p.L.modes.getD tr.2 dm
  let invSrc ← invRowOf p mSrc
  let invTgt ← invRowOf p mTgt
  ihandoffQuery p.L.stateVars n invSrc mSrc.evolve mTgt.guard (evolveR p) invTgt

/-- Mode-independent: every declared invariant row is syntactically the same formula. -/
def modeIndependent (p : PProblem) : Bool :=
  match p.invariants with
  | [] => true
  | kv :: rest => rest.all (fun kv' => kv'.2 == kv.2)

end RelCertifier.Handoff
