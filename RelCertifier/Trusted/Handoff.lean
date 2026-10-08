/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cross-mode handoff query (leaf)

A benchmark may declare one relational invariant per LEFT mode. The cover certifies
each left mode's residence against that mode's own row, but a run of the full left
program also SWITCHES mode: at a declared left transition `m' → m` the state is
unchanged and only the left mode variable changes, so the mode-keyed global invariant
`Φ ≡ ⋀_m (u_L = m → φ_inv(m))` survives the switch exactly when the static implication

    φ_inv(m') ∧ guard_m(x_L)  →  φ_inv(m)

holds. This file defines that query at the SMT-IR level, once, so that the runner
(`Verdicts/RunHandoff.lean`) sends Z3 exactly the formula whose host denotation the
composition theorem (`Proofs/Encoding/ModeHandoff.lean`) consumes — the same
"mechanization follows the code" discipline as the flow queries.

The query is `UNSAT(φ_inv(m') ∧ guard_m ∧ ¬φ_inv(m))`, over the joint variables; the
invariant rows lower through `invComponents` (the certifier's own lowering) and the
guard through `lowerF` on the left side (the same encoding `admissible` uses). It
carries no evolve domain: the implication is required on all of the state space, which
is stronger than the loop invariant needs and keeps the statement free of any
bookkeeping conjunct.

For a MODE-INDEPENDENT invariant (every row syntactically identical) every handoff
query is trivially unsat; the runner still issues and counts them, reporting the
benchmark as vacuous rather than skipping it (the silent-pass rule).
-/
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.InvComponents

namespace RelCertifier.Handoff

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- `base ∧ ⋀_{g ∈ comps} g ≤ 0` — the lowered invariant conjunction, folded exactly as
`OracleAPI.admissible` folds it. -/
def iinvConj {n : ℕ} (comps : List (ITerm n)) (base : IForm n) : IForm n :=
  comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) base

/-- The handoff query for rows `invSrc` (source left mode) and `invTgt` (target left
mode) across the target's guard: `(⋀ src ≤ 0 ∧ guard_tgt) ∧ ¬(⋀ tgt ≤ 0)`. `none` if any
part fails to lower — the caller reports it, never treats it as passed. -/
def ihandoffQuery (vars : List String) (n : ℕ) (invSrc guardTgt invTgt : PForm) :
    Option (IForm n) := do
  let cs ← Oracle.invComponents vars n invSrc
  let gT ← lowerF vars n Side.L guardTgt
  let ct ← Oracle.invComponents vars n invTgt
  pure (IForm.and (iinvConj cs gT) (IForm.neg (iinvConj ct IForm.tt)))

/-- Index of a left mode by name. -/
def leftModeIndex (p : PProblem) (name : String) : Option ℕ :=
  p.L.modes.findIdx? (fun m => m.name == name)

/-- The invariant row of a left mode, by name — strict, no fallback (the same lookup
`certifyWithData` performs). -/
def invRowOf (p : PProblem) (m : PMode) : Option PForm :=
  (p.invariants.find? (fun kv => kv.1 == m.name)).map Prod.snd

/-- Every declared left transition `(m', m)` as a pair of mode indices, in declaration
order, self-loops included. A `next` entry that does not resolve is dropped here and
surfaces as a count mismatch against `declaredTransitions` in the runner. -/
def transitions (p : PProblem) : List (ℕ × ℕ) :=
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  (List.range p.L.modes.length).flatMap (fun m' =>
    ((p.L.modes.getD m' dm).next.filterMap (leftModeIndex p)).map (fun t => (m', t)))

/-- How many left transitions the file declares (the sum of the `next` list lengths). -/
def declaredTransitions (p : PProblem) : ℕ :=
  (p.L.modes.map (fun m => m.next.length)).sum

/-- The handoff query of one declared transition, built from the problem's own rows. -/
def queryOf (p : PProblem) (n : ℕ) (tr : ℕ × ℕ) : Option (IForm n) := do
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mSrc := p.L.modes.getD tr.1 dm
  let mTgt := p.L.modes.getD tr.2 dm
  let invSrc ← invRowOf p mSrc
  let invTgt ← invRowOf p mTgt
  ihandoffQuery p.L.stateVars n invSrc mTgt.guard invTgt

/-- Mode-independent: every declared invariant row is syntactically the same formula. -/
def modeIndependent (p : PProblem) : Bool :=
  match p.invariants with
  | [] => true
  | kv :: rest => rest.all (fun kv' => kv'.2 == kv.2)

end RelCertifier.Handoff
