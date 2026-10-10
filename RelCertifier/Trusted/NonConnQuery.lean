/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The non-connection queries (leaf)

Paper Section 4.3 / Theorem 2: a declared right edge `mR → mSuc` is pruned from the
cover's all-successors obligation when the successor's guard is a single STRICT
threshold `{g > 0}` on one variable and two Z3 checks are both `unsat`:

* `sourceCheck  = guard_mR ∧ evolve_mR ∧ cut_mR ∧ g > 0`           (no entry state is
  on the far side of the threshold);
* `barrierCheck = evolve_mR ∧ cut_mR ∧ g = 0 ∧ Lie_R g ≥ 0`         (on the threshold the
  right flow moves `g` strictly down, with the left frozen).

This leaf defines the two queries ONCE, at the SMT-IR level, so that the certifier's
pruning step (`OracleAPI.nonConnPrune`), the verdict runner (the non-connection phase of
`relcert --run-verdicts-v2`, `VerdictsV2.runNonConnAllV2`) and the kernel bridge (`Proofs/Encoding/NonConnBridge.lean`, which consumes
`z3solve (q).toHost = unsat` for exactly these two `IForm`s and yields the hypotheses of
`nonconn_sound`) cannot drift — the same "mechanization follows the code" discipline as
the handoff query (`Trusted/Handoff.lean`).

`cutR` is the source mode's checked cut (the kept atoms of `OracleAPI.checkedCut`, or of
`checkedCutX` under `RELCERT_IMPLIED_CUT=1`, conjoined; `tt` when none), conjoined to both
domains.

Scope: a strict scalar successor guard (`a > b` / `a < b`), or a conjunction whose
LEADING conjunct is one (`a < b and …`, the parser's left-nested `and`): the barrier is
then the leading conjunct alone, and since the guard implies it, a state outside
`{g > 0}` is outside the guard (the conclusion of `nonconn_sound` is about `g > 0`, which
the whole guard implies). Anything else (a closed leading conjunct, a disjunction) yields
`none` and the edge is kept (incompleteness, never unsoundness). The conjunction case was
added on 2026-10-10 for the multi-link AEB sinks of `platoon3_*`, whose guards must carry
the other links' operating range (`docs/SUITE-REDESIGN.md` §21); no other file in
`benchmarks/` has a compound guard with a strict leading conjunct, so no other pruning
changed.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Checker.EvolStrengthening

namespace RelCertifier.NonConn

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- The successor guard's safe-side term `g`, with `guard ⊆ {g > 0}`: `a > b ↦ a − b`,
`a < b ↦ b − a`; for a conjunction, the safe-side term of its leading conjunct (the guard
implies it); `none` for anything else. -/
def guardTerm (vars : List String) (n : ℕ) (guard : PForm) : Option (ITerm n) :=
  match guard with
  | PForm.cmp ">" a b =>
      (lowerE vars n Side.R a).bind fun ea =>
        (lowerE vars n Side.R b).map fun eb => ITerm.bin .sub ea eb
  | PForm.cmp "<" a b =>
      (lowerE vars n Side.R a).bind fun ea =>
        (lowerE vars n Side.R b).map fun eb => ITerm.bin .sub eb ea
  | PForm.and a _ => guardTerm vars n a
  | _ => none

/-- The pruning queries `(sourceCheck, barrierCheck)` for the declared edge `mR → mSuc`
under the source cut `cutR`; `none` if the guard is not a strict scalar threshold or any
part fails to lower. -/
def queries (vars : List String) (n : ℕ) (cutR : IForm n) (mR mSuc : PMode) :
    Option (IForm n × IForm n) := do
  let g    ← guardTerm vars n mSuc.guard
  let domR0 ← lowerF vars n Side.R mR.evolve
  let domR := IForm.and domR0 cutR
  let srcR0 ← lowerF vars n Side.R (PForm.and mR.guard mR.evolve)
  let srcR := IForm.and srcR0 cutR
  let fR   ← dynOf vars n Side.R mR
  let lie  := ilieDeriv g (fun _ => ITerm.rat 0) fR (ITerm.rat 1)        -- right-only Lie
  let gPos := IForm.cmp .gt g (ITerm.rat 0)
  pure (IForm.and srcR gPos,                                             -- sourceCheck
        IForm.and domR (IForm.and (IForm.cmp .eq g (ITerm.rat 0))
          (IForm.cmp .ge lie (ITerm.rat 0))))                            -- barrierCheck

/-- The source cut as the certifier builds it from kept atoms: `tt` conjoined with each
kept atom's lowered form, in order (`OracleAPI.checkedCut`'s fold). Used by the runner to
rebuild `cutR` from the emitted cut certificate. -/
def cutOfAtoms (vars : List String) (n : ℕ) (atoms : List PForm) : Option (IForm n) := do
  let fs ← atoms.mapM (lowerF vars n Side.R)
  pure (fs.foldl (fun d f => IForm.and d f) IForm.tt)

/-- The kept atoms of a right mode in an emitted cut certificate (`[]` if the mode has
no entry) — the list `cutOfAtoms` folds to rebuild the source mode's cut. -/
def rightCutAtoms (cuts : Oracle.EvolStrengthening) (mode : String) : List PForm :=
  match cuts.R.find? (fun r => r.1 == mode) with
  | some r => r.2.map (·.1)
  | none => []

end RelCertifier.NonConn
