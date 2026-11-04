/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The non-connection queries (leaf)

The pruning of paper Section 6.1, establishing the non-connection certificate of
Definition 6 (Section 4.2): a declared right mode change `mR → mSuc` is pruned (dropped
from the retained successors) when the successor's guard is a single strict threshold
`{g > 0}` on one variable and two Z3 checks are both `unsat`:

* `sourceCheck  = guard_mR ∧ evolve_mR ∧ cut_mR ∧ g > 0`           (no entry state is
  on the far side of the threshold);
* `barrierCheck = evolve_mR ∧ cut_mR ∧ g = 0 ∧ Lie_R g ≥ 0`         (on the threshold the
  right flow moves `g` strictly down, with the left frozen).

The source check assumes only the right mode's guard, domain and mode fact, so the
certificate holds for both source settings and both segment kinds of Definition 6.

This leaf defines the two queries once, at the SMT-IR level, so that the certifier's
pruning step (`OracleAPI.nonConnPrune`), the verdict runner (the non-connection phase of
`relcert --run-verdicts-v2`, `VerdictsV2.runNonConnAllV2`) and the kernel bridge
(`Proofs/Encoding/NonConnBridge.lean`, which consumes `z3solve (q).toHost = unsat` for
exactly these two `IForm`s and yields the hypotheses of `nonconn_sound`) share one
definition, as for the handoff query (`Trusted/Handoff.lean`).

`cutR` is the source mode's mode fact (paper Definition 2; the kept atoms of
`OracleAPI.checkedCut`, or of `checkedCutX` under `RELCERT_IMPLIED_CUT=1`, conjoined; `tt`
when none), conjoined to both domains.

Scope: a strict single-threshold successor guard (`a > b` / `a < b`), or a conjunction
whose leading conjunct is one (`a < b and …`, the parser's left-nested `and`): the barrier
is then the leading conjunct alone, and since the guard implies it, a state outside
`{g > 0}` is outside the guard (the conclusion of `nonconn_sound` is about `g > 0`, which
the whole guard implies). Anything else (a closed leading conjunct, a disjunction) yields
`none` and the mode change is retained (incompleteness, never unsoundness). The
conjunction case serves guards that carry another component's operating range next to
the threshold (the multi-link sinks of `platoon3_*`).
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

/-- The pruning queries `(sourceCheck, barrierCheck)` for the declared mode change
`mR → mSuc` under the source mode fact `cutR`; `none` if the guard is not a strict
single threshold (or a conjunction led by one) or any part fails to lower. -/
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

/-- The source mode fact as the certifier builds it from kept atoms: `tt` conjoined with
each kept atom's lowered form, in order (`OracleAPI.checkedCut`'s fold). Used by the
runner to rebuild `cutR` from the emitted mode-fact record. -/
def cutOfAtoms (vars : List String) (n : ℕ) (atoms : List PForm) : Option (IForm n) := do
  let fs ← atoms.mapM (lowerF vars n Side.R)
  pure (fs.foldl (fun d f => IForm.and d f) IForm.tt)

/-- The kept atoms of a right mode in an emitted mode-fact record (`[]` if the mode has
no entry): the list `cutOfAtoms` folds to rebuild the source mode's fact. -/
def rightCutAtoms (cuts : Oracle.EvolStrengthening) (mode : String) : List PForm :=
  match cuts.R.find? (fun r => r.1 == mode) with
  | some r => r.2.map (·.1)
  | none => []

end RelCertifier.NonConn
