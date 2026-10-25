/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The non-connection bridge — the runner's two queries ARE Definition 6's checks

`Trusted/NonConnQuery.lean` builds, at the SMT-IR level, the two pruning queries the
certifier sends Z3 for a declared right edge `mR → mSuc` with a strict scalar successor
guard `{g > 0}`, or a conjunction whose leading conjunct is one (`g > 0` is then that
conjunct, which the guard implies; paper Section 4.2). `Checker/NonConn.lean` proves the
soundness of Definition 6 (`nonconn_sound`): if `sourceCheck` and `barrierCheck` of a `NonConnObligation` are both
unsatisfiable, no state the source mode's right flow reaches satisfies the successor
guard. This leaf ties the two together, once, generically:

* `queries_eq` — the explicit shape `NonConn.queries` returns when every part lowers
  (the `some`-facts are kernel-established per benchmark, as for the other pins);
* `hostObligation` — the `NonConnObligation` the lowered pieces denote: `g` is the
  guard's safe-side term, `sysR` is the right field with the left frozen at `λ = 1`
  (`jointSys 0 fR 1` — the field `nonconn_sound`'s `Lie` is taken along), `domain` and
  `source` carry the source mode's checked cut exactly as the queries do;
* `sourceCheck_iff` / `barrierCheck_iff` — the printed queries' host denotations are
  satisfaction-equivalent to the obligation's two checks (the only difference is the
  `ℚ`-literal zero against `Term.const 0`, and `lieDeriv g 0 fR 1` against
  `lieAlong g (jointSys 0 fR 1)`, both the semantic `Lie`);
* `nonconn_of_unsat` — the composition: two `z3solve … = unsat` facts on exactly the
  runner's queries yield `nonconn_sound`'s conclusion (Definition 6) for the edge.

How the paper's route uses it: the bridge instances do not consume this lemma directly. They
take the same two queries per pruned edge as the barrier of each pruned exit
(`Proofs/Encoding/Emitted/Barrier.lean`, `Emitted/Anchor.lean`: `nonconn_entry`,
`guard_pos_of_barrier`), 88 queries for the suite's 44 pruned edges. This file is the
standalone statement of Definition 6's soundness for one edge, the kernel-checked content of
the certificate the tool emits (`CoverEmitE.pruned`); its per-benchmark instance was part of
the archived standalone route (commit 29663d8).

New leaf; the three standard axioms plus `z3_unsat_sound` where the verdicts enter.
-/
import RelCertifier.Trusted.NonConnQuery
import RelCertifier.Trusted.Oracle

namespace RelCertifier.NonConn

open DL RelCertifier RelCertifier.Parse RelCertifier.Run

variable {n : ℕ}

/-! ## The queries, explicitly -/

/-- The `sourceCheck` query the builder returns: `(source ∧ cut) ∧ g > 0`. -/
def srcQuery (gI : ITerm n) (srcI cutR : IForm n) : IForm n :=
  IForm.and (IForm.and srcI cutR) (IForm.cmp .gt gI (.rat 0))

/-- The `barrierCheck` query the builder returns: `(evolve ∧ cut) ∧ g = 0 ∧ Lie_R g ≥ 0`. -/
def barQuery (gI : ITerm n) (domI cutR : IForm n) (fI : Fin n → ITerm n) : IForm n :=
  IForm.and (IForm.and domI cutR) (IForm.and (IForm.cmp .eq gI (.rat 0))
    (IForm.cmp .ge (ilieDeriv gI (fun _ => .rat 0) fI (.rat 1)) (.rat 0)))

/-- `queries` at lowered pieces is exactly the pair above. -/
theorem queries_eq {vars : List String} {cutR : IForm n} {mR mSuc : PMode}
    {gI : ITerm n} {domI srcI : IForm n} {fI : Fin n → ITerm n}
    (hg : guardTerm vars n mSuc.guard = some gI)
    (hdom : lowerF vars n Side.R mR.evolve = some domI)
    (hsrc : lowerF vars n Side.R (PForm.and mR.guard mR.evolve) = some srcI)
    (hdyn : dynOf vars n Side.R mR = some fI) :
    queries vars n cutR mR mSuc = some (srcQuery gI srcI cutR, barQuery gI domI cutR fI) := by
  simp [queries, hg, hdom, hsrc, hdyn, srcQuery, barQuery]

/-! ## The host obligation -/

/-- The `NonConnObligation` the lowered pieces denote. -/
noncomputable def hostObligation (gI : ITerm n) (domI srcI cutR : IForm n)
    (fI : Fin n → ITerm n) : NonConnObligation (Var n) :=
  { g := gI.toHost
    guard := Formula.cmp .gt gI.toHost (Term.const 0)
    sysR := jointSys (fun _ => Term.const 0) (fun i => (fI i).toHost) (Term.const 1)
    domain := (IForm.and domI cutR).toHost
    source := (IForm.and srcI cutR).toHost }

theorem hostObligation_link (gI : ITerm n) (domI srcI cutR : IForm n)
    (fI : Fin n → ITerm n) (ω : State (Var n)) :
    Formula.sat (hostObligation gI domI srcI cutR fI).guard ω
      ↔ 0 < Term.eval (hostObligation gI domI srcI cutR fI).g ω := by
  simp [hostObligation, Formula.sat, CompOp.interp, Term.eval]

theorem hostObligation_wf (gI : ITerm n) (domI srcI cutR : IForm n)
    (fI : Fin n → ITerm n) : (hostObligation gI domI srcI cutR fI).sysR.WellFormed :=
  jointSys_wellFormed _ _ _

/-- The printed source query denotes the obligation's `sourceCheck` (satisfaction-wise:
the `ℚ`-literal zero is the real zero). -/
theorem sourceCheck_iff (gI : ITerm n) (domI srcI cutR : IForm n)
    (fI : Fin n → ITerm n) (σ : State (Var n)) :
    Formula.sat (srcQuery gI srcI cutR).toHost σ
      ↔ Formula.sat (sourceCheck (hostObligation gI domI srcI cutR fI)) σ := by
  simp [srcQuery, sourceCheck, hostObligation, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval]

/-- The printed barrier query denotes the obligation's `barrierCheck`: both Lie terms
evaluate to the semantic `Lie` along the frozen-left right field. -/
theorem barrierCheck_iff (gI : ITerm n) (domI srcI cutR : IForm n)
    (fI : Fin n → ITerm n) (σ : State (Var n)) :
    Formula.sat (barQuery gI domI cutR fI).toHost σ
      ↔ Formula.sat (barrierCheck (hostObligation gI domI srcI cutR fI)) σ := by
  have hlie : Term.eval (ilieDeriv gI (fun _ => ITerm.rat 0) fI (ITerm.rat 1)).toHost σ
      = Term.eval (lieAlong gI.toHost
          (jointSys (fun _ => Term.const 0) (fun i => (fI i).toHost) (Term.const 1))) σ := by
    rw [ilieDeriv_toHost, lieDeriv_correct, lieAlong_correct]
    simp [ITerm.toHost]
  simp only [barQuery, barrierCheck, hostObligation, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp]
  rw [hlie]
  simp [Term.eval]

/-! ## The composition -/

/-- **Definition 6's conclusion from the runner's two verdicts.** If Z3 answers `unsat` on the printed
source and barrier queries of a pruned edge, then from every state in the source region
(the source mode's guard, evolve and checked cut) no state reached by the source mode's
right flow — the left frozen, inside the (cut-narrowed) evolve domain — satisfies the
successor guard `g > 0`. -/
theorem nonconn_of_unsat (gI : ITerm n) (domI srcI cutR : IForm n) (fI : Fin n → ITerm n)
    (hsrc : z3solve (srcQuery gI srcI cutR).toHost = Verdict.unsat)
    (hbar : z3solve (barQuery gI domI cutR fI).toHost = Verdict.unsat) :
    ∀ ν, Formula.sat (IForm.and srcI cutR).toHost ν →
      ∀ ω, Program.sem (Program.ode
          (jointSys (fun _ => Term.const 0) (fun i => (fI i).toHost) (Term.const 1))
          (IForm.and domI cutR).toHost) ν ω →
        ¬ Formula.sat (Formula.cmp .gt gI.toHost (Term.const 0)) ω := by
  intro ν hν ω hrun
  have h1 := z3_unsat_sound hsrc
  have h2 := z3_unsat_sound hbar
  exact nonconn_sound (hostObligation gI domI srcI cutR fI)
    (hostObligation_wf gI domI srcI cutR fI) (hostObligation_link gI domI srcI cutR fI)
    hν
    (fun σ hσ => h1 σ ((sourceCheck_iff gI domI srcI cutR fI σ).mpr hσ))
    (fun σ hσ => h2 σ ((barrierCheck_iff gI domI srcI cutR fI σ).mpr hσ))
    ω hrun

end RelCertifier.NonConn
