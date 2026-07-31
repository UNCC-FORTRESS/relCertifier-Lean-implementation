/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Modal query pins — the runner's rebuilt query IS the theorem's query

The modal instances' verdict hypotheses have the strata-narrowed shape

    z3solve (flowQuery ⟨(g :: gs)[i], fL l, fR m, Term.const λ,
      strataDomHost (domL ∧ domR) ((g :: gs).take i)⟩) = unsat  ∨  …strict  ∨  …superlevel

A runner can only send *text* to Z3, so it must rebuild that query at the SMT-IR
level and print it. These lemmas prove the rebuild denotes exactly the host-level
term the hypothesis names — the same job `Verdicts/Watertank.lean` does for the
flagship and `GenericPins.lean` does for the cut probes, for the one query shape
those two do not cover.

Why this matters concretely: an audit that *reconstructs* what a theorem asks Z3,
rather than proving the reconstruction correct, is unreliable. On 2026-07-31 four
separate reconstruction attempts produced false alarms (wrong component order,
wrong invariant row, parse-pin names read as binders, failed joint attempts read
as live certificates) before one real defect was isolated — see
`docs/VERDICT-EVIDENCE-AUDIT.md` §4. With these pins the reconstruction cannot be
silently wrong: a mismatched rebuild fails to typecheck.

Composed from the existing bridges (`iflowQuery_toHost`, `istrataDomHost_toHost`)
— no new mathematics, only the shape the modal instances actually use.
-/
import RelCertifier.Verdicts.Combinators
import RelCertifier.Verdicts.Mirrors

namespace RelCertifier

variable {n : ℕ}

/-- **Route A, strata-narrowed.** The IR query built over a narrowed domain denotes
the host `flowQuery` the hypothesis names. -/
theorem imodalQuery_toHost (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n)
    (D : IForm n) (pre : List (ITerm n)) :
    (iflowQuery g fL fR lam (istrataDomHost D pre)).toHost
      = flowQuery ⟨g.toHost, (fun i => (fL i).toHost), (fun i => (fR i).toHost),
          lam.toHost, strataDomHost D.toHost (pre.map ITerm.toHost)⟩ := by
  rw [iflowQuery_toHost, istrataDomHost_toHost]

/-- **Route B (strict boundary), strata-narrowed.** -/
theorem imodalQueryStrict_toHost (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n)
    (D : IForm n) (pre : List (ITerm n)) :
    (iflowQueryStrict g fL fR lam (istrataDomHost D pre)).toHost
      = flowQueryStrict ⟨g.toHost, (fun i => (fL i).toHost), (fun i => (fR i).toHost),
          lam.toHost, strataDomHost D.toHost (pre.map ITerm.toHost)⟩ := by
  rw [iflowQueryStrict_toHost, istrataDomHost_toHost]

/-- **Route C (superlevel), strata-narrowed.** -/
theorem imodalQuerySuperlevel_toHost (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n)
    (D : IForm n) (pre : List (ITerm n)) :
    (iflowQuerySuperlevel g fL fR lam (istrataDomHost D pre)).toHost
      = flowQuerySuperlevel ⟨g.toHost, (fun i => (fL i).toHost), (fun i => (fR i).toHost),
          lam.toHost, strataDomHost D.toHost (pre.map ITerm.toHost)⟩ := by
  rw [iflowQuerySuperlevel_toHost, istrataDomHost_toHost]

end RelCertifier
