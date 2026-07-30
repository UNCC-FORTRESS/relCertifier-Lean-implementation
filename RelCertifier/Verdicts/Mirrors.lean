/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The verdict column — IR mirrors of the theorem hypotheses

The theorems' hypotheses are `z3solve (query) = unsat` facts over HOST formulas;
`z3solve` is opaque, operationally realized as "print the IR mirror, run Z3"
(the trust wording: parser + printer + Z3-on-unsat + kernel). This directory is the
EMPIRICAL column, kept separate from `Instances/` (the kernel column): the IR mirrors of
the hypothesis queries, kernel identity theorems `mirror.toHost = hypothesis-query` (so
what Z3 sees IS what the theorem assumes), and the `--run-verdicts` runner producing the
dated report (docs/VERDICTS.md).

COVERAGE (2026-07-30): identity theorems exist per benchmark for watertank
(`Watertank.lean`) and per query SHAPE generically (`GenericPins.lean`, used by the cut
probes). The verdict packs of the other modal instances are measured through the same
printer but are not yet pinned here — recorded as the open item in
`docs/CERTIFICATION-CHECK.md` § Check 3.

This file: the missing route-C mirror (`iflowQuerySuperlevel`), completing the
route-A/B mirrors from `Smt.lean`/`CutLift.lean`.
-/
import RelCertifier.Proofs.Soundness.CutLift

namespace RelCertifier

/-- IR mirror of the superlevel query (route C). -/
def iflowQuerySuperlevel {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n)
    (lam : ITerm n) (domain : IForm n) : IForm n :=
  IForm.and domain (IForm.and (IForm.cmp .ge g (.rat 0))
    (IForm.cmp .gt (ilieDeriv g fL fR lam) (.rat 0)))

theorem iflowQuerySuperlevel_toHost {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n)
    (lam : ITerm n) (domain : IForm n) :
    (iflowQuerySuperlevel g fL fR lam domain).toHost
      = flowQuerySuperlevel ⟨g.toHost, (fun i => (fL i).toHost),
          (fun i => (fR i).toHost), lam.toHost, domain.toHost⟩ := by
  simp [iflowQuerySuperlevel, flowQuerySuperlevel, IForm.toHost, ITerm.toHost,
    ilieDeriv_toHost]

end RelCertifier
