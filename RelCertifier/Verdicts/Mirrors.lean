/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The route-C mirror

The theorems' hypotheses are `z3solve (query) = unsat` facts over host formulas;
`z3solve` is opaque, operationally realized as "print the IR mirror, run Z3" (the trust
wording: parser + printer + Z3-on-unsat + kernel). A runner therefore needs, per query
shape, an IR mirror with a kernel identity `mirror.toHost = hypothesis-query`, so what Z3
sees IS what the theorem assumes.

Routes A and B have their mirrors in `Trusted/Smt.lean` / `Proofs/Soundness/CutLift.lean`;
this file supplies route C (`iflowQuerySuperlevel`, the superlevel route), used by the
legacy-pack runner (`Verdicts/RunModal`) and the suite_v2 runner (`VerdictsV2/ModalX`).
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
