/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# End-to-end demo theorem (watertank): one term from checker cert to `rvalid`

Materializes, for one concrete benchmark, the composition that the pipeline performs
per benchmark at run time:

    kernel `rfl` well-formedness certificate  (decideWellFormed watertankSuiteM)
      + `Faithful` kernel certificate          (FaithfulCerts: instance = parsed file)
      → wellformed_sound                       (GuardSettlingH, kernel)
      → theorem3_faithful_settling             (rvalid over ⟦L⟧ ≫ ⟦R⟧)

The hypotheses that remain NAMED here are exactly the pipeline's designed residuals,
none of them checker-shaped:
* `hcert` — the per-mode Z3 `BoxLe` certificates (the `z3_unsat_sound` leaf, produced by
  the certifier at run time);
* freshness/disjointness of the auxiliary coordinates `mv`, `tg` and the L/R variable
  split — mechanical facts about the encoding's variable bookkeeping;
* `hbudget` — the declared mission horizon (`bound_T`): left runs last at most `k`
  segments, a modeling assumption of every benchmark;
* `hψ`/`hddF` — the relational-invariant encoding and its bridge shape.

Everything checker-shaped — settling, staying, landing, the guard geometry — is
DISCHARGED by the kernel below, with no per-benchmark proof text beyond `rfl`.
-/
import RelCertifier.WellFormedChecker
import RelCertifier.FaithfulCerts

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

/-- **Watertank, end to end.** From the kernel checker certificate (a `rfl` inside
`wellformed_sound`'s application) and the run-time residuals, the ∀∃ refinement claim
`rvalid (theorem3Form …)` for the transcribed watertank model. -/
theorem watertank_end_to_end
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (domL : Formula (Var 1)) (k : ℕ) (ϕinv : RFormula (Var 1))
    -- encoding of the relational invariant
    (hψ : encode (Equiv.refl (Var 1)) ϕinv = invLe g)
    -- auxiliary-coordinate freshness (mechanical bookkeeping facts)
    (hg : mv ∉ g.fv) (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (watertankSuiteM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (watertankSuiteM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (watertankSuiteM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (htgb : tg ∉ (leftBlock fL).bound) (htgr : tg ∉ (leftBlock fL).readVars)
    (htgϕ : tg ∉ domL.fv)
    (htgR : tg ∉ ((rightAutomatonBody watertankSuiteM.graph mv).rename
        (Equiv.refl (Var 1))).fv)
    (htgφ : tg ∉ (starInvGF watertankSuiteM.graph watertankSuiteM.GdOf mv g).fv)
    -- L/R disjointness of the encoding
    (hdis : Disjoint
        (Program.vars ((rightAutomatonBody watertankSuiteM.graph mv).rename
          (Equiv.refl (Var 1))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg ((watertankSuiteM.dt : ℝ)))))
    (hdMULTI : Disjoint (Program.vars (Program.ode (leftBlock fL) domL))
        (Program.vars ((rightAutomatonBody watertankSuiteM.graph mv).rename
          (Equiv.refl (Var 1)))))
    (hddF : Disjoint
        (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody watertankSuiteM.graph mv))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsL
        (Equiv.refl (Var 1) '' (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody watertankSuiteM.graph mv))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsR))
    -- the declared mission horizon (bound_T)
    (hbudget : ∀ (σ' : State (Var 1)), ∀ {r : ℝ} {Φ : ℝ → State (Var 1)},
        ODESol (leftBlock fL) domL σ' r Φ → r ≤ (k : ℝ) * (watertankSuiteM.dt : ℝ))
    -- the Z3 flow certificates (the z3_unsat_sound leaf, per mode)
    (hcert : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (watertankSuiteM.GdOf q) ν →
          BoxLe (Program.ode m.sys watertankSuiteM.envF) (fun ω => Term.eval g ω) ν) :
    RFormula.rvalid (theorem3Form (Program.ode (leftBlock fL) domL)
      (rightAutomatonBody watertankSuiteM.graph mv)
      (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)) := by
  have hH : GuardSettlingH watertankSuiteM.graph watertankSuiteM.GdOf mv g
      (Term.const 1) tg ((watertankSuiteM.dt : ℝ)) fL watertankSuiteM.envF :=
    wellformed_sound watertankSuiteM mv tg g fL
      rfl                       -- ← the kernel checker certificate
      (by norm_num [SettlingModel.dt, watertankSuiteM])
      hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert
  exact theorem3_faithful_settling watertankSuiteM.graph watertankSuiteM.GdOf mv g fL
    domL watertankSuiteM.envF tg ((watertankSuiteM.dt : ℝ)) k (Term.const 1) ϕinv
    hψ hH htgb htgr htgϕ htgR htgφ hdis hdMULTI hbudget hddF

end RelCertifier
