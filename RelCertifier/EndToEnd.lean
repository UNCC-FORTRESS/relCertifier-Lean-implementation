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
import RelCertifier.ClockedTop
import RelCertifier.FvDischarge

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

/-- **Watertank, end to end — PHYSICAL ∀-side (historical form).** CAVEAT: `hbudget`
demands every unclocked left flow last at most `k·dt`; for autonomous dynamics whose
envelope never forces exit (watertank included) such flows exist for every duration, so
this hypothesis is satisfiable only if `domL` itself bounds time. Prefer the cadenced
form below, where segment boundedness is semantic and no budget exists. Kept as the
faithful record of the pre-C architecture. -/
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

/-- **Watertank, end to end, CLOCKED ∀-side** — the preferred form. Relative to
`watertank_end_to_end`: the mission-budget hypothesis and all six clock-freshness
side conditions are GONE (segment boundedness is semantic in `clockedSeg`; the loop
rule `faModal_LOCK` replaces the counted physical collapse). What remains: the
invariant encoding, the aux-freshness of `g`, the two variable-hygiene facts
(task B's targets), and the Z3 certificates. -/
theorem watertank_end_to_end_clocked
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (domL : Formula (Var 1)) (ϕinv : RFormula (Var 1))
    (hψ : encode (Equiv.refl (Var 1)) ϕinv = invLe g)
    (hg : mv ∉ g.fv) (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (watertankSuiteM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (watertankSuiteM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (watertankSuiteM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hdis : Disjoint
        (Program.vars (clockedSeg (leftBlock fL) domL tg ((watertankSuiteM.dt : ℝ))))
        (Program.vars ((rightAutomatonBody watertankSuiteM.graph mv).rename
          (Equiv.refl (Var 1)))))
    (hddF : Disjoint
        (faShape (Program.star (clockedSeg (leftBlock fL) domL tg
            ((watertankSuiteM.dt : ℝ))))
          (Program.star (rightAutomatonBody watertankSuiteM.graph mv))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsL
        (Equiv.refl (Var 1) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL tg
            ((watertankSuiteM.dt : ℝ))))
          (Program.star (rightAutomatonBody watertankSuiteM.graph mv))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsR))
    (hcert : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (watertankSuiteM.GdOf q) ν →
          BoxLe (Program.ode m.sys watertankSuiteM.envF) (fun ω => Term.eval g ω) ν) :
    RFormula.rvalid (theorem3Form
      (clockedSeg (leftBlock fL) domL tg ((watertankSuiteM.dt : ℝ)))
      (rightAutomatonBody watertankSuiteM.graph mv)
      (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)) := by
  have hH : GuardSettlingH watertankSuiteM.graph watertankSuiteM.GdOf mv g
      (Term.const 1) tg ((watertankSuiteM.dt : ℝ)) fL watertankSuiteM.envF :=
    wellformed_sound watertankSuiteM mv tg g fL rfl
      (by norm_num [SettlingModel.dt, watertankSuiteM])
      hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert
  exact theorem3_faithful_settling_clocked watertankSuiteM.graph watertankSuiteM.GdOf
    mv g fL domL watertankSuiteM.envF tg ((watertankSuiteM.dt : ℝ)) (Term.const 1)
    ϕinv hψ hH hdis hddF

/-- **Watertank, end to end, ε-CADENCED BOTH SIDES, calculus coupling — the final form.**
Both stars clocked (`clockedSeg` left, `rightAutomatonBodyC` right); the per-segment
obligation passes through the `R*` slot (`faModal_LOCK_starR`), so the statement neither
assumes a budget nor forces lockstep. Residuals: the invariant encoding, aux-freshness of
`g` (`hg`, `htgg`), the tg-side and variable-hygiene facts (task B's targets), and the Z3
certificates. -/
theorem watertank_end_to_end_cadenced
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (domL : Formula (Var 1)) (ϕinv : RFormula (Var 1))
    (hψ : encode (Equiv.refl (Var 1)) ϕinv = invLe g)
    (hg : mv ∉ g.fv) (htgg : tg ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (watertankSuiteM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (watertankSuiteM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (watertankSuiteM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (htgS : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ fR, m.sys = rightBlock fR (Term.const 1) →
        tg ∉ (rightBlock fR (Term.const 1)).bound ∧
        (∀ p ∈ rightBlock fR (Term.const 1), tg ∉ (p.2 : Term (Var 1)).fv))
    (htgdom : tg ∉ watertankSuiteM.envF.fv)
    (hdis : Disjoint
        (Program.vars (clockedSeg (leftBlock fL) domL tg ((watertankSuiteM.dt : ℝ))))
        (Program.vars ((Program.star (rightAutomatonBodyC watertankSuiteM.graph mv tg
          ((watertankSuiteM.dt : ℝ)))).rename (Equiv.refl (Var 1)))))
    (hddF : Disjoint
        (faShape (Program.star (clockedSeg (leftBlock fL) domL tg
            ((watertankSuiteM.dt : ℝ))))
          (Program.star (rightAutomatonBodyC watertankSuiteM.graph mv tg
            ((watertankSuiteM.dt : ℝ))))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsL
        (Equiv.refl (Var 1) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL tg
            ((watertankSuiteM.dt : ℝ))))
          (Program.star (rightAutomatonBodyC watertankSuiteM.graph mv tg
            ((watertankSuiteM.dt : ℝ))))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsR))
    (hcert : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (watertankSuiteM.GdOf q) ν →
          BoxLe (Program.ode m.sys watertankSuiteM.envF) (fun ω => Term.eval g ω) ν) :
    RFormula.rvalid (theorem3Form
      (clockedSeg (leftBlock fL) domL tg ((watertankSuiteM.dt : ℝ)))
      (rightAutomatonBodyC watertankSuiteM.graph mv tg ((watertankSuiteM.dt : ℝ)))
      (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)) := by
  have hH : GuardSettlingH watertankSuiteM.graph watertankSuiteM.GdOf mv g
      (Term.const 1) tg ((watertankSuiteM.dt : ℝ)) fL watertankSuiteM.envF :=
    wellformed_sound watertankSuiteM mv tg g fL rfl
      (by norm_num [SettlingModel.dt, watertankSuiteM])
      hg hmvclk hmvtg hmvGd htgGd hfrzGd hcert
  exact theorem3_faithful_settling_cadenced' watertankSuiteM.graph watertankSuiteM.GdOf
    mv g fL domL watertankSuiteM.envF tg ((watertankSuiteM.dt : ℝ)) (Term.const 1)
    ϕinv hψ hH htgg htgS htgdom hdis hddF

end RelCertifier
