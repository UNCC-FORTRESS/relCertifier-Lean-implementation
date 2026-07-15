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
import RelCertifier.Checker.WellFormedChecker
import RelCertifier.Instances.FaithfulCerts
import RelCertifier.Proofs.Encoding.ClockedTop
import RelCertifier.Proofs.Encoding.FvDischarge
import RelCertifier.Proofs.Transfer.FaithfulBridge

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
      hg hmvclk hmvtg hmvGd htgGd hfrzGd
  exact theorem3_faithful_settling watertankSuiteM.graph watertankSuiteM.GdOf mv g fL
    domL watertankSuiteM.envF tg ((watertankSuiteM.dt : ℝ)) k (Term.const 1) ϕinv
    hψ hH (wellformed_gbox watertankSuiteM g hcert) htgb htgr htgϕ htgR htgφ hdis hdMULTI hbudget hddF

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
      hg hmvclk hmvtg hmvGd htgGd hfrzGd
  exact theorem3_faithful_settling_clocked watertankSuiteM.graph watertankSuiteM.GdOf
    mv g fL domL watertankSuiteM.envF tg ((watertankSuiteM.dt : ℝ)) (Term.const 1)
    ϕinv hψ hH (wellformed_gbox watertankSuiteM g hcert) hdis hddF

/-- **Watertank, end to end, ε-CADENCED BOTH SIDES, calculus coupling — the final form.**
Both stars clocked (`clockedSeg` left, `rightAutomatonBodyC` right); the per-segment
obligation passes through the `R*` slot (`faModal_LOCK_starR`), so the statement neither
assumes a budget nor forces lockstep. Residuals: the invariant encoding, aux-freshness of
`g` (`hg`, `htgg`), the tg-side and variable-hygiene facts (task B's targets), and the Z3
certificates. -/
theorem watertank_end_to_end_cadenced
    (mv tg tr : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (domL : Formula (Var 1)) (ϕinv : RFormula (Var 1))
    (hψ : encode (Equiv.refl (Var 1)) ϕinv = invLe g)
    (hg : mv ∉ g.fv) (htgg : tr ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (watertankSuiteM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (watertankSuiteM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (watertankSuiteM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (htgS : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ fR, m.sys = rightBlock fR (Term.const 1) →
        tr ∉ (rightBlock fR (Term.const 1)).bound ∧
        (∀ p ∈ rightBlock fR (Term.const 1), tr ∉ (p.2 : Term (Var 1)).fv))
    (htgdom : tr ∉ watertankSuiteM.envF.fv)
    (htrGd : ∀ q', tr ∉ (watertankSuiteM.GdOf q').fv)
    (hdis : Disjoint
        (Program.vars (clockedSeg (leftBlock fL) domL tg ((watertankSuiteM.dt : ℝ))))
        (Program.vars ((Program.star (rightAutomatonBodyC watertankSuiteM.graph mv tr
          ((watertankSuiteM.dt : ℝ)))).rename (Equiv.refl (Var 1)))))
    (hddF : Disjoint
        (faShape (Program.star (clockedSeg (leftBlock fL) domL tg
            ((watertankSuiteM.dt : ℝ))))
          (Program.star (rightAutomatonBodyC watertankSuiteM.graph mv tr
            ((watertankSuiteM.dt : ℝ))))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsL
        (Equiv.refl (Var 1) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL tg
            ((watertankSuiteM.dt : ℝ))))
          (Program.star (rightAutomatonBodyC watertankSuiteM.graph mv tr
            ((watertankSuiteM.dt : ℝ))))
          (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)).varsR))
    (hcert : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (watertankSuiteM.GdOf q) ν →
          BoxLe (Program.ode m.sys watertankSuiteM.envF) (fun ω => Term.eval g ω) ν) :
    RFormula.rvalid (theorem3Form
      (clockedSeg (leftBlock fL) domL tg ((watertankSuiteM.dt : ℝ)))
      (rightAutomatonBodyC watertankSuiteM.graph mv tr ((watertankSuiteM.dt : ℝ)))
      (ψpostG watertankSuiteM.graph watertankSuiteM.GdOf mv ϕinv)) := by
  have hH : GuardSettlingH watertankSuiteM.graph watertankSuiteM.GdOf mv g
      (Term.const 1) tg ((watertankSuiteM.dt : ℝ)) fL watertankSuiteM.envF :=
    wellformed_sound watertankSuiteM mv tg g fL rfl
      (by norm_num [SettlingModel.dt, watertankSuiteM])
      hg hmvclk hmvtg hmvGd htgGd hfrzGd
  exact theorem3_faithful_settling_cadenced' watertankSuiteM.graph watertankSuiteM.GdOf
    mv g fL domL watertankSuiteM.envF tg tr ((watertankSuiteM.dt : ℝ)) (Term.const 1)
    ϕinv hψ hH htgg htgS htgdom htrGd (wellformed_gbox watertankSuiteM g hcert) hdis hddF

/-! ## The Faithful bridge, instantiated: watertank

The kernel `faithfulSettling` certificate (named below; the anonymous copy lives in
`FaithfulCerts`) plus the concrete side-condition discharges upgrade the scaled model's
per-mode settling obligation to the REAL parsed model — `realFieldOf` (the ode text as a
polynomial term), `realEnvOf` (the parsed evolve bounds), `realGdOf` (parsed guard band ∧
evolve bounds) — at the real duration `u·dt` with `u = (ε_R/λ)/dtQ = 1` for this
transcription. Chained with `wellformed_sound`, the Z3 certificates are the only
non-structural inputs. -/

/-- Per-mode `GuardSettlingB` extraction from the Tier-B H bundle: the H's existential
field witness is the mode's own `fieldOf` (right blocks are injective in the field). -/
theorem GuardSettlingH_B (M : SettlingModel n) {mv : Var n} {g : Term (Var n)}
    {tg : Var n} {dt : ℝ} {fL : Fin n → Term (Var n)}
    (hH : GuardSettlingH M.graph M.GdOf mv g (Term.const 1) tg dt fL M.envF)
    {q : ℕ} {m : SettlingMode n} (hm : M.modes[q]? = some m) :
    GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF dt q := by
  obtain ⟨-, -, -, -, -, -, -, hmodes⟩ := hH
  have hma : M.graph.modeAt q = some (m.toRMode M) := by
    rw [graph_modeAt, hm]
    rfl
  obtain ⟨fR, hsys, -, -, hB, -⟩ := hmodes q (m.toRMode M) hma
  have hfr : m.fieldOf = fR := rightBlock_inj hsys
  rw [hfr]
  exact hB

/-- The kernel fidelity certificate, named. -/
theorem watertank_faithful :
    faithfulSettling Parse.watertank_IR watertankSuite_meta watertankSuiteM = true := rfl

/-- The parsed cadence: `ε_R = 1.0` lowers to the raw fraction `10/10`. -/
theorem watertank_epsR : parseQ Parse.watertank_IR.R.epsilon = some ⟨10, 10⟩ := rfl

/-- The transcription's time unit is `1` real second per `dt`-tick. -/
theorem watertank_u_val :
    (qDiv (qDiv (⟨10, 10⟩ : QF) watertankSuite_meta.lam)
      (qOfInt watertankSuiteM.dtQ)).val = 1 := by
  have h10 : qDiv (qDiv (⟨10, 10⟩ : QF) watertankSuite_meta.lam)
      (qOfInt watertankSuiteM.dtQ) = (⟨10, 10⟩ : QF) := rfl
  rw [h10]
  norm_num [QF.val]

/-- **The bridge at watertank, per mode**: scaled settling ⟹ real settling. -/
theorem watertank_bridge_per_mode {q : ℕ} {pm : Parse.PMode} {m : SettlingMode 1}
    (hpm : Parse.watertank_IR.R.modes[q]? = some pm)
    (hm : watertankSuiteM.modes[q]? = some m) (dts : ℝ)
    (hB : GuardSettlingB watertankSuiteM.graph watertankSuiteM.GdOf m.fieldOf
      (Term.const 1) watertankSuiteM.envF dts q) :
    GuardSettlingB watertankSuiteM.graph (realGdOf Parse.watertank_IR watertankSuiteM)
      (realFieldOf Parse.watertank_IR.R.stateVars pm 1) (Term.const 1)
      (realEnvOf Parse.watertank_IR.R.stateVars 1 pm) ((1 : ℝ) * dts) q := by
  have h := faithfulSettling_rescale Parse.watertank_IR watertankSuite_meta watertankSuiteM
    watertank_epsR watertank_faithful
    (by decide)
    rfl
    (by
      intro j hj
      interval_cases j
      exact Int.zero_lt_one)
    (by
      intro j
      fin_cases j
      norm_num [sigmaOf, QF.val, watertankSuite_meta, List.getD, qMk])
    (by rw [watertank_u_val]; norm_num)
    (by decide)
    hpm hm dts hB
  rwa [watertank_u_val] at h

/-- **Watertank, REAL-model end to end.** From the per-mode Z3 `BoxLe` certificates and
the freshness data, every declared mode of the REAL parsed benchmark — real ode text,
real evolve bounds, real guard bands — satisfies the settling obligation at the real
duration. The chain: `decideWellFormed` (kernel) → `wellformed_sound` → per-mode
`GuardSettlingB` (scaled) → `faithfulSettling` (kernel) + `GuardSettlingB_rescale` →
real model. -/
theorem watertank_real_settling
    (mv tg : Var 1) (g : Term (Var 1)) (fL : Fin 1 → Term (Var 1))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ (watertankSuiteM.GdOf q').fv)
    (htgGd : ∀ q', tg ∉ (watertankSuiteM.GdOf q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ (watertankSuiteM.GdOf q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hcert : ∀ q m, watertankSuiteM.graph.modeAt q = some m →
        ∀ ν, Formula.sat (watertankSuiteM.GdOf q) ν →
          BoxLe (Program.ode m.sys watertankSuiteM.envF) (fun ω => Term.eval g ω) ν) :
    ∀ q pm m, Parse.watertank_IR.R.modes[q]? = some pm →
      watertankSuiteM.modes[q]? = some m →
      GuardSettlingB watertankSuiteM.graph (realGdOf Parse.watertank_IR watertankSuiteM)
        (realFieldOf Parse.watertank_IR.R.stateVars pm 1) (Term.const 1)
        (realEnvOf Parse.watertank_IR.R.stateVars 1 pm)
        ((1 : ℝ) * (watertankSuiteM.dt : ℝ)) q := by
  intro q pm m hpm hm
  have hH : GuardSettlingH watertankSuiteM.graph watertankSuiteM.GdOf mv g
      (Term.const 1) tg ((watertankSuiteM.dt : ℝ)) fL watertankSuiteM.envF :=
    wellformed_sound watertankSuiteM mv tg g fL rfl
      (by norm_num [SettlingModel.dt, watertankSuiteM])
      hg hmvclk hmvtg hmvGd htgGd hfrzGd
  exact watertank_bridge_per_mode hpm hm _ (GuardSettlingH_B watertankSuiteM hH hm)

end RelCertifier
