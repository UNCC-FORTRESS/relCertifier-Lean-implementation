/-
GAP 1 — the end-to-end theorem for genuine multi-flow covers: `decideCovered`/`cert ⟹ Theorem 3`.

Composes `Hmulti_from_cover` (the emit, cert-sourced) into `theorem3_faithful_multi_of_emit` (the
reposition-inclusive multi Theorem 3). Mirror of `decideCovered_implies_theorem3_faithful` (single
flow), now for covers where the right switches modes mid-residence. The Z3 leaf lives at `cert`
construction (parametric here — 3 axioms); `cert` is load-bearing for the `rvalid` conjunct.
-/
import RelCertifier.RepositionDischarge
import RelCertifier.RepositionFinish

namespace RelCertifier
open DL DLCalTiming DLRel Function

variable {n : ℕ}

/-- **The end-to-end multi-flow theorem.** From the cover certificate (`cert`, where the Z3 leaf
lives), the structural R-projection alignment (`RightProjAlign`, no Z3), and the multi-flow emit
(`EmitSegs`, the declared-edge mode-switch sequences), the transition-faithful ∀∃ refinement modality
over the real automaton `R_real Gr mv` holds at every bi-state — for **genuine multi-flow** covers
(the right switches modes within one left residence). AND (Island A) the co-execution invariant holds
throughout, from `decideCovered Gj = true` via `check_sound`.

Each per-segment `faModal` is drawn from **`cert.segPres`** (`Hmulti_from_cover` ← `box_joint_to_clocked`
← `cert`), NOT assumed. `#print axioms = [propext, Classical.choice, Quot.sound]`: parametric in `cert`,
so the Z3 leaf enters only when `cert` is constructed (per-mode, `segPres_from_flowCert`, 4th axiom
`z3_unsat_sound`). `cert` is load-bearing (delete → no box → no coupling → no `rvalid`). -/
theorem decideCovered_implies_theorem3_faithful_multi
    (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n) (fuel : ℕ) (cfg : Config)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n)) (tg : Var n) (dt : ℝ)
    (ϕinv : RFormula (Var n))
    (hchk : decideCovered Gj fuel cfg = true)
    (cert : CoverCert Gj g) (hdt : 0 ≤ dt)
    (hg : mv ∉ g.fv) (hmvL0 : mv ∉ (leftBlock fL0).bound)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (htgLb : tg ∉ (leftBlock fL0).bound) (htgLr : tg ∉ (leftBlock fL0).readVars)
    (htgdL0 : tg ∉ domL0.fv) (htgg : tg ∉ g.fv)
    (htgRight : ∀ q m, Gr.modeAt q = some m →
      tg ∉ m.sys.bound ∧ tg ∉ m.sys.readVars ∧ tg ∉ m.sys.boundSet ∧ tg ∉ m.dom.fv)
    (hRPA : RightProjAlign Gj Gr g mv fL0 domL0 lam)
    (hemit : EmitSegs Gr g mv fL0 domL0 tg dt)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length)
    (hd : Disjoint (Program.vars (bigChoice [Program.ode (leftBlock fL0) domL0]))
        (Program.vars ((rightAutomatonBody Gr mv).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (bigChoice [Program.ode (leftBlock fL0) domL0]))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice [Program.ode (leftBlock fL0) domL0]))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice [Program.ode (leftBlock fL0) domL0])
        (rightAutomatonBody Gr mv) (RFormula.and ϕinv (mvValidR mv Gr.modes.length)))
    ∧ (∀ ν, InvHolds g ν → CoexecInvThroughout Gj g cfg ν) :=
  ⟨theorem3_faithful_multi_of_emit Gr mv g [Program.ode (leftBlock fL0) domL0] ϕinv hg hψ
      hfresh htt hlt hd
      (Hmulti_from_cover Gj Gr g mv fL0 domL0 lam tg dt cert hdt hmvL0 hg hφL0 htgLb htgLr htgdL0
        htgg htgRight hRPA hemit) hddF,
   fun ν hinit => check_sound Gj g cert fuel cfg hchk ν hinit⟩

end RelCertifier
