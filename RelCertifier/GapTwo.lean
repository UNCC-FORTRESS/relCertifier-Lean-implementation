/-
GAP 2 — the left-mode family. Quantify the reposition-inclusive multi-flow theorem over ALL left
modes, not one fixed `mL`.

GAP 1 (`theorem3_faithful_multi_reposition`) fixes one left mode + one reposition mode. GAP 2 lifts to
the full left automaton `L* = star (bigChoice (all left modes ++ reposition))` by `faModal_bigChoiceL`
composition over the per-mL GAP-1 hsteps.

**The cross-left-mode join (resolved, no new content):** a left-mode switch `mL → mL'` is
**per-iteration loop re-entry**. The loop `relational_loop_multi` runs `faModal_MULTI` over
`star (bigChoice leftProgs)`; each iteration fires one `bigChoice` branch (one left mode) and preserves
the loop invariant `phiInv = invLe g ∧ mvValid`. The right's mode is carried in `mv` (state); each
iteration's hstep reads `mv` and dispatches. So `mL → mL'` is the next iteration picking a different
branch — the right re-syncs via `mv`, which the invariant carries. **`mv` is the sync**; no cross-mL
argument. `faModal_bigChoiceL` composes the per-mL hsteps; `faModal_MULTI` wraps the star.
-/
import RelCertifier.RepositionEndToEnd

namespace RelCertifier
open DL DLCalTiming DLRel Function

variable {n : ℕ}

/-- Per-left-mode flow data + its cert-sourced obligations (the GAP-1 flow-mode hypotheses, bundled
so the family can range over a `List`). Each is one left mode `ode (leftBlock fL) domL` with its
`RightProjAlign` (cert-linked to `Gj`) and `EmitSegs` (the mode-switch sequences). -/
structure FlowModeData (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (lam : Term (Var n)) (tg : Var n) (dt : ℝ) where
  fL : Fin n → Term (Var n)
  domL : Formula (Var n)
  hmvL : mv ∉ (leftBlock fL).bound
  hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars
  htgLb : tg ∉ (leftBlock fL).bound
  htgLr : tg ∉ (leftBlock fL).readVars
  htgdL : tg ∉ domL.fv
  hRPA : RightProjAlign Gj Gr g mv fL domL lam
  hemit : EmitSegs Gr g mv fL domL tg dt

/-- The left program of a flow-mode datum. -/
def FlowModeData.prog {Gj Gr : SearchGraph (Var n)} {g : Term (Var n)} {mv : Var n}
    {lam : Term (Var n)} {tg : Var n} {dt : ℝ}
    (d : FlowModeData Gj Gr g mv lam tg dt) : Program (Var n) :=
  Program.ode (leftBlock d.fL) d.domL

/-- **GAP 2 — the left-family theorem.** The reposition-inclusive multi Theorem 3 over the **full**
left automaton: `L_flat = bigChoice ((all flow modes) ++ [frozen reposition])`, wrapped to `L*` by the
loop. Each flow mode's hstep is the GAP-1 `Hmulti_from_cover` (cert-sourced from `cert.segPres`); the
reposition mode's is `Hmulti_from_cover_dyn` (from `cert.repoDynPresPre`). `faModal_bigChoiceL` composes
them per iteration; the left-mode switch is loop re-entry. Exhaustive over `flowModes` (every left mode
supplied contributes its branch — no mode dropped). `#print axioms = [propext, Classical.choice,
Quot.sound]`, parametric in `cert`. -/
theorem theorem3_faithful_family
    (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n) (lam : Term (Var n))
    (tg : Var n) (dt : ℝ) (ϕinv : RFormula (Var n))
    (cert : CoverCert Gj g) (hdt : 0 ≤ dt) (hg : mv ∉ g.fv)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (flowModes : List (FlowModeData Gj Gr g mv lam tg dt))
    -- frozen reposition mode (fL = 0)
    (domRepo : Formula (Var n))
    (hmvL0' : mv ∉ (leftBlock (fun _ => Term.const 0)).bound)
    (hφL0' : domRepo.fv ⊆ (leftBlock (fun _ => Term.const 0)).boundSet ∪
              (leftBlock (fun _ => Term.const 0)).readVars)
    (htgLb' : tg ∉ (leftBlock (fun _ => Term.const 0)).bound)
    (htgLr' : tg ∉ (leftBlock (fun _ => Term.const 0)).readVars)
    (htgdRepo : tg ∉ domRepo.fv)
    (hRPA_dyn : RightProjAlign_dyn Gj Gr g mv domRepo lam)
    (hemit' : EmitSegs Gr g mv (fun _ => Term.const 0) domRepo tg dt)
    -- shared automaton facts
    (htgg : tg ∉ g.fv)
    (htgRight : ∀ q m, Gr.modeAt q = some m →
      tg ∉ m.sys.bound ∧ tg ∉ m.sys.readVars ∧ tg ∉ m.sys.boundSet ∧ tg ∉ m.dom.fv)
    (hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length)
    (leftProgs : List (Program (Var n)))
    (hleftProgs : leftProgs = flowModes.map FlowModeData.prog ++
      [Program.ode (leftBlock (fun _ => Term.const 0)) domRepo])
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody Gr mv).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs)
      (rightAutomatonBody Gr mv) (RFormula.and ϕinv (mvValidR mv Gr.modes.length))) := by
  subst hleftProgs
  refine theorem3_faithful_multi_of_emit Gr mv g _ ϕinv hg hψ hfresh htt hlt hd ?_ hddF
  -- the family Hmulti: dispatch each left mode to its cert-sourced hstep
  intro P hP q hqlt σ hmvq hσ
  rcases List.mem_append.mp hP with hflow | hfrozen
  · -- a flow mode: GAP-1 Hmulti_from_cover with this mode's cert alignment
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hflow
    exact Hmulti_from_cover Gj Gr g mv d.fL d.domL lam tg dt cert hdt d.hmvL hg d.hφL d.htgLb
      d.htgLr d.htgdL htgg htgRight d.hRPA d.hemit _ (List.mem_singleton.mpr rfl) q hqlt σ hmvq hσ
  · -- the frozen reposition mode: Hmulti_from_cover_dyn
    rw [List.mem_singleton] at hfrozen; subst hfrozen
    exact Hmulti_from_cover_dyn Gj Gr g mv domRepo lam tg dt cert hdt hmvL0' hg hφL0' htgLb'
      htgLr' htgdRepo htgg htgRight hRPA_dyn hemit' _ (List.mem_singleton.mpr rfl) q hqlt σ hmvq hσ

end RelCertifier
