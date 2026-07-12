/-
GAP 2 — the left-mode family. Quantify the reposition-inclusive multi-flow theorem over ALL left
modes, not one fixed `mL`.

GAP 1 (`theorem3_faithful_multi_reposition`) fixes one left mode + one reposition mode. GAP 2 lifts to
the full left automaton `L* = star (bigChoice (all left modes ++ reposition))` by `faModal_bigChoiceL`
composition over the per-mL GAP-1 hsteps.

**Per-mL `Gj`/`cert` (the correct structure).** Each left mode has its OWN cover graph `Gj` and
certificate `cert` (matching-crux (a): `certifyCore`'s `for mL` runs a SEPARATE cover per left mode,
`mL` frozen). `RightProjAlign Gj Gr … fL` forces `Gj`'s joint modes to `jointSys fL fR` — so a SHARED
`Gj` across distinct `fL` is jointly unsatisfiable (`jointSys` injective in `fL`). Hence `FlowModeData`
carries `Gj`+`cert` per mode; only the RIGHT automaton `Gr` (and `g`,`mv`,`ϕinv`) is shared. Each
mode's hstep is `faModal (ode leftBlock fL) (star rightAutomatonBody Gr) φinv` — shared right, per-mode
left — and `faModal_bigChoiceL` composes over the left choice.

**The cross-left-mode join (no new content):** a left-mode switch `mL → mL'` is per-iteration loop
re-entry. `faModal_MULTI` preserves `phiInv = invLe g ∧ mvValid`; the right's mode is carried in `mv`;
each iteration reads `mv` and dispatches. `mv` is the sync.
-/
import RelCertifier.RepositionEndToEnd

namespace RelCertifier
open DL DLCalTiming DLRel Function

variable {n : ℕ}

/-- Per-left-mode data: its OWN cover graph `Gj` + certificate `cert`, the left field/domain, and the
cert-sourced obligations (`RightProjAlign`, `EmitSegs`). Only `Gr` (the shared right automaton) and
`g`/`mv`/`lam`/`tg`/`dt` are shared across the family. -/
structure FlowModeData (Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (lam : Term (Var n)) (tg : Var n) (dt : ℝ) where
  Gj    : SearchGraph (Var n)
  cert  : CoverCert Gj g
  fL    : Fin n → Term (Var n)
  domL  : Formula (Var n)
  hmvL  : mv ∉ (leftBlock fL).bound
  hφL   : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars
  htgLb : tg ∉ (leftBlock fL).bound
  htgLr : tg ∉ (leftBlock fL).readVars
  htgdL : tg ∉ domL.fv
  hRPA  : RightProjAlign Gj Gr g mv fL domL lam
  hemit : EmitSegs Gr g mv fL domL tg dt

/-- The left program of a flow-mode datum. -/
def FlowModeData.prog {Gr : SearchGraph (Var n)} {g : Term (Var n)} {mv : Var n}
    {lam : Term (Var n)} {tg : Var n} {dt : ℝ}
    (d : FlowModeData Gr g mv lam tg dt) : Program (Var n) :=
  Program.ode (leftBlock d.fL) d.domL

/-- **GAP 2 — the left-family theorem.** The reposition-inclusive multi Theorem 3 over the **full**
left automaton `L* = star (bigChoice (all flow modes ++ [frozen reposition]))`. Each flow mode uses
its OWN `Gj`/`cert` (per-`mL` cover) via GAP-1 `Hmulti_from_cover`; the reposition mode uses its own
`Gj_repo`/`cert_repo` via `Hmulti_from_cover_dyn`. `faModal_bigChoiceL` composes them per iteration;
the left-mode switch is loop re-entry. Exhaustive over `flowModes` (no mode dropped). `#print axioms =
[propext, Classical.choice, Quot.sound]`, parametric in the per-mode `cert`s. -/
theorem theorem3_faithful_family
    (Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n) (lam : Term (Var n))
    (tg : Var n) (dt : ℝ) (ϕinv : RFormula (Var n))
    (hdt : 0 ≤ dt) (hg : mv ∉ g.fv)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (flowModes : List (FlowModeData Gr g mv lam tg dt))
    -- frozen reposition mode (fL = 0), its own Gj_repo/cert_repo
    (Gj_repo : SearchGraph (Var n)) (cert_repo : CoverCert Gj_repo g)
    (domRepo : Formula (Var n))
    (hmvL0' : mv ∉ (leftBlock (fun _ => Term.const 0)).bound)
    (hφL0' : domRepo.fv ⊆ (leftBlock (fun _ => Term.const 0)).boundSet ∪
              (leftBlock (fun _ => Term.const 0)).readVars)
    (htgLb' : tg ∉ (leftBlock (fun _ => Term.const 0)).bound)
    (htgLr' : tg ∉ (leftBlock (fun _ => Term.const 0)).readVars)
    (htgdRepo : tg ∉ domRepo.fv)
    (hRPA_dyn : RightProjAlign_dyn Gj_repo Gr g mv domRepo lam)
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
  intro P hP q hqlt σ hmvq hσ
  rcases List.mem_append.mp hP with hflow | hfrozen
  · -- a flow mode: GAP-1 Hmulti_from_cover with THIS mode's own Gj/cert
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hflow
    exact Hmulti_from_cover d.Gj Gr g mv d.fL d.domL lam tg dt d.cert hdt d.hmvL hg d.hφL d.htgLb
      d.htgLr d.htgdL htgg htgRight d.hRPA d.hemit _ (List.mem_singleton.mpr rfl) q hqlt σ hmvq hσ
  · -- the frozen reposition mode: Hmulti_from_cover_dyn with its own Gj_repo/cert_repo
    rw [List.mem_singleton] at hfrozen; subst hfrozen
    exact Hmulti_from_cover_dyn Gj_repo Gr g mv domRepo lam tg dt cert_repo hdt hmvL0' hg hφL0' htgLb'
      htgLr' htgdRepo htgg htgRight hRPA_dyn hemit' _ (List.mem_singleton.mpr rfl) q hqlt σ hmvq hσ

end RelCertifier
