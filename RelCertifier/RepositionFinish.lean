/-
GAP 1 finish — the transition-faithful **multi-flow** Theorem 3 (`rvalid` form).

`theorem3_faithful` (single-body hstep, `relational_loop_faithful`) covers single-flow-per-residence
covers: each right mode covers the whole left residence. Genuine multi-flow (the right switches modes
*mid*-residence) produces a **star-right** hstep — one left residence ↔ a mode-switching star — which
`relational_loop_multi` (`faModal_MULTI`, star-right) consumes. `star (star R) = star R`, so the
`R_real` is unchanged: `faShape (star L)(star R) ψ`, the same Theorem-3 shape.

This file is the mirror of `theorem3_faithful` over `relational_loop_multi`, taking the star-right
hstep assembled by `hstep_assembled_multi` (`BridgeReposition`).
-/
import RelCertifier.BridgeReposition
import RelCertifier.BridgeFinish
import RelCertifier.EncodingBridge

namespace RelCertifier
open DL DLCalTiming DLRel Function

variable {n : ℕ}

/-- **Transition-faithful multi-flow Theorem 3, `rvalid` form.** With mode-validity carried in the
invariant, the **star-right** loop step (`hstep`, one residence ↔ a mode-switching star of declared
`G`-edges — the genuine multi-flow) yields the ∀∃ refinement modality over the real automaton
`R_real G mv = star (rightAutomatonBody G mv)`, valid at every bi-state. Mirror of `theorem3_faithful`
over `relational_loop_multi` (the star-right loop). -/
theorem theorem3_faithful_multi (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInv g mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv)) (phiInv g mv G.modes.length)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
            (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and ϕinv (mvValidR mv G.modes.length))) := by
  set k := G.modes.length
  set ψpost := RFormula.and ϕinv (mvValidR mv k) with hψpost
  set Lp := Program.star (bigChoice leftProgs)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost = phiInv g mv k := encode_and_mvValidR hψ
  intro bs
  rw [theorem3Form]
  refine (RFormula_sat_imp _ _ bs).mpr ?_
  intro hpre
  obtain ⟨ν, hbdg⟩ := exists_bridge (Equiv.refl (Var n))
    (faShape Lp Rp ψpost).varsL (faShape Lp Rp ψpost).varsR hddF bs
  have hbψ : Bridges (Equiv.refl (Var n)) ψpost.varsL ψpost.varsR bs ν :=
    hbdg.mono (varsL_subset_faShape Lp Rp ψpost) (varsR_subset_faShape Lp Rp ψpost)
  have hdψ : Disjoint ψpost.varsL (Equiv.refl (Var n) '' ψpost.varsR) :=
    hddF.mono (varsL_subset_faShape Lp Rp ψpost)
      (Set.image_mono (varsR_subset_faShape Lp Rp ψpost))
  have hInvν : Formula.sat (phiInv g mv k) ν := by
    rw [← hencψ]; exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_multi (bigChoice leftProgs) (rightAutomatonBody G mv) ψpost ν bs hd
    (by rw [hencψ]; exact hInvν)
    (fun σ hσ => by rw [hencψ] at hσ ⊢; exact hstep σ hσ) hddF hbdg

/-- **The reposition-inclusive multi Theorem 3, modulo the emit `Hmulti`.** Chains the assembled
star-right hstep (`hstep_assembled_multi`) into `theorem3_faithful_multi`. `Hmulti` is the emit
boundary: per current mode `q`, the right's genuine-multi-flow response — a `segs` mode-switch
sequence (each seg a declared `G`-edge; a **reposition** appears as a `sys = []` zero-motion mode,
a **flow** as a real ODE) and the `bigSeq`-response `faModal` over `invLe g` (from `multiseg_clocked`
+ `clockLift_collapse` for flow segments, `reposition_step_pres`/`dynreposition_faModal` for
reposition segments — the per-segment coupling **dispatch**). NO `jointOK` gate: the segments are
flow-or-reposition, and the switch of each is still a declared `G`-edge (`faithful_rights_bridge`,
`EdgeTargetsValid`). This puts reposition-using covers (Hold, story, rover, watertank, rung2) in
scope of the transition-faithful ∀∃ modality. -/
theorem theorem3_faithful_multi_of_emit (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n)) (hg : mv ∉ g.fv)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (invLe g) σ →
      ∃ (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
        (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
        P = Program.ode (leftBlock fL) domL ∧ MvFrozen fL mv ∧
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
            (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and ϕinv (mvValidR mv G.modes.length))) :=
  theorem3_faithful_multi G mv g leftProgs ϕinv hψ hd
    (hstep_assembled_multi G mv g leftProgs hg hfresh htt hlt Hmulti) hddF

end RelCertifier
