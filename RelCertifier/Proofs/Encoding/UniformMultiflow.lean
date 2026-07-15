/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Uniform-suite multi-flow: clocked ε-windows (task H5)

The paper's round structure over the GAP-1 machinery, with the LEFT ε_L-window stated as a
`bigSeq` of `k` clocked pieces (`clockedSeg`, each capped at `dt = ε_R/λ` by the clock).
This makes the window budget STRUCTURAL — the analytic `r ≤ k·dt` hypothesis of `EmitSegs`
(unsatisfiable for uncapped physical residences) disappears; the clock caps every piece.

`theorem3_faithful_multi_of_emit` demands plain-ode left elements only through the
mv-framing fact, so we generalize the `hstep` layer to any mv-framing left program
(`hstep_single_multi'`, `hstep_assembled_multi'`, `theorem3_faithful_multi_of_emit'`) and
give the window instantiation: `Hmulti_window` assembles the per-piece cert-sourced
couplings (`segment_faModalB_from_cert` — the JOINT certificates) via `multiseg_clocked`,
stopping at the clocked window (no physical collapse). Repositions remain separate
plain-ode frozen-left loop elements, exactly as in `theorem3_faithful_multi_reposition`.
-/
import RelCertifier.Proofs.Encoding.RepositionEndToEnd

namespace RelCertifier

open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-- The clocked ε-window: `k` clock-capped pieces of the same left mode. -/
def windowSeg (leftSys : ODESystem (Var n)) (domL : Formula (Var n)) (tg : Var n)
    (dt : ℝ) (k : ℕ) : Program (Var n) :=
  bigSeq (List.replicate k (clockedSeg leftSys domL tg dt))

/-- A program frames `mv`: no run changes it. -/
def FramesMv (P : Program (Var n)) (mv : Var n) : Prop :=
  ∀ σ ν, Program.sem P σ ν → ν mv = σ mv

/-- Plain left odes frame `mv` (the original chain's case). -/
theorem framesMv_ode (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (mv : Var n)
    (hmvL : mv ∉ (leftBlock fL).bound) :
    FramesMv (Program.ode (leftBlock fL) domL) mv :=
  fun _ _ hsem => leftBlock_frames_mv fL domL mv hmvL hsem

/-- A clocked segment frames every variable outside `{tg} ∪ leftSys.bound`. -/
theorem framesMv_clockedSeg (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (mv : Var n) (hmvtg : mv ≠ tg)
    (hmvL : mv ∉ leftSys.bound) :
    FramesMv (clockedSeg leftSys domL tg dt) mv := by
  intro σ ν hsem
  obtain ⟨κ, hassign, κ', hode, htest⟩ := hsem
  rw [sem_assign] at hassign
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hode
  rw [sem_test] at htest
  obtain ⟨rfl, -⟩ := htest
  have hmv : mv ∉ (DLCalTiming.clk tg leftSys).bound := by
    intro hc
    unfold DLCalTiming.clk at hc
    rw [ODESystem.bound, List.map_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hmvL (by rwa [ODESystem.bound])
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      exact hmvtg hc
  rw [← hΦr]
  calc Φ r mv = κ mv := hmask r (Set.right_mem_Icc.mpr hr) mv hmv
    _ = σ mv := hassign.2 mv hmvtg

/-- `bigSeq` of framing programs frames. -/
theorem framesMv_bigSeq (mv : Var n) : ∀ (ps : List (Program (Var n))),
    (∀ P ∈ ps, FramesMv P mv) → FramesMv (bigSeq ps) mv := by
  intro ps
  induction ps with
  | nil =>
      intro _ σ ν hsem
      rw [bigSeq, sem_test] at hsem
      obtain ⟨rfl, -⟩ := hsem
      rfl
  | cons P ps ih =>
      intro h σ ν hsem
      obtain ⟨κ, hP, hrest⟩ := hsem
      calc ν mv = κ mv := ih (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)) κ ν hrest
        _ = σ mv := h P (List.mem_cons_self ..) σ κ hP

/-- The clocked window frames `mv`. -/
theorem framesMv_window (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ) (mv : Var n) (hmvtg : mv ≠ tg)
    (hmvL : mv ∉ leftSys.bound) :
    FramesMv (windowSeg leftSys domL tg dt k) mv := by
  refine framesMv_bigSeq mv _ ?_
  intro P hP
  rw [List.eq_of_mem_replicate hP]
  exact framesMv_clockedSeg leftSys domL tg dt mv hmvtg hmvL

/-! ## The generalized hstep layer (mv-framing lefts) -/

/-- `hstep_single_multi` with the left generalized from a plain ode to any mv-framing
program. The plain-ode shape was load-bearing only through `leftBlock_frames_mv`. -/
theorem hstep_single_multi' (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (g : Term (Var n)) (P : Program (Var n))
    (hg : mv ∉ g.fv) (hframe : FramesMv P mv) (hqlt : q < G.modes.length)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (segs : List (ℕ × RMode (Var n) × REdge (Var n)))
    (halign : ∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1)
    (hchain : List.IsChain (fun a b => a.2.2.tgt = b.1) segs)
    (hhead : ∀ s, segs.head? = some s → s.1 = q)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hfaModal : Formula.sat (faModal (Equiv.refl (Var n)) P
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P
      (Program.star (rightAutomatonBody G mv)) (phiInv g mv G.modes.length)) σ := by
  rw [faModal_sat] at hfaModal ⊢
  intro ν hleft
  obtain ⟨μ, hbigSeq, hinvμ⟩ := hfaModal ν hleft
  have hνmv : ν mv = (q : ℝ) := (hframe σ ν hleft).trans hmvq
  rw [Program.rename_refl] at hbigSeq
  obtain ⟨qf, hqfvalid, hstar⟩ :=
    faithful_rights_bridge G mv hfresh htt hlt segs halign hchain q hqlt hhead hbigSeq
  have hupdν : Function.update ν mv (q : ℝ) = ν := by
    funext x
    by_cases hx : x = mv
    · subst hx; rw [Function.update_self, hνmv]
    · rw [Function.update_of_ne hx]
  rw [hupdν] at hstar
  refine ⟨Function.update μ mv (qf : ℝ), by rw [Program.rename_refl]; exact hstar, ?_⟩
  rw [phiInv, sat_and]
  refine ⟨?_, ?_⟩
  · rw [sat_invLe] at hinvμ ⊢
    rwa [Term.coincidence g (fun y hy =>
      Function.update_of_ne (fun hc => hg (by rw [← hc]; exact hy)) _ _)]
  · rw [sat_mvValid]
    exact ⟨qf, hqfvalid, Function.update_self mv (qf : ℝ) μ⟩

/-- `hstep_assembled_multi`, generalized. -/
theorem hstep_assembled_multi' (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (hg : mv ∉ g.fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (invLe g) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ) :
    ∀ σ, Formula.sat (phiInv g mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv)) (phiInv g mv G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq⟩ := sat_mvValid.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBody G mv))
    (phiInv g mv G.modes.length) σ leftProgs ?_
  intro P hP
  obtain ⟨segs, halign, hchain, hhead, hfaModal⟩ := Hmulti P hP q hqlt σ hmvq hφ'.1
  exact hstep_single_multi' G mv q g P hg (hframes P hP) hqlt hfresh htt hlt segs halign
    hchain hhead hmvq hfaModal

/-- `theorem3_faithful_multi_of_emit`, generalized to mv-framing lefts. -/
theorem theorem3_faithful_multi_of_emit' (G : SearchGraph (Var n)) (mv : Var n)
    (g : Term (Var n)) (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hg : mv ∉ g.fv)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (invLe g) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
            (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
            (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and ϕinv (mvValidR mv G.modes.length))) :=
  theorem3_faithful_multi G mv g leftProgs ϕinv hψ hd
    (hstep_assembled_multi' G mv g leftProgs hg hfresh htt hlt hframes Hmulti) hddF

/-! ## The window response: per-piece joint certificates via `multiseg_clocked` -/

/-- **The window `Hmulti`.** For the clocked ε-window (`k` pieces), the response `faModal`
over the mode-switch sequence, each piece's coupling cert-sourced
(`segment_faModalB_from_cert` — the JOINT certificate at that piece's right mode/λ). No
budget hypothesis: the clock caps every piece. Requires the emitted sequence to have
exactly `k` segments (the cover pads with certified self-loop staying pieces). -/
theorem Hmulti_window (leftSys_fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (g : Term (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ)
    (rights : List (Program (Var n))) (hklen : rights.length = k)
    (hdis : ∀ Q ∈ rights, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock leftSys_fL) domL tg dt)))
    (hcouple : ∀ Q ∈ rights, ∀ σ', Formula.sat (invLe g) σ' →
        faModalB (Equiv.refl (Var n)) (Program.ode (clk tg (leftBlock leftSys_fL)) domL) Q
          (invLe g) tg dt (Function.update σ' tg 0))
    {σ : State (Var n)} (hσ : Formula.sat (invLe g) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (windowSeg (leftBlock leftSys_fL) domL tg dt k) (bigSeq rights) (invLe g)) σ := by
  have hmc := multiseg_clocked (invLe g) (leftBlock leftSys_fL) domL tg dt rights hdis
    hcouple σ hσ
  unfold windowSeg
  rw [← hklen]
  rwa [List.map_const'] at hmc

/-! ## The suite assembly: per-mode λ alignment, window emit, and the top theorem -/

/-- `RightProjAlign` with a PER-MODE stretch: each right mode carries its own λ (the
cover picks λ per piece; in the uniform suite the stretch is tied to the right mode). -/
def RightProjAlignV (Gj Gr : SearchGraph (Var n)) (g : Term (Var n))
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) : Prop :=
  ∀ (q : ℕ) (m' : RMode (Var n)), Gr.modeAt q = some m' →
    ∃ (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
      (mj : RMode (Var n)),
      m'.sys = rightBlock fR lam ∧ m'.dom = domR ∧
      Disjoint ((leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
               ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars) ∧
      domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars ∧
      Gj.modeAt q = some mj ∧ mj.jointOK = true ∧
      mj.sys = jointSys fL0 fR lam ∧ mj.dom = Formula.and domL0 domR ∧
      (∀ ν, HExistSeg fL0 fR lam domL0 domR ν)

/-- The emitted window responses: per start mode, a mode-switch sequence of EXACTLY `k`
segments (the cover pads with certified self-loop staying pieces), declared-edge aligned,
with the footprint facts. No duration bound — the window's clock caps every piece. -/
def EmitWindows (Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (k : ℕ) : Prop :=
  ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) → Formula.sat (invLe g) σ →
    ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
      segs.length = k ∧
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      (∀ Q ∈ segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom),
        Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
          (Program.vars (clockedSeg (leftBlock fL0) domL0 tg dt)))

/-- **The window `Hmulti`, cert-sourced.** Per start mode: the emitted `k`-segment
response, each piece's bounded coupling drawn from `cert.segPres` (the JOINT certificate,
via `segment_faModalB_from_cert`), assembled by `Hmulti_window`. -/
theorem Hmulti_window_from_cover (Gj Gr : SearchGraph (Var n)) (g : Term (Var n))
    (mv : Var n) (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (tg : Var n)
    (dt : ℝ) (k : ℕ) (cert : CoverCert Gj g)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (htgLb : tg ∉ (leftBlock fL0).bound) (htgLr : tg ∉ (leftBlock fL0).readVars)
    (htgdL0 : tg ∉ domL0.fv) (htgg : tg ∉ g.fv)
    (htgRight : ∀ q m, Gr.modeAt q = some m →
      tg ∉ m.sys.bound ∧ tg ∉ m.sys.readVars ∧ tg ∉ m.sys.boundSet ∧ tg ∉ m.dom.fv)
    (hRPA : RightProjAlignV Gj Gr g fL0 domL0)
    (hemit : EmitWindows Gr g mv fL0 domL0 tg dt k) :
    ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (invLe g) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n))
          (windowSeg (leftBlock fL0) domL0 tg dt k)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ := by
  intro q hqlt σ hmvq hσ
  obtain ⟨segs, hklen, halign, hchain, hhead, hdis⟩ := hemit q hqlt σ hmvq hσ
  refine ⟨segs, halign, hchain, hhead, ?_⟩
  refine Hmulti_window fL0 domL0 g tg dt k _ (by rw [List.length_map]; exact hklen)
    hdis ?_ hσ
  intro Q hQ σ' hσ'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hQ
  obtain ⟨hmodeAt, -⟩ := halign s hs
  obtain ⟨fR, lam, domR, mj, hsys, hdom, hdisj0, hφR, hmj, hjOK, hmjsys, hmjdom, hES⟩ :=
    hRPA s.1 s.2.1 hmodeAt
  obtain ⟨htgRb, htgRr, htgRbs, htgdR⟩ := htgRight s.1 s.2.1 hmodeAt
  rw [hsys] at htgRb htgRr htgRbs
  rw [hdom] at htgdR
  rw [hsys, hdom]
  have hbox : Formula.sat (Formula.box (Program.ode (leftBlock fL0 ++ rightBlock fR lam)
      (Formula.and domL0 domR)) (invLe g)) σ' := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    have hBL := cert.segPres s.1 mj hmj hjOK σ' ((sat_invLe g σ').mp hσ')
    rw [hmjsys, hmjdom] at hBL
    exact hBL ω (by rw [← jointSys_split] at hω; exact hω)
  exact segment_faModalB_from_cert g fL0 fR lam domL0 domR tg dt hdisj0 hφL0 hφR
    htgLb htgLr htgRb htgRr htgRbs htgdL0 htgdR htgg hbox (hES (Function.update σ' tg 0))

/-- **The uniform-suite multi-flow Theorem 3.** Left = the clocked ε_L-windows (one per
left mode, `k` clock-capped pieces each); right = the transition-faithful automaton star;
every within-window piece coupled by its JOINT certificate (`cert.segPres`), sequences
from the emitted cover. The window budget is structural (the clock), so no analytic
duration hypothesis appears. Repositions can be added as further frozen-left plain-ode
elements of `leftData` in the standard way. -/
theorem theorem3_uniform_multiflow (Gj Gr : SearchGraph (Var n)) (g : Term (Var n))
    (mv : Var n) (tg : Var n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (ϕinv : RFormula (Var n)) (cert : CoverCert Gj g)
    (hg : mv ∉ g.fv) (htgg : tg ∉ g.fv) (hmvtg : mv ≠ tg)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length)
    (htgRight : ∀ q m, Gr.modeAt q = some m →
      tg ∉ m.sys.bound ∧ tg ∉ m.sys.readVars ∧ tg ∉ m.sys.boundSet ∧ tg ∉ m.dom.fv)
    (hleft : ∀ d ∈ leftData, mv ∉ (leftBlock d.1).bound
      ∧ d.2.1.fv ⊆ (leftBlock d.1).boundSet ∪ (leftBlock d.1).readVars
      ∧ tg ∉ (leftBlock d.1).bound ∧ tg ∉ (leftBlock d.1).readVars ∧ tg ∉ d.2.1.fv
      ∧ RightProjAlignV Gj Gr g d.1 d.2.1
      ∧ EmitWindows Gr g mv d.1 d.2.1 tg dt d.2.2)
    (hd : Disjoint (Program.vars (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2))))
        (Program.vars ((rightAutomatonBody Gr mv).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
            windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2))))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
            windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2))))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftData.map (fun d => windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2)))
      (rightAutomatonBody Gr mv)
      (RFormula.and ϕinv (mvValidR mv Gr.modes.length))) := by
  refine theorem3_faithful_multi_of_emit' Gr mv g _ ϕinv hg hψ hfresh htt hlt ?_ hd ?_ hddF
  · -- every window frames mv
    intro P hP
    obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hP
    refine framesMv_window (leftBlock d.1) d.2.1 tg dt d.2.2 mv hmvtg ?_
    exact (hleft d hd').1
  · -- the window Hmulti, cert-sourced
    intro P hP q hqlt σ hmvq hσ
    obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hP
    obtain ⟨-, hφL0, htgLb, htgLr, htgdL0, hRPA, hemit⟩ := hleft d hd'
    exact Hmulti_window_from_cover Gj Gr g mv d.1 d.2.1 tg dt d.2.2 cert hφL0 htgLb htgLr
      htgdL0 htgg htgRight hRPA hemit q hqlt σ hmvq hσ

end RelCertifier
