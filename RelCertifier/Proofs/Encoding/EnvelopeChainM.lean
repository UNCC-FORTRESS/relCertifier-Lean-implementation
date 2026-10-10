/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L6 — the list-invariant modal chain (multi-component Theorem 3)

The modal chain (`phiInvE`, the couplings, `hstep_*_multiE`,
`theorem3_faithful_multiE_LR`) is single-invariant-term: `invLe g` throughout. Most
benchmarks have multi-component relational invariants (up to 8 conjuncts at the time) —
what the R4/R5 notes recorded as debt, and what this file pays. `AOp` has no
`max`, so no single term denotes the conjunction; the chain must be generalized.

This file delivers the generalization as F-PARAMETRIC MIRRORS over an opaque loop
formula `F` (instantiated at `FM g gs`, the nonempty invariant conjunction): the deep
cores (`faModal_ODE_G'_bounded`, `faithful_rights_bridge`, `relational_loop_multi`,
`multiseg_clocked`) are already formula-parametric, so each mirror is thin. The one
g-specific device (`box_joint_to_clocked`) is reused PER COMPONENT — boxes distribute
over conjunction (`sat_box_and`), so the `FM` box folds from component boxes.

New leaf (imports `EnvelopeChain` + `CanonicalInv`); no upstream edits.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Flow.ViabilityWiring

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## The nonempty invariant conjunction and its relational form -/

/-- `g₀ ≤ 0 ∧ … ∧ gₘ ≤ 0`, nonempty (head + tail). -/
def FM (g : Term (Var n)) (gs : List (Term (Var n))) : Formula (Var n) :=
  gs.foldr (fun g' acc => Formula.and (invLe g') acc) (invLe g)

theorem sat_FM_iff (g : Term (Var n)) (gs : List (Term (Var n))) (ν : State (Var n)) :
    Formula.sat (FM g gs) ν ↔ ∀ g' ∈ g :: gs, Term.eval g' ν ≤ 0 := by
  induction gs with
  | nil =>
      simp [FM, sat_invLe]
  | cons g' rest ih =>
      constructor
      · rintro ⟨h1, h2⟩ gi hgi
        rcases List.mem_cons.mp hgi with rfl | hgi
        · exact (ih.mp h2) gi List.mem_cons_self
        · rcases List.mem_cons.mp hgi with rfl | hgi
          · exact (sat_invLe _ _).mp h1
          · exact (ih.mp h2) gi (List.mem_cons_of_mem _ hgi)
      · intro h
        refine ⟨(sat_invLe _ _).mpr (h g' (List.mem_cons_of_mem _ List.mem_cons_self)), ?_⟩
        refine ih.mpr ?_
        intro gi hgi
        rcases List.mem_cons.mp hgi with rfl | hgi
        · exact h gi List.mem_cons_self
        · exact h gi (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hgi))

theorem notMem_FM_fv {g : Term (Var n)} {gs : List (Term (Var n))} {v : Var n}
    (h : ∀ g' ∈ g :: gs, v ∉ g'.fv) : v ∉ (FM g gs).fv := by
  induction gs with
  | nil =>
      intro hv
      exact h g List.mem_cons_self (by simpa [FM, invLe, Formula.fv, Term.fv] using hv)
  | cons g' rest ih =>
      intro hv
      rcases hv with hv | hv
      · exact h g' (List.mem_cons_of_mem _ List.mem_cons_self)
          (by simpa [invLe, Formula.fv, Term.fv] using hv)
      · exact ih (fun gi hgi => h gi (by
          rcases List.mem_cons.mp hgi with rfl | hgi
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hgi))) hv

/-- The relational conjunction of canonical invariants. -/
def canonInvM (g : Term (Var n)) (gs : List (Term (Var n))) : RFormula (Var n) :=
  gs.foldr (fun g' acc => RFormula.and (canonInv g') acc) (canonInv g)

theorem encode_canonInvM (g : Term (Var n)) (gs : List (Term (Var n))) :
    encode (Equiv.refl (Var n)) (canonInvM g gs) = FM g gs := by
  induction gs with
  | nil => exact encode_canonInv g
  | cons g' rest ih =>
      show encode _ (RFormula.and (canonInv g') (canonInvM g rest))
        = Formula.and (invLe g') (FM g rest)
      have hdist : encode (Equiv.refl (Var n))
          (RFormula.and (canonInv g') (canonInvM g rest))
          = Formula.and (encode (Equiv.refl (Var n)) (canonInv g'))
            (encode (Equiv.refl (Var n)) (canonInvM g rest)) := by
        unfold encode
        simp only [RFormula.renameR, RFormula.enc]
      rw [hdist, encode_canonInv, ih]

theorem canonInvM_varsL (g : Term (Var n)) (gs : List (Term (Var n)))
    (hg : ∀ g' ∈ g :: gs, g'.fv ⊆ range Lv ∪ range Rv) :
    (canonInvM g gs).varsL ⊆ range Lv := by
  induction gs with
  | nil => exact canonInv_varsL g (hg g List.mem_cons_self)
  | cons g' rest ih =>
      intro x hx
      rcases hx with hx | hx
      · exact canonInv_varsL g' (hg g' (List.mem_cons_of_mem _ List.mem_cons_self)) hx
      · exact ih (fun gi hgi => hg gi (by
          rcases List.mem_cons.mp hgi with rfl | hgi
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hgi))) hx

theorem canonInvM_varsR (g : Term (Var n)) (gs : List (Term (Var n))) :
    (canonInvM g gs).varsR ⊆ range Rv := by
  induction gs with
  | nil => exact canonInv_varsR g
  | cons g' rest ih =>
      intro x hx
      rcases hx with hx | hx
      · exact canonInv_varsR g' hx
      · exact ih hx

/-! ## Component boxes fold into the conjunction box -/

theorem sat_box_and {P : Program (Var n)} {A B : Formula (Var n)} {σ : State (Var n)}
    (hA : Formula.sat (Formula.box P A) σ) (hB : Formula.sat (Formula.box P B) σ) :
    Formula.sat (Formula.box P (Formula.and A B)) σ := by
  rw [sat_box] at hA hB ⊢
  exact fun ω hω => ⟨hA ω hω, hB ω hω⟩

/-- The clocked box for `FM`, folded from per-component `box_joint_to_clocked`. -/
theorem box_FM_clocked (g : Term (Var n)) (gs : List (Term (Var n)))
    (fLb Rb : ODESystem (Var n)) (dom : Formula (Var n)) (tg : Var n)
    (htgLb : tg ∉ fLb.bound) (htgRb : tg ∉ Rb.bound)
    (htgLr : tg ∉ fLb.readVars) (htgRr : tg ∉ Rb.readVars)
    (htgdom : tg ∉ dom.fv)
    (htggs : ∀ g' ∈ g :: gs, tg ∉ g'.fv)
    {σ : State (Var n)}
    (hboxes : ∀ g' ∈ g :: gs, Formula.sat
      (Formula.box (Program.ode (fLb ++ Rb) dom) (invLe g')) σ) :
    Formula.sat (Formula.box (Program.ode (DLCalTiming.clk tg fLb ++ Rb) dom)
      (FM g gs)) (Function.update σ tg 0) := by
  induction gs with
  | nil =>
      exact box_joint_to_clocked g fLb Rb dom tg htgLb htgRb htgLr htgRr htgdom
        (htggs g List.mem_cons_self) (hboxes g List.mem_cons_self)
  | cons g' rest ih =>
      refine sat_box_and ?_ ?_
      · exact box_joint_to_clocked g' fLb Rb dom tg htgLb htgRb htgLr htgRr htgdom
          (htggs g' (List.mem_cons_of_mem _ List.mem_cons_self))
          (hboxes g' (List.mem_cons_of_mem _ List.mem_cons_self))
      · refine ih (fun gi hgi => htggs gi ?_) (fun gi hgi => hboxes gi ?_) <;>
          · rcases List.mem_cons.mp hgi with rfl | hgi
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hgi)

/-! ## The multi-component bounded coupling -/

/-- `segment_faModalB_from_certB`, list invariant: the loop formula is `FM g gs`, its
clocked box folded from the per-component certificate boxes. -/
theorem segment_faModalB_from_certB_list (g : Term (Var n)) (gs : List (Term (Var n)))
    (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (domL domR : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (hdisj0 : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                       ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (htgLb : tg ∉ (leftBlock fL).bound) (htgLr : tg ∉ (leftBlock fL).readVars)
    (htgRb : tg ∉ (rightBlock fR lam).bound) (htgRr : tg ∉ (rightBlock fR lam).readVars)
    (htgRbs : tg ∉ (rightBlock fR lam).boundSet)
    (htgdL : tg ∉ domL.fv) (htgdR : tg ∉ domR.fv)
    (htggs : ∀ g' ∈ g :: gs, tg ∉ g'.fv)
    {σ : State (Var n)}
    (hboxes : ∀ g' ∈ g :: gs, Formula.sat (Formula.box
      (Program.ode (leftBlock fL ++ rightBlock fR lam)
        (Formula.and domL domR)) (invLe g')) σ)
    (hES : HExistSegB fL fR lam domL domR dt (Function.update σ tg 0)) :
    faModalB (Equiv.refl (Var n)) (Program.ode (clk tg (leftBlock fL)) domL)
      (Program.ode (rightBlock fR lam) domR) (FM g gs) tg dt
      (Function.update σ tg 0) := by
  have hrv := clk_readVars (leftBlock fL) tg
  have hbs := clk_boundSet (leftBlock fL) tg
  refine faModal_ODE_G'_bounded (Equiv.refl (Var n)) (clk tg (leftBlock fL))
    (rightBlock fR lam) domL domR (FM g gs) tg dt (Function.update σ tg 0)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [ODESystem.rename_refl, hbs, hrv]
    have hset : (leftBlock fL).boundSet ∪ {tg} ∪ (leftBlock fL).readVars
        = ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars) ∪ {tg} := by
      ext y; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto
    rw [hset]
    refine Set.disjoint_union_left.mpr ⟨hdisj0, ?_⟩
    rw [Set.disjoint_singleton_left, Set.mem_union]
    exact fun hc => hc.elim htgRbs htgRr
  · rw [hbs, hrv]
    exact hφL.trans (Set.union_subset_union_left _ Set.subset_union_left)
  · rw [Formula.rename_refl, ODESystem.rename_refl]; exact hφR
  · rw [ODESystem.rename_refl, Formula.rename_refl]
    have htgdom : tg ∉ (Formula.and domL domR).fv := by
      simp only [Formula.fv, Set.mem_union, not_or]; exact ⟨htgdL, htgdR⟩
    exact box_FM_clocked g gs (leftBlock fL) (rightBlock fR lam)
      (Formula.and domL domR) tg htgLb htgRb htgLr htgRr htgdom htggs hboxes
  · simp only [ODESystem.rename_refl, Formula.rename_refl]
    exact hExist_clocked_of_HExistSegB fL fR lam domL domR tg dt htgLb htgLr htgRb
      htgRr htgdL htgdR hES

/-! ## The F-parametric step and loop lemmas -/

/-- `phiInvE` with an opaque loop formula in place of `invLe g`. -/
def phiInvF (F env : Formula (Var n)) (mv : Var n) (k : ℕ) : Formula (Var n) :=
  Formula.and (Formula.and F env) (mvValid mv k)

/-- `hstep_single_multiE`, F-parametric. -/
theorem hstep_single_multiF (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (F env : Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hframe : FramesMv P mv) (hqlt : q < G.modes.length)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (segs : List (ℕ × RMode (Var n) × REdge (Var n)))
    (halign : ∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1)
    (hchain : List.IsChain (fun a b => a.2.2.tgt = b.1) segs)
    (hhead : ∀ s, segs.head? = some s → s.1 = q)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hfaModal : Formula.sat (faModal (Equiv.refl (Var n)) P
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and F env)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P
      (Program.star (rightAutomatonBody G mv)) (phiInvF F env mv G.modes.length)) σ := by
  rw [faModal_sat] at hfaModal ⊢
  intro ν hleft
  obtain ⟨μ, hbigSeq, hpostμ⟩ := hfaModal ν hleft
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
  have hinvμ := hpostμ.1
  have henvμ := hpostμ.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rwa [(Formula.coincidence F (fun y hy =>
      Function.update_of_ne (fun hc => hF (by rw [← hc]; exact hy)) _ _) :
        Formula.sat F _ ↔ Formula.sat F μ)]
  · rwa [(Formula.coincidence env (fun y hy =>
      Function.update_of_ne (fun hc => henv (by rw [← hc]; exact hy)) _ _) :
        Formula.sat env _ ↔ Formula.sat env μ)]
  · rw [sat_mvValid]
    exact ⟨qf, hqfvalid, Function.update_self mv (qf : ℝ) μ⟩

/-- `hstep_assembled_multiE`, F-parametric. -/
theorem hstep_assembled_multiF (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n))
    (leftProgs : List (Program (Var n))) (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and F env)) σ) :
    ∀ σ, Formula.sat (phiInvF F env mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv)) (phiInvF F env mv G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq⟩ := sat_mvValid.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBody G mv))
    (phiInvF F env mv G.modes.length) σ leftProgs ?_
  intro P hP
  obtain ⟨segs, halign, hchain, hhead, hfaModal⟩ := Hmulti P hP q hqlt σ hmvq hφ'.1
  exact hstep_single_multiF G mv q F env P hF henv (hframes P hP) hqlt hfresh htt hlt
    segs halign hchain hhead hmvq hfaModal

/-- Encoding of the F-parametric postcondition (mirror of `encode_phiInvE_LR`). -/
theorem encode_phiInvF_LR {ϕinv : RFormula (Var n)} {F : Formula (Var n)}
    {domL domR : Formula (Var n)} {mv : Var n} {k : ℕ}
    (hψ : encode (Equiv.refl (Var n)) ϕinv = F) :
    encode (Equiv.refl (Var n))
      (RFormula.and (RFormula.and ϕinv (envLR domL domR)) (mvValidR mv k))
      = phiInvF F (Formula.and domL domR) mv k := by
  have hdist : encode (Equiv.refl (Var n))
      (RFormula.and (RFormula.and ϕinv (envLR domL domR)) (mvValidR mv k))
      = Formula.and (Formula.and (encode (Equiv.refl (Var n)) ϕinv)
          (encode (Equiv.refl (Var n)) (envLR domL domR)))
        (encode (Equiv.refl (Var n)) (mvValidR mv k)) := by
    unfold encode; simp only [RFormula.renameR, RFormula.enc]
  rw [hdist, hψ, encode_envLR, encode_mvValidR]; rfl

/-- **The list-invariant Theorem 3 assembly** (mirror of `theorem3_faithful_multiE_LR`
over an opaque loop formula). -/
theorem theorem3_faithful_multiF_LR (G : SearchGraph (Var n)) (mv : Var n)
    (F : Formula (Var n)) (domL domR : Formula (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = F)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInvF F (Formula.and domL domR) mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv))
        (phiInvF F (Formula.and domL domR) mv G.modes.length)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and ϕinv (envLR domL domR))
            (mvValidR mv G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and ϕinv (envLR domL domR))
            (mvValidR mv G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and (RFormula.and ϕinv (envLR domL domR))
        (mvValidR mv G.modes.length))) := by
  set k := G.modes.length
  set ψpost := RFormula.and (RFormula.and ϕinv (envLR domL domR)) (mvValidR mv k)
    with hψpost
  set Lp := Program.star (bigChoice leftProgs)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost
      = phiInvF F (Formula.and domL domR) mv k := encode_phiInvF_LR hψ
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
  have hInvν : Formula.sat (phiInvF F (Formula.and domL domR) mv k) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_multi (bigChoice leftProgs) (rightAutomatonBody G mv) ψpost ν bs hd
    (by rw [hencψ]; exact hInvν)
    (fun σ hσ => by rw [hencψ] at hσ ⊢; exact hstep σ hσ) hddF hbdg

/-! ## The F-parametric one-piece prefixed window -/

/-- `Hmulti_window1_prefixed` over an opaque loop formula (the L6 window form; the L2
right-only variant composes via `faModalB_repoPathR`'s φ-parametricity). -/
theorem Hmulti_window1_prefixedF (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (F env : Formula (Var n)) (a : Fin n) (dt : ℝ)
    (htgF : ((Side.Aux, a) : Var n) ∉ F.fv) (htgenv : ((Side.Aux, a) : Var n) ∉ env.fv)
    (hops : List (RepoHop n))
    (hhops : ∀ h ∈ hops, (∀ i, (h.fR i).fv ⊆ range Rv) ∧ h.lam.fv ⊆ range Rv
      ∧ h.domR.fv ⊆ range Rv)
    (hR : ∀ h ∈ hops, ∀ σ, Formula.sat (Formula.and F env) σ →
      σ ((Side.Aux, a) : Var n) = 0 →
      ∃ ρ, Program.sem (h.prog domL) σ ρ ∧ Formula.sat (Formula.and F env) ρ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (piece : Program (Var n))
    (hcouple : ∀ σ, Formula.sat (Formula.and F env) σ →
      σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        piece (Formula.and F env) ((Side.Aux, a) : Var n) dt σ)
    {σ : State (Var n)} (hσ : Formula.sat (Formula.and F env) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (windowSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt 1)
      (bigSeq ((hops.map (fun h => h.prog domL)) ++ [piece]))
      (Formula.and F env)) σ := by
  have htgφ : ((Side.Aux, a) : Var n) ∉ (Formula.and F env).fv := by
    intro h
    rcases h with h | h
    · exact htgF h
    · exact htgenv h
  have hupdφ : Formula.sat (Formula.and F env)
      (Function.update σ ((Side.Aux, a) : Var n) 0) := by
    rwa [(Formula.coincidence (Formula.and F env) (fun v hv =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv)) _ _) :
        Formula.sat (Formula.and F env) _ ↔ _)]
  have hpath := faModalB_repoPath hfL hdomL hops hhops hR hcouple
    (Function.update σ ((Side.Aux, a) : Var n) 0) hupdφ (Function.update_self _ _ _)
  have hseg := (faModalB_clockedSeg_iff (leftBlock fL) domL _
    (Formula.and F env) ((Side.Aux, a) : Var n) dt σ).mpr hpath
  have hcong := sat_faModal_congrR (Q' := bigSeq ((hops.map (fun h => h.prog domL))
      ++ [piece])) (fun ν μ => by
    rw [foldr_prog_map]
    exact sem_foldr_seq_bigSeq (hops.map (fun h => h.prog domL)) piece ν μ) hseg
  exact sat_faModal_monoL
    (fun ν μ h => (sem_windowSeg_one (leftBlock fL) domL _ dt).mp h) hcong

end RelCertifier
