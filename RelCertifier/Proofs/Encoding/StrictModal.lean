/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Strict invariant rows in the modal chain (extension `strict-atoms`)

The list-invariant modal chain (`EnvelopeChainM`) is F-parametric except for the clocked box
of the loop formula (`box_FM_clocked`), which folds per-component `box_joint_to_clocked`, a
lemma specialized to `invLe`. This file:

* generalizes the clock lifting to any formula the fresh clock does not read
  (`box_clock_lift_F`, `box_joint_to_clocked_F`; `invLe g` and `invLt g` are instances);
* folds the per-component boxes of the flagged atoms into the clocked box of `FMS`
  (`box_FMS_clocked`) and assembles the bounded coupling (`segment_faModalB_from_certB_listS`);
* turns the strict flow certificates (`BoxLt`, routes A and B) and the closure certificates
  (`BoxLe`) into the per-component boxes (`sat_box_invAt_of_holds`);
* instantiates the F-parametric Theorem 3 assembly at `F := FMS g gs m`
  (`theorem3_faithful_multiS_LR`), which with an all-false mask is the existing statement
  (`theorem3_faithful_multiS_LR_collapse`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.StrictInv

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## Clock lifting, formula-generic -/

/-- `boxLe_clock_lift` for any formula the fresh clock does not read. -/
theorem box_clock_lift_F (sys : ODESystem (Var n)) (dom : Formula (Var n)) (φ : Formula (Var n))
    (tg : Var n) (htgb : tg ∉ sys.bound) (htgr : tg ∉ sys.readVars) (htgd : tg ∉ dom.fv)
    (htgφ : tg ∉ φ.fv) {ω : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode sys dom) φ) ω) :
    Formula.sat (Formula.box (Program.ode (clk tg sys) dom) φ) ω := by
  rw [sat_box] at h ⊢
  intro ν hν
  have hdrop := clockReduce sys dom tg htgb htgr htgd hν
  have hinv := h _ hdrop
  exact (Formula.coincidence φ (fun y hy =>
    Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hy)) _ _)).mp hinv

/-- `box_joint_to_clocked` for any formula the fresh clock does not read. -/
theorem box_joint_to_clocked_F (φ : Formula (Var n)) (A B : ODESystem (Var n))
    (dom : Formula (Var n)) (tg : Var n)
    (htgAb : tg ∉ A.bound) (htgBb : tg ∉ B.bound)
    (htgAr : tg ∉ A.readVars) (htgBr : tg ∉ B.readVars)
    (htgd : tg ∉ dom.fv) (htgφ : tg ∉ φ.fv) {σ : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode (A ++ B) dom) φ) σ) :
    Formula.sat (Formula.box (Program.ode ((clk tg A) ++ B) dom) φ)
      (Function.update σ tg 0) := by
  have htgABb : tg ∉ (A ++ B).bound := by
    simp only [ODESystem.bound, List.map_append, List.mem_append]
    exact fun hc => hc.elim htgAb htgBb
  have htgABr : tg ∉ (A ++ B).readVars := by
    simp only [ODESystem.readVars, Set.mem_setOf_eq]
    rintro ⟨p, hp, hpx⟩
    exact (List.mem_append.mp hp).elim (fun ha => htgAr ⟨p, ha, hpx⟩)
      (fun hb => htgBr ⟨p, hb, hpx⟩)
  have hφfv : φ.fv ⊆ {x | x ≠ tg} := fun y hy hc => htgφ (hc ▸ hy)
  have hstart : Formula.sat (Formula.box (Program.ode (A ++ B) dom) φ)
      (Function.update σ tg 0) := by
    rw [sat_box] at h ⊢
    intro ν hν
    have hWsub : (Program.ode (A ++ B) dom).fv ⊆ {x | x ≠ tg} := by
      refine Set.union_subset (Set.union_subset ?_ ?_) ?_
      · intro x hx hc; exact htgABb (hc ▸ hx)
      · intro x hx hc; exact htgABr (hc ▸ hx)
      · intro x hx hc; exact htgd (hc ▸ hx)
    have hag : Set.EqOn (Function.update σ tg 0) σ {x | x ≠ tg} :=
      fun x hx => Function.update_of_ne hx 0 σ
    obtain ⟨ω2, hrun2, heq⟩ := Program.coincidence (Program.ode (A ++ B) dom) hWsub hag hν
    have hinv := h ω2 hrun2
    exact (Formula.coincidence φ (heq.mono (hφfv.trans Set.subset_union_left))).mpr hinv
  exact box_ode_perm (List.Perm.symm (clk_mid_perm A B tg)) dom φ
    (box_clock_lift_F (A ++ B) dom φ tg htgABb htgABr htgd htgφ hstart)

/-- The instance at `invLe g` is the existing `box_joint_to_clocked`. -/
theorem box_joint_to_clocked_F_invLe (g : Term (Var n)) (A B : ODESystem (Var n))
    (dom : Formula (Var n)) (tg : Var n)
    (htgAb : tg ∉ A.bound) (htgBb : tg ∉ B.bound)
    (htgAr : tg ∉ A.readVars) (htgBr : tg ∉ B.readVars)
    (htgd : tg ∉ dom.fv) (htgg : tg ∉ g.fv) {σ : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode (A ++ B) dom) (invLe g)) σ) :
    Formula.sat (Formula.box (Program.ode ((clk tg A) ++ B) dom) (invLe g))
      (Function.update σ tg 0) :=
  box_joint_to_clocked_F (invLe g) A B dom tg htgAb htgBb htgAr htgBr htgd
    (by simpa [invLe, Formula.fv, Term.fv] using htgg) h

theorem notMem_invAt_fv {b : Bool} {g : Term (Var n)} {v : Var n} (h : v ∉ g.fv) :
    v ∉ (invAt b g).fv := by
  rw [invAt_fv]; simpa [invLe, Formula.fv, Term.fv] using h

/-! ## Per-component boxes from the certificates -/

/-- A flagged component's box: a strict component from a `BoxLt` (routes A/B,
`flow_cert_sound_lt`, `flow_cert_sound_strict_lt`), a closure component from a `BoxLe`. -/
theorem sat_box_invAt_of_holds {α : Program (Var n)} {b : Bool} {g : Term (Var n)}
    {σ : State (Var n)} (h : ∀ ω, Program.sem α σ ω → HoldsAt b g ω) :
    Formula.sat (Formula.box α (invAt b g)) σ := by
  rw [sat_box]; intro ω hω; exact (sat_invAt b g ω).mpr (h ω hω)

theorem sat_box_invLt_of_BoxLt {α : Program (Var n)} {g : Term (Var n)} {σ : State (Var n)}
    (h : BoxLt α (fun ω => Term.eval g ω) σ) : Formula.sat (Formula.box α (invAt true g)) σ :=
  sat_box_invAt_of_holds (b := true) (fun ω hω => h ω hω)

theorem sat_box_invLe_of_BoxLe {α : Program (Var n)} {g : Term (Var n)} {σ : State (Var n)}
    (h : BoxLe α (fun ω => Term.eval g ω) σ) : Formula.sat (Formula.box α (invAt false g)) σ :=
  sat_box_invAt_of_holds (b := false) (fun ω hω => h ω hω)

/-! ## The clocked box of `FMS` -/

/-- The clocked box of a flagged fold, from the per-atom unclocked boxes. -/
theorem box_foldAt_clocked (ts : List (Bool × Term (Var n))) (B : Formula (Var n))
    (fLb Rb : ODESystem (Var n)) (dom : Formula (Var n)) (tg : Var n)
    (htgLb : tg ∉ fLb.bound) (htgRb : tg ∉ Rb.bound)
    (htgLr : tg ∉ fLb.readVars) (htgRr : tg ∉ Rb.readVars)
    (htgdom : tg ∉ dom.fv)
    (htgts : ∀ c ∈ ts, tg ∉ c.2.fv)
    {σ : State (Var n)}
    (hB : Formula.sat (Formula.box (Program.ode (DLCalTiming.clk tg fLb ++ Rb) dom) B)
      (Function.update σ tg 0))
    (hboxes : ∀ c ∈ ts, Formula.sat
      (Formula.box (Program.ode (fLb ++ Rb) dom) (invAt c.1 c.2)) σ) :
    Formula.sat (Formula.box (Program.ode (DLCalTiming.clk tg fLb ++ Rb) dom)
      (foldAt ts B)) (Function.update σ tg 0) := by
  induction ts with
  | nil => exact hB
  | cons c rest ih =>
      refine sat_box_and ?_ ?_
      · exact box_joint_to_clocked_F (invAt c.1 c.2) fLb Rb dom tg htgLb htgRb htgLr htgRr
          htgdom (notMem_invAt_fv (htgts c List.mem_cons_self))
          (hboxes c List.mem_cons_self)
      · exact ih (fun c' hc' => htgts c' (List.mem_cons_of_mem _ hc'))
          (fun c' hc' => hboxes c' (List.mem_cons_of_mem _ hc'))

/-- **`box_FM_clocked`, mask-selected**: the clocked box for `FMS`, folded from the
per-component boxes of the flagged atoms. -/
theorem box_FMS_clocked (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool)
    (fLb Rb : ODESystem (Var n)) (dom : Formula (Var n)) (tg : Var n)
    (htgLb : tg ∉ fLb.bound) (htgRb : tg ∉ Rb.bound)
    (htgLr : tg ∉ fLb.readVars) (htgRr : tg ∉ Rb.readVars)
    (htgdom : tg ∉ dom.fv)
    (htggs : ∀ g' ∈ g :: gs, tg ∉ g'.fv)
    {σ : State (Var n)}
    (hboxes : ∀ c ∈ tagS (g :: gs) m, Formula.sat
      (Formula.box (Program.ode (fLb ++ Rb) dom) (invAt c.1 c.2)) σ) :
    Formula.sat (Formula.box (Program.ode (DLCalTiming.clk tg fLb ++ Rb) dom)
      (FMS g gs m)) (Function.update σ tg 0) := by
  rw [tagS_cons] at hboxes
  refine box_foldAt_clocked (tagS gs m.tail) _ fLb Rb dom tg htgLb htgRb htgLr htgRr htgdom
    (fun c hc => htggs c.2 (List.mem_cons_of_mem _ (mem_tagS_snd hc))) ?_
    (fun c hc => hboxes c (List.mem_cons_of_mem _ hc))
  exact box_joint_to_clocked_F _ fLb Rb dom tg htgLb htgRb htgLr htgRr htgdom
    (notMem_invAt_fv (htggs g List.mem_cons_self)) (hboxes _ List.mem_cons_self)

/-! ## The mask-selected bounded coupling -/

/-- **`segment_faModalB_from_certB_list`, mask-selected**: the loop formula is `FMS g gs m`,
its clocked box folded from the per-component certificate boxes (strict components from
`BoxLt`, the rest from `BoxLe`). -/
theorem segment_faModalB_from_certB_listS (g : Term (Var n)) (gs : List (Term (Var n)))
    (m : List Bool) (fL fR : Fin n → Term (Var n))
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
    (hboxes : ∀ c ∈ tagS (g :: gs) m, Formula.sat (Formula.box
      (Program.ode (leftBlock fL ++ rightBlock fR lam)
        (Formula.and domL domR)) (invAt c.1 c.2)) σ)
    (hES : HExistSegB fL fR lam domL domR dt (Function.update σ tg 0)) :
    faModalB (Equiv.refl (Var n)) (Program.ode (clk tg (leftBlock fL)) domL)
      (Program.ode (rightBlock fR lam) domR) (FMS g gs m) tg dt
      (Function.update σ tg 0) := by
  have hrv := clk_readVars (leftBlock fL) tg
  have hbs := clk_boundSet (leftBlock fL) tg
  refine faModal_ODE_G'_bounded (Equiv.refl (Var n)) (clk tg (leftBlock fL))
    (rightBlock fR lam) domL domR (FMS g gs m) tg dt (Function.update σ tg 0)
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
    exact box_FMS_clocked g gs m (leftBlock fL) (rightBlock fR lam)
      (Formula.and domL domR) tg htgLb htgRb htgLr htgRr htgdom htggs hboxes
  · simp only [ODESystem.rename_refl, Formula.rename_refl]
    exact hExist_clocked_of_HExistSegB fL fR lam domL domR tg dt htgLb htgLr htgRb
      htgRr htgdL htgdR hES

/-! ## Theorem 3 at the mask-selected row -/

/-- **The list-invariant Theorem 3 assembly at a strict row**: `theorem3_faithful_multiF_LR`
at `F := FMS g gs m`, `ϕinv := canonInvMS g gs m`. -/
theorem theorem3_faithful_multiS_LR (G : SearchGraph (Var n)) (mv : Var n)
    (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool)
    (domL domR : Formula (Var n)) (leftProgs : List (Program (Var n)))
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInvF (FMS g gs m) (Formula.and domL domR) mv
        G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv))
        (phiInvF (FMS g gs m) (Formula.and domL domR) mv G.modes.length)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and (canonInvMS g gs m) (envLR domL domR))
            (mvValidR mv G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and (canonInvMS g gs m) (envLR domL domR))
            (mvValidR mv G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and (RFormula.and (canonInvMS g gs m) (envLR domL domR))
        (mvValidR mv G.modes.length))) :=
  theorem3_faithful_multiF_LR G mv (FMS g gs m) domL domR leftProgs (canonInvMS g gs m)
    (encode_canonInvMS g gs m) hd hstep hddF

/-- **Collapse**: with an all-false mask the strict statement is the existing one. -/
theorem theorem3_faithful_multiS_LR_collapse (G : SearchGraph (Var n)) (mv : Var n)
    (g : Term (Var n)) (gs : List (Term (Var n))) {m : List Bool} (hm : ∀ b ∈ m, b = false)
    (domL domR : Formula (Var n)) (leftProgs : List (Program (Var n))) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and (RFormula.and (canonInvMS g gs m) (envLR domL domR))
        (mvValidR mv G.modes.length))) ↔
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvValidR mv G.modes.length))) := by
  rw [canonInvMS_allFalse g gs hm]

end RelCertifier
