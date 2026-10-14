/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Pointwise coupling: the segment-existence premise at the start state only

`couple_cutX` asks for right-segment existence at EVERY anchor state, but uses it only at the
start state. `couple_cutX_at` is the same proof with the premise at the start state, so an
instance may discharge existence from facts that hold there and are not invariant (a right
guard and the control period, for a constant field). `window_of_faModalB` turns the coupling
at the reset state into the one-window response.
-/
import RelCertifier.Proofs.Encoding.CutRespond

namespace RelCertifier

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-- `couple_cutX` with the existence premise at the start state `σ` only (same proof). -/
theorem couple_cutX_at (g : Term (Var n)) (gs comps : List (Term (Var n)))
    (cL cR : List (CutAtomP n)) (fL fR : Fin n → Term (Var n)) (lamv : ℝ) (hlam : 0 < lamv)
    (domL domR : Formula (Var n)) (b : Fin n) (dt : ℝ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    (hcompsLR : ∀ g' ∈ g :: gs ++ atomTerms cL cR, g'.fv ⊆ range Lv ∪ range Rv)
    (hsub1 : ∀ c ∈ comps, c ∈ g :: gs) (hsub2 : ∀ g' ∈ g :: gs, g' ∈ comps)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR)
    (hstayL : AtomsStayC cL (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hstayR : AtomsStayC cR (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hverd : VerdXCore comps fL fR lamv (domCutX (Formula.and domL domR) cL cR))
    {σ : State (Var n)} (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms cL cR))
        (Formula.and domL domR)) σ)
    (hESσ : HExistSegB fL fR (Term.const lamv) domL domR dt
        (Function.update σ ((Side.Aux, b) : Var n) 0)) :
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, b) : Var n) (leftBlock fL)) domL)
        (Program.ode (rightBlock fR (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms cL cR)) (Formula.and domL domR))
        ((Side.Aux, b) : Var n) dt (Function.update σ ((Side.Aux, b) : Var n) 0) := by
  set tg : Var n := ((Side.Aux, b) : Var n) with htgdef
  set A := FM g (gs ++ atomTerms cL cR) with hA
  have htgA : tg ∉ (Formula.and A (Formula.and domL domR)).fv := by
    intro h
    rcases h with h | h | h
    · exact notMem_FM_fv (fun g' hg' hx => by
        rcases hcompsLR g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
        · exact aux_ne_Lv b i hi.symm
        · exact aux_ne_Rv b i hi.symm) h
    · exact aux_notin_range_Lv b (hdomL h)
    · exact aux_notin_range_Rv b (hdomR h)
  set σ' := Function.update σ tg 0 with hσ'def
  have hσ' : Formula.sat (Formula.and A (Formula.and domL domR)) σ' := by
    rwa [(Formula.coincidence (Formula.and A (Formula.and domL domR)) (fun v hv =>
      Function.update_of_ne (fun hc => htgA (by rw [← hc]; exact hv)) _ _) :
        Formula.sat (Formula.and A (Formula.and domL domR)) _ ↔ _)]
  -- the narrowed preservation, lifted to the bare domain
  have hnarrow : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (domCutX (Formula.and domL domR) cL cR) :=
    segPresAll_from_strata_verdicts' fL fR (Term.const lamv) _ comps hverd
  have hnarrow' : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (Formula.and (Formula.and domL domR) (Formula.and (cutF cL) (cutF cR))) := by
    refine segPresAll_congr (fun x => ?_) hnarrow
    rw [sat_domCutX]
    simp only [Formula.sat, sat_cutF]
  have hlift := segPresAll_cut_liftX hiffL hiffR hstayL hstayR hnarrow'
  obtain ⟨hFσ, hatσ⟩ := (sat_FM_append g gs _ σ').mp hσ'.1
  obtain ⟨hLσ, hRσ⟩ := (atomTerms_iff hiffL hiffR σ').mp hatσ
  have hcompsσ : ∀ c ∈ comps, Term.eval c σ' ≤ 0 :=
    fun c hc => (sat_FM_iff g gs σ').mp hFσ c (hsub1 c hc)
  have hboxes : ∀ g' ∈ g :: (gs ++ atomTerms cL cR), Formula.sat (Formula.box
      (Program.ode (leftBlock fL ++ rightBlock fR (Term.const lamv))
        (Formula.and domL domR)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    rw [← jointSys_split] at hω
    obtain ⟨hcω, hLω, hRω⟩ := hlift σ' hLσ hRσ hcompsσ ω hω
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hcω _ (hsub2 _ List.mem_cons_self)
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact hcω _ (hsub2 _ (List.mem_cons_of_mem _ hg'))
      · exact (atomTerms_iff hiffL hiffR ω).mpr ⟨hLω, hRω⟩ g' hg'
  have hbase := segment_faModalB_from_certB_list g (gs ++ atomTerms cL cR) fL fR
    (Term.const lamv) domL domR tg dt
    (LR_blocks_disjoint _ _ _ hfL hfR (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomL hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomR hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
      exact aux_ne_Lv b i hi)
    (fun h => aux_notin_range_Lv b (leftBlock_readVars_sub fL hfL h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub fR (Term.const lamv) _ h
      exact aux_ne_Rv b i hi)
    (fun h => aux_notin_range_Rv b (rightBlock_readVars_sub fR
      (Term.const lamv) hfR (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv b (rightBlock_boundSet_sub fR (Term.const lamv) h))
    (fun h => aux_notin_range_Lv b (hdomL h))
    (fun h => aux_notin_range_Rv b (hdomR h))
    (fun g' hg' hx => by
      rcases hcompsLR g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact aux_ne_Lv b i hi.symm
      · exact aux_ne_Rv b i hi.symm)
    hboxes (by
      have := hESσ
      rwa [show Function.update σ' tg 0 = σ' from by
        rw [hσ'def, Function.update_idem]] at *)
  have hupd : Function.update σ' tg (0 : ℝ) = σ' := by
    rw [hσ'def, Function.update_idem]
  rw [hupd] at hbase
  have hstr : faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
      (Program.ode (rightBlock fR (Term.const lamv)) domR)
      (Formula.and A (Formula.and domL domR)) tg dt σ' := by
    refine faModalB_strengthen_plant ?_ hbase
    intro ν μ hplant hsem
    have hdomLν : Formula.sat domL ν := sem_ode_ends_in_domain hplant.1
    have hdomRμ : Formula.sat domR μ := sem_ode_ends_in_domain hsem
    have hdomLμ : Formula.sat domL μ := by
      rwa [(Formula.coincidence domL (fun v hv' => sem_ode_mask hsem (by
        obtain ⟨i, rfl⟩ := hdomL hv'
        intro hb
        obtain ⟨j, hj⟩ := rightBlock_bound_sub fR (Term.const lamv) _ hb
        exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
          Formula.sat domL μ ↔ Formula.sat domL ν)]
    exact ⟨hdomLμ, hdomRμ⟩
  refine faModalB_monoQ ?_ hstr
  intro ν μ hsem
  exact sem_rightBlock_reparam lamv 1 hlam one_pos hsem

/-- **One window from the reset-state coupling.** A one-segment window of the left against one
right program `Q`, from the coupling at `σ[tg ↦ 0]`. -/
theorem window_of_faModalB (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (Q : Program (Var n)) (φ : Formula (Var n)) (tg : Var n) (dt : ℝ) {σ : State (Var n)}
    (h : faModalB (Equiv.refl (Var n)) (Program.ode (clk tg leftSys) domL) Q φ tg dt
      (Function.update σ tg 0)) :
    Formula.sat (faModal (Equiv.refl (Var n)) (windowSeg leftSys domL tg dt 1) (bigSeq [Q]) φ)
      σ := by
  have hc := (faModalB_clockedSeg_iff leftSys domL Q φ tg dt σ).mpr h
  rw [faModal_sat] at hc ⊢
  intro ν hν
  obtain ⟨κ, h1, h2⟩ := hν
  obtain ⟨rfl, -⟩ := h2
  obtain ⟨μ, hμ, hφ⟩ := hc κ h1
  rw [Program.rename_refl] at hμ ⊢
  exact ⟨μ, ⟨μ, hμ, rfl, trivial⟩, hφ⟩

end RelCertifier
