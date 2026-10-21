/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The clocked mode-keyed assembly (W3)

The mode-keyed chain of `ModeHandoff` (`theorem3_modeKeyed`, `hstepMode_GR`,
`hd_modeKeyed_G`, `hddF_modeKeyed_G`) over the CLOCKED right body
`rightAutomatonBodyC G mv tg dt` of `ClockedRight`: the right side owns the mode variable
`(Aux, a)` and the right clock `(Aux, d)`, the left side the left clock `(Aux, b)` and the
left mode variable `(Aux, c)`. Everything is additive; the unclocked chain is untouched.
-/
import RelCertifier.Proofs.Encoding.Theorem3General
import RelCertifier.Proofs.Encoding.ModeHandoff

set_option autoImplicit false

namespace RelCertifier

open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-- Two auxiliary coordinates on each side (`sides_disjoint3` with the right clock). -/
theorem sides_disjoint4 {S T : Set (Var n)} (a b c d : Fin n) (hba : b ≠ a) (hca : c ≠ a)
    (hbd : b ≠ d) (hcd : c ≠ d)
    (hS : S ⊆ ({((Side.Aux, b) : Var n), ((Side.Aux, c) : Var n)} : Set (Var n)) ∪ range Lv)
    (hT : T ⊆ ({((Side.Aux, a) : Var n), ((Side.Aux, d) : Var n)} : Set (Var n)) ∪ range Rv) :
    Disjoint S T := by
  rw [Set.disjoint_left]
  intro x hxS hxT
  rcases hS hxS with hx | ⟨i, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hT hxT with hx' | ⟨j, hj⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx with rfl | rfl <;> rcases hx' with hx' | hx'
      · exact hba (by simpa [Prod.ext_iff] using hx')
      · exact hbd (by simpa [Prod.ext_iff] using hx')
      · exact hca (by simpa [Prod.ext_iff] using hx')
      · exact hcd (by simpa [Prod.ext_iff] using hx')
    · rcases hx with rfl | rfl <;> exact absurd hj (by simp [Rv, Prod.ext_iff])
  · rcases hT hxT with hx' | ⟨j, hj⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with hx' | hx' <;> exact absurd hx' (by simp [Lv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- `hd_modeKeyed_G` over the clocked body. -/
theorem hd_modeKeyed_GC (A : LeftAut n) (G : SearchGraph (Var n)) (a b c d : Fin n)
    (hba : b ≠ a) (hca : c ≠ a) (hbd : b ≠ d) (hcd : c ≠ d) (dt : ℝ)
    (hwin : ∀ t < A.numModes, Program.vars (A.window t)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    Disjoint (Program.vars (leftAutomatonBody A ((Side.Aux, c) : Var n)))
      (Program.vars ((rightAutomatonBodyC G ((Side.Aux, a) : Var n) ((Side.Aux, d) : Var n)
        dt).rename (Equiv.refl (Var n)))) := by
  refine sides_disjoint4 a b c d hba hca hbd hcd ?_ ?_
  · refine vars_leftAutomatonBody_sub A _ _ ?_ ?_ ?_ hnext
    · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
    · intro t ht x hx
      rcases hwin t ht hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
    · intro t ht x hx
      exact Or.inr (hgrd t ht hx)
  · intro x hx
    rw [Program.rename_refl] at hx
    rcases vars_bodyCG_sub G _ _ _ hgR hRv hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

/-- `hddF_modeKeyed_G` over the clocked body. -/
theorem hddF_modeKeyed_GC (A : LeftAut n) (G : SearchGraph (Var n)) (a b c d : Fin n)
    (hba : b ≠ a) (hca : c ≠ a) (hbd : b ≠ d) (hcd : c ≠ d) (dt : ℝ)
    (ϕ : ℕ → RFormula (Var n)) (domL domR : Formula (Var n)) (BkR : RFormula (Var n))
    (hwin : ∀ t < A.numModes, Program.vars (A.window t)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hϕL : ∀ m < A.numModes, (ϕ m).varsL ⊆ range Lv)
    (hϕR : ∀ m < A.numModes, (ϕ m).varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv)
    (hBkL : BkR.varsL = ∅)
    (hBkR : BkR.varsR ⊆ {((Side.Aux, a) : Var n)} ∪ range Rv) :
    Disjoint (faShape (Program.star (leftAutomatonBody A ((Side.Aux, c) : Var n)))
        (Program.star (rightAutomatonBodyC G ((Side.Aux, a) : Var n) ((Side.Aux, d) : Var n) dt))
        (psiK ((Side.Aux, c) : Var n) ϕ A.numModes domL domR BkR)).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (leftAutomatonBody A ((Side.Aux, c) : Var n)))
        (Program.star (rightAutomatonBodyC G ((Side.Aux, a) : Var n) ((Side.Aux, d) : Var n) dt))
        (psiK ((Side.Aux, c) : Var n) ϕ A.numModes domL domR BkR)).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint4 a b c d hba hca hbd hcd ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_leftAutomatonBody_sub A _ _ ?_ ?_ ?_ hnext
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
      · intro t ht x hx
        rcases hwin t ht hx with hx | hx
        · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
        · exact Or.inr hx
      · intro t ht x hx
        exact Or.inr (hgrd t ht hx)
    · refine psiK_varsL_sub _ ϕ _ domL domR BkR _ ?_ ?_ ?_ ?_
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
      · intro m hm x hx; exact Or.inr (hϕL m hm hx)
      · intro x hx; exact Or.inr (hdomLv hx)
      · rw [hBkL]; exact Set.empty_subset _
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyCG_sub G _ _ _ hgR hRv hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr hv
    · refine psiK_varsR_sub _ ϕ _ domL domR BkR _ ?_ ?_ ?_
      · intro m hm x hx; exact Or.inr (hϕR m hm hx)
      · intro x hx; exact Or.inr (hdomRv hx)
      · intro x hx
        rcases hBkR hx with hx | hx
        · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
        · exact Or.inr hx

/-- The per-left-mode form of `Hmulti_regionGC` (for `hstepMode_GRC`). -/
theorem HMode_regionGC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (guard cuts : ℕ → Formula (Var n))
    (hGg : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
    (F env : Formula (Var n)) (P : Program (Var n))
    (hframeG : ∀ q, q < G.modes.length → ∀ σ ν, Program.sem P σ ν →
      Formula.sat (guard q) σ → Formula.sat (guard q) ν)
    (H : ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ → Formula.sat (guard q) σ → Formula.sat (cuts q) σ →
      GRespC G tg dt q P (fun qf => Formula.and (Formula.and F env) (cuts qf)) σ) :
    ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and F env) (regionG guard cuts q)) σ →
      GRespC G tg dt q P (fun qf => Formula.and (Formula.and F env) (regionG guard cuts qf)) σ := by
  intro q hq σ hmv hσ
  refine grespC_guard guard hGg (fun ν hν => hframeG q hq σ ν hν hσ.2.1) ?_
    (H q hq σ hmv hσ.1 hσ.2.1 hσ.2.2)
  intro q' μ hp hg
  exact ⟨hp.1, hg, hp.2⟩

/-- The per-left-mode clocked guarded step for the mode-keyed chain (`hstepMode_GR` over the
clocked body). -/
theorem hstepMode_GRC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv) (hregf : ∀ q', mv ∉ (regions q').fv)
    (hmvtg : mv ≠ tg)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframe : FramesMv P mv)
    (H : ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and F env) (regions q)) σ →
      GRespC G tg dt q P (fun qf => Formula.and (Formula.and F env) (regions qf)) σ) :
    ∀ σ, Formula.sat (Formula.and (Formula.and F env) (mvRegion mv regions G.modes.length)) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) P (Program.star (rightAutomatonBodyC G mv tg dt))
        (Formula.and (Formula.and F env) (mvRegion mv regions G.modes.length))) σ := by
  intro σ hσ
  obtain ⟨q, hq, hmvq, hreg⟩ := sat_mvRegion.mp hσ.2
  exact hstep_single_GRC G mv tg dt q F env regions P hF henv hregf hframe hq hmvtg hfresh hgf hlt
    hmvq (H q hq σ hmvq ⟨hσ.1, hreg⟩)

/-- `theorem3_modeKeyed` with the right body abstracted (the loop rule never looks inside
it); the clocked chain instantiates `Rb := rightAutomatonBodyC G mv tg dt`. -/
theorem theorem3_modeKeyed_gen (A : LeftAut n) (ul : Var n) (Rb : Program (Var n))
    (F : ℕ → Formula (Var n)) (ϕ : ℕ → RFormula (Var n))
    (domL domR : Formula (Var n)) (Bk : Formula (Var n)) (BkR : RFormula (Var n))
    (hψ : ∀ m, encode (Equiv.refl (Var n)) (ϕ m) = F m)
    (hB : encode (Equiv.refl (Var n)) BkR = Bk)
    (hd : Disjoint (Program.vars (leftAutomatonBody A ul))
        (Program.vars (Rb.rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInvK ul F A.numModes (Formula.and domL domR) Bk) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (leftAutomatonBody A ul)
        (Program.star Rb)
        (phiInvK ul F A.numModes (Formula.and domL domR) Bk)) σ)
    (hddF : Disjoint (faShape (Program.star (leftAutomatonBody A ul))
          (Program.star Rb)
          (psiK ul ϕ A.numModes domL domR BkR)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (leftAutomatonBody A ul))
          (Program.star Rb)
          (psiK ul ϕ A.numModes domL domR BkR)).varsR)) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody A ul) Rb
      (psiK ul ϕ A.numModes domL domR BkR)) := by
  set ψpost := psiK ul ϕ A.numModes domL domR BkR with hψpost
  set Lp := Program.star (leftAutomatonBody A ul)
  set Rp := Program.star Rb
  have hencψ : encode (Equiv.refl (Var n)) ψpost
      = phiInvK ul F A.numModes (Formula.and domL domR) Bk :=
    encode_psiK ul ϕ F A.numModes domL domR BkR Bk hψ hB
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
  have hInvν : Formula.sat (phiInvK ul F A.numModes (Formula.and domL domR) Bk) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_multi (leftAutomatonBody A ul) Rb ψpost ν bs hd
    (by rw [hencψ]; exact hInvν)
    (fun σ hσ => by rw [hencψ] at hσ ⊢; exact hstep σ hσ) hddF hbdg

end RelCertifier
