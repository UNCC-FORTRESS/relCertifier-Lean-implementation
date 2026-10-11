/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cover replay with a window-local middle-switch obligation

`ReplayEngine.replay_gresp` asks for the choreography's middle-of-window obligation
(`hmid`: every piece boundary switches into a joint node) for every window length, also when
the window has one piece and no piece boundary. A cover whose joint nodes are not closed under
the right's switches (a right mode that is only a reposition node of the window, but which the
right may be in when a one-piece window ends) answers one-piece windows with a final switch
into any enabled successor and has no middle switch at all. `replay_gresp_k` is the same
replay with `hmid` needed only when the window has a piece boundary (`0 < k`).

New leaf; no upstream edits (the bodies are `replay_pieces` / `replay_gresp` with `hmid`
threaded through the induction).
-/
import RelCertifier.Proofs.Encoding.ReplayEngine

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

section PieceK


variable (G : SearchGraph (Var n)) (M : ℕ → RMode (Var n)) (fR : ℕ → Fin n → Term (Var n))
  (domR : Formula (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n)
  (hgR : GuardsRight G)
  (hfL : ∀ i, (fL i).fv ⊆ range Lv)
  (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (lam : ℝ) (hlam : 0 < lam)
  (J : ℕ → Prop) (hfR : ∀ q, J q → ∀ i, (fR q i).fv ⊆ range Rv) (rank : ℕ → ℕ) (K : ℕ) (hrank : ∀ q, J q → rank q < K)
  (hmode : ∀ q, J q → G.modeAt q = some (M q))
  (hsys : ∀ q, J q → (M q).sys = rightBlock (fR q) (Term.const 1))
  (hdomM : ∀ q, J q → (M q).dom = domR)
  (A : ℕ → Formula (Var n))
  (hbox : ∀ q, J q → ∀ σ ω, Formula.sat (A q) σ →
    Program.sem (Program.ode (jointSys fL (fR q) (Term.const lam)) (Formula.and domL domR)) σ ω →
    Formula.sat (A q) ω)
  (hhand : ∀ q, J q → ∀ e ∈ G.edgesFrom q, ∀ y, Formula.sat (A q) y → SwitchLegal e y →
    Formula.sat (A e.tgt) y)

include hgR hfL hfR hdomL hdomR hlam hrank hmode hsys hdomM hbox hhand in
theorem replay_pieces_k (dt : ℝ) (Pre Efin : ℕ → State (Var n) → Prop)
    (hfin : HMove G M J rank Pre Efin)
    (hAfv : ∀ q, (A q).fv ⊆ range Lv ∪ range Rv)
    (htgL : ∀ i, tg ≠ Lv i) (ω₀ : State (Var n)) :
    ∀ (k : ℕ), (0 < k → HMove G M J rank Pre (fun q' μ => J q' ∧ Pre q' μ)) →
      ∀ (σ ν : State (Var n)),
      Program.sem (windowSeg (leftBlock fL) domL tg dt (k + 1)) σ ν →
      ∀ q, J q → ∀ ρ, Pre q ρ → Formula.sat (A q) (mergeLR ω₀ σ ρ) →
      RRespP G q (fun q' μ => Efin q' μ ∧ Formula.sat (A q') (mergeLR ω₀ ν μ) ∧
        ∀ i, μ (Lv i) = ρ (Lv i)) ρ := by
  intro k
  induction k with
  | zero =>
      intro _ σ ν hw q hq ρ hPre hA
      simp only [zero_add, windowSeg, List.replicate_one, bigSeq] at hw
      obtain ⟨mid, hseg, hrest⟩ := hw
      rw [sem_test] at hrest
      obtain ⟨rfl, -⟩ := hrest
      obtain ⟨r, ΦL, hL, hΦr, -⟩ := clockedSeg_sol hseg
      have hA0 : Formula.sat (A q) (mergeLR ω₀ (ΦL 0) ρ) := by
        refine (sat_of_agree (hAfv q) (y := mergeLR ω₀ σ ρ) (fun i => ?_) (fun i => ?_)).mpr hA
        · rw [mergeLR_L, mergeLR_L, hL.hΦ0, Function.update_of_ne (htgL i).symm]
        · rw [mergeLR_R, mergeLR_R]
      have h := replay_piece G M fR domR fL domL tg hgR hfL hdomL hdomR lam hlam J hfR rank K
        hrank hmode hsys hdomM A hbox hhand Pre Efin hfin hL ω₀ q hq 0 le_rfl hL.hr ρ hPre hA0
      rwa [hΦr] at h
  | succ k ih =>
      intro hmid σ ν hw q hq ρ hPre hA
      have hw' : Program.sem (bigSeq (clockedSeg (leftBlock fL) domL tg dt ::
          List.replicate (k + 1) (clockedSeg (leftBlock fL) domL tg dt))) σ ν := hw
      obtain ⟨mid, hseg, hrest⟩ := hw'
      obtain ⟨r, ΦL, hL, hΦr, -⟩ := clockedSeg_sol hseg
      have hA0 : Formula.sat (A q) (mergeLR ω₀ (ΦL 0) ρ) := by
        refine (sat_of_agree (hAfv q) (y := mergeLR ω₀ σ ρ) (fun i => ?_) (fun i => ?_)).mpr hA
        · rw [mergeLR_L, mergeLR_L, hL.hΦ0, Function.update_of_ne (htgL i).symm]
        · rw [mergeLR_R, mergeLR_R]
      have h1 := replay_piece G M fR domR fL domL tg hgR hfL hdomL hdomR lam hlam J hfR rank K
        hrank hmode hsys hdomM A hbox hhand Pre (fun q' μ => J q' ∧ Pre q' μ)
        (hmid (Nat.succ_pos k)) hL ω₀ q hq 0 le_rfl hL.hr ρ hPre hA0
      rw [hΦr] at h1
      refine rrespP_bind' h1 ?_
      rintro q' μ ⟨⟨hJ', hPre'⟩, hA', hμL⟩
      have hrest' : Program.sem (windowSeg (leftBlock fL) domL tg dt (k + 1)) mid ν := hrest
      refine rrespP_mono ?_ (ih (fun _ => hmid (Nat.succ_pos k)) mid ν hrest' q' hJ' μ hPre' hA')
      rintro q'' μ' ⟨hE, hA'', hμ'L⟩
      exact ⟨hE, hA'', fun i => (hμ'L i).trans (hμL i)⟩

end PieceK

theorem replay_gresp_k (G : SearchGraph (Var n)) (M : ℕ → RMode (Var n))
    (fR : ℕ → Fin n → Term (Var n)) (domR : Formula (Var n)) (fL : Fin n → Term (Var n))
    (domL gL : Formula (Var n)) (b : Fin n)
    (hgR : GuardsRight G) (hfL : ∀ i, (fL i).fv ⊆ range Lv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv) (hgL : gL.fv ⊆ range Lv)
    (lam : ℝ) (hlam : 0 < lam)
    (J D : ℕ → Prop) (hfR : ∀ q, J q ∨ D q → ∀ i, (fR q i).fv ⊆ range Rv) (rank rankD : ℕ → ℕ) (K : ℕ) (hrank : ∀ q, J q → rank q < K)
    (hmode : ∀ q, J q ∨ D q → G.modeAt q = some (M q))
    (hsys : ∀ q, J q ∨ D q → (M q).sys = rightBlock (fR q) (Term.const 1))
    (hdomM : ∀ q, J q ∨ D q → (M q).dom = domR)
    (A : ℕ → Formula (Var n)) (hAfv : ∀ q, (A q).fv ⊆ range Lv ∪ range Rv)
    (hbox : ∀ q, J q → ∀ σ ω, Formula.sat (A q) σ →
      Program.sem (Program.ode (jointSys fL (fR q) (Term.const lam)) (Formula.and domL domR))
        σ ω → Formula.sat (A q) ω)
    (hboxD : ∀ q, D q → ∀ σ ω, Formula.sat (A q) σ → Formula.sat gL σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (A q) ω)
    (hhand : ∀ q, J q ∨ D q → ∀ e ∈ G.edgesFrom q, ∀ y, Formula.sat (A q) y →
      SwitchLegal e y → Formula.sat (A e.tgt) y)
    (Pre PreD Efin : ℕ → State (Var n) → Prop)
    (hPreR : ∀ q x y, (∀ i, x (Rv i) = y (Rv i)) → Pre q x → Pre q y)
    (hPreDR : ∀ q x y, (∀ i, x (Rv i) = y (Rv i)) → PreD q x → PreD q y)
    (hfin : HMove G M J rank Pre Efin)
    (hexit : HExit G M J D rankD Pre PreD)
    (dt : ℝ) (k : ℕ)
    (hmid : 0 < k → HMove G M J rank Pre (fun q' μ => J q' ∧ Pre q' μ)) (q : ℕ) (σ : State (Var n))
    (hstart : Formula.sat gL σ →
      ((J q ∧ Pre q σ) ∨ (D q ∧ ¬ J q ∧ PreD q σ)) ∧ Formula.sat (A q) σ)
    (hσL : Formula.sat domL σ)
    (post : ℕ → Formula (Var n))
    (hpost : ∀ ν, Program.sem (windowSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) dt (k+1)) σ ν →
      ∀ q' μ, (∀ i, μ (Lv i) = ν (Lv i)) → Efin q' μ →
        Formula.sat (A q') (mergeLR σ ν μ) → Formula.sat (post q') μ) :
    GResp G q (gwindowSeg gL (leftBlock fL) domL ((Side.Aux, b) : Var n) dt (k+1)) post σ := by
  refine gresp_gate (fun hg => gresp_of_rresp (fun ν hwin => ?_))
  obtain ⟨hcase, hAσ⟩ := hstart hg
  set tg : Var n := ((Side.Aux, b) : Var n)
  have hP := vars_windowSegL_sub fL domL b dt (k+1) hfL hdomL
  have hR : ∀ i, ν (Rv i) = σ (Rv i) := by
    intro i
    refine (Program.bound_effect _ hwin (Rv i) ?_).symm
    intro hb
    rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
    · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
  have hA0 : Formula.sat (A q) (mergeLR σ σ ν) := by
    refine (sat_of_agree (hAfv q) (y := σ) (fun i => ?_) (fun i => ?_)).mpr hAσ
    · rw [mergeLR_L]
    · rw [mergeLR_R, hR i]
  have hcase' : (J q ∧ Pre q ν) ∨ (D q ∧ ¬ J q ∧ PreD q ν) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, hPreR q σ ν (fun i => (hR i).symm) h2⟩
    · exact Or.inr ⟨h1, h2, hPreDR q σ ν (fun i => (hR i).symm) h3⟩
  have hrepo := replay_repo G M fR domR domL gL hgR hdomL hdomR hgL J D
    (fun q hq => hfR q (Or.inr hq)) rankD
    (fun q hq => hmode q (Or.inr hq)) (fun q hq => hsys q (Or.inr hq))
    (fun q hq => hdomM q (Or.inr hq)) A hboxD (fun q hq => hhand q (Or.inr hq)) Pre PreD hexit
    σ σ hg hσL q ν hcase' hA0
  have htgL : ∀ i, tg ≠ Lv i := fun i h => by simp [tg, Lv, Prod.ext_iff] at h
  refine rresp_of_rrespP (rrespP_bind' hrepo ?_)
  rintro q' μ ⟨hJ', hPre', hA', hμL⟩
  have hpieces := replay_pieces_k G M fR domR fL domL tg hgR hfL hdomL hdomR lam hlam J
    (fun q hq => hfR q (Or.inl hq)) rank K
    hrank (fun q hq => hmode q (Or.inl hq)) (fun q hq => hsys q (Or.inl hq))
    (fun q hq => hdomM q (Or.inl hq)) A hbox (fun q hq => hhand q (Or.inl hq)) dt Pre Efin
    hfin hAfv htgL σ k hmid σ ν hwin q' hJ' μ hPre' hA'
  refine rrespP_mono ?_ hpieces
  rintro q'' μ' ⟨hE, hA'', hμ'L⟩
  exact hpost ν hwin q'' μ' (fun i => (hμ'L i).trans (hμL i)) hE hA''

end RelCertifier
