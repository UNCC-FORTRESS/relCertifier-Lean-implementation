/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Theorem 3, generically, at a strict row (extension `strict-atoms`)

`theorem3_of_coverX` with the declared row read through its strictness mask: the loop
formula is `FMS g gs msk` (strict components `< 0`) and the relational row `canonInvMS`.
The proof is the existing one: the row enters only through its free variables
(`notMem_FMS_fv`), its encoding (`encode_canonInvMS`) and its projections
(`canonInvMS_varsL/R`); preservation is carried by the anchor `A` of the cover hypotheses,
which for a strict row must carry `FMS` (`hAstart`, `hApost`). With an all-false mask the
statement is the existing one (`theorem3_of_coverXS_collapse`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.Theorem3General
import RelCertifier.Proofs.Encoding.StrictInv

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

section AssemblyS

variable (Gr : SearchGraph (Var n)) (a b d : Fin n) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
  (dt : ℝ)
  (g : Term (Var n)) (gs : List (Term (Var n))) (msk : List Bool)
  (comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv)
  (domL domR : Formula (Var n)) (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (guard cuts : ℕ → Formula (Var n))
  (hguards : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = guard e.tgt)
  (hgR : GuardsRight Gr) (hguardR : ∀ q, (guard q).fv ⊆ range Rv)
  (hcutsR : ∀ q, (cuts q).fv ⊆ range Rv)
  (fR : ℕ → Fin n → Term (Var n))
  (hfR : ∀ q, q < Gr.modes.length → ∀ i, (fR q i).fv ⊆ range Rv)
  (hsys : ∀ q m, Gr.modeAt q = some m → m.sys = rightBlock (fR q) (Term.const 1))
  (hdomM : ∀ q m, Gr.modeAt q = some m → m.dom = domR)
  (hweight : ∀ q m, Gr.modeAt q = some m → m.weight = 1)
  (hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length)
  (L : ℕ) (gL : ℕ → Formula (Var n)) (fL : ℕ → Fin n → Term (Var n))
  (hgLv : ∀ l, l < L → (gL l).fv ⊆ range Lv) (hfL : ∀ l, l < L → ∀ i, (fL l i).fv ⊆ range Lv)
  (epsR : ℝ) (reg : Formula (Var n)) (hregR : reg.fv ⊆ range Rv)
  (hwf : WellFormedRIn Gr guard reg epsR)
  (ch : ℕ → ChoiceData) (B : ℕ → ℕ) (δ : ℕ → ℝ) (lam : ℕ → ℕ → ℝ)
  (A : ℕ → ℕ → Formula (Var n))
  (hAreg : ∀ l, l < L → ∀ q y, Formula.sat (A l q) y → Formula.sat reg y)
  (RJ : ℕ → ℕ → Formula (Var n))
  (RR RS : ℕ → ℕ → SrcSetting → Formula (Var n))
  (H : ∀ l, l < L → CoverHyps Gr (ch l) fR domR (fL l) domL (gL l) guard ((Side.Aux, d) : Var n)
    epsR (δ l) (lam l) (A l) (RJ l) (RR l) (RS l))
  (hdt : ∀ l, l < L → dt ≤ (B l : ℝ) * δ l)
  (hcov : ∀ l, l < L → ∀ q, q < Gr.modes.length →
    AdmissibleStart (gL l) (FMS g gs msk) (Formula.and domL domR) (guard q) (cuts q) →
    CoveredX Gr (ch l) ⟨q, B l, SrcSetting.preJ⟩)
  (hAstart : ∀ l, l < L → ∀ q σ, Formula.sat (gL l) σ →
    Formula.sat (Formula.and (FMS g gs msk) (Formula.and domL domR)) σ →
    Formula.sat (guard q) σ → Formula.sat (cuts q) σ → Formula.sat (A l q) σ)
  (hApost : ∀ l, l < L → ∀ q' y, Formula.sat (A l q') y →
    Formula.sat (Formula.and (Formula.and (FMS g gs msk) (Formula.and domL domR)) (cuts q')) y)

include hgR hguards hguardR hcutsR hfR hsys hdomM hweight hgLv hfL hdomL hdomR hregR hAreg hwf H hdt hcov
  hAstart hApost comps_fv in
/-- **Every window answered from its cover**, at a strict row (`Hmulti_of_coverX` with
`FMS g gs msk`). -/
theorem Hmulti_of_coverXS :
    ∀ P ∈ leftProgsOf b dt domL L gL fL, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ,
      σ ((Side.Aux, a) : Var n) = (q : ℝ) →
      Formula.sat (Formula.and (FMS g gs msk) (Formula.and domL domR)) σ →
      Formula.sat (guard q) σ → Formula.sat (cuts q) σ →
      GRespC Gr ((Side.Aux, d) : Var n) epsR q P
        (fun qf => Formula.and (Formula.and (FMS g gs msk) (Formula.and domL domR)) (cuts qf)) σ := by
  intro P hP q hq σ _ hσ hg hc
  simp only [leftProgsOf, leftDataOf, List.map_map, List.mem_map, List.mem_range] at hP
  obtain ⟨l, hl, rfl⟩ := hP
  simp only [Function.comp]
  have Hl := H l hl
  refine coverX_gresp Gr (ch l) fR domR (fL l) domL (gL l) b guard ((Side.Aux, d) : Var n)
    (aux_notin_range_Lv d) (aux_notin_range_Rv d) hgR hguards hguardR (hfL l hl)
    hdomL hdomR (hgLv l hl) hfR hsys hdomM hweight epsR (δ l) Hl.hδ (lam l) Hl.hlam Hl.hspan (A l)
    Hl.hAfv Hl.hAdom Hl.hbox Hl.hhand reg hregR (hAreg l hl) hwf Hl.hprune
    Hl.hrepoProg (RJ l) Hl.hRJ Hl.hcovJ (RR l) Hl.hRR Hl.hcovR (RS l) Hl.hRS Hl.hcovS dt (B l)
    (hdt l hl) q σ hg (fun hgate => hcov l hl q hq ⟨σ, hgate, hσ, hg, hc⟩)
    (fun hgate => hAstart l hl q σ hgate hσ hg hc) _ ?_
  intro ν _ q' μ hμL hgq' hAq'
  have hpostm := hApost l hl q' _ hAq'
  have hfv : (Formula.and (Formula.and (FMS g gs msk) (Formula.and domL domR)) (cuts q')).fv ⊆
      range Lv ∪ range Rv := by
    intro v hv
    rcases hv with (hv | hv | hv) | hv
    · by_contra hcon
      exact notMem_FMS_fv (fun g' hg' hx => hcon (comps_fv g' hg' hx)) hv
    · exact Or.inl (hdomL hv)
    · exact Or.inr (hdomR hv)
    · exact Or.inr (hcutsR q' hv)
  refine (sat_of_agree hfv (y := μ) (fun i => ?_) (fun i => ?_)).mp hpostm
  · rw [mergeLR_L, hμL i]
  · rw [mergeLR_R]

include hab had hbd hgR hguards hguardR hcutsR hfR hsys hdomM hweight hlt hgLv hfL hdomL hdomR hregR hAreg
  hwf H hdt hcov hAstart hApost comps_fv in
/-- **Theorem 3 at a strict row** (`theorem3_of_coverX` with the loop formula `FMS g gs msk`:
strict components `< 0`). The ∀∃ relational
invariance of the declared row with the evolve envelope and the right mode's region, over the
guard-gated left windows and the CLOCKED guarded right automaton (right clock `(Aux, d)`,
cap `ε_R`), from: Assumption 1 (`hwf`), a cover of every admissible start of every window
(`hcov`), and the certificates each cover consumes (`H`).
-/
theorem theorem3_of_coverXS :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsOf b dt domL L gL fL))
      (rightAutomatonBodyC Gr ((Side.Aux, a) : Var n) ((Side.Aux, d) : Var n) epsR)
      (RFormula.and (RFormula.and (canonInvMS g gs msk) (envLR domL domR))
        (mvRegionR ((Side.Aux, a) : Var n) (regionG guard cuts) Gr.modes.length))) := by
  set mv : Var n := ((Side.Aux, a) : Var n) with hmv
  set tr : Var n := ((Side.Aux, d) : Var n) with htr
  have hmvtr : mv ≠ tr := by simp [hmv, htr, Prod.ext_iff, had]
  have hmvF : mv ∉ (FMS g gs msk).fv := notMem_FMS_fv (fun g' hg' hx => by
    rcases comps_fv g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact aux_ne_Lv a i hi.symm
    · exact aux_ne_Rv a i hi.symm)
  have hmvenv : mv ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv a (hdomL h)
    · exact aux_notin_range_Rv a (hdomR h)
  have hmvreg : ∀ q, mv ∉ (regionG guard cuts q).fv := fun q =>
    notMem_regionG_fv (fun h => aux_notin_range_Rv a (hguardR q h))
      (fun h => aux_notin_range_Rv a (hcutsR q h))
  have hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
    intro q m hm y hy
    rw [hsys q m hm, hdomM q m hm] at hy
    rcases hy with (hy | hy) | hy
    · exact rightBlock_boundSet_sub (fR q) (Term.const 1) hy
    · exact rightBlock_readVars_sub (fR q) (Term.const 1) (hfR q (modeAt_lt hm)) (by simp [Term.fv]) hy
    · exact hdomR hy
  have hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
    intro q m hm hmv'
    exact aux_notin_range_Rv a (hRv q m hm (vars_ode_sub _ _ (Or.inl hmv')))
  have hL := hL_of domL L gL fL hgLv hfL hdomL
  have hframes : ∀ P ∈ leftProgsOf b dt domL L gL fL, FramesMv P mv := by
    intro P hP
    simp only [leftProgsOf, List.mem_map] at hP
    obtain ⟨d, hd, rfl⟩ := hP
    refine framesMv_gwindow d.1 d.2.1 d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2 mv
      (by simp [hmv, Prod.ext_iff, hab]) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
    exact aux_ne_Lv a i hi
  refine theorem3_faithful_multiR_LR_gen Gr mv (rightAutomatonBodyC Gr mv tr epsR) (FMS g gs msk)
    domL domR (regionG guard cuts) (leftProgsOf b dt domL L gL fL) (canonInvMS g gs msk)
    (encode_canonInvMS g gs msk) ?_ ?_ ?_
  · refine sides_disjoint a b d hab.symm hbd ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgsOf, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 b dt d.2.2.2 (hL d hd).1
        (hL d hd).2.1 (hL d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyCG_sub Gr mv tr epsR hgR hRv hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
  · exact hstep_assembled_GRC Gr mv tr epsR (FMS g gs msk) (Formula.and domL domR)
      (regionG guard cuts) (leftProgsOf b dt domL L gL fL) hmvF hmvenv hmvreg hmvtr hfresh
      (guardsFresh_of_right Gr a hgR) hlt hframes
      (Hmulti_regionGC Gr mv tr epsR guard cuts hguards (FMS g gs msk) (Formula.and domL domR)
        (leftProgsOf b dt domL L gL fL)
        (fun P hP q _ σ ν hrun => by
          simp only [leftProgsOf, List.mem_map] at hP
          obtain ⟨d, hd, rfl⟩ := hP
          exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 b dt d.2.2.2 (hL d hd).1
            (hL d hd).2.1 (hL d hd).2.2) (hguardR q) hrun)
        (Hmulti_of_coverXS Gr a b d dt g gs msk comps_fv domL domR hdomL hdomR guard cuts hguards
          hgR hguardR hcutsR fR hfR hsys hdomM hweight L gL fL hgLv hfL epsR reg hregR hwf ch B δ
          lam A hAreg RJ RR RS H hdt hcov hAstart hApost))
  · exact hddF_multiR_GC Gr a b d dt epsR (leftDataOf domL L gL fL) (regionG guard cuts)
      (canonInvMS g gs msk) domL domR hab hbd hgR hRv hL
      (fun q _ => regionG_fv_sub (hguardR q) (hcutsR q))
      (canonInvMS_varsL g gs msk comps_fv) (canonInvMS_varsR g gs msk) hdomL hdomR

end AssemblyS

/-- **Collapse**: with an all-false mask the strict Theorem 3 statement is the existing one. -/
theorem theorem3_of_coverXS_collapse (L : List (Program (Var n))) (Gr : SearchGraph (Var n))
    (mv tr : Var n) (epsR : ℝ) (g : Term (Var n)) (gs : List (Term (Var n))) {msk : List Bool}
    (hm : ∀ b ∈ msk, b = false) (domL domR : Formula (Var n)) (R : RFormula (Var n)) :
    RFormula.rvalid (theorem3Form (bigChoice L) (rightAutomatonBodyC Gr mv tr epsR)
      (RFormula.and (RFormula.and (canonInvMS g gs msk) (envLR domL domR)) R)) ↔
    RFormula.rvalid (theorem3Form (bigChoice L) (rightAutomatonBodyC Gr mv tr epsR)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR)) R)) := by
  rw [canonInvMS_allFalse g gs hm]

end RelCertifier
