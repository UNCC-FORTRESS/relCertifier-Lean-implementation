/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L2 × L6 — the right-only prefixed k-piece window over a list invariant

The k > 1 multi-component benchmarks (9 of the 21 budget>1 set) compose the L2
assembly (`Hmulti_windowR_prefixed`, right-only hops) with the L6 loop formula
(`FM g gs`). This file is the composition mirror: the same proof with the opaque
loop formula `F` in place of `invLe g` — every ingredient (`multiseg_clocked`,
`faModalB_repoPathR`, `hdisH_progR`, the fold/flatten lemmas) is already
φ-parametric.

New leaf (imports `RepoPrefixR` + `EnvelopeChainM`); no upstream edits.
-/
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.EnvelopeChainM

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- **The right-only prefixed k-piece window, list-invariant form.** -/
theorem Hmulti_windowRF_prefixed (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (F env : Formula (Var n)) (a : Fin n) (dt : ℝ) (k : ℕ)
    (htgF : ((Side.Aux, a) : Var n) ∉ F.fv) (htgenv : ((Side.Aux, a) : Var n) ∉ env.fv)
    (hops : List (RepoHop n))
    (hhops : ∀ h ∈ hops, (∀ i, (h.fR i).fv ⊆ range Rv) ∧ h.lam.fv ⊆ range Rv
      ∧ h.domR.fv ⊆ range Rv)
    (hφL : ∀ σ, Formula.sat (Formula.and F env) σ → Formula.sat domL σ)
    (hR : ∀ h ∈ hops, ∀ σ, Formula.sat (Formula.and F env) σ →
      σ ((Side.Aux, a) : Var n) = 0 →
      ∃ ρ, Program.sem h.progR σ ρ ∧ Formula.sat (Formula.and F env) ρ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (pieces : List (Program (Var n))) (hklen : pieces.length = k) (hk : 0 < k)
    (hdisP : ∀ Q ∈ pieces, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)))
    (hcouple : ∀ Q ∈ pieces, ∀ σ, Formula.sat (Formula.and F env) σ →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q (Formula.and F env) ((Side.Aux, a) : Var n) dt
        (Function.update σ ((Side.Aux, a) : Var n) 0))
    {σ : State (Var n)} (hσ : Formula.sat (Formula.and F env) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (windowSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt k)
      (bigSeq ((hops.map (fun h => h.progR)) ++ pieces))
      (Formula.and F env)) σ := by
  set φ := Formula.and F env with hφdef
  have htgφ : ((Side.Aux, a) : Var n) ∉ φ.fv := by
    intro h
    rcases h with h | h
    · exact htgF h
    · exact htgenv h
  obtain ⟨p₁, rest, rfl⟩ : ∃ p₁ rest, pieces = p₁ :: rest := by
    cases pieces with
    | nil => exact absurd hklen (by simp; omega)
    | cons p₁ rest => exact ⟨p₁, rest, rfl⟩
  set folded := hops.foldr (fun h q => Program.seq h.progR q) p₁ with hfolded
  have hfoldvars : ∀ x ∈ Program.vars folded,
      x ∈ Program.vars p₁ ∨ ∃ h ∈ hops, x ∈ Program.vars h.progR := by
    rw [hfolded, foldr_progR_map]
    intro x hx
    rcases vars_foldr_seq_sub _ _ x hx with hx | ⟨hp, hhp, hx⟩
    · exact Or.inl hx
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hhp
      exact Or.inr ⟨h, hh, hx⟩
  have hm := multiseg_clocked φ (leftBlock fL) domL ((Side.Aux, a) : Var n) dt
    (folded :: rest)
    (by
      intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQr
      · rw [Set.disjoint_left]
        intro x hxQ hxW
        rw [Program.rename_refl] at hxQ
        rcases hfoldvars x hxQ with hx | ⟨h, hh, hx⟩
        · exact absurd hxW (Set.disjoint_left.mp (hdisP p₁ List.mem_cons_self)
            (by rwa [Program.rename_refl]))
        · obtain ⟨hhfR, hhlam, hhdomR⟩ := hhops h hh
          exact absurd hxW (Set.disjoint_left.mp
            (hdisH_progR h hhfR hhlam hhdomR hfL hdomL) hx)
      · exact hdisP Q (List.mem_cons_of_mem _ hQr))
    (by
      intro Q hQ σ' hσ'
      rcases List.mem_cons.mp hQ with rfl | hQr
      · have hupdφ : Formula.sat φ (Function.update σ' ((Side.Aux, a) : Var n) 0) := by
          rwa [(Formula.coincidence φ (fun v hv =>
            Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv)) _ _) :
              Formula.sat φ _ ↔ Formula.sat φ σ')]
        have hupdtg : (Function.update σ' ((Side.Aux, a) : Var n) 0)
            ((Side.Aux, a) : Var n) = 0 := Function.update_self _ _ _
        refine faModalB_repoPathR hfL hdomL hφL hops hhops hR
          (fun τ hτ hτtg => ?_) (Function.update σ' ((Side.Aux, a) : Var n) 0)
          hupdφ hupdtg
        have hupdτ : Function.update τ ((Side.Aux, a) : Var n) 0 = τ := by
          funext x
          by_cases hx : x = ((Side.Aux, a) : Var n)
          · subst hx; rw [Function.update_self, hτtg]
          · rw [Function.update_of_ne hx]
        have := hcouple p₁ List.mem_cons_self τ hτ
        rwa [hupdτ] at this
      · exact hcouple Q (List.mem_cons_of_mem _ hQr) σ' hσ')
    σ hσ
  have hlen : (folded :: rest).length = k := by simpa using hklen
  have hleft : (folded :: rest).map
      (fun _ => clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)
      = List.replicate k (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt) := by
    rw [List.map_const', hlen]
  rw [hleft] at hm
  have hfold_eq : folded = (hops.map (fun h => h.progR)).foldr
      (fun h q => Program.seq h q) p₁ := by
    rw [hfolded, foldr_progR_map]
  have hflat := sem_bigSeq_fold_head (hops.map (fun h => h.progR)) p₁ rest
  refine sat_faModal_congrR (fun ν μ => ?_) hm
  rw [hfold_eq]
  exact hflat ν μ

end RelCertifier
