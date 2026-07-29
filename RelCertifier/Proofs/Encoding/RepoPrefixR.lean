/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L2 — right-only reposition hops (the k > 1 window unblock)

`Hmulti_window_prefixed`'s `hdisH` is UNSATISFIABLE for nonempty hop lists: the
frozen-left hop program (`RepoHop.prog`) binds every left coordinate (derivative 0)
and conjoins `domL` into its domain, so its variables always meet the clocked left
segment's (the recorded S1 negative finding). The fix is a SHAPE change: state the
hop as the mode's own right-block program (`RepoHop.progR`) — right-only on both the
field and the domain, exactly the shape the final response already uses and for which
the identical disjointness discharges in `emitWindows_self`.

No re-proof of the S1 core: a right-only hop run CONVERTS to the frozen-left joint
form (the response anchors carry the envelope, so `domL` holds at the anchor and the
right-only run keeps the left coordinates fixed — `hop_run_toJoint`), the existing
`faModalB_repoPrefix` fires, and the response transports back along the diamond's
covariance (`faModalB_monoQ` + `sem_ode_dom_and_right` + `sem_rightBlock_frozen_iff`).

`Hmulti_windowR_prefixed` is the k-piece window with right-only hops; its hop
disjointness is DERIVED from the side-split data (`hdisH_progR`), not assumed.

New leaf (imports `EnvelopeChain`); no upstream edits, no battery rebuild.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- The hop's RIGHT-ONLY program: the mode's own right block over its own domain. -/
def RepoHop.progR (h : RepoHop n) : Program (Var n) :=
  Program.ode (rightBlock h.fR h.lam) h.domR

/-- `faModalB` is covariant in the response program (the diamond side). -/
theorem faModalB_monoQ {P Q Q' : Program (Var n)} {φ : Formula (Var n)}
    {tg : Var n} {dt : ℝ} {ω : State (Var n)}
    (h : ∀ ν μ, Program.sem Q ν μ → Program.sem Q' ν μ)
    (hb : faModalB (Equiv.refl (Var n)) P Q φ tg dt ω) :
    faModalB (Equiv.refl (Var n)) P Q' φ tg dt ω := by
  intro ν hplant
  obtain ⟨μ, hsem, hφ⟩ := hb ν hplant
  rw [Program.rename_refl] at hsem ⊢
  exact ⟨μ, h ν μ hsem, hφ⟩

/-- A right-only hop run at a `domL`-anchor is a frozen-left joint run: the right
block binds no left coordinate, so `domL` (left-variable-only) holds along the run by
coincidence with the anchor, and `sem_rightBlock_frozen_iff` converts. -/
theorem hop_run_toJoint {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {ω₀ ρ₁ : State (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv)
    (hdomLω : Formula.sat domL ω₀)
    (hrun : Program.sem (Program.ode (rightBlock fR lam) domR) ω₀ ρ₁) :
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
      (Formula.and domL domR)) ω₀ ρ₁ := by
  refine (sem_rightBlock_frozen_iff hfR hlam).mpr ?_
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hrun
  refine ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, ?_⟩
  intro t ht
  refine ⟨?_, hdom t ht⟩
  have heq : Set.EqOn (Φ t) ω₀ domL.fv := by
    intro v hv
    refine hmask t ht v ?_
    obtain ⟨i, rfl⟩ := hdomL hv
    intro hb
    obtain ⟨j, hj⟩ := rightBlock_bound_sub fR lam _ hb
    exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
  exact (Formula.coincidence domL heq).mpr hdomLω

/-- A frozen-left joint response run is a right-only response run. -/
theorem joint_run_toR {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {ν μ : State (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hrun : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
      (Formula.and domL domR)) ν μ) :
    Program.sem (Program.ode (rightBlock fR lam) domR) ν μ :=
  sem_ode_dom_and_right ((sem_rightBlock_frozen_iff hfR hlam).mp hrun)

/-- **The right-only reposition prefix.** `faModalB_repoPrefix` with the hop stated as
the mode's own program: convert the hop run to the joint form (the anchor carries
`domL` via `hφL`), fire the S1 core, transport the response back. -/
theorem faModalB_repoPrefixR {fL fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {φ : Formula (Var n)} {Q : Program (Var n)}
    {a : Fin n} {dt : ℝ} {ω₀ : State (Var n)}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hdomR : domR.fv ⊆ range Rv)
    (hφL : ∀ σ, Formula.sat φ σ → Formula.sat domL σ)
    (hω₀tg : ω₀ ((Side.Aux, a) : Var n) = 0)
    (hω₀φ : Formula.sat φ ω₀)
    (hR : ∃ ρ₁, Program.sem (Program.ode (rightBlock fR lam) domR) ω₀ ρ₁
      ∧ Formula.sat φ ρ₁)
    (hQ : ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q φ ((Side.Aux, a) : Var n) dt σ) :
    faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
      (Program.seq (Program.ode (rightBlock fR lam) domR) Q)
      φ ((Side.Aux, a) : Var n) dt ω₀ := by
  obtain ⟨ρ₁, hrun, hρ₁φ⟩ := hR
  have hjoint := faModalB_repoPrefix hfL hdomL hfR hlam hdomR hω₀tg
    ⟨ρ₁, hop_run_toJoint hfR hlam hdomL (hφL ω₀ hω₀φ) hrun, hρ₁φ⟩ hQ
  refine faModalB_monoQ ?_ hjoint
  rintro ν μ ⟨κ, hhop, hQrun⟩
  exact ⟨κ, joint_run_toR hfR hlam hhop, hQrun⟩

/-- **Right-only multi-hop prefix.** `faModalB_repoPath` over `progR` hops. -/
theorem faModalB_repoPathR {fL : Fin n → Term (Var n)} {domL : Formula (Var n)}
    {φ : Formula (Var n)} {Q : Program (Var n)} {a : Fin n} {dt : ℝ}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hφL : ∀ σ, Formula.sat φ σ → Formula.sat domL σ)
    (hops : List (RepoHop n))
    (hhops : ∀ h ∈ hops, (∀ i, (h.fR i).fv ⊆ range Rv) ∧ h.lam.fv ⊆ range Rv
      ∧ h.domR.fv ⊆ range Rv)
    (hR : ∀ h ∈ hops, ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      ∃ ρ, Program.sem h.progR σ ρ ∧ Formula.sat φ ρ)
    (hQ : ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q φ ((Side.Aux, a) : Var n) dt σ) :
    ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        (hops.foldr (fun h q => Program.seq h.progR q) Q)
        φ ((Side.Aux, a) : Var n) dt σ := by
  induction hops with
  | nil => exact hQ
  | cons h hs ih =>
      intro σ hσ hσtg
      obtain ⟨hhfR, hhlam, hhdomR⟩ := hhops h (List.mem_cons_self)
      have ihs := ih (fun h' hh' => hhops h' (List.mem_cons_of_mem _ hh'))
        (fun h' hh' => hR h' (List.mem_cons_of_mem _ hh'))
      exact faModalB_repoPrefixR hfL hdomL hhfR hhlam hhdomR hφL hσtg hσ
        (hR h (List.mem_cons_self) σ hσ hσtg) ihs

/-- Zero-duration static hop, right-only domain: exists from any anchor whose right
projection satisfies the hop domain. -/
theorem static_hop_existsR {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domR : Formula (Var n)} {σ : State (Var n)}
    (hdomRσ : Formula.sat domR σ) :
    ∃ ρ, Program.sem (Program.ode (rightBlock fR lam) domR) σ ρ ∧ ρ = σ := by
  refine ⟨σ, ⟨0, fun _ => σ, le_refl 0, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
  · intro t ht p hp
    have h0 : t = 0 := le_antisymm ht.2 ht.1
    subst h0
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hempty : (Set.Icc (0:ℝ) 0) \ {0} = (∅ : Set ℝ) := by
      simp [Set.Icc_self]
    rw [hempty, nhdsWithin_empty]
    exact Filter.tendsto_bot
  · intro t ht x hx
    rfl
  · intro t ht
    exact hdomRσ

/-- Folding `progR` hops = folding the mapped program list. -/
theorem foldr_progR_map (hops : List (RepoHop n)) (p : Program (Var n)) :
    hops.foldr (fun h q => Program.seq h.progR q) p
      = (hops.map RepoHop.progR).foldr (fun h q => Program.seq h q) p := by
  induction hops with
  | nil => rfl
  | cons h hs ih => simp [ih]

/-- The hop program's variables are right-side (the L2 disjointness, DERIVED). -/
theorem hdisH_progR {fL : Fin n → Term (Var n)} {domL : Formula (Var n)}
    {a : Fin n} {dt : ℝ} (h : RepoHop n)
    (hhfR : ∀ i, (h.fR i).fv ⊆ range Rv) (hhlam : h.lam.fv ⊆ range Rv)
    (hhdomR : h.domR.fv ⊆ range Rv)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv) :
    Disjoint (Program.vars h.progR)
      (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)) := by
  rw [Set.disjoint_left]
  intro x hx hxW
  have hxR : x ∈ range Rv := by
    rcases vars_ode_sub _ _ hx with hx | hx
    · rcases hx with hx | hx
      · exact rightBlock_boundSet_sub h.fR h.lam hx
      · exact rightBlock_readVars_sub h.fR h.lam hhfR hhlam hx
    · exact hhdomR hx
  rcases vars_clockedSegL_sub fL domL a dt hfL hdomL hxW with hx' | hx'
  · rw [Set.mem_singleton_iff] at hx'
    obtain ⟨i, hi⟩ := hxR
    rw [hx'] at hi
    exact absurd hi (by simp [Rv, Prod.ext_iff])
  · obtain ⟨i, hi⟩ := hxR
    obtain ⟨j, hj⟩ := hx'
    rw [← hi] at hj
    exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **The right-only prefixed k-piece window (the k > 1 assembly, unblocked).** As
`Hmulti_window_prefixed`, with the hops stated as the modes' own right-block programs;
the hop disjointness is derived from the side-split data instead of assumed (the joint
form's `hdisH` is unsatisfiable — the S1 negative finding this file resolves). -/
theorem Hmulti_windowR_prefixed (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (g : Term (Var n)) (env : Formula (Var n)) (a : Fin n) (dt : ℝ) (k : ℕ)
    (htgg : ((Side.Aux, a) : Var n) ∉ g.fv) (htgenv : ((Side.Aux, a) : Var n) ∉ env.fv)
    (hops : List (RepoHop n))
    (hhops : ∀ h ∈ hops, (∀ i, (h.fR i).fv ⊆ range Rv) ∧ h.lam.fv ⊆ range Rv
      ∧ h.domR.fv ⊆ range Rv)
    (hφL : ∀ σ, Formula.sat (Formula.and (invLe g) env) σ → Formula.sat domL σ)
    (hR : ∀ h ∈ hops, ∀ σ, Formula.sat (Formula.and (invLe g) env) σ →
      σ ((Side.Aux, a) : Var n) = 0 →
      ∃ ρ, Program.sem h.progR σ ρ ∧ Formula.sat (Formula.and (invLe g) env) ρ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (pieces : List (Program (Var n))) (hklen : pieces.length = k) (hk : 0 < k)
    (hdisP : ∀ Q ∈ pieces, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)))
    (hcouple : ∀ Q ∈ pieces, ∀ σ, Formula.sat (Formula.and (invLe g) env) σ →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q (Formula.and (invLe g) env) ((Side.Aux, a) : Var n) dt
        (Function.update σ ((Side.Aux, a) : Var n) 0))
    {σ : State (Var n)} (hσ : Formula.sat (Formula.and (invLe g) env) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (windowSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt k)
      (bigSeq ((hops.map (fun h => h.progR)) ++ pieces))
      (Formula.and (invLe g) env)) σ := by
  set φ := Formula.and (invLe g) env with hφdef
  have htgφ : ((Side.Aux, a) : Var n) ∉ φ.fv := by
    intro h
    rcases h with h | h
    · exact htgg (by simpa [invLe, Formula.fv, Term.fv] using h)
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
