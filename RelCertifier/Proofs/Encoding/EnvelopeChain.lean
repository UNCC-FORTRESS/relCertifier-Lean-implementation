/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S1 — the envelope-carrying modal chain

The plain chain's loop invariant (`invLe g ∧ mvValid`) quantifies response anchors over
ALL invariant states, including right-outside-envelope ones — making the unconditioned
existence hypotheses (`hES`) false in general and static hops domain-less. The fix is a
SOUND strengthening of the loop invariant with the right-envelope conjunct: every
response run ends inside its evolve domain (`sem`'s domain-at-endpoint), so the
conjunct is preserved for free, and every anchor the loop ever presents is an
envelope state — exactly the conditioning the viability certificates (S3) and the
reposition hops need.

This file mirrors `hstep_single_multi'`/`hstep_assembled_multi'`/
`theorem3_faithful_multi_of_emit'` with `phiInvE g env mv k := invLe g ∧ env ∧ mvValid`
(the envelope `env` an Rv-only formula — under the universal-evolve well-formedness it
is THE shared evolve conjunct of every mode). Copied, not edited, for cascade hygiene.
-/
import RelCertifier.Proofs.Encoding.UniformFvDischarge
import RelCertifier.Proofs.Encoding.RepoPrefix

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-- The envelope-carrying loop invariant: `g ≤ 0 ∧ env ∧ mvValid`. -/
def phiInvE (g : Term (Var n)) (env : Formula (Var n)) (mv : Var n) (k : ℕ) :
    Formula (Var n) :=
  Formula.and (Formula.and (invLe g) env) (mvValid mv k)

/-- The relational form of the envelope conjunct (right projection). -/
def envR (env : Formula (Var n)) : RFormula (Var n) :=
  RFormula.proj DLRel.Side.R env

theorem encode_envR (env : Formula (Var n)) :
    encode (Equiv.refl (Var n)) (envR env) = env := by
  unfold encode envR
  simp [RFormula.renameR, RFormula.enc, Formula.rename_refl]

/-- Strengthen a coupling's postcondition with the envelope, provided every response
run ends inside it (e.g. because the response is an ode whose domain implies it). -/
theorem faModalB_strengthen {P Q : Program (Var n)} {φ env : Formula (Var n)}
    {tg : Var n} {dt : ℝ} {σ : State (Var n)}
    (hend : ∀ ν μ, Program.sem Q ν μ → Formula.sat env μ)
    (h : faModalB (Equiv.refl (Var n)) P Q φ tg dt σ) :
    faModalB (Equiv.refl (Var n)) P Q (Formula.and φ env) tg dt σ := by
  intro ν hν
  obtain ⟨μ, hsem, hφ⟩ := h ν hν
  rw [Program.rename_refl] at hsem
  refine ⟨μ, by rwa [Program.rename_refl], hφ, hend ν μ hsem⟩

/-- An ode response whose domain's right conjunct is the envelope ends inside it
(zero-duration runs included: the domain holds at every time, including `r = 0` where
the endpoint is the start — which then must itself satisfy the domain). -/
theorem sem_ode_ends_in_domain {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys dom) ν μ) :
    Formula.sat dom μ := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  rw [← hΦr]
  exact hdom r (Set.right_mem_Icc.mpr hr)

/-- `hstep_single_multi'` with the envelope conjunct. -/
theorem hstep_single_multiE (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (g : Term (Var n)) (env : Formula (Var n)) (P : Program (Var n))
    (hg : mv ∉ g.fv) (henv : mv ∉ env.fv)
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
        (Formula.and (invLe g) env)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P
      (Program.star (rightAutomatonBody G mv)) (phiInvE g env mv G.modes.length)) σ := by
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
  · rw [sat_invLe] at hinvμ ⊢
    rwa [Term.coincidence g (fun y hy =>
      Function.update_of_ne (fun hc => hg (by rw [← hc]; exact hy)) _ _)]
  · rwa [(Formula.coincidence env (fun y hy =>
      Function.update_of_ne (fun hc => henv (by rw [← hc]; exact hy)) _ _) :
        Formula.sat env _ ↔ Formula.sat env μ)]
  · rw [sat_mvValid]
    exact ⟨qf, hqfvalid, Function.update_self mv (qf : ℝ) μ⟩

/-- `hstep_assembled_multi'` with the envelope conjunct. -/
theorem hstep_assembled_multiE (G : SearchGraph (Var n)) (mv : Var n)
    (g : Term (Var n)) (env : Formula (Var n))
    (leftProgs : List (Program (Var n))) (hg : mv ∉ g.fv) (henv : mv ∉ env.fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (invLe g) env) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe g) env)) σ) :
    ∀ σ, Formula.sat (phiInvE g env mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv)) (phiInvE g env mv G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq⟩ := sat_mvValid.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBody G mv))
    (phiInvE g env mv G.modes.length) σ leftProgs ?_
  intro P hP
  obtain ⟨segs, halign, hchain, hhead, hfaModal⟩ := Hmulti P hP q hqlt σ hmvq hφ'.1
  exact hstep_single_multiE G mv q g env P hg henv (hframes P hP) hqlt hfresh htt hlt
    segs halign hchain hhead hmvq hfaModal

/-- Encoding of the envelope-carrying postcondition. -/
theorem encode_phiInvE {ϕinv : RFormula (Var n)} {g : Term (Var n)}
    {env : Formula (Var n)} {mv : Var n} {k : ℕ}
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g) :
    encode (Equiv.refl (Var n))
      (RFormula.and (RFormula.and ϕinv (envR env)) (mvValidR mv k))
      = phiInvE g env mv k := by
  have hdist : encode (Equiv.refl (Var n))
      (RFormula.and (RFormula.and ϕinv (envR env)) (mvValidR mv k))
      = Formula.and (Formula.and (encode (Equiv.refl (Var n)) ϕinv)
          (encode (Equiv.refl (Var n)) (envR env)))
        (encode (Equiv.refl (Var n)) (mvValidR mv k)) := by
    unfold encode; simp only [RFormula.renameR, RFormula.enc]
  rw [hdist, hψ, encode_envR, encode_mvValidR]; rfl

/-- **The envelope-carrying multi Theorem 3.** `theorem3_faithful_multi` with
`ψ = (ϕinv ∧ ⌊env⌋_R) ∧ mvValidR` — the loop invariant that keeps every response
anchor inside the right envelope. -/
theorem theorem3_faithful_multiE (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (env : Formula (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInvE g env mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv)) (phiInvE g env mv G.modes.length)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and ϕinv (envR env)) (mvValidR mv G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and ϕinv (envR env)) (mvValidR mv G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and (RFormula.and ϕinv (envR env)) (mvValidR mv G.modes.length))) := by
  set k := G.modes.length
  set ψpost := RFormula.and (RFormula.and ϕinv (envR env)) (mvValidR mv k) with hψpost
  set Lp := Program.star (bigChoice leftProgs)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost = phiInvE g env mv k := encode_phiInvE hψ
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
  have hInvν : Formula.sat (phiInvE g env mv k) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_multi (bigChoice leftProgs) (rightAutomatonBody G mv) ψpost ν bs hd
    (by rw [hencψ]; exact hInvν)
    (fun σ hσ => by rw [hencψ] at hσ ⊢; exact hstep σ hσ) hddF hbdg

/-- Pointwise run-equivalent program lists have run-equivalent `bigSeq`s. -/
theorem sem_bigSeq_congr {ps qs : List (Program (Var n))}
    (h : List.Forall₂ (fun p q => ∀ ν μ, Program.sem p ν μ ↔ Program.sem q ν μ) ps qs) :
    ∀ ν μ, Program.sem (bigSeq ps) ν μ ↔ Program.sem (bigSeq qs) ν μ := by
  induction h with
  | nil => intro ν μ; exact Iff.rfl
  | cons hpq _ ih =>
      intro ν μ
      constructor
      · rintro ⟨κ, hp, hrest⟩
        exact ⟨κ, (hpq ν κ).mp hp, (ih κ μ).mp hrest⟩
      · rintro ⟨κ, hq, hrest⟩
        exact ⟨κ, (hpq ν κ).mpr hq, (ih κ μ).mpr hrest⟩

/-- Fold-of-seq variable peel (generic). -/
theorem vars_foldr_seq_sub (hs : List (Program (Var n))) (p : Program (Var n)) :
    ∀ x ∈ Program.vars (hs.foldr (fun h q => Program.seq h q) p),
      x ∈ Program.vars p ∨ ∃ h ∈ hs, x ∈ Program.vars h := by
  induction hs with
  | nil => exact fun x hx => Or.inl hx
  | cons h hs ih =>
      intro x hx
      rcases vars_seq_sub _ _ hx with hx | hx
      · exact Or.inr ⟨h, List.mem_cons_self, hx⟩
      · rcases ih x hx with hx | ⟨h', hh', hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨h', List.mem_cons_of_mem _ hh', hx⟩

/-- Folding hop programs = folding the mapped program list. -/
theorem foldr_prog_map (hops : List (RepoHop n)) (domL : Formula (Var n))
    (p : Program (Var n)) :
    hops.foldr (fun h q => Program.seq (h.prog domL) q) p
      = (hops.map (fun h => h.prog domL)).foldr (fun h q => Program.seq h q) p := by
  induction hops with
  | nil => rfl
  | cons h hs ih => simp [List.map_cons, List.foldr_cons, ih]

/-- **The prefixed window response (S1 assembly).** The clocked `k`-piece window's
`faModal`, response = reposition-hop prefix (frozen-left programs) followed by the `k`
pieces: `faModalB_repoPath` folds the prefix into the first piece's coupling,
`multiseg_clocked` composes, and fold-head associativity flattens the response program
to the hop-programs-then-pieces list. φ = the envelope-carrying `(invLe g) ∧ env`. -/
theorem Hmulti_window_prefixed (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (g : Term (Var n)) (env : Formula (Var n)) (a : Fin n) (dt : ℝ) (k : ℕ)
    (htgg : ((Side.Aux, a) : Var n) ∉ g.fv) (htgenv : ((Side.Aux, a) : Var n) ∉ env.fv)
    (hops : List (RepoHop n))
    (hhops : ∀ h ∈ hops, (∀ i, (h.fR i).fv ⊆ range Rv) ∧ h.lam.fv ⊆ range Rv
      ∧ h.domR.fv ⊆ range Rv)
    (hR : ∀ h ∈ hops, ∀ σ, Formula.sat (Formula.and (invLe g) env) σ →
      σ ((Side.Aux, a) : Var n) = 0 →
      ∃ ρ, Program.sem (h.prog domL) σ ρ ∧ Formula.sat (Formula.and (invLe g) env) ρ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (pieces : List (Program (Var n))) (hklen : pieces.length = k) (hk : 0 < k)
    (hdisP : ∀ Q ∈ pieces, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)))
    (hdisH : ∀ h ∈ hops, Disjoint (Program.vars (h.prog domL))
        (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)))
    (hcouple : ∀ Q ∈ pieces, ∀ σ, Formula.sat (Formula.and (invLe g) env) σ →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q (Formula.and (invLe g) env) ((Side.Aux, a) : Var n) dt
        (Function.update σ ((Side.Aux, a) : Var n) 0))
    {σ : State (Var n)} (hσ : Formula.sat (Formula.and (invLe g) env) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (windowSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt k)
      (bigSeq ((hops.map (fun h => h.prog domL)) ++ pieces))
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
  set folded := hops.foldr (fun h q => Program.seq (h.prog domL) q) p₁ with hfolded
  have hfoldvars : ∀ x ∈ Program.vars folded,
      x ∈ Program.vars p₁ ∨ ∃ h ∈ hops, x ∈ Program.vars (h.prog domL) := by
    rw [hfolded, foldr_prog_map]
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
        · exact absurd hxW (Set.disjoint_left.mp (hdisH h hh) hx)
      · exact hdisP Q (List.mem_cons_of_mem _ hQr))
    (by
      intro Q hQ σ' hσ'
      rcases List.mem_cons.mp hQ with rfl | hQr
      · -- the folded coupling: repoPath feeding the first piece
        have hupdφ : Formula.sat φ (Function.update σ' ((Side.Aux, a) : Var n) 0) := by
          rwa [(Formula.coincidence φ (fun v hv =>
            Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv)) _ _) :
              Formula.sat φ _ ↔ Formula.sat φ σ')]
        have hupdtg : (Function.update σ' ((Side.Aux, a) : Var n) 0)
            ((Side.Aux, a) : Var n) = 0 := Function.update_self _ _ _
        refine faModalB_repoPath hfL hdomL hops hhops hR
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
  -- flatten: the folded head ↔ the hop-programs-then-pieces list; the left side is the window
  have hlen : (folded :: rest).length = k := by simpa using hklen
  have hleft : (folded :: rest).map
      (fun _ => clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)
      = List.replicate k (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt) := by
    rw [List.map_const', hlen]
  rw [hleft] at hm
  have hfold_eq : folded = (hops.map (fun h => h.prog domL)).foldr
      (fun h q => Program.seq h q) p₁ := by
    rw [hfolded, foldr_prog_map]
  have hflat := sem_bigSeq_fold_head (hops.map (fun h => h.prog domL)) p₁ rest
  refine sat_faModal_congrR (fun ν μ => ?_) hm
  rw [hfold_eq]
  exact hflat ν μ

/-- Static hop: with the envelope being the joint universal domain, a zero-duration
run of the hop program exists from every invariant anchor — no hypothesis needed. -/
theorem static_hop_exists {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {g : Term (Var n)} {σ : State (Var n)}
    (hσ : Formula.sat (Formula.and (invLe g) (Formula.and domL domR)) σ) :
    ∃ ρ, Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
        (Formula.and domL domR)) σ ρ
      ∧ Formula.sat (Formula.and (invLe g) (Formula.and domL domR)) ρ := by
  refine ⟨σ, ⟨0, fun _ => σ, le_refl 0, rfl, rfl, ?_, ?_, ?_⟩, hσ⟩
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
    exact hσ.2

end RelCertifier
