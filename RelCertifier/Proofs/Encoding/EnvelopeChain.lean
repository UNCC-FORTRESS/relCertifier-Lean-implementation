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

end RelCertifier
