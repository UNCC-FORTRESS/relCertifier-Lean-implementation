/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# R1 — the window witness from the graph structure; the cover from the checker

Replaces the ASSUMED `EmitWindows` device (docs/ROADMAP.md R1). Two honest halves,
mirroring `rvalid_from_cert`'s finding:

* **The modal witness needs no budget walk.** For an all-joint graph, the per-window
  response is the code's own `retainedSucc` self-loop: stay `k` clock-capped pieces in
  the current mode, along its DECLARED self-edge (every benchmark declares one —
  kernel-checked per instance). `emitWindows_self` produces `EmitWindows` from exactly
  that structure — no `Covered` needed, because each piece's certificate is consumed
  downstream through `RightProjAlignV` (`cert.segPres`), and `theorem3Form`'s content is
  invariant preservation, for which the budget is witness *strategy*, not statement.
* **The budget walk is the tool's CERTIFIED gate.** `decideCovered` (which the tool
  itself runs) re-validated in kernel yields `Covered` (`decideCovered_sound`) and the
  semantic throughout-invariant (`check_sound`) — carried as the second conjunct of the
  top theorem, exactly as `decideCovered_implies_theorem3_faithful_multi` does.

`Covered.jointOK_head` is the inversion tying the two: on a no-reposition graph, a
covered start mode is joint-certified — the checker cannot accept an uncertified stay.

Scope: all-joint graphs (`jointOK` everywhere, reposition flags false). Reposition-node
windows land with R2's statement conditioning (the interleaved-left family).
-/
import RelCertifier.Proofs.Encoding.UniformFvDischarge
import RelCertifier.Checker.Checker

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## The `Covered` inversion (no-reposition graphs) -/

/-- On a graph with no reposition certificates, a covered configuration's head mode is
joint-certified: the verified checker cannot accept a stay in an uncertified mode. -/
theorem Covered.jointOK_head (G : SearchGraph (Var n)) {q B : ℕ} {σs : SrcSetting}
    (hnorepo : ∀ q' m, G.modeAt q' = some m →
      m.repoPreOK = false ∧ m.repoPostOK = false ∧
      m.repoDynPreOK = false ∧ m.repoDynPostOK = false)
    (hcov : Covered G ⟨q, B, σs⟩) :
    ∃ m, G.modeAt q = some m ∧ m.jointOK = true := by
  cases hcov with
  | base m hm hj _ => exact ⟨m, hm, hj⟩
  | step m hm hj _ _ => exact ⟨m, hm, hj⟩
  | stepRepositionPre m hm hrepo _ _ _ =>
      exact absurd hrepo (by simp [(hnorepo q m hm).1])
  | stepRepositionPost m hm hrepo _ _ _ =>
      exact absurd hrepo (by simp [(hnorepo q m hm).2.1])
  | stepRepositionDynPre m hm hrepo _ _ _ =>
      exact absurd hrepo (by simp [(hnorepo q m hm).2.2.1])
  | stepRepositionDynPost m hm hrepo _ _ _ =>
      exact absurd hrepo (by simp [(hnorepo q m hm).2.2.2])

/-! ## The self-stay window witness -/

/-- A constant list is a chain of any reflexive-at-`x` relation. -/
theorem isChain_replicate {α : Type*} {R : α → α → Prop} (x : α) (hx : R x x) :
    ∀ k, List.IsChain R (List.replicate k x) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      match k, ih with
      | 0, _ => simp
      | k + 1, ih =>
          rw [List.replicate_succ]
          rw [List.replicate_succ] at ih ⊢
          refine ih.cons ?_
          intro y hy
          rw [List.head?_cons, Option.mem_some_iff] at hy
          rw [← hy]
          exact hx

/-- **The window response, from the declared self-loop.** Every benchmark mode declares
its self-edge (`next` contains the mode itself — checked per instance); the response to a
`k`-piece window is `k` residences in the current mode along that edge — the code's
`retainedSucc q = q :: …` self-loop, realized on the declared edge. Produces the
`EmitWindows` fact structurally; certification of each piece is NOT assumed here — it is
consumed downstream from `cert.segPres` via `RightProjAlignV`. -/
theorem emitWindows_self (Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv tg : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (dt : ℝ) (k : ℕ)
    (hself : ∀ q, q < Gr.modes.length → ∃ e ∈ Gr.edgesFrom q, e.tgt = q)
    (hdis : ∀ q m, Gr.modeAt q = some m →
      Disjoint (Program.vars ((Program.ode m.sys m.dom).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL0) domL0 tg dt))) :
    EmitWindows Gr g mv fL0 domL0 tg dt k := by
  intro q hq σ _ _
  have hm : ∃ m, Gr.modeAt q = some m := by
    unfold SearchGraph.modeAt
    exact ⟨Gr.modes[q], List.getElem?_eq_getElem hq⟩
  obtain ⟨m, hm⟩ := hm
  obtain ⟨e, he, htgt⟩ := hself q hq
  refine ⟨List.replicate k (q, m, e), List.length_replicate, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [List.eq_of_mem_replicate hs]
    exact ⟨hm, he⟩
  · exact isChain_replicate (q, m, e) htgt k
  · intro s hs
    match k, hs with
    | k + 1, hs =>
        rw [List.replicate_succ, List.head?_cons, Option.some.injEq] at hs
        rw [← hs]
  · intro Q hQ
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hQ
    rw [List.eq_of_mem_replicate hs]
    exact hdis q m hm

/-! ## The top theorem, Emit-free — the checker in the conjunction -/

/-- **The uniform multi-flow theorem from the checker's cover (R1 gate).** Relative to
`theorem3_uniform_multiflow`: the ASSUMED `EmitWindows` is GONE — the window response is
the declared-self-edge stay (`emitWindows_self`); and the verified checker's acceptance
(`decideCovered`, the very function the tool runs) enters as a per-start hypothesis whose
kernel re-run yields the semantic throughout-invariant conjunct (`check_sound`), exactly
as in `decideCovered_implies_theorem3_faithful_multi`. On a no-reposition graph the
checker's acceptance also certifies (via `Covered.jointOK_head`) that every start mode is
joint-certified — the structural tie between the two conjuncts. -/
theorem theorem3_uniform_from_covered (Gr : SearchGraph (Var n)) (g : Term (Var n))
    (mv : Var n) (tg : Var n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (ϕinv : RFormula (Var n))
    (Gj : SearchGraph (Var n)) (cert : CoverCert Gj g) (fuel : ℕ) (B : ℕ)
    (hchk : ∀ q, q < Gj.modes.length →
      decideCovered Gj fuel ⟨q, B, SrcSetting.preJ⟩ = true)
    (hg : mv ∉ g.fv) (htgg : tg ∉ g.fv) (hmvtg : mv ≠ tg)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length)
    (htgRight : ∀ q m, Gr.modeAt q = some m →
      tg ∉ m.sys.bound ∧ tg ∉ m.sys.readVars ∧ tg ∉ m.sys.boundSet ∧ tg ∉ m.dom.fv)
    (hself : ∀ q, q < Gr.modes.length → ∃ e ∈ Gr.edgesFrom q, e.tgt = q)
    (hleft : ∀ d ∈ leftData, mv ∉ (leftBlock d.1).bound
      ∧ d.2.1.fv ⊆ (leftBlock d.1).boundSet ∪ (leftBlock d.1).readVars
      ∧ tg ∉ (leftBlock d.1).bound ∧ tg ∉ (leftBlock d.1).readVars ∧ tg ∉ d.2.1.fv
      ∧ RightProjAlignV Gj Gr g d.1 d.2.1
      ∧ (∀ q m, Gr.modeAt q = some m →
          Disjoint (Program.vars ((Program.ode m.sys m.dom).rename (Equiv.refl (Var n))))
            (Program.vars (clockedSeg (leftBlock d.1) d.2.1 tg dt))))
    (hd : Disjoint (Program.vars (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2))))
        (Program.vars ((rightAutomatonBody Gr mv).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
            windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2))))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
            windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2))))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftData.map (fun d => windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2)))
      (rightAutomatonBody Gr mv)
      (RFormula.and ϕinv (mvValidR mv Gr.modes.length)))
    ∧ (∀ q, q < Gj.modes.length → ∀ ν, InvHolds g ν →
        CoexecInvThroughout Gj g ⟨q, B, SrcSetting.preJ⟩ ν) := by
  constructor
  · refine theorem3_uniform_multiflow Gr g mv tg dt leftData ϕinv hg htgg hmvtg hψ
      hfresh htt hlt htgRight ?_ hd hddF
    intro d hd'
    obtain ⟨hmvL, hφL, htgLb, htgLr, htgdL, hRPA, hdis⟩ := hleft d hd'
    exact ⟨hmvL, hφL, htgLb, htgLr, htgdL, ⟨Gj, cert, hRPA⟩,
      emitWindows_self Gr g mv tg d.1 d.2.1 dt d.2.2 hself hdis⟩
  · intro q hq ν hinit
    exact check_sound Gj g cert fuel ⟨q, B, SrcSetting.preJ⟩ (hchk q hq) ν hinit

end RelCertifier
