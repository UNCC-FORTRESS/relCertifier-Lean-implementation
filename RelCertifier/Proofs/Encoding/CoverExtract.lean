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
      m.repoDynPreOK = false ∧ m.repoDynPostOK = false)
    (hcov : Covered G ⟨q, B, σs⟩) :
    ∃ m, G.modeAt q = some m ∧ m.jointOK = true := by
  cases hcov with
  | base m hm hj _ => exact ⟨m, hm, hj⟩
  | step m hm hj _ _ => exact ⟨m, hm, hj⟩
  | stepRepositionDynPre m hm hrepo _ _ _ =>
      exact absurd hrepo (by simp [(hnorepo q m hm).1])
  | stepRepositionDynPost m hm hrepo _ _ _ =>
      exact absurd hrepo (by simp [(hnorepo q m hm).2])

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

/-! ## R2 — guard-gated windows (the left automaton's entry semantics) -/

/-- The guard-gated window: `test guardL ; k clocked pieces` — the mode is enterable
only where its guard holds, matching the automaton (and making guard-incompatible
(window, right-state) obligations vacuous exactly where the invariant excludes them). -/
def gwindowSeg (guardL : Formula (Var n)) (leftSys : ODESystem (Var n))
    (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ) : Program (Var n) :=
  Program.seq (Program.test guardL) (windowSeg leftSys domL tg dt k)

theorem framesMv_test (φ : Formula (Var n)) (mv : Var n) :
    FramesMv (Program.test φ) mv := by
  intro σ ν h
  obtain ⟨rfl, -⟩ := h
  rfl

theorem framesMv_seq {P Q : Program (Var n)} {mv : Var n}
    (hP : FramesMv P mv) (hQ : FramesMv Q mv) : FramesMv (Program.seq P Q) mv := by
  intro σ ν h
  obtain ⟨μ, hPμ, hQν⟩ := h
  rw [hQ μ ν hQν, hP σ μ hPμ]

theorem framesMv_gwindow (guardL : Formula (Var n)) (fL : Fin n → Term (Var n))
    (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ) (mv : Var n)
    (hmvtg : mv ≠ tg) (hmvL : mv ∉ (leftBlock fL).bound) :
    FramesMv (gwindowSeg guardL (leftBlock fL) domL tg dt k) mv :=
  framesMv_seq (framesMv_test guardL mv)
    (framesMv_window (leftBlock fL) domL tg dt k mv hmvtg hmvL)

/-- Guarded window variables: the guard's plus the window's. -/
theorem vars_gwindowSegL_sub (guardL : Formula (Var n)) (fL : Fin n → Term (Var n))
    (domL : Formula (Var n)) (b : Fin n) (dt : ℝ) (k : ℕ)
    (hguard : guardL.fv ⊆ range Lv) (hfL : ∀ i, (fL i).fv ⊆ range Lv)
    (hdomL : domL.fv ⊆ range Lv) :
    Program.vars (gwindowSeg guardL (leftBlock fL) domL ((Side.Aux, b) : Var n) dt k)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv := by
  intro x hx
  rcases vars_seq_sub _ _ hx with hx | hx
  · rw [vars_test_eq] at hx
    exact Or.inr (hguard hx)
  · exact vars_windowSegL_sub fL domL b dt k hfL hdomL hx

/-- **The guarded uniform theorem (R2 gate).** Left = guard-gated windows, one per left
mode; response = the declared-self-edge stay; checker cover in the conjunction. Relative
to `theorem3_uniform_from_covered`: `leftData` carries each mode's lowered guard, the
window is enterable only where it holds (`faModal_seqL` discharges the gate: the response
obligation arises only at guard-satisfying entries), and the two variable-hygiene facts
absorb the guard via its side-split. mv = (Aux,a), tg = (Aux,b). -/
theorem theorem3_uniform_guarded (Gr : SearchGraph (Var n)) (g : Term (Var n))
    (a b : Fin n) (dt : ℝ)
    (leftData : List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (ϕinv : RFormula (Var n))
    (Gj : SearchGraph (Var n)) (cert : CoverCert Gj g) (fuel : ℕ) (B : ℕ)
    (hab : a ≠ b)
    (hchk : ∀ q, q < Gj.modes.length →
      decideCovered Gj fuel ⟨q, B, SrcSetting.preJ⟩ = true)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hgLR : g.fv ⊆ range Lv ∪ range Rv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length)
    (hself : ∀ q, q < Gr.modes.length → ∃ e ∈ Gr.edgesFrom q, e.tgt = q)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv)
      ∧ d.2.2.1.fv ⊆ range Lv)
    (hRPA : ∀ d ∈ leftData, RightProjAlignV Gj Gr g d.2.1 d.2.2.1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftData.map (fun d =>
        gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2)))
      (rightAutomatonBody Gr ((Side.Aux, a) : Var n))
      (RFormula.and ϕinv (mvValidR ((Side.Aux, a) : Var n) Gr.modes.length)))
    ∧ (∀ q, q < Gj.modes.length → ∀ ν, InvHolds g ν →
        CoexecInvThroughout Gj g ⟨q, B, SrcSetting.preJ⟩ ν) := by
  have haux : ∀ (c : Fin n) x, x ∈ range Lv ∪ range Rv → ((Side.Aux, c) : Var n) ≠ x := by
    rintro c x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact aux_ne_Lv c i
    · exact fun h => aux_ne_Rv c i h
  have hmvtg : ((Side.Aux, a) : Var n) ≠ ((Side.Aux, b) : Var n) := by
    simpa [Prod.ext_iff] using hab
  constructor
  · refine theorem3_faithful_multi_of_emit' Gr ((Side.Aux, a) : Var n) g _ ϕinv
      (fun hmem => haux a _ (hgLR hmem) rfl) hψ
      (fun q m hm hmv => aux_notin_range_Rv a (hRv q m hm (vars_ode_sub _ _ (Or.inl hmv))))
      htt hlt ?_ ?_ ?_ ?_
    · -- frames
      intro P hP
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hP
      refine framesMv_gwindow d.1 d.2.1 d.2.2.1 _ dt d.2.2.2 _ hmvtg ?_
      intro h
      obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
      exact aux_ne_Lv a i hi
    · -- hd: guarded windows on Lv-side vs automaton on {mv} ∪ Rv
      refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
      · refine vars_bigChoice_sub _ _ ?_
        intro p hp
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
        exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 b dt d.2.2.2 (hL d hd).1
          (hL d hd).2.1 (hL d hd).2.2
      · intro x hx
        rw [Program.rename_refl] at hx
        rcases vars_bodyU_sub Gr _ htt hRv hx with hx | hx
        · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
        · exact Or.inr hx
    · -- the guarded window Hmulti: gate by faModal_seqL, then the self-stay response
      intro P hP q hqlt σ hmvq hσ
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hP
      obtain ⟨hguard, hfL, hdomL⟩ := hL d hd
      have hdis : ∀ q' m, Gr.modeAt q' = some m →
          Disjoint (Program.vars ((Program.ode m.sys m.dom).rename (Equiv.refl (Var n))))
            (Program.vars (clockedSeg (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt)) := by
        intro q' m hm
        rw [Set.disjoint_left]
        intro x hxR hxL
        have hR := hRv q' m hm (by
          rw [Program.rename_refl] at hxR
          exact vars_ode_sub _ _ hxR)
        rcases vars_clockedSegL_sub d.2.1 d.2.2.1 b dt hfL hdomL hxL with hx | hx
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact aux_notin_range_Rv b hR
        · obtain ⟨i, rfl⟩ := hx
          obtain ⟨j, hj⟩ := hR
          exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
      obtain ⟨segs, halign, hchain, hhead, hfa⟩ :=
        Hmulti_window_from_cover Gj Gr g ((Side.Aux, a) : Var n) d.2.1 d.2.2.1
          ((Side.Aux, b) : Var n) dt d.2.2.2 cert
          (fun v hv => Or.inl ((hdomL hv).elim (fun i hi => hi ▸ Lv_mem_leftBlock_boundSet d.2.1 i)))
          (fun h => (leftBlock_bound_sub d.2.1 _ h).elim (fun i hi => aux_ne_Lv b i hi))
          (fun h => aux_notin_range_Lv b (leftBlock_readVars_sub d.2.1 hfL h))
          (fun h => aux_notin_range_Lv b (hdomL h))
          (fun hmem => haux b _ (hgLR hmem) rfl)
          (fun q' m hm => by
            have hsub := hRv q' m hm
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro h
              exact aux_notin_range_Rv b (hsub (Or.inl (Or.inl (by
                simpa [ODESystem.boundSet, Set.mem_setOf_eq] using h))))
            · exact fun h => aux_notin_range_Rv b (hsub (Or.inl (Or.inr h)))
            · exact fun h => aux_notin_range_Rv b (hsub (Or.inl (Or.inl h)))
            · exact fun h => aux_notin_range_Rv b (hsub (Or.inr h)))
          (hRPA d hd)
          (emitWindows_self Gr g ((Side.Aux, a) : Var n) ((Side.Aux, b) : Var n)
            d.2.1 d.2.2.1 dt d.2.2.2 hself hdis)
          q hqlt σ hmvq hσ
      refine ⟨segs, halign, hchain, hhead, ?_⟩
      refine faModal_seqL (Equiv.refl (Var n)) (Program.test d.1) _ _ _ σ ?_
      rw [sat_box]
      intro ν hν
      obtain ⟨rfl, -⟩ := hν
      exact hfa
    · -- hddF: guarded-window sides
      rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
      refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
      · rw [faShape_varsL', pvars_star', ψmulti_varsL]
        refine Set.union_subset ?_ (fun v hv => Or.inr (hinvL hv))
        refine vars_bigChoice_sub _ _ ?_
        intro p hp
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
        exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 b dt d.2.2.2 (hL d hd).1
          (hL d hd).2.1 (hL d hd).2.2
      · rw [faShape_varsR', pvars_star']
        refine Set.union_subset ?_ ?_
        · intro v hv
          rcases vars_bodyU_sub Gr _ htt hRv hv with hv | hv
          · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
          · exact Or.inr hv
        · intro v hv
          rcases ψmulti_varsR_sub _ Gr.modes.length ϕinv hv with hv | hv
          · exact Or.inr (hinvR hv)
          · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
  · intro q hq ν hinit
    exact check_sound Gj g cert fuel ⟨q, B, SrcSetting.preJ⟩ (hchk q hq) ν hinit

end RelCertifier
