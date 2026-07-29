/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L4 — the region-carrying modal chain (the `rung2c` conditioning)

The E/F chains carry `mvValid mv k` — the mode variable holds SOME declared index —
so the loop invariant tells the step provider nothing about WHERE the right execution
is while it holds a given mode. `refinement_ladder_rover_rung2c_6dof` needs more: its
right graph is the one-way chain `STEEP → MODER → FLAT`, and the three backward
(window, start) pairs are dischargeable only by VACUITY, which requires the invariant
to pin each mode's PRESERVED region (`s_r ≥ b(q)`, forward-invariant by
`lowR_preserved`) so that the guard-gated left window (`gwindowSeg`, R2) cannot fire
against a right state that has already crossed the window's band.

This file upgrades `mvValid` to `mvRegion mv regions k` — the big-or of
`mv = q ∧ regions q` — through the whole F-parametric chain:

* `qfOf` + `faithful_rights_bridge_pinned`: the bigSeq→star bridge with the final
  mode PINNED to the last segment's target (the existing bridge's existential hides
  it, and the region fact at the loop's close is per-final-mode). Mirror induction of
  `faithful_rights_bridge` — new leaf, `BridgeReposition` untouched.
* `hstep_single_multiR` / `hstep_assembled_multiR`: the step provider now RECEIVES
  the start mode's region fact and OWES the landing mode's (`regions (qfOf segs q)`)
  in its `faModal` target.
* `theorem3_faithful_multiR_LR` + `hddF_multiR`: the `rvalid` assembly with
  `mvRegionR` in the postcondition and guard-gated windows on the left.

The suite-wide caveat from `ModeRegion.lean` stands: only 95 of 129 right-mode guard
lower bounds are forward-invariant, so this chain is for instances whose regions ARE
preserved — it is not a shared default.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.CoverExtract
import RelCertifier.Proofs.Encoding.FvDischarge

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## The pinned final mode -/

/-- The final mode of a segment chain: the last segment's edge target, or the start
mode if the chain is empty. -/
def qfOf (segs : List (ℕ × RMode (Var n) × REdge (Var n))) (q0 : ℕ) : ℕ :=
  (segs.getLast?).elim q0 (fun s => s.2.2.tgt)

theorem qfOf_nil (q0 : ℕ) : qfOf ([] : List (ℕ × RMode (Var n) × REdge (Var n))) q0 = q0 :=
  rfl

theorem qfOf_cons (s : ℕ × RMode (Var n) × REdge (Var n))
    (rest : List (ℕ × RMode (Var n) × REdge (Var n))) (q0 : ℕ) :
    qfOf (s :: rest) q0 = qfOf rest s.2.2.tgt := by
  cases rest with
  | nil => rfl
  | cons r rs =>
      show ((s :: r :: rs).getLast?).elim q0 _ = ((r :: rs).getLast?).elim s.2.2.tgt _
      rw [List.getLast?_cons_cons]
      rcases h : (r :: rs).getLast? with - | x
      · exact absurd h (by simp)
      · rfl

/-- The pinned final mode is declared whenever the start is and every edge target is. -/
theorem qfOf_lt (G : SearchGraph (Var n))
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (segs : List (ℕ × RMode (Var n) × REdge (Var n)))
    (halign : ∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1)
    (q0 : ℕ) (hq0 : q0 < G.modes.length) : qfOf segs q0 < G.modes.length := by
  rcases h : segs.getLast? with - | s
  · simpa [qfOf, h] using hq0
  · have hmem : s ∈ segs := List.mem_of_getLast? h
    have := (halign s hmem).2
    simpa [qfOf, h] using hlt s.1 s.2.2 this

/-- **The bigSeq→star bridge, final mode pinned** (mirror induction of
`faithful_rights_bridge`; the existential there hides which mode the star run ends
in, and the region-carrying chain needs it to be `qfOf segs q0`). -/
theorem faithful_rights_bridge_pinned (G : SearchGraph (Var n)) (mv : Var n)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length) :
    ∀ (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
      (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) →
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs →
      ∀ (q0 : ℕ), ∀ {ν μ : State (Var n)},
        (∀ s, segs.head? = some s → s.1 = q0) →
        Program.sem (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) ν μ →
        Program.sem (Program.star (rightAutomatonBody G mv))
          (Function.update ν mv (q0 : ℝ)) (Function.update μ mv ((qfOf segs q0) : ℝ)) := by
  intro segs
  induction segs with
  | nil =>
      intro _ _ q0 _ _ _ hrun
      rw [List.map_nil, bigSeq, sem_test] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Relation.ReflTransGen.refl
  | cons s rest ih =>
      intro halign hchain q0 ν μ hstart hrun
      have hq0 : s.1 = q0 := hstart s rfl
      subst hq0
      simp only [List.map_cons, bigSeq] at hrun
      obtain ⟨κ, hflow, hrest⟩ := hrun
      obtain ⟨hm, he⟩ := halign s (List.mem_cons_self ..)
      have hfirst := single_seg_R_real G mv s.1 s.2.1 (hfresh s.1 s.2.1 hm) hm he
        (htt s.1 s.2.2 he) (hlt s.1 s.2.2 he) hflow
      have htailstart : ∀ t, rest.head? = some t → t.1 = s.2.2.tgt := by
        intro t ht
        rcases rest with - | ⟨r, rs⟩
        · exact absurd ht (by simp)
        · simp only [List.head?_cons, Option.some.injEq] at ht
          subst ht; exact hchain.rel.symm
      have htail := ih (fun t ht => halign t (List.mem_cons_of_mem s ht))
        hchain.of_cons s.2.2.tgt htailstart hrest
      rw [qfOf_cons]
      exact Relation.ReflTransGen.trans hfirst htail

/-! ## The region-carrying mode conjunct -/

/-- `mv` holds a declared index AND the right execution sits in that mode's
(preserved) region: `⋁_{q<k} (mv = q ∧ regions q)`. -/
def mvRegion (mv : Var n) (regions : ℕ → Formula (Var n)) (k : ℕ) : Formula (Var n) :=
  bigOr ((List.range k).map (fun q => Formula.and (modeIs mv q) (regions q)))

theorem sat_mvRegion {mv : Var n} {regions : ℕ → Formula (Var n)} {k : ℕ}
    {ν : State (Var n)} :
    Formula.sat (mvRegion mv regions k) ν ↔
      ∃ q < k, ν mv = (q : ℝ) ∧ Formula.sat (regions q) ν := by
  simp only [mvRegion, sat_bigOr, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨f, ⟨q, hq, rfl⟩, hf⟩
    exact ⟨q, hq,
      by simpa only [modeIs, Formula.sat, CompOp.interp, Term.eval] using hf.1, hf.2⟩
  · rintro ⟨q, hq, hν, hreg⟩
    exact ⟨Formula.and (modeIs mv q) (regions q), ⟨q, hq, rfl⟩,
      ⟨by simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, hν], hreg⟩⟩

theorem mvRegion_fv_sub (mv : Var n) (regions : ℕ → Formula (Var n)) (k : ℕ)
    {S : Set (Var n)} (hreg : ∀ q < k, (regions q).fv ⊆ S) :
    (mvRegion mv regions k).fv ⊆ {mv} ∪ S := by
  refine bigOr_fv_sub ?_
  intro f hf
  simp only [List.mem_map, List.mem_range] at hf
  obtain ⟨q, hq, rfl⟩ := hf
  intro v hv
  simp only [Formula.fv, Set.mem_union] at hv
  rcases hv with hv | hv
  · exact Or.inl (by simpa only [modeIs, Formula.fv, Term.fv, Set.union_empty] using hv)
  · exact Or.inr (hreg q hq hv)

/-- The region-carrying loop invariant: `(F ∧ env) ∧ mvRegion`. -/
def phiInvR (F env : Formula (Var n)) (mv : Var n) (regions : ℕ → Formula (Var n))
    (k : ℕ) : Formula (Var n) :=
  Formula.and (Formula.and F env) (mvRegion mv regions k)

/-! ## The step and loop lemmas -/

/-- `hstep_single_multiF` with the region conjunct: the provider's `faModal` target
owes the LANDING mode's region (`regions (qfOf segs q)`), and the pinned bridge
carries it to the mv-updated loop-close witness. -/
theorem hstep_single_multiR (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv) (hregf : ∀ q', mv ∉ (regions q').fv)
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
        (Formula.and (Formula.and F env) (regions (qfOf segs q)))) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P
      (Program.star (rightAutomatonBody G mv))
      (phiInvR F env mv regions G.modes.length)) σ := by
  rw [faModal_sat] at hfaModal ⊢
  intro ν hleft
  obtain ⟨μ, hbigSeq, hpostμ⟩ := hfaModal ν hleft
  have hνmv : ν mv = (q : ℝ) := (hframe σ ν hleft).trans hmvq
  rw [Program.rename_refl] at hbigSeq
  have hstar := faithful_rights_bridge_pinned G mv hfresh htt hlt segs halign hchain q
    hhead hbigSeq
  have hupdν : Function.update ν mv (q : ℝ) = ν := by
    funext x
    by_cases hx : x = mv
    · subst hx; rw [Function.update_self, hνmv]
    · rw [Function.update_of_ne hx]
  rw [hupdν] at hstar
  refine ⟨Function.update μ mv ((qfOf segs q) : ℝ),
    by rw [Program.rename_refl]; exact hstar, ?_⟩
  obtain ⟨⟨hFμ, henvμ⟩, hregμ⟩ := hpostμ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rwa [(Formula.coincidence F (fun y hy =>
      Function.update_of_ne (fun hc => hF (by rw [← hc]; exact hy)) _ _) :
        Formula.sat F _ ↔ Formula.sat F μ)]
  · rwa [(Formula.coincidence env (fun y hy =>
      Function.update_of_ne (fun hc => henv (by rw [← hc]; exact hy)) _ _) :
        Formula.sat env _ ↔ Formula.sat env μ)]
  · rw [sat_mvRegion]
    refine ⟨qfOf segs q, qfOf_lt G hlt segs halign q hqlt,
      Function.update_self mv _ μ, ?_⟩
    rwa [(Formula.coincidence (regions (qfOf segs q)) (fun y hy =>
      Function.update_of_ne (fun hc => hregf _ (by rw [← hc]; exact hy)) _ _) :
        Formula.sat (regions (qfOf segs q)) _ ↔ _)]

/-- `hstep_assembled_multiF` with the region conjunct: the provider RECEIVES the
start mode's region fact and owes the landing mode's. -/
theorem hstep_assembled_multiR (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n))
    (leftProgs : List (Program (Var n))) (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hregf : ∀ q', mv ∉ (regions q').fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ → Formula.sat (regions q) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and F env) (regions (qfOf segs q)))) σ) :
    ∀ σ, Formula.sat (phiInvR F env mv regions G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv))
        (phiInvR F env mv regions G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq, hregq⟩ := sat_mvRegion.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBody G mv))
    (phiInvR F env mv regions G.modes.length) σ leftProgs ?_
  intro P hP
  obtain ⟨segs, halign, hchain, hhead, hfaModal⟩ := Hmulti P hP q hqlt σ hmvq hφ'.1 hregq
  exact hstep_single_multiR G mv q F env regions P hF henv hregf (hframes P hP) hqlt
    hfresh htt hlt segs halign hchain hhead hmvq hfaModal

/-! ## The RFormula layer -/

/-- The region conjunct as a right-projection rel formula. -/
def mvRegionR (mv : Var n) (regions : ℕ → Formula (Var n)) (k : ℕ) : RFormula (Var n) :=
  RFormula.proj DLRel.Side.R (mvRegion mv regions k)

theorem encode_mvRegionR (mv : Var n) (regions : ℕ → Formula (Var n)) (k : ℕ) :
    encode (Equiv.refl (Var n)) (mvRegionR mv regions k) = mvRegion mv regions k := by
  unfold encode mvRegionR
  simp only [RFormula.renameR, RFormula.enc, Formula.rename_refl]

theorem encode_phiInvR_LR {ϕinv : RFormula (Var n)} {F : Formula (Var n)}
    {domL domR : Formula (Var n)} {mv : Var n} {regions : ℕ → Formula (Var n)} {k : ℕ}
    (hψ : encode (Equiv.refl (Var n)) ϕinv = F) :
    encode (Equiv.refl (Var n))
      (RFormula.and (RFormula.and ϕinv (envLR domL domR)) (mvRegionR mv regions k))
      = phiInvR F (Formula.and domL domR) mv regions k := by
  have hdist : encode (Equiv.refl (Var n))
      (RFormula.and (RFormula.and ϕinv (envLR domL domR)) (mvRegionR mv regions k))
      = Formula.and (Formula.and (encode (Equiv.refl (Var n)) ϕinv)
          (encode (Equiv.refl (Var n)) (envLR domL domR)))
        (encode (Equiv.refl (Var n)) (mvRegionR mv regions k)) := by
    unfold encode; simp only [RFormula.renameR, RFormula.enc]
  rw [hdist, hψ, encode_envLR, encode_mvRegionR]; rfl

/-- **The region-carrying Theorem 3 assembly** (mirror of `theorem3_faithful_multiF_LR`
with `mvRegionR` in the postcondition). -/
theorem theorem3_faithful_multiR_LR (G : SearchGraph (Var n)) (mv : Var n)
    (F : Formula (Var n)) (domL domR : Formula (Var n))
    (regions : ℕ → Formula (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = F)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInvR F (Formula.and domL domR) mv regions
        G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv))
        (phiInvR F (Formula.and domL domR) mv regions G.modes.length)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and ϕinv (envLR domL domR))
            (mvRegionR mv regions G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
          (RFormula.and (RFormula.and ϕinv (envLR domL domR))
            (mvRegionR mv regions G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and (RFormula.and ϕinv (envLR domL domR))
        (mvRegionR mv regions G.modes.length))) := by
  set k := G.modes.length
  set ψpost := RFormula.and (RFormula.and ϕinv (envLR domL domR))
    (mvRegionR mv regions k) with hψpost
  set Lp := Program.star (bigChoice leftProgs)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost
      = phiInvR F (Formula.and domL domR) mv regions k := encode_phiInvR_LR hψ
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
  have hInvν : Formula.sat (phiInvR F (Formula.and domL domR) mv regions k) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_multi (bigChoice leftProgs) (rightAutomatonBody G mv) ψpost ν bs hd
    (by rw [hencψ]; exact hInvν)
    (fun σ hσ => by rw [hencψ] at hσ ⊢; exact hstep σ hσ) hddF hbdg

/-! ## The R-shape `hddF` discharger (guard-gated windows) -/

theorem ψmultiR_varsL_sub (mv : Var n) (regions : ℕ → Formula (Var n)) (len : ℕ)
    (ϕinv : RFormula (Var n)) (domL domR : Formula (Var n)) :
    (RFormula.and (RFormula.and ϕinv (envLR domL domR))
        (mvRegionR mv regions len)).varsL
      ⊆ ϕinv.varsL ∪ domL.fv := by
  have h : (RFormula.and (RFormula.and ϕinv (envLR domL domR))
        (mvRegionR mv regions len)).varsL
      = (ϕinv.varsL ∪ (envLR domL domR).varsL) ∪ (mvRegionR mv regions len).varsL := rfl
  rw [h, envLR_varsL]
  have hmv : (mvRegionR mv regions len).varsL = ∅ := by
    simp [mvRegionR, RFormula.varsL]
  rw [hmv, Set.union_empty]

theorem ψmultiR_varsR_sub (mv : Var n) (regions : ℕ → Formula (Var n)) (len : ℕ)
    (ϕinv : RFormula (Var n)) (domL domR : Formula (Var n))
    {S : Set (Var n)} (hreg : ∀ q < len, (regions q).fv ⊆ S) :
    (RFormula.and (RFormula.and ϕinv (envLR domL domR))
        (mvRegionR mv regions len)).varsR
      ⊆ (ϕinv.varsR ∪ domR.fv) ∪ ({mv} ∪ S) := by
  have h : (RFormula.and (RFormula.and ϕinv (envLR domL domR))
        (mvRegionR mv regions len)).varsR
      = (ϕinv.varsR ∪ (envLR domL domR).varsR) ∪ (mvRegionR mv regions len).varsR := rfl
  rw [h, envLR_varsR]
  refine Set.union_subset (Set.subset_union_left) ?_
  have hmv : (mvRegionR mv regions len).varsR = (mvRegion mv regions len).fv := rfl
  rw [hmv]
  exact fun v hv => Or.inr (mvRegion_fv_sub mv regions len hreg hv)

/-- **The `hddF` discharger, R-shape**: guard-gated windows on the left, the region
conjunct on the right (regions read only right variables). -/
theorem hddF_multiR (Gr : SearchGraph (Var n)) (a b : Fin n) (dt : ℝ)
    (leftData : List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (regions : ℕ → Formula (Var n))
    (ϕinv : RFormula (Var n)) (domL domR : Formula (Var n)) (hab : a ≠ b)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
      d.2.2.1.fv ⊆ range Lv)
    (hreg : ∀ q < Gr.modes.length, (regions q).fv ⊆ range Rv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv) :
    Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
          gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
          gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 b dt d.2.2.2 (hL d hd).1
        (hL d hd).2.1 (hL d hd).2.2
    · intro v hv
      rcases ψmultiR_varsL_sub _ regions Gr.modes.length ϕinv domL domR hv with hv | hv
      · exact Or.inr (hinvL hv)
      · exact Or.inr (hdomLv hv)
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyU_sub Gr _ htt hRv hv with hv | hv
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv
    · intro v hv
      rcases ψmultiR_varsR_sub _ regions Gr.modes.length ϕinv domL domR hreg hv
        with (hv | hv) | (hv | hv)
      · exact Or.inr (hinvR hv)
      · exact Or.inr (hdomRv hv)
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv

end RelCertifier
