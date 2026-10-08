/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Sink extension — a pruned emergency mode in the right automaton

A benchmark of the pruning suite (`docs/PRUNING.md`) declares one extra right mode (an
emergency / fallback sink: self-loop only, uncertifiable if entered) and one edge from an
existing right mode to it. The certifier prunes that edge by a non-connection
certificate (paper Section 4.3; `Trusted/NonConnQuery.lean`, `Checker/NonConn.lean`), so
the emitted cover, and the response the modal instance exhibits, never take it.

The modal statement over the ENLARGED automaton cannot keep the plain `mvValid`
bookkeeping: `mvValid mv (k+1)` admits the sink as a start mode, and from the sink the
right has no response (it can only flow with the emergency field or stand still, while
the left window moves), so that statement is false. What the non-connection certificate
licenses is the mode-REGION bookkeeping of `EnvelopeChainR.lean` with the region `⊥` at
the sink and `⊤` at every original mode (`sinkRegions`): the right is never in the sink,
and every response keeps it out. That is exactly `mvValid mv k` over the original mode
indices, stated as a region so the generic R-chain (`theorem3_faithful_multiR_LR`) carries
it through the loop.

This leaf supplies the generic pieces:

* `SearchGraph.extend` — the graph with one mode and some edges appended, and the
  transfer of every graph-shape fact the chain consumes (`modeAt`, `edgesFrom`, the `⊤`
  guards, the target bound, the `Rv`-closure, freshness);
* `sinkRegions`, with its trivial free-variable and satisfaction facts;
* `sat_faModal_monoPost` — `faModal` is monotone in its postcondition;
* `Hmulti_sink_extend` — the step provider of the ORIGINAL instance (`HmultiA`-shaped,
  `(F ∧ env)` postcondition) becomes the region-carrying provider over the extended graph:
  a start in an original mode reuses the original segment chain unchanged (its landing is
  an original mode, region `⊤`); a start in the sink is excluded by its region `⊥`.

So a pruning-suite leaf is: the extended graph, the four shape facts for the new mode,
and one application each of `Hmulti_sink_extend`, `hstep_assembled_multiR`,
`hdis_multi`, `hddF_multiR_plain` and `theorem3_faithful_multiR_LR`. No instance proof
is re-done; the pruned edge is never taken.

New leaf over `EnvelopeChainR`; no upstream edits; the three standard axioms.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainR

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## The extended graph -/

/-- `G` with one mode appended (index `G.modes.length`) and edges appended. -/
def SearchGraph.extend (G : SearchGraph (Var n)) (m : RMode (Var n))
    (es : List (REdge (Var n))) : SearchGraph (Var n) :=
  { modes := G.modes ++ [m], edges := G.edges ++ es }

theorem extend_modes_length (G : SearchGraph (Var n)) (m : RMode (Var n))
    (es : List (REdge (Var n))) :
    (G.extend m es).modes.length = G.modes.length + 1 := by
  simp [SearchGraph.extend]

/-- An original mode keeps its index and its data. -/
theorem extend_modeAt_of_orig (G : SearchGraph (Var n)) (m : RMode (Var n))
    (es : List (REdge (Var n))) {q : ℕ} {m' : RMode (Var n)}
    (h : G.modeAt q = some m') : (G.extend m es).modeAt q = some m' := by
  have hq : q < G.modes.length := by
    by_contra hge
    rw [not_lt] at hge
    have : G.modeAt q = none := by
      simp [SearchGraph.modeAt, List.getElem?_eq_none hge]
    rw [this] at h
    exact absurd h (by simp)
  simp only [SearchGraph.modeAt, SearchGraph.extend] at h ⊢
  rw [List.getElem?_append_left hq]
  exact h

/-- Every mode of the extended graph is an original one, or the appended one at index
`G.modes.length`. -/
theorem extend_modeAt_cases (G : SearchGraph (Var n)) (m : RMode (Var n))
    (es : List (REdge (Var n))) {q : ℕ} {m' : RMode (Var n)}
    (h : (G.extend m es).modeAt q = some m') :
    G.modeAt q = some m' ∨ (q = G.modes.length ∧ m' = m) := by
  simp only [SearchGraph.modeAt, SearchGraph.extend] at h
  by_cases hq : q < G.modes.length
  · left
    rw [List.getElem?_append_left hq] at h
    exact h
  · right
    rw [not_lt] at hq
    rw [List.getElem?_append_right hq] at h
    rcases Nat.lt_or_ge (q - G.modes.length) 1 with hlt | hge
    · have hz : q - G.modes.length = 0 := by omega
      rw [hz] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩
    · rw [List.getElem?_eq_none (by simpa using hge)] at h
      exact absurd h (by simp)

/-- An original edge stays an edge out of its source. -/
theorem extend_edgesFrom_of_orig (G : SearchGraph (Var n)) (m : RMode (Var n))
    (es : List (REdge (Var n))) {q : ℕ} {e : REdge (Var n)}
    (h : e ∈ G.edgesFrom q) : e ∈ (G.extend m es).edgesFrom q := by
  simp only [SearchGraph.edgesFrom, SearchGraph.extend, List.filter_append,
    List.mem_append] at h ⊢
  exact Or.inl h

/-- Every edge out of `q` in the extended graph is an original edge out of `q` or one of
the appended edges. -/
theorem extend_edgesFrom_cases (G : SearchGraph (Var n)) (m : RMode (Var n))
    (es : List (REdge (Var n))) {q : ℕ} {e : REdge (Var n)}
    (h : e ∈ (G.extend m es).edgesFrom q) : e ∈ G.edgesFrom q ∨ e ∈ es := by
  simp only [SearchGraph.edgesFrom, SearchGraph.extend, List.filter_append,
    List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_filter h)

/-! ## Transfer of the graph-shape facts -/

theorem extend_htt (G : SearchGraph (Var n)) (m : RMode (Var n)) (es : List (REdge (Var n)))
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hes : ∀ e ∈ es, e.guard = Formula.tt) :
    ∀ q, ∀ e ∈ (G.extend m es).edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  rcases extend_edgesFrom_cases G m es he with h | h
  · exact htt q e h
  · exact hes e h

theorem extend_hlt (G : SearchGraph (Var n)) (m : RMode (Var n)) (es : List (REdge (Var n)))
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hes : ∀ e ∈ es, e.tgt < G.modes.length + 1) :
    ∀ q, ∀ e ∈ (G.extend m es).edgesFrom q, e.tgt < (G.extend m es).modes.length := by
  intro q e he
  rw [extend_modes_length]
  rcases extend_edgesFrom_cases G m es he with h | h
  · exact Nat.lt_succ_of_lt (hlt q e h)
  · exact hes e h

theorem extend_hRv (G : SearchGraph (Var n)) (m : RMode (Var n)) (es : List (REdge (Var n)))
    (hRv : ∀ q m', G.modeAt q = some m' →
      m'.sys.boundSet ∪ m'.sys.readVars ∪ m'.dom.fv ⊆ range Rv)
    (hm : m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    ∀ q m', (G.extend m es).modeAt q = some m' →
      m'.sys.boundSet ∪ m'.sys.readVars ∪ m'.dom.fv ⊆ range Rv := by
  intro q m' hq
  rcases extend_modeAt_cases G m es hq with h | ⟨-, rfl⟩
  · exact hRv q m' h
  · exact hm

/-- Freshness of `mv` for every mode of the extended graph, from the `Rv`-closure. -/
theorem extend_hfresh (G : SearchGraph (Var n)) (m : RMode (Var n))
    (es : List (REdge (Var n))) (a : Fin n)
    (hRv : ∀ q m', (G.extend m es).modeAt q = some m' →
      m'.sys.boundSet ∪ m'.sys.readVars ∪ m'.dom.fv ⊆ range Rv) :
    ∀ q m', (G.extend m es).modeAt q = some m' →
      ((Side.Aux, a) : Var n) ∉ (Program.ode m'.sys m'.dom).fv := by
  intro q m' hm hmv
  exact aux_notin_range_Rv a (hRv q m' hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The sink regions -/

/-- `⊤` on the original mode indices `q < k`, `⊥` elsewhere (the sink). -/
def sinkRegions (k : ℕ) : ℕ → Formula (Var n) :=
  fun q => if q < k then Formula.tt else Formula.neg Formula.tt

theorem sinkRegions_fv (k q : ℕ) : (sinkRegions (n := n) k q).fv = ∅ := by
  unfold sinkRegions
  split <;> simp [Formula.fv]

theorem sinkRegions_fv_sub (k q : ℕ) {S : Set (Var n)} :
    (sinkRegions (n := n) k q).fv ⊆ S := by
  rw [sinkRegions_fv]; exact Set.empty_subset S

theorem notMem_sinkRegions_fv (k q : ℕ) (v : Var n) : v ∉ (sinkRegions (n := n) k q).fv := by
  rw [sinkRegions_fv]; exact Set.notMem_empty v

theorem sat_sinkRegions_of_lt {k q : ℕ} (h : q < k) (σ : State (Var n)) :
    Formula.sat (sinkRegions (n := n) k q) σ := by
  simp only [sinkRegions, if_pos h]
  trivial

theorem not_sat_sinkRegions {k q : ℕ} (h : ¬ q < k) (σ : State (Var n)) :
    ¬ Formula.sat (sinkRegions (n := n) k q) σ := by
  simp [sinkRegions, h, Formula.sat]

/-! ## `faModal` is monotone in its postcondition -/

theorem sat_faModal_monoPost {P Q : Program (Var n)} {φ ψ : Formula (Var n)}
    {σ : State (Var n)}
    (h : ∀ μ, Formula.sat φ μ → Formula.sat ψ μ)
    (hQ : Formula.sat (faModal (Equiv.refl (Var n)) P Q φ) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P Q ψ) σ := by
  unfold faModal at hQ ⊢
  rw [sat_box] at hQ ⊢
  intro ν hν
  have hdia := hQ ν hν
  rw [sat_diamond] at hdia ⊢
  push Not at hdia ⊢
  obtain ⟨μ, hsem, hφ⟩ := hdia
  exact ⟨μ, hsem, h μ hφ⟩

/-! ## The provider transfer -/

/-- **The original step provider, over the extended graph, with the sink regions.** A
start in an original mode answers with the original segment chain (lifted edge by edge),
landing in an original mode where the region is `⊤`; a start in the sink is vacuous
(its region is `⊥`). -/
theorem Hmulti_sink_extend (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n)) (leftProgs : List (Program (Var n)))
    (m : RMode (Var n)) (es : List (REdge (Var n)))
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (H : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and F env)) σ) :
    ∀ P ∈ leftProgs, ∀ (q : ℕ), q < (G.extend m es).modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ →
      Formula.sat (sinkRegions G.modes.length q) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, (G.extend m es).modeAt s.1 = some s.2.1 ∧
          s.2.2 ∈ (G.extend m es).edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and F env)
            (sinkRegions G.modes.length (qfOf segs q)))) σ := by
  intro P hP q _ σ hmv hσ hreg
  by_cases hq : q < G.modes.length
  · obtain ⟨segs, halign, hchain, hhead, hfa⟩ := H P hP q hq σ hmv hσ
    refine ⟨segs, ?_, hchain, hhead, ?_⟩
    · intro s hs
      exact ⟨extend_modeAt_of_orig G m es (halign s hs).1,
        extend_edgesFrom_of_orig G m es (halign s hs).2⟩
    · refine sat_faModal_monoPost ?_ hfa
      intro μ hμ
      exact ⟨hμ, sat_sinkRegions_of_lt (qfOf_lt G hlt segs halign q hq) μ⟩
  · exact absurd hreg (not_sat_sinkRegions hq σ)

end RelCertifier
