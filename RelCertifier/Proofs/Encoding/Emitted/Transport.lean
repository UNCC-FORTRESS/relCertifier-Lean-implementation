/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Assumption 1, transported to the generic right automaton

The suite's `WellFormedR` lemmas are stated over each benchmark's standalone right automaton
(its modes listed, its edges a literal list faithful to the file's `next` lists). The generic
automaton `grOf` has the same modes (same fields, same domain) and at least the same edge
targets; Assumption 1 transports.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLCalTiming Parse Run Set

variable {n : ℕ}

theorem wellFormedRIn_transport {G G' : SearchGraph (Var n)} {guard guard' : ℕ → Formula (Var n)}
    {reg : Formula (Var n)} {ε : ℝ} (h : WellFormedRIn G guard reg ε)
    (hlen : G'.modes.length ≤ G.modes.length)
    (hmode : ∀ q m', G'.modeAt q = some m' →
      ∃ m, G.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom)
    (hguard : ∀ q, guard' q = guard q)
    (hedge : ∀ q e, e ∈ G.edgesFrom q → ∃ e' ∈ G'.edgesFrom q, e'.tgt = e.tgt) :
    WellFormedRIn G' guard' reg ε := by
  intro q hq m' hm' x hg hd hreg
  obtain ⟨m, hm, hsys, hdom⟩ := hmode q m' hm'
  have := h q (lt_of_lt_of_le hq hlen) m hm x (by rw [← hguard]; exact hg)
    (by rw [hdom]; exact hd) hreg
  rw [hsys, hdom] at this
  refine ⟨this.1, fun t Φ ht H => ?_⟩
  obtain ⟨e, he, hs⟩ := this.2 t Φ ht H
  obtain ⟨e', he', htgt⟩ := hedge q e he
  exact ⟨e', he', by rw [hguard, htgt]; exact hs⟩

/-- A region kept by every mode's flow of one automaton is kept by the other's (same modes). -/
theorem regionInvariant_transport {G G' : SearchGraph (Var n)} {reg : Formula (Var n)}
    (h : RegionInvariant G reg)
    (hmode : ∀ q m', G'.modeAt q = some m' →
      ∃ m, G.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom) :
    RegionInvariant G' reg := by
  intro q m' hm' x t Φ hx H
  obtain ⟨m, hm, hsys, hdom⟩ := hmode q m' hm'
  exact h q m hm x t Φ hx (by rw [hsys, hdom]; exact H)

theorem wellFormedR_transport {G G' : SearchGraph (Var n)} {guard guard' : ℕ → Formula (Var n)}
    {ε : ℝ} (h : WellFormedR G guard ε) (hlen : G'.modes.length ≤ G.modes.length)
    (hmode : ∀ q m', G'.modeAt q = some m' →
      ∃ m, G.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom)
    (hguard : ∀ q, guard' q = guard q)
    (hedge : ∀ q e, e ∈ G.edgesFrom q → ∃ e' ∈ G'.edgesFrom q, e'.tgt = e.tgt) :
    WellFormedR G' guard' ε := by
  intro q hq m' hm' x hg hd htt
  obtain ⟨m, hm, hsys, hdom⟩ := hmode q m' hm'
  have := h q (lt_of_lt_of_le hq hlen) m hm x (by rw [← hguard]; exact hg)
    (by rw [hdom]; exact hd) htt
  rw [hsys, hdom] at this
  refine ⟨this.1, fun t Φ ht H => ?_⟩
  obtain ⟨e, he, hs⟩ := this.2 t Φ ht H
  obtain ⟨e', he', htgt⟩ := hedge q e he
  exact ⟨e', he', by rw [hguard, htgt]; exact hs⟩

/-- The edge correspondence for a standalone automaton whose edges are a literal list
faithful to the file (`edgeList_eq_IR`). -/
theorem edges_transport {p : PProblem} {G : SearchGraph (Var n)} {pr : String → String → Bool}
    {L : List (ℕ × ℕ)} {f : ℕ × ℕ → REdge (Var n)} (hG : G.edges = L.map f)
    (hf : ∀ e, (f e).src = e.1 ∧ (f e).tgt = e.2)
    (hL : L = (List.range (nR p)).flatMap (fun q =>
      (mRof p q).next.map (fun nm => (q, tgtIdx p nm)))) :
    ∀ q e, e ∈ G.edgesFrom q → ∃ e' ∈ (grOf p n pr).edgesFrom q, e'.tgt = e.tgt := by
  intro q e he
  have hmem : e ∈ G.edges := List.mem_of_mem_filter he
  have hsrc : e.src = q := by
    unfold SearchGraph.edgesFrom at he
    rw [List.mem_filter] at he
    exact decide_eq_true_eq.mp he.2
  rw [hG] at hmem
  obtain ⟨pr', hpr', rfl⟩ := List.mem_map.mp hmem
  rw [hL] at hpr'
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hpr'
  obtain ⟨q', hq', nm, hnm, rfl⟩ := hpr'
  have hsq : q' = q := by rw [← hsrc, (hf _).1]
  subst hsq
  exact ⟨edgeOf p n pr q' nm, edge_mem_grOf hq' hnm, by rw [(hf _).2]; rfl⟩

/-- Every edge of a standalone automaton names a declared successor of its source mode, by
index (decided in the kernel; the guards are never read). -/
def edgesCovered (p : PProblem) (G : SearchGraph (Var n)) : Bool :=
  G.edges.all (fun e => (mRof p e.src).next.any (fun nm => tgtIdx p nm == e.tgt))

theorem edges_transport_check {p : PProblem} {G : SearchGraph (Var n)}
    {pr : String → String → Bool} (h : edgesCovered p G = true) (hsrc : ∀ e ∈ G.edges, e.src < nR p) :
    ∀ q e, e ∈ G.edgesFrom q → ∃ e' ∈ (grOf p n pr).edgesFrom q, e'.tgt = e.tgt := by
  intro q e he
  have hmem : e ∈ G.edges := List.mem_of_mem_filter he
  have hq : e.src = q := by
    unfold SearchGraph.edgesFrom at he
    rw [List.mem_filter] at he
    exact decide_eq_true_eq.mp he.2
  simp only [edgesCovered, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨nm, hnm, htgt⟩ := h e hmem
  have hlt := hsrc e hmem
  rw [hq] at hnm hlt
  exact ⟨edgeOf p n pr q nm, edge_mem_grOf hlt hnm, by rw [← hq]; exact htgt⟩

/-- The sources of a standalone automaton's edges are in range (decided in the kernel). -/
def edgesSrcOK (p : PProblem) (G : SearchGraph (Var n)) : Bool :=
  G.edges.all (fun e => decide (e.src < nR p))

theorem edgesSrcOK_sound {p : PProblem} {G : SearchGraph (Var n)} (h : edgesSrcOK p G = true) :
    ∀ e ∈ G.edges, e.src < nR p := by
  simp only [edgesSrcOK, List.all_eq_true, decide_eq_true_eq] at h
  exact h

end Emitted
end RelCertifier
