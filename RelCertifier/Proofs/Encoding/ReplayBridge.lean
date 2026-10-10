/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cover replays, carried to the paper's left automaton

A cover replay answers a GATED left window: the window's own guard test puts the left inside
its guard at the window's start, which a reposition pack before the first joint segment
assumes (`dynPre`'s domain carries the left guard). The carried-over benchmarks state their
left automaton with plain windows and the lowered IR guards on the edges (`LeftAut.ofP`); a
guarded left edge (`?guard_t ; window_t`) is a run of the gated window of `t`, so the generic
bridge `theorem3_leftAut_of_choiceR` applies to a Theorem 3 proved over the choice of the
gated windows (`ofP_hsim_gated`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.Proofs.Encoding.ReplayEngine

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- The gated windows of plain window data and the edges' guards. -/
noncomputable def gatedData (guards : List (Formula (Var n)))
    (data : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ)) :
    List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ) :=
  List.zipWith (fun g d => (g, d.1, d.2.1, d.2.2)) guards data

/-- **A guarded left edge is a run of the gated window.** -/
theorem ofP_hsim_gated (data : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (guards : List (Formula (Var n))) (tg : Var n) (dt : ℝ) (next : List (List ℕ))
    (hlen : guards.length = data.length) :
    ∀ t < (LeftAut.ofP data guards tg dt next).numModes, ∀ σ ν,
      Formula.sat ((LeftAut.ofP data guards tg dt next).guard t) σ →
      Program.sem ((LeftAut.ofP data guards tg dt next).window t) σ ν →
      Program.sem (bigChoice ((gatedData guards data).map (fun d =>
        gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2))) σ ν := by
  intro t ht σ ν hg hw
  rw [LeftAut.ofP_numModes] at ht
  have htg : t < guards.length := by omega
  have hz : t < (gatedData guards data).length := by
    simp [gatedData, List.length_zipWith, hlen, ht]
  have hmem : (gatedData guards data).map (fun d =>
      gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2) ≠ [] →
      gwindowSeg guards[t] (leftBlock data[t].1) data[t].2.1 tg dt data[t].2.2 ∈
        (gatedData guards data).map (fun d =>
          gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2) := by
    intro _
    refine List.mem_map.mpr ⟨(guards[t], data[t].1, data[t].2.1, data[t].2.2), ?_, rfl⟩
    have := List.getElem_mem hz
    simpa [gatedData, List.getElem_zipWith] using this
  refine sem_bigChoice_of_mem (hmem (by
    intro h; rw [List.map_eq_nil_iff] at h; rw [h] at hz; simp at hz)) ?_
  refine ⟨σ, ⟨rfl, ?_⟩, ?_⟩
  · have : (LeftAut.ofP data guards tg dt next).guard t = guards[t] := by
      simp only [LeftAut.guard, LeftAut.ofP]
      rw [List.getD_eq_getElem _ _ htg]
    rwa [this] at hg
  · have : (LeftAut.ofP data guards tg dt next).window t =
        windowSeg (leftBlock data[t].1) data[t].2.1 tg dt data[t].2.2 := by
      simp only [LeftAut.window, LeftAut.ofP]
      rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
    rwa [this] at hw

/-- The gated windows of guarded window data whose own guard component is `⊤` (the
carried-over `LeftAut.ofGI` data), with the edges' guards in its place. -/
noncomputable def gatedDataGI (guards : List (Formula (Var n)))
    (data : List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ)) :
    List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ) :=
  List.zipWith (fun g d => (g, d.2.1, d.2.2.1, d.2.2.2)) guards data

/-- **A guarded left edge of `LeftAut.ofGI` data is a run of the gated window**, when the data's
own guard components are `⊤`. -/
theorem ofGI_hsim_gated (data : List (Formula (Var n) × (Fin n → Term (Var n)) ×
      Formula (Var n) × ℕ))
    (guards : List (Formula (Var n))) (tg : Var n) (dt : ℝ) (next : List (List ℕ))
    (hlen : guards.length = data.length) (htt : ∀ d ∈ data, d.1 = Formula.tt) :
    ∀ t < (LeftAut.ofGI data guards tg dt next).numModes, ∀ σ ν,
      Formula.sat ((LeftAut.ofGI data guards tg dt next).guard t) σ →
      Program.sem ((LeftAut.ofGI data guards tg dt next).window t) σ ν →
      Program.sem (bigChoice ((gatedDataGI guards data).map (fun d =>
        gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2))) σ ν := by
  intro t ht σ ν hg hw
  rw [LeftAut.ofGI_numModes] at ht
  have htg : t < guards.length := by omega
  have hz : t < (gatedDataGI guards data).length := by
    simp [gatedDataGI, List.length_zipWith, hlen, ht]
  refine sem_bigChoice_of_mem (p := gwindowSeg guards[t] (leftBlock data[t].2.1) data[t].2.2.1
    tg dt data[t].2.2.2) ?_ ?_
  · refine List.mem_map.mpr ⟨(guards[t], data[t].2.1, data[t].2.2.1, data[t].2.2.2), ?_, rfl⟩
    have := List.getElem_mem hz
    simpa [gatedDataGI, List.getElem_zipWith] using this
  · have hgt : (LeftAut.ofGI data guards tg dt next).guard t = guards[t] := by
      simp only [LeftAut.guard, LeftAut.ofGI]
      rw [List.getD_eq_getElem _ _ htg]
    have hwt : (LeftAut.ofGI data guards tg dt next).window t =
        gwindowSeg Formula.tt (leftBlock data[t].2.1) data[t].2.2.1 tg dt data[t].2.2.2 := by
      simp only [LeftAut.window, LeftAut.ofGI]
      rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map,
        htt _ (List.getElem_mem ht)]
    rw [hgt] at hg
    rw [hwt] at hw
    obtain ⟨κ, ⟨rfl, -⟩, hrun⟩ := hw
    exact ⟨σ, ⟨rfl, hg⟩, hrun⟩

end RelCertifier
