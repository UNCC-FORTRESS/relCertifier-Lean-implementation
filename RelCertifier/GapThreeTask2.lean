/-
GAP 3, Task 2 — assumed → derived. Discharge `RightProjAlign` from `graphOf`'s structure.

GAP 1/2 took `RightProjAlign` as an **assumed** hypothesis tying the abstract graphs `Gj`/`Gr`. With
`Gj := graphOf_Gj L R lam mL` and `Gr := graphOf_Gr R lam`, `RightProjAlign` is now a **theorem** —
`RightProjAlign_from_graphOf` proves it from `graphOf`'s per-`mR` structure (the alignment: each `Gr`
mode and its paired `Gj` mode come from the SAME `R.modes[q]`, so `m'.sys = rightBlock`, `mj.sys =
jointSys`, `mj.jointOK = true`, matching edges — all by `rfl`/unfolding). What remains are the honest
**CSF framework side-conditions** (dynamics-independence `hdisj`, domain own-vars `hφR`, duration
existence `HExistSeg`) + `R`-well-formedness (`next` non-empty, in-range) — exactly the boundary the
single-flow pipeline already carries (`certified_relational`'s `hExist`/`hdisj`), NOT `RightProjAlign`
re-assumed. So `RightProjAlign` leaves the hypothesis list; the structural alignment is derived.

(`EmitSegs` — the per-residence mode-switch **sequences** — is the runtime cover's search output, the
emit boundary; it is discharged in Task 3 from `cgReal`, not here.)
-/
import RelCertifier.GapThreeFoundation
import RelCertifier.BridgeDischarge

namespace RelCertifier
open DL

variable {n : ℕ}

/-- **Task 2 — `RightProjAlign` derived from `graphOf`.** The per-mode alignment holds by construction
(both `Gr` and `Gj(mL)` read the same `R.modes[q]`); only the CSF side-conditions + `R`-wf are carried
(`hside`), exactly as the single-flow pipeline carries `hExist`/`hdisj`. `RightProjAlign` is a theorem
here, not an assumption. -/
theorem RightProjAlign_from_graphOf (L R : HybridAut n) (g : Term (Var n)) (mv : Var n)
    (lam : Term (Var n)) (mL : HybridMode n)
    (hside : ∀ (q : ℕ) (mR : HybridMode n), R.modes[q]? = some mR →
      Disjoint ((leftBlock mL.dyn).boundSet ∪ (leftBlock mL.dyn).readVars)
               ((rightBlock mR.dyn lam).boundSet ∪ (rightBlock mR.dyn lam).readVars) ∧
      mR.dom.fv ⊆ (rightBlock mR.dyn lam).boundSet ∪ (rightBlock mR.dyn lam).readVars ∧
      (∀ ν, HExistSeg mL.dyn mR.dyn lam mL.dom mR.dom ν) ∧
      mR.next ≠ [] ∧ (∀ tgt ∈ mR.next, tgt < R.modes.length)) :
    RightProjAlign (graphOf_Gj L R lam mL) (graphOf_Gr R lam) g mv mL.dyn mL.dom lam := by
  intro q m' hm'
  -- extract the underlying R-mode `mR` at index q
  simp only [SearchGraph.modeAt, graphOf_Gr, List.getElem?_map] at hm'
  cases hq : R.modes[q]? with
  | none => rw [hq] at hm'; simp at hm'
  | some mR =>
      rw [hq] at hm'; simp only [Option.map_some, Option.some.injEq] at hm'
      obtain ⟨hdisj, hφR, hES, hnext, hrange⟩ := hside q mR hq
      have hqlt : q < R.modes.length := by
        have := List.getElem?_eq_some_iff.mp hq; exact this.1
      -- a declared ⊤-edge from q exists (next non-empty), targeting in-range
      obtain ⟨tgt0, htgt0⟩ := List.exists_mem_of_ne_nil mR.next hnext
      refine ⟨mR.dyn, mR.dom, { src := q, tgt := tgt0, guard := Formula.tt, pruned := false },
        { sys := jointSys mL.dyn mR.dyn lam, dom := Formula.and mL.dom mR.dom, weight := 1,
          dynSys := jointSys (fun _ => Term.const 0) mR.dyn lam,
          dynDomPre := Formula.and mL.dom mR.dom, dynDomPost := Formula.and mL.dom mR.dom },
        ?_, ?_, ?_, rfl, ?_, hdisj, hφR, ?_, rfl, rfl, rfl, hES⟩
      · rw [← hm']  -- m'.sys = rightBlock mR.dyn lam
      · rw [← hm']  -- m'.dom = mR.dom
      · -- the edge is in edgesFrom q
        rw [SearchGraph.edgesFrom, List.mem_filter]
        refine ⟨?_, by simp⟩
        show _ ∈ (graphOf_Gr R lam).edges
        simp only [graphOf_Gr, HybridAut.edgesOf]
        refine List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hqlt, ?_⟩
        rw [hq]
        exact List.mem_map.mpr ⟨tgt0, htgt0, rfl⟩
      · -- e.tgt < Gr.modes.length
        simp only [graphOf_Gr, List.length_map]
        exact hrange tgt0 htgt0
      · -- Gj.modeAt q = some (the joint mode)
        simp only [SearchGraph.modeAt, graphOf_Gj, List.getElem?_map, hq, Option.map_some]

end RelCertifier
