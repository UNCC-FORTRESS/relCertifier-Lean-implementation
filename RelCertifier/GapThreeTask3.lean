/-
GAP 3, Task 3 — the tooling-soundness theorem. Tie the whole chain to the ACTUAL programs L, R.

Instantiates the GAP-2 family at `graphOf(L,R)`: per left mode `mL`, `Gj := graphOf_Gj L R lam mL`
with `RightProjAlign` **derived** (Task 2's `RightProjAlign_from_graphOf`, not assumed), and its
`cert`/`EmitSegs` **emitted** per mode (the existing certified_relational boundary — `z3_unsat_sound`
at the leaf, parametric here). The conclusion's programs are `graphOf`-derived, hence about L, R's
**real** dynamics (`jointSys mL.dyn mR.dyn`, `mL.dom ∧ mR.dom`) — not `cgReal`'s placeholders.

Three confirmations (held):
1. Z3 certs enter as parameters (`cert : CoverCert (graphOf_Gj …)`), parametric — no new trust.
2. Certs about `graphOf`'s REAL dynamics — `cert`'s TYPE is `CoverCert (graphOf_Gj …)`, whose modes
   carry `jointSys mL.dyn mR.dyn` (the real L,R fields), not `cgReal`'s `sys := []`.
3. `decideCovered` (topology) is NOT load-bearing for `rvalid` (established: `rvalid_from_cert`); the
   modality comes from the per-mode `cert`s. So no `cgReal`↔`graphOf` topology-match obligation here.

`RightProjAlign` is discharged (Task 2); `EmitSegs` and `cert` are the emitted boundary.
-/
import RelCertifier.GapTwo
import RelCertifier.GapThreeTask2

namespace RelCertifier
open DL DLCalTiming DLRel Function

variable {n : ℕ}

/-- The per-left-mode CSF framework side-conditions + `R`-well-formedness that Task 2 needs to derive
`RightProjAlign` from `graphOf` (the honest boundary the single-flow pipeline already carries). -/
def graphOfSide (L R : HybridAut n) (lam : Term (Var n)) (mL : HybridMode n) : Prop :=
  ∀ (q : ℕ) (mR : HybridMode n), R.modes[q]? = some mR →
    Disjoint ((leftBlock mL.dyn).boundSet ∪ (leftBlock mL.dyn).readVars)
             ((rightBlock mR.dyn lam).boundSet ∪ (rightBlock mR.dyn lam).readVars) ∧
    mR.dom.fv ⊆ (rightBlock mR.dyn lam).boundSet ∪ (rightBlock mR.dyn lam).readVars ∧
    (∀ ν, HExistSeg mL.dyn mR.dyn lam mL.dom mR.dom ν) ∧
    mR.next ≠ [] ∧ (∀ tgt ∈ mR.next, tgt < R.modes.length)

/-- The per-left-mode freshness (`mv`/`tg` disjoint from the left block/domain). -/
def graphOfFresh (mv tg : Var n) (mL : HybridMode n) : Prop :=
  MvFrozen mL.dyn mv ∧
  mL.dom.fv ⊆ (leftBlock mL.dyn).boundSet ∪ (leftBlock mL.dyn).readVars ∧
  tg ∉ (leftBlock mL.dyn).bound ∧ tg ∉ (leftBlock mL.dyn).readVars ∧ tg ∉ mL.dom.fv

/-- Build the per-mode `FlowModeData` at `graphOf`, with `RightProjAlign` **derived** from `graphOf`'s
structure (`RightProjAlign_from_graphOf`) — the alignment is a theorem, `cert`/`EmitSegs` are emitted. -/
def graphOfFlowMode (L R : HybridAut n) (g : Term (Var n)) (mv : Var n) (lam : Term (Var n))
    (tg : Var n) (dt : ℝ) (mL : HybridMode n)
    (cert : CoverCert (graphOf_Gj L R lam mL) g) (hg : mv ∉ g.fv)
    (hside : graphOfSide L R lam mL) (hfr : graphOfFresh mv tg mL)
    (hemit : EmitSegs (graphOf_Gr R lam) g mv mL.dyn mL.dom tg dt) :
    FlowModeData (graphOf_Gr R lam) g mv lam tg dt :=
  { Gj := graphOf_Gj L R lam mL, cert := cert, fL := mL.dyn, domL := mL.dom,
    hmvL := hfr.1, hφL := hfr.2.1, htgLb := hfr.2.2.1, htgLr := hfr.2.2.2.1, htgdL := hfr.2.2.2.2,
    hRPA := RightProjAlign_from_graphOf L R g mv lam mL hside,
    hemit := hemit }

/-- **GAP 3 — the tooling-soundness theorem.** Given hybrid automata `L, R`, per left mode its emitted
`cert`/`EmitSegs` + carried CSF side-conditions, and the emitted frozen-reposition data, the
transition-faithful ∀∃ refinement modality holds over the programs **derived from L, R** (`graphOf`):
`rvalid (theorem3Form (bigChoice (L.leftProgs ++ [frozen])) (rightAutomatonBody (graphOf_Gr R lam) mv) …)`.
The modality is about L, R's **real** dynamics (via `graphOf`), the alignment is **derived** (Task 2),
`cert`/`EmitSegs` are the existing emit boundary. `#print axioms = [propext, Classical.choice,
Quot.sound]`, parametric in the emitted `cert`s (`z3_unsat_sound` at construction). -/
theorem tooling_sound (L R : HybridAut n) (g : Term (Var n)) (mv : Var n) (lam : Term (Var n))
    (tg : Var n) (dt : ℝ) (ϕinv : RFormula (Var n)) (hdt : 0 ≤ dt) (hg : mv ∉ g.fv)
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (flowModes : List (FlowModeData (graphOf_Gr R lam) g mv lam tg dt))
    (hflow : flowModes.map FlowModeData.prog = L.leftProgs)
    -- frozen reposition mode: its own emitted cert/alignment
    (Gj_repo : SearchGraph (Var n)) (cert_repo : CoverCert Gj_repo g) (domRepo : Formula (Var n))
    (hmvL0' : MvFrozen (fun _ => Term.const 0) mv)
    (hφL0' : domRepo.fv ⊆ (leftBlock (fun _ => Term.const 0)).boundSet ∪
              (leftBlock (fun _ => Term.const 0)).readVars)
    (htgLb' : tg ∉ (leftBlock (fun _ => Term.const 0)).bound)
    (htgLr' : tg ∉ (leftBlock (fun _ => Term.const 0)).readVars)
    (htgdRepo : tg ∉ domRepo.fv)
    (hRPA_dyn : RightProjAlign_dyn Gj_repo (graphOf_Gr R lam) g mv domRepo lam)
    (hemit' : EmitSegs (graphOf_Gr R lam) g mv (fun _ => Term.const 0) domRepo tg dt)
    -- shared automaton facts (over the derived right graph)
    (htgg : tg ∉ g.fv)
    (htgRight : ∀ q m, (graphOf_Gr R lam).modeAt q = some m →
      tg ∉ m.sys.bound ∧ tg ∉ m.sys.readVars ∧ tg ∉ m.sys.boundSet ∧ tg ∉ m.dom.fv)
    (hfresh : ∀ q m, (graphOf_Gr R lam).modeAt q = some m →
      mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ (graphOf_Gr R lam).edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ (graphOf_Gr R lam).edgesFrom q, e.tgt < (graphOf_Gr R lam).modes.length)
    (hd : Disjoint (Program.vars (bigChoice (L.leftProgs ++
          [Program.ode (leftBlock (fun _ => Term.const 0)) domRepo])))
        (Program.vars ((rightAutomatonBody (graphOf_Gr R lam) mv).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (bigChoice (L.leftProgs ++
            [Program.ode (leftBlock (fun _ => Term.const 0)) domRepo])))
          (Program.star (rightAutomatonBody (graphOf_Gr R lam) mv))
            (RFormula.and ϕinv (mvValidR mv (graphOf_Gr R lam).modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (L.leftProgs ++
            [Program.ode (leftBlock (fun _ => Term.const 0)) domRepo])))
          (Program.star (rightAutomatonBody (graphOf_Gr R lam) mv))
            (RFormula.and ϕinv (mvValidR mv (graphOf_Gr R lam).modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice (L.leftProgs ++
        [Program.ode (leftBlock (fun _ => Term.const 0)) domRepo]))
      (rightAutomatonBody (graphOf_Gr R lam) mv)
      (RFormula.and ϕinv (mvValidR mv (graphOf_Gr R lam).modes.length))) := by
  have hlp : flowModes.map FlowModeData.prog ++
      [Program.ode (leftBlock (fun _ => Term.const 0)) domRepo]
      = L.leftProgs ++ [Program.ode (leftBlock (fun _ => Term.const 0)) domRepo] := by
    rw [hflow]
  rw [← hlp] at hd hddF ⊢
  exact theorem3_faithful_family (graphOf_Gr R lam) g mv lam tg dt ϕinv hdt hg hψ flowModes
    Gj_repo cert_repo domRepo hmvL0' hφL0' htgLb' htgLr' htgdRepo hRPA_dyn hemit' htgg htgRight
    hfresh htt hlt _ rfl hd hddF

end RelCertifier
