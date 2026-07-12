/-
Part B — the missing Link 2: discharge `hstep`/`Hpair` from the cover, closing the two islands.

`theorem3_faithful` (Island B) took `hstep` as a hypothesis; `hstep_assembled` reduces it to the
per-pair certificate family `Hpair`. Nothing discharged `Hpair` from the checker — the seam
`check_sound`'s cover ⟹ `hstep` was a comment (Phase-1 Link 2). This file writes it.

Architecture (verified against the code — two graphs, related by the projection lemmas):
* `Gj` — the **cover** search graph: its modes carry the JOINT system `m.sys = jointSys fL fR lam`
  (`RightReach.evolve` runs `ode m.sys`; `CoverCert.segPres` is a joint `BoxLe`).
* `Gr` — the **R_real** search graph: its modes carry the RIGHT-only block `m'.sys = rightBlock fR lam`
  (`rightAutomatonBody`/`R_real` step through `m'.sys`).
The cover certifies `Gj`; the ∀∃ modality is over `Gr`. `segment_faModal` is the decoupler between
them: a joint `BoxLe` (from the per-segment Z3 flow cert `z3solve (flowQuery …) = unsat`, via
`flow_certified`/`segPres_from_flowCert` — the same object as `cert.segPres`) becomes
`faModal (ode leftBlock) (ode rightBlock) (invLe g)` — exactly `Hpair`'s per-pair certificate for `Gr`.
The composed `decideCovered_implies_theorem3_faithful` therefore bottoms out at `z3_unsat_sound`.

Scope of this discharge (each an honest boundary — see the module note at the bottom):
* ONE fixed left mode (`leftProgs = [ode (leftBlock fL0) domL0]`) — a single `CoverCert` fixes one
  left mode; the full left automaton is a family of covers.
* ALL-`jointOK` right modes (flow segments) — reposition modes (`jointOK = false`) carry a static
  `repoPres`, not a flow `faModal`, so the flow wrap does not reach them.
* The reification alignment (`Gr` mode ↔ `Gj` joint mode ↔ reified `leftBlock`/`rightBlock`), the
  `segment_faModal` footprint side-conditions, and per-segment `hExist` are carried as hypotheses —
  the framework side-conditions, exactly as `certified_relational` carries `hExist`/`hdisj`/`Bridges`.
-/
import RelCertifier.BridgeUnit2
import RelCertifier.BridgeFinish
import RelCertifier.Reify
import RelCertifier.Cover
import RelCertifier.Cover.Coexec
import RelCertifier.Checker
import RelCertifier.Oracle

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-- `segment_faModal`'s per-segment duration-existence side-condition (`hExist`), packaged at a
state `ν`. Carried, exactly as the CSF calculus ships it (finite-escape countermodel `y'=y²`). -/
def HExistSeg (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
    (ν : State (Var n)) : Prop :=
  ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
    (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
        HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
    (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL t x = ν x) →
    (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
    ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))

/-- **Where the Z3 leaf enters.** A `CoverCert`'s per-segment `SegPreserves` is not an assumption:
each is `flow_certified` applied to a `z3solve (flowQuery o) = unsat` — so `#print axioms` on this
grounding is `[propext, Classical.choice, Quot.sound, z3_unsat_sound]`, the exact boundary of
`certified_relational`. `hpair_from_cover` takes the assembled `CoverCert` (hence is parametric,
3 axioms); this lemma exhibits that the certificate it consumes bottoms out at the one Z3 leaf. -/
theorem segPres_from_flowCert (o : FlowObligation n)
    (hz3 : z3solve (flowQuery o) = Verdict.unsat) :
    SegPreservesOn o.g (jointSys o.fL o.fR o.lam) o.domain :=
  fun _ hinv => flow_certified o hz3 hinv

/-- **The Link-2 discharge (single left mode, flow modes).** From the reification alignment to the
R_real graph `Gr` and the per-segment **Z3 flow certificate** (`z3solve (flowQuery …) = unsat`),
produce the per-pair certificate family `Hpair` that `hstep_assembled` consumes — the per-pair
`faModal` coming from `flow_certified` (the one Z3 leaf) via `segment_faModal`, NOT assumed. This is
exactly `cert.segPres` unfolded to the raw Z3 obligation (`segPres_from_flowCert`), so the leaf shows
in the axioms — the same boundary as `certified_relational`. -/
theorem hpair_from_cover
    (Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n))
    (hmvL0 : mv ∉ (leftBlock fL0).bound)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (halign : ∀ (q : ℕ) (m' : RMode (Var n)), Gr.modeAt q = some m' →
      ∃ (fR : Fin n → Term (Var n)) (domR : Formula (Var n)) (e : REdge (Var n)),
        m'.sys = rightBlock fR lam ∧ m'.dom = domR ∧
        e ∈ Gr.edgesFrom q ∧ e.guard = Formula.tt ∧ e.tgt < Gr.modes.length ∧
        Disjoint ((leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
                 ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars) ∧
        domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars ∧
        z3solve (flowQuery (⟨g, fL0, fR, lam, Formula.and domL0 domR⟩ : FlowObligation n))
          = Verdict.unsat ∧
        (∀ ν, HExistSeg fL0 fR lam domL0 domR ν)) :
    ∀ P ∈ [Program.ode (leftBlock fL0) domL0], ∀ (q : ℕ) (m : RMode (Var n)),
      Gr.modeAt q = some m →
      ∃ (fL fR : Fin n → Term (Var n)) (lam' : Term (Var n)) (domL domR : Formula (Var n))
        (e : REdge (Var n)),
        P = Program.ode (leftBlock fL) domL ∧ mv ∉ (leftBlock fL).bound ∧
        m.sys = rightBlock fR lam' ∧ m.dom = domR ∧
        e ∈ Gr.edgesFrom q ∧ e.guard = Formula.tt ∧ e.tgt < Gr.modes.length ∧
        (∀ s, Formula.sat (invLe g) s → Formula.sat (faModal (Equiv.refl (Var n))
          (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam') domR) (invLe g)) s) := by
  intro P hP q m' hm'
  simp only [List.mem_singleton] at hP; subst hP
  obtain ⟨fR, domR, e, hsys, hdom, hef, hetg, hetv, hdisj, hφR, hz3, hExist⟩ := halign q m' hm'
  refine ⟨fL0, fR, lam, domL0, domR, e, rfl, hmvL0, hsys, hdom, hef, hetg, hetv, ?_⟩
  intro s hInv
  -- the joint BoxLe at s, from the per-segment Z3 flow certificate (the one trusted leaf)
  have hbox := segPres_from_flowCert
    (⟨g, fL0, fR, lam, Formula.and domL0 domR⟩ : FlowObligation n) hz3 s
    ((sat_invLe g s).mp hInv)
  -- decouple it into the per-pair faModal
  exact segment_faModal g fL0 fR lam domL0 domR s hdisj hφL0 hφR hbox (hExist s)

/-- **The end-to-end theorem — the two islands in one signature.** From the checker's positive
verdict on the joint cover graph (`decideCovered Gj = true`), its cover certificate (`cert`, where
the Z3 leaf lives), and the reification alignment to the R_real graph, the paper's ∀∃ refinement
modality over the *real* automaton holds at every bi-state — AND the co-execution invariant holds
throughout (Island A). `hstep`/`Hpair` are DISCHARGED (from the per-segment Z3 flow certs via
`hpair_from_cover`), not assumed. `#print axioms` = `[propext, Classical.choice, Quot.sound,
z3_unsat_sound]` — the two islands in one signature, bottoming out at the single Z3 leaf. -/
theorem decideCovered_implies_theorem3_faithful
    (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n) (fuel : ℕ) (cfg : Config)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n))
    (ϕinv : RFormula (Var n))
    (hchk : decideCovered Gj fuel cfg = true)
    (cert : CoverCert Gj g)
    (hg : mv ∉ g.fv)
    (hmvL0 : mv ∉ (leftBlock fL0).bound)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (halign : ∀ (q : ℕ) (m' : RMode (Var n)), Gr.modeAt q = some m' →
      ∃ (fR : Fin n → Term (Var n)) (domR : Formula (Var n)) (e : REdge (Var n)),
        m'.sys = rightBlock fR lam ∧ m'.dom = domR ∧
        e ∈ Gr.edgesFrom q ∧ e.guard = Formula.tt ∧ e.tgt < Gr.modes.length ∧
        Disjoint ((leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
                 ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars) ∧
        domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars ∧
        z3solve (flowQuery (⟨g, fL0, fR, lam, Formula.and domL0 domR⟩ : FlowObligation n))
          = Verdict.unsat ∧
        (∀ ν, HExistSeg fL0 fR lam domL0 domR ν))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hd : Disjoint (Program.vars (bigChoice [Program.ode (leftBlock fL0) domL0]))
        (Program.vars ((rightAutomatonBody Gr mv).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (bigChoice [Program.ode (leftBlock fL0) domL0]))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice [Program.ode (leftBlock fL0) domL0]))
          (Program.star (rightAutomatonBody Gr mv))
            (RFormula.and ϕinv (mvValidR mv Gr.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice [Program.ode (leftBlock fL0) domL0])
        (rightAutomatonBody Gr mv) (RFormula.and ϕinv (mvValidR mv Gr.modes.length)))
    ∧ (∀ ν, InvHolds g ν → CoexecInvThroughout Gj g cfg ν) := by
  refine ⟨?_, fun ν hinit => check_sound Gj g cert fuel cfg hchk ν hinit⟩
  -- discharge Hpair from the per-segment Z3 certs, then run the Island-B chain (units 1-5)
  have Hpair := hpair_from_cover Gr g mv fL0 domL0 lam hmvL0 hφL0 halign
  have hstep := hstep_assembled Gr mv g [Program.ode (leftBlock fL0) domL0] hg Hpair
  exact theorem3_faithful Gr mv g [Program.ode (leftBlock fL0) domL0] ϕinv hψ hd hstep hddF

end RelCertifier
