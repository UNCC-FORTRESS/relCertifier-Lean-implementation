/-
# The single-flow chain: discharging `Hpair` from a cover certificate

`theorem3_faithful` (`BridgeFinish.lean`) takes the per-pair certificate family `Hpair` as a
hypothesis, through `hstep_assembled`. This file derives `Hpair` from a `CoverCert`, the flow
certificates (Definition 5) that the checker validates on the cover graph.

Two graphs, related by a structural alignment:
* `Gj`, the cover search graph: its modes carry the joint product system
  `m.sys = jointSys fL fR lam` (Eq. (14)); `CoverCert.segPres` is a joint `BoxLe`.
* `Gr`, the right automaton's graph: its modes carry the right block `m'.sys = rightBlock fR lam`
  (`rightAutomatonBody` steps through `m'.sys`).
The cover certifies `Gj`; the ∀∃ modality is over `Gr`. `RightProjAlign` states that each `Gr` mode
is the right projection of a certified joint mode of `Gj`. `segment_faModal` turns the joint `BoxLe`
of `cert.segPres` into the per-pair `faModal (ode leftBlock) (ode rightBlock) (invLe g)` that
`Hpair` asks for, with no further `z3solve` hypothesis.

The discharge is certificate-level (`cert.segPres` to `segment_faModal` to `faModal`), and
`theorem3_faithful` builds the automaton run directly (`diamond_right_wrap`), so the run-level
projection lemmas (`rightReach_project`, `ode_project_right`) are not on this path.

Scope:
* one fixed left mode (`leftProgs = [ode (leftBlock fL0) domL0]`): a `CoverCert` fixes one left mode;
* joint segments only (`jointOK` right modes): right-only segments are handled by the multi-flow chain
  (`dynreposition_faModal`, `BridgeReposition.lean`);
* the alignment of `Gr` modes with `Gj` joint modes and the reified blocks, the footprint side
  conditions of `segment_faModal`, and the per-segment duration existence `hExist` are hypotheses.
-/
import RelCertifier.Proofs.Encoding.BridgeUnit2
import RelCertifier.Proofs.Encoding.BridgeFinish
import RelCertifier.Core.Reify
import RelCertifier.Checker.Cover
import RelCertifier.Checker.Cover.Coexec
import RelCertifier.Checker.Checker
import RelCertifier.Trusted.Oracle

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-- `segment_faModal`'s per-segment duration-existence side condition (`hExist`) at a state `ν`:
for every left run `ΦL` of duration `s ≥ 0` from `ν` inside `domL`, some right run `ΦR` of duration
`s` from `ΦL s` solves the right block at `lam` inside `domR`, other variables frozen. It is a
hypothesis, as in the CSF calculus (finite escape, `y' = y²`, rules out deriving it). -/
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

/-- **Where the Z3 answer enters.** If Z3 reports `unsat` on the flow query of a flow obligation
`o`, then the joint system `jointSys o.fL o.fR o.lam` preserves `o.g` on `o.domain`
(`SegPreservesOn`), by `flow_certified`. Its axioms add `z3_unsat_sound` (Appendix B.4) to the
standard three; `hpair_from_cover` takes the assembled `CoverCert` and stays parametric. -/
theorem segPres_from_flowCert (o : FlowObligation n)
    (hz3 : z3solve (flowQuery o) = Verdict.unsat) :
    SegPreservesOn o.g (jointSys o.fL o.fR o.lam) o.domain :=
  fun _ hinv => flow_certified o hz3 hinv

/-- The structural alignment of the right graph `Gr` with the cover graph `Gj`: every mode `m'` of
`Gr` at `q` is the right block `rightBlock fR lam` of a joint mode `mj` of `Gj` at `q` with
`mj.jointOK`, `mj.sys = jointSys fL0 fR lam` and `mj.dom = domL0 ∧ domR`; it also has an
unguarded in-range edge, disjoint left and right footprints, `domR` over the right block's variables,
and `HExistSeg` at every state. It carries no Z3 obligation; the flow certificate comes from
`cert`. -/
def RightProjAlign (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n)) : Prop :=
  ∀ (q : ℕ) (m' : RMode (Var n)), Gr.modeAt q = some m' →
    ∃ (fR : Fin n → Term (Var n)) (domR : Formula (Var n)) (e : REdge (Var n)) (mj : RMode (Var n)),
      m'.sys = rightBlock fR lam ∧ m'.dom = domR ∧
      e ∈ Gr.edgesFrom q ∧ e.guard = Formula.tt ∧ e.tgt < Gr.modes.length ∧
      Disjoint ((leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
               ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars) ∧
      domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars ∧
      Gj.modeAt q = some mj ∧ mj.jointOK = true ∧
      mj.sys = jointSys fL0 fR lam ∧ mj.dom = Formula.and domL0 domR ∧
      (∀ ν, HExistSeg fL0 fR lam domL0 domR ν)

/-- **`Hpair` from a cover certificate (one left mode, joint segments).** For the one left program
`ode (leftBlock fL0) domL0` and every mode `m` of `Gr`, there are blocks, domains and an unguarded
edge such that `m` runs `rightBlock fR lam'` and every state satisfying `invLe g` satisfies the
per-pair `faModal` of the left and right flows for `invLe g`. Each `faModal` comes from
`cert.segPres` (the joint flow certificate, Definition 5) through `segment_faModal`; there is no
`z3solve` hypothesis. -/
theorem hpair_from_cover
    (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n))
    (cert : CoverCert Gj g)
    (hmvL0 : mv ∉ (leftBlock fL0).bound)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (hproj : RightProjAlign Gj Gr g mv fL0 domL0 lam) :
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
  obtain ⟨fR, domR, e, mj, hsys, hdom, hef, hetg, hetv, hdisj, hφR, hmj, hjOK, hmjsys, hmjdom,
    hExist⟩ := hproj q m' hm'
  refine ⟨fL0, fR, lam, domL0, domR, e, rfl, hmvL0, hsys, hdom, hef, hetg, hetv, ?_⟩
  intro s hInv
  -- the joint BoxLe at s comes from the COVER CERTIFICATE (cert.segPres on Gj), not assumed
  have hbox := cert.segPres q mj hmj hjOK s ((sat_invLe g s).mp hInv)
  rw [hmjsys, hmjdom] at hbox
  -- decouple it into the per-pair faModal
  exact segment_faModal g fL0 fR lam domL0 domR s hdisj hφL0 hφR hbox (hExist s)

/-- **The ∀∃ claim from `cert` alone.** From the cover certificate and the alignment
`RightProjAlign`, `theorem3Form` (the form of Eq. (10)) over the one left flow and the right automaton
`rightAutomatonBody Gr mv`, with invariant `ϕinv ∧ mvValidR`, is valid (`rvalid`). No coverage
decision (`decideCovered`) is needed: the loop rule preserves the invariant over any number of
iterations, so the modality needs every joint mode certified, not a closed cover. -/
theorem rvalid_from_cert
    (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n))
    (ϕinv : RFormula (Var n))
    (cert : CoverCert Gj g)
    (hg : mv ∉ g.fv)
    (hmvL0 : mv ∉ (leftBlock fL0).bound)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (hproj : RightProjAlign Gj Gr g mv fL0 domL0 lam)
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
      (rightAutomatonBody Gr mv) (RFormula.and ϕinv (mvValidR mv Gr.modes.length))) :=
  theorem3_faithful Gr mv g [Program.ode (leftBlock fL0) domL0] ϕinv hψ hd
    (hstep_assembled Gr mv g [Program.ode (leftBlock fL0) domL0] hg
      (hpair_from_cover Gj Gr g mv fL0 domL0 lam cert hmvL0 hφL0 hproj)) hddF

/-- **Single-flow end-to-end theorem.** From the checker's verdict `decideCovered Gj fuel cfg = true`,
the cover certificate `cert`, and the alignment `RightProjAlign`, two things hold: `theorem3Form`
over the one left flow and the right automaton `rightAutomatonBody Gr mv` is valid (`rvalid`), and
from every state satisfying the invariant the co-execution invariant holds throughout
(`CoexecInvThroughout`, by `check_sound`). The first conjunct uses only `cert`
(`rvalid_from_cert`); the second uses `decideCovered`.

The theorem is parametric in `cert`, so its axioms are the standard three; `z3_unsat_sound` enters
where `cert` is constructed from Z3 answers (`segPres_from_flowCert`). -/
theorem decideCovered_implies_theorem3_faithful
    (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n) (fuel : ℕ) (cfg : Config)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n))
    (ϕinv : RFormula (Var n))
    (hchk : decideCovered Gj fuel cfg = true)
    (cert : CoverCert Gj g)
    (hg : mv ∉ g.fv)
    (hmvL0 : mv ∉ (leftBlock fL0).bound)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (hproj : RightProjAlign Gj Gr g mv fL0 domL0 lam)
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
  refine ⟨rvalid_from_cert Gj Gr g mv fL0 domL0 lam ϕinv cert hg hmvL0 hφL0 hproj hψ hd hddF,
    fun ν hinit => check_sound Gj g cert fuel cfg hchk ν hinit⟩

end RelCertifier
