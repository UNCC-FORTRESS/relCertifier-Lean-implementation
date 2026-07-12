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
The cover certifies `Gj`; the ∀∃ modality is over `Gr`, linked to `Gj` by the structural
`RightProjAlign` (each `Gr` mode is the R-projection of a certified `Gj` joint mode — the same
per-mode relation `rightReach_project.hmode` uses). `segment_faModal` is the CERTIFICATE decoupler:
a joint `BoxLe` from `cert.segPres` becomes `faModal (ode leftBlock) (ode rightBlock) (invLe g)`,
exactly `Hpair`'s per-pair certificate for `Gr` — sourced from `cert`, no `z3solve` re-assumed.

Note on the run-level projection lemmas (`rightReach_project`, `ode_project_right`, the witness
`rightReach_is_R_real_run`): those project co-execution *runs* (a `RightReach` / joint ODE run to a
right-only one). The discharge here is CERTIFICATE-level (`cert.segPres` `BoxLe` → `segment_faModal`
→ `faModal`), and `theorem3_faithful` builds the automaton run directly (`diamond_right_wrap`), so the
run-level lemmas are not on this path; `RightProjAlign` is their `hmode` alignment carried as the
structural link. See the acceptance discussion in the composed theorem's doc.

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

/-- The **structural** joint↔right projection alignment (`hproj`): each R_real-graph mode `m'` at `q`
is the right-projection of a certified joint mode `mj` of the cover graph — same `q`, `m'.sys` the
right block of `mj.sys = jointSys …`. This is the SAME per-mode relation `rightReach_project.hmode`
consumes (`Gr` is `Gj`'s R-projection), and it carries NO Z3 obligation — only the reification shapes,
`jointOK`, edge facts, footprint disjointness, and the CSF `hExist` side-condition. Legitimate to carry
(a structural graph fact); the flow certificate itself comes from `cert`, not from here. -/
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

/-- **The Link-2 discharge (single left mode, flow modes).** Produce the per-pair certificate family
`Hpair` that `hstep_assembled` consumes — each per-pair `faModal` sourced from **`cert.segPres`** (the
cover certificate the checker validated on `Gj`, carried to the R-projected mode `m'` by the structural
alignment) via `segment_faModal`. NOT assumed: there is **no `z3solve = unsat` hypothesis** here — the
flow certificate is `cert`, and `cert` is load-bearing (delete it and the per-pair `faModal` is gone). -/
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

/-- **The `rvalid` half, from `cert` alone — no `decideCovered`.** Discharges the transition-faithful
∀∃ modality from the cover certificate + the structural R-projection alignment, with NO `hchk`, `fuel`,
or `cfg`. Its very existence is the honest finding: `decideCovered` (the coverage/budget DECISION) is
**not** load-bearing for `rvalid` — the `faModal_LOCK` loop preserves the invariant over any number of
iterations, so the modality needs every mode CERTIFIED (`cert.segPres`), not the cover to close. `cert`
IS load-bearing (it is a required argument feeding `hpair_from_cover`). -/
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

/-- **The end-to-end theorem — the two islands in one signature.** From the checker's positive
verdict on the joint cover graph (`decideCovered Gj = true`), its cover certificate (`cert`, where
the Z3 leaf lives), and the **structural** R-projection alignment `RightProjAlign` (no Z3 obligation),
the paper's ∀∃ refinement modality over the *real* automaton holds at every bi-state — AND the
co-execution invariant holds throughout (Island A). `hstep`/`Hpair` are DISCHARGED from **`cert`**
(`hpair_from_cover` draws each per-pair `faModal` from `cert.segPres`, the cover certificate the
checker validates), NOT assumed — there is no `z3solve = unsat` hypothesis.

`#print axioms = [propext, Classical.choice, Quot.sound]`: the theorem is *parametric in the cover
certificate* `cert`, so the Z3 leaf does not appear here — it enters when `cert` is CONSTRUCTED,
per-mode, by `segPres_from_flowCert`/`flow_certified` (that grounding has the 4th axiom
`z3_unsat_sound`). There is no form with BOTH no-`z3solve`-hypothesis AND `z3_unsat_sound`-in-axioms:
a `Prop` `CoverCert` cannot apply the axiom (3 axioms); applying it needs the raw obligation (the
illegitimate hypothesis). Taking `cert : CoverCert` is the legitimate choice.

Load-bearing: `cert` is required for the `rvalid` conjunct (delete it → `hpair_from_cover` has no
`segPres` → no `faModal`). `hchk` (`decideCovered`) is load-bearing for the **throughput** conjunct
(`CoexecInvThroughout`, via `check_sound`), NOT for `rvalid`: the `faModal_LOCK` loop preserves the
invariant over any number of iterations, so the ∀∃ modality needs every mode CERTIFIED (`cert.segPres`),
not the coverage/budget DECISION. rvalid rests on the flow-certificate half of the checker (`cert`);
the coverage half (`decideCovered`) supplies the throughput guarantee. -/
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
