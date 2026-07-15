/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Tool-level connection — Z3 verdict ⟹ the paper's ∀∃ (single-sync fragment)

NOTE (transition-faithful variant). `certified_relational` here proves the ∀∃ modality over the
**flat** right choice-star `(⨆ right modes)*` — a valid but *weaker* over-approximation of the
paper's automaton (its ∃-right ranges over any mode sequence, not only declared transitions). The
**transition-faithful** landing is `BridgeFinish.theorem3_faithful`, whose right program is
`R_real = star(rightAutomatonBody)` (jumps only along declared edges). Both rest on the same
`z3_unsat_sound` leaf; `theorem3_faithful` is the one that pins the ∃-right to the real automaton.

Wires the running tool's inputs into the proven CSF-side chain (`reified_relational`). The one
junction needing care is `pair_faModal` (Step 2): the per-segment `faModal` is discharged from a
**Z3 UNSAT on the evolution-domain flow query** — the *same* query the tool checks and the proof
consumes, with no runtime-labeling gap.

**The query junction (checker-construction lesson).** `flow_certified` (Oracle.lean) applies
`z3solve` to `flowQuery o` and yields `BoxLe (ode (jointSys o.fL o.fR o.lam) o.domain)` — for the
*same* obligation `o`. The runtime builds `o.domain = domL ∧ domR` from `mL.evolve`/`mR.evolve`
(`flowQueryIR`/`segParts`, evolution domain — guards removed). So:
* the query the proof consumes (`flowQuery o`, `o.domain = domL∧domR`) **is** the query Z3 checks;
* `hdom : o.domain = domL ∧ domR` pins it to the evolution domain (a guard-narrowed domain would
  be a *different* `o.domain`, breaking `hdom` — the guard-bug class is a mismatch, not a false
  discharge);
* `z3_unsat_sound` is the only leaf; no new trusted surface.

`hExist` (the CSF duration-existence side-condition) is carried explicitly, as everywhere.
-/
import RelCertifier.Proofs.Encoding.Reification
import RelCertifier.Trusted.Oracle
import RelCertifier.Trusted.Run

namespace RelCertifier

open DL DLCalTiming DLRel RelCertifier.Parse RelCertifier.Run

/-- **Step 2 — the `hpair` discharge (the trust-critical junction).** From a Z3 UNSAT on the
**evolution-domain** flow query `flowQuery o` (with `o.domain = domL ∧ domR`, `hdom`), the CSF
duration-existence side-condition `hExist` (per state), and the structural independence/support
hypotheses, the per-segment `faModal` holds at **every** invariant-satisfying state — exactly the
per-pair obligation `reified_relational` consumes.

The `BoxLe` comes from `flow_certified` (`z3_unsat_sound` + `flow_cert_sound`) on `flowQuery o`;
`hdom` rewrites its domain to `domL ∧ domR`; `segment_faModal` finishes. The query is
evolution-domain by `hdom` and is literally `flowQuery o` — the same one Z3 checked. -/
theorem pair_faModal {n : ℕ} (o : FlowObligation n) (domL domR : Formula (Var n))
    (hdom : o.domain = Formula.and domL domR)
    (hdisj : Disjoint ((leftBlock o.fL).boundSet ∪ (leftBlock o.fL).readVars)
                      ((rightBlock o.fR o.lam).boundSet ∪ (rightBlock o.fR o.lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock o.fL).boundSet ∪ (leftBlock o.fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock o.fR o.lam).boundSet ∪ (rightBlock o.fR o.lam).readVars)
    (hz3 : z3solve (flowQuery o) = Verdict.unsat)
    (hExist : ∀ (ν : State (Var n)), ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ leftBlock o.fL,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Set.Icc 0 s) t) →
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock o.fL).bound → ΦL t x = ν x) →
        (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ rightBlock o.fR o.lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Set.Icc 0 s) t) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock o.fR o.lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat domR (ΦR t))) :
    ∀ σ, Formula.sat (invLe o.g) σ →
      Formula.sat (faModal (Equiv.refl (Var n))
        (Program.ode (leftBlock o.fL) domL) (Program.ode (rightBlock o.fR o.lam) domR)
        (invLe o.g)) σ := by
  intro σ hσ
  rw [sat_invLe] at hσ
  have hcert : BoxLe (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) σ := flow_certified o hz3 hσ
  rw [hdom] at hcert
  exact segment_faModal o.g o.fL o.fR o.lam domL domR σ hdisj hφL hφR hcert (hExist σ)

/-- A single-sync certified segment: one left mode ↦ one right mode, with the evolution-domain
Z3 verdict and the per-pair support hypotheses. The `hz3` field is the tool's UNSAT on the
**evolution-domain** flow query `flowQuery ⟨g, fL, fR, lam, domL ∧ domR⟩`. -/
structure CertSeg (n : ℕ) (g : Term (Var n)) where
  fL : Fin n → Term (Var n)
  fR : Fin n → Term (Var n)
  lam : Term (Var n)
  domL : Formula (Var n)
  domR : Formula (Var n)
  hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                   ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
  hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars
  hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars
  hz3 : z3solve (flowQuery ⟨g, fL, fR, lam, Formula.and domL domR⟩) = Verdict.unsat
  hExist : ∀ (ν : State (Var n)), ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
      (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
          HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Set.Icc 0 s) t) →
      (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL t x = ν x) →
      (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
      ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
            HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Set.Icc 0 s) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat domR (ΦR t))

/-- The reified left/right host programs of a certified segment (evolution-domain ODE modes). -/
def CertSeg.leftProg {n : ℕ} {g : Term (Var n)} (s : CertSeg n g) : Program (Var n) :=
  Program.ode (leftBlock s.fL) s.domL
def CertSeg.rightProg {n : ℕ} {g : Term (Var n)} (s : CertSeg n g) : Program (Var n) :=
  Program.ode (rightBlock s.fR s.lam) s.domR

/-- **Tool-level end-to-end (single-sync fragment).** Given a list of single-sync certified
segments (each backed by an evolution-domain Z3 UNSAT), the relational invariant `ψ` (with
`encode id ψ = invLe g`), and the structural `Bridges`/disjointness, the paper's ∀∃ relational
modality over the looped choice-automata holds at the bi-state. This is what the tool's
`CERTIFIED` (on a fully-single-sync benchmark, `decideCovered = true`) provably produces —
`[|(L*,R*)⟩⟩ ψ`, the paper's Theorem-3 conclusion (**flat** `R*`).

The `decideCovered = true ⟹` connection is no longer comment-only: for the **transition-faithful**
`R_real`, `BridgeDischarge.decideCovered_implies_theorem3_faithful` proves it as a theorem
(`decideCovered = true` in the hypotheses, `rvalid(theorem3Form … faithful)` in the conclusion,
`hstep` discharged from the per-segment Z3 flow certs, axioms + `z3_unsat_sound`).

Residual TCB: the parser (lowering `PProblem → CertSeg`s) and Z3 `unsat` (`z3_unsat_sound`);
`hExist` is CSF's explicit duration-existence side-condition (true for the bounded domains). -/
theorem certified_relational {n : ℕ} (g : Term (Var n)) (segs : List (CertSeg n g))
    (ψ : RFormula (Var n)) (ν : State (Var n)) (bs : BiState (Var n))
    (hψ : encode (Equiv.refl (Var n)) ψ = invLe g)
    (hd : Disjoint (Program.vars (bigChoice (segs.map CertSeg.leftProg)))
        (Program.vars ((bigChoice (segs.map CertSeg.rightProg)).rename (Equiv.refl (Var n)))))
    (hinv : Formula.sat (encode (Equiv.refl (Var n)) ψ) ν)
    (hdd : Disjoint (faShape (Program.star (bigChoice (segs.map CertSeg.leftProg)))
          (Program.star (bigChoice (segs.map CertSeg.rightProg))) ψ).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (segs.map CertSeg.leftProg)))
          (Program.star (bigChoice (segs.map CertSeg.rightProg))) ψ).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star (bigChoice (segs.map CertSeg.leftProg)))
          (Program.star (bigChoice (segs.map CertSeg.rightProg))) ψ).varsL
        (faShape (Program.star (bigChoice (segs.map CertSeg.leftProg)))
          (Program.star (bigChoice (segs.map CertSeg.rightProg))) ψ).varsR bs ν) :
    RFormula.sat (faShape (Program.star (bigChoice (segs.map CertSeg.leftProg)))
      (Program.star (bigChoice (segs.map CertSeg.rightProg))) ψ) bs := by
  refine reified_relational (segs.map CertSeg.leftProg) (segs.map CertSeg.rightProg)
    ψ ν bs ?_ hd hinv hdd hb
  intro P hP
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hP
  refine ⟨s.rightProg, List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
  intro σ hσ
  rw [hψ] at hσ ⊢
  exact pair_faModal ⟨g, s.fL, s.fR, s.lam, Formula.and s.domL s.domR⟩ s.domL s.domR rfl
    s.hdisj s.hφL s.hφR s.hz3 s.hExist σ hσ

/-! ## Parser emit — `PProblem → CertSeg`, and its irreducible trust boundary

A **complete pure** `PProblem → CertSeg` is impossible by design: `CertSeg.hz3 : z3solve … = unsat`
mentions the **opaque** `z3solve` (realized by the Z3 process in IO — kept opaque so the pure
kernel never depends on Z3), so its truth is not a kernel value. `hExist` is the CSF analytic
side-condition. So the emit splits: the **data** (`fL/fR/lam/domL/domR`) is a pure lowering of the
parsed model; the **proofs** (`hz3` at the Z3 boundary, `hExist` the side-condition, `hdisj` the
per-benchmark independence) enter through the smart constructor. This is the correct structure —
the same `z3_unsat_sound` boundary the whole tool rests on. -/

/-- Pure lowered **data** of one single-sync segment (no proofs). -/
structure SegData (n : ℕ) where
  fL : Fin n → Term (Var n)
  fR : Fin n → Term (Var n)
  lam : Term (Var n)
  domL : Formula (Var n)
  domR : Formula (Var n)

/-- **The parser emit (data).** Lower a `(leftMode, rightMode, λ)` triple of the parsed model to
`SegData` — dynamics via `dynOf`, evolution domains via `lowerF` (the **evolve** fields, guards
removed — guard-bug class barred), IR→host via `toHost`. `none` if any component is unlowerable
(→ the tool's `ERROR`, never a silent certify). This is the actual `PProblem`-level lowering; the
`CertSeg` proofs are supplied separately (below). -/
def lowerSeg (vars : List String) (n : ℕ) (mL mR : PMode) (lam : ℚ) : Option (SegData n) := do
  let fLi ← dynOf vars n Side.L mL
  let fRi ← dynOf vars n Side.R mR
  let domLi ← lowerF vars n Side.L mL.evolve
  let domRi ← lowerF vars n Side.R mR.evolve
  some { fL := fun i => (fLi i).toHost, fR := fun i => (fRi i).toHost,
         lam := Term.const (lam : ℝ), domL := domLi.toHost, domR := domRi.toHost }

/-- **Smart constructor completing the data to a `CertSeg`.** Takes the lowered `SegData` plus the
irreducible boundary inputs — `hz3` (the Z3 verdict on the **evolution-domain** query
`flowQuery ⟨g, d.fL, d.fR, d.lam, domL∧domR⟩`, realized by the Z3 process via `z3_unsat_sound`),
`hExist` (the CSF duration-existence side-condition), and the structural `hdisj`/`hφL`/`hφR` (the
per-benchmark independence + support, checkable from the lowering). Makes the trust boundary
explicit: data is pure, proofs enter here. -/
def SegData.toCertSeg {n : ℕ} (d : SegData n) (g : Term (Var n))
    (hdisj : Disjoint ((leftBlock d.fL).boundSet ∪ (leftBlock d.fL).readVars)
                      ((rightBlock d.fR d.lam).boundSet ∪ (rightBlock d.fR d.lam).readVars))
    (hφL : d.domL.fv ⊆ (leftBlock d.fL).boundSet ∪ (leftBlock d.fL).readVars)
    (hφR : d.domR.fv ⊆ (rightBlock d.fR d.lam).boundSet ∪ (rightBlock d.fR d.lam).readVars)
    (hz3 : z3solve (flowQuery ⟨g, d.fL, d.fR, d.lam, Formula.and d.domL d.domR⟩) = Verdict.unsat)
    (hExist : ∀ (ν : State (Var n)), ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ leftBlock d.fL,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Set.Icc 0 s) t) →
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock d.fL).bound → ΦL t x = ν x) →
        (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat d.domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ rightBlock d.fR d.lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Set.Icc 0 s) t) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock d.fR d.lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat d.domR (ΦR t))) :
    CertSeg n g :=
  { fL := d.fL, fR := d.fR, lam := d.lam, domL := d.domL, domR := d.domR,
    hdisj := hdisj, hφL := hφL, hφR := hφR, hz3 := hz3, hExist := hExist }

end RelCertifier
