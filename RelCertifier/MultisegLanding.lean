/-
`multiseg_landing` — the landing-selected joint-tree-walk ∃-witness (statement-first core).

The redesign that ELIMINATES `WFBoundary` clause 2 by construction: instead of folding a pre-fixed
segment list (`multiseg_het`), walk `Covered`'s ∀-successor tree, selecting at each junction the branch
whose domain the constructed right-flow endpoint `μ_R` landed in. Because the state stays in its mode's
domain (ODE domain-constraint) and successor domains OVERLAP (verified per benchmark — shared/nested
evolve-domains), the switch is an interior overlap point: `μ_R ∈ domR_next` holds BY SELECTION (no
guard, `⊤`-switch free, no first-passage).

This file lands the composable core statement-first:
* `LandingH` — the (trivially-true, ODE-constrained) landing hypothesis.
* `segment_landing` — the per-node dispatch: an in-domain entry + `WellFormedFlow` (existence) +
  the cover's joint box discharge one segment's `faModal` via `segment_faModal`. Confirms pieces 3
  (`WellFormedFlow`, banked) and 4 (`segment_faModal`, banked) COMPOSE sorry-free, with the in-domain
  entry `hνdom` the landing supplies by construction.
The full `multiseg_landing` induction over `Covered` (composing these via `faModal_seq`/`faModal_MR`,
threading `invLe g`) is the remaining build; its per-node step is `segment_landing`.
-/
import RelCertifier.Reify
import RelCertifier.WFBoundary

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- **The landing hypothesis (trivially true from the ODE domain-constraint).** At every reachable
flow endpoint `μ` of mode `m`, `μ` is in `m`'s domain or in a successor's — the disjunction the
landing-selection case-splits. The first disjunct always holds (a run of `ode m.sys m.dom` stays in
`m.dom`), so `LandingH` is free; the second disjunct fires at interior overlap points (successor
domains overlap, per the benchmark gate), giving the switch. No guard, no reachability. -/
def LandingH (G : SearchGraph (Var n)) : Prop :=
  ∀ (q : ℕ) (m : RMode (Var n)), G.modeAt q = some m → ∀ (μ : State (Var n)),
    Formula.sat m.dom μ →
      (Formula.sat m.dom μ ∨
        ∃ q' ∈ G.retainedSucc q, ∃ m', G.modeAt q' = some m' ∧ Formula.sat m'.dom μ)

/-- **Per-node dispatch (pieces 3 + 4 compose).** One segment's `faModal`, from: the cover's joint
box (`hcert`), the per-mode flow well-formedness (`hwff`, `WellFormedFlow` — existence), the L/R split
(`hfrz`), and the IN-DOMAIN ENTRY `hνdom` (which the landing-selection supplies by construction — the
segment is entered where the flow landed, in this mode's domain). `HExistSeg` is discharged within-
segment by the banked `hExistSeg_of_wellFormedFlow`; `segment_faModal` (banked) decouples joint →
frozen-left right-response. No guard, no cross-switch `HExistSeg`, no first-passage. -/
theorem segment_landing (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys fL fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) ν)
    (hwff : WellFormedFlow fR lam domR)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hνdom : Formula.sat domR ν) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (invLe g)) ν :=
  segment_faModal g fL fR lam domL domR ν hdisj hφL hφR hcert
    (hExistSeg_of_wellFormedFlow fL fR lam domL domR ν hwff hfrz hνdom)

/-- **The overlap gate (checked per benchmark).** Two mode domains overlap non-trivially: some state
satisfies both. This is the load-bearing condition that makes the landing switch an INTERIOR point
(no first-passage) — the flow reaches a state in both `domCur` and `domSucc`, where the switch fires.
Verified for the whole suite (shared/nested evolve-domains). Stated as a checkable hypothesis, not a
hidden assumption. -/
def SuccDomOverlap (domCur domSucc : Formula (Var n)) : Prop :=
  ∃ μ : State (Var n), Formula.sat domCur μ ∧ Formula.sat domSucc μ

/-- **Clause 2 by construction — the discharge is a CHECK at the constructed endpoint, not an
assumption over all states.** The next segment's in-domain entry `hνdom : sat domSucc μ_R` is verified
at the SPECIFIC `μ_R` the current segment's right run landed at (a decidable membership at a concrete
state), then fed to `segment_landing`. Contrast the `∀ν HExistSeg` / `WFBoundary` clause 2, which
assumed the guard at every state: here it is *decided* at the one landing state. So `HExistSeg` for the
next segment discharges from a per-endpoint check — no guard premise, no first-passage, no `∀ν`. This
lemma is `segment_landing` at the landed state `μ_R`, making explicit that its `hνdom` is the
by-construction landing check. -/
theorem segment_landing_at (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (μ_R : State (Var n))
    (hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys fL fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) μ_R)
    (hwff : WellFormedFlow fR lam domR)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hland : Formula.sat domR μ_R) :   -- CHECKED at the constructed landing endpoint (clause 2 by construction)
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (invLe g)) μ_R :=
  segment_landing g fL fR lam domL domR μ_R hdisj hφL hφR hcert hwff hfrz hland

/-- **The flow-diamond — the input to `diamond_right_wrap` for the star step.** From `WellFormedFlow`
(the frozen-left right run exists in `domR` — existence, banked), an in-domain start `hν`, and the
frozen-left flow's `g`-preservation `hg` (`BoxLe`, from `cert.repoDynPres`/`DI_nonstrict`), the right
flow's diamond holds: `⟨ode rightBlock domR⟩(invLe g)`. This is the per-segment `∃`-right run with
`g≤0` at its endpoint — `diamond_right_wrap` then wraps it into one `rightAutomatonBody` body-step
(the star's unit), with the mode landing-selected. -/
theorem wff_to_diamond (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR : Formula (Var n)) (ν : State (Var n))
    (hwff : WellFormedFlow fR lam domR) (hν : Formula.sat domR ν)
    (hg : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν) :
    Formula.sat (Formula.diamond (Program.ode (rightBlock fR lam) domR) (invLe g)) ν := by
  obtain ⟨ΦR, hΦR0, hder, hmask, hdom⟩ := hwff ν hν 1 (by norm_num)
  have hsem : Program.sem (Program.ode (rightBlock fR lam) domR) ν (ΦR 1) :=
    ⟨1, ΦR, by norm_num, hΦR0, rfl, hder, hmask, hdom⟩
  rw [diamond_sem]
  exact ⟨ΦR 1, hsem, by rw [sat_invLe]; exact hg _ hsem⟩

end RelCertifier
