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

end RelCertifier
