/-
`HExistSeg` re-cast as a per-mode well-formedness property of the evolution domain.

The insight: `HExistSeg` ("a domain-staying right trajectory exists for the segment duration") is not a
fact to be *derived through the multi-flow fold* — it is a **well-formedness property of the mode's
evolution domain**: from any in-domain start, the mode's ODE has a domain-staying solution. Stated once
per mode (`WellFormedFlow`), checked at the model level (ODE-existence + domain-invariance), it
discharges `HExistSeg` at any in-domain state via the cross-side masking seam — no guards, no
`RightReach`, no cross-switch reasoning inside the fold.

`hExistSeg_of_wellFormedFlow` is the discharge: `WellFormedFlow fR lam domR` (the per-mode right-flow
existence) + `sat domR ν` (the start is in-domain) ⟹ `HExistSeg fL fR lam domL domR ν`. It generalizes
the banked `hExist_from_rover` (which is one field-specific `WellFormedFlow` witness) to any field whose
domain is a valid flow-region.
-/
import RelCertifier.BridgeDischarge

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- **Per-mode flow well-formedness (the re-cast of `HExistSeg`).** From every in-domain start `base`,
the right block's ODE has a **domain-staying** solution for every duration `s ≥ 0`: `ΦR` starts at
`base`, follows `rightBlock fR lam`, freezes the non-right coordinates, and stays in `domR` throughout.
This is a property of the mode `(fR, lam, domR)` alone — ODE-existence (Picard, intrinsic) ∧
domain-invariance (`domR` forward-invariant under the field). Checkable per mode, at the model level. -/
def WellFormedFlow (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n)) : Prop :=
  ∀ (base : State (Var n)), Formula.sat domR base → ∀ (s : ℝ), 0 ≤ s →
    ∃ ΦR : ℝ → State (Var n), ΦR 0 = base ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = base x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))

/-- **Bounded-`dt` per-mode flow well-formedness — the HONEST, Z3-sourced replacement for the `∀s` form.**
Identical to `WellFormedFlow` but the domain-staying is required ONLY up to the segment budget `s ≤ dt`
(`dt = ε_r/λ`, the cover's fixed cut). The `∀s` form (above) is FALSE for growing-bounded fields (a
coordinate `px' = vx > 0` bounded `px ≤ 15` exits over unbounded time — `WellFormedFlow_rover_false`);
this bounded form is what the tool ACTUALLY checks per segment via Z3 (`SegPreserves`), and it is TRUE for
those fields over one short segment on loose domains (reachable travel `≤ bound_T·v_max` stays interior).
It bottoms out at the same `z3_unsat_sound` leaf — no new trust; it is not a `∀base` Lean derivation but
the per-segment domain check the cover performs. -/
def WellFormedFlowB (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (dt : ℝ) : Prop :=
  ∀ (base : State (Var n)), Formula.sat domR base → ∀ (s : ℝ), 0 ≤ s → s ≤ dt →
    ∃ ΦR : ℝ → State (Var n), ΦR 0 = base ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = base x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))

/-- `WellFormedFlow` (∀s) trivially implies the bounded form (just drop the `s ≤ dt` witnesses). So the
bounded form is WEAKER — the honest, satisfiable version — and any `∀s` witness (e.g. at `domR = ⊤`)
still gives it. -/
theorem WellFormedFlowB_of_WellFormedFlow (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR : Formula (Var n)) (dt : ℝ) (h : WellFormedFlow fR lam domR) :
    WellFormedFlowB fR lam domR dt := fun base hb s hs _ => h base hb s hs

/-- **The discharge — `HExistSeg` from `WellFormedFlow` at an in-domain start.** Given the per-mode
`WellFormedFlow` (right-flow existence + domain-staying), that `domR` reads only coordinates the left
block does not evolve (`hfrz`, the L/R split — `domR` is a right-side domain), and that the segment
start `ν` is in the domain (`hνdom`), `HExistSeg` holds. The left run masks (freezes) the right
coordinates, so `ΦL s` agrees with `ν` on `domR.fv`, hence `sat domR (ΦL s)`; `WellFormedFlow` at
`base = ΦL s` supplies the right witness. No fold, no guard, no cross-switch reasoning. -/
theorem hExistSeg_of_wellFormedFlow (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hwf : WellFormedFlow fR lam domR)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hνdom : Formula.sat domR ν) :
    HExistSeg fL fR lam domL domR ν := by
  intro s ΦL hs0 hΦL0 _ hmaskL _
  -- ΦL s agrees with ν on domR.fv (right coords frozen by the left run's mask), so sat domR (ΦL s)
  have hΦLs_dom : Formula.sat domR (ΦL s) := by
    have heqon : Set.EqOn ν (ΦL s) domR.fv := by
      intro x hx
      have hxL : x ∉ (leftBlock fL).bound := hfrz x hx
      exact (hmaskL s (right_mem_Icc.mpr hs0) x hxL).symm
    exact (Formula.coincidence domR heqon).mp hνdom
  -- WellFormedFlow at base = ΦL s (in domR) gives the right witness
  obtain ⟨ΦR, hΦR0, hRder, hRmask, hRdom⟩ := hwf (ΦL s) hΦLs_dom s hs0
  exact ⟨ΦR, hΦR0, hRder, hRmask, hRdom⟩

/-- **Bounded-`dt` within-segment `∃`-witness** — `HExistSeg` restricted to segment durations `s ≤ dt`.
The landing/cover segments are duration-bounded (fixed cut `dt = ε_r/λ`), so this is exactly the
within-segment existence the proof needs — and, unlike the `∀s` `HExistSeg`, it is dischargeable from the
HONEST bounded-`dt` domain-invariance `WellFormedFlowB` (which is Z3-checked and TRUE for growing-bounded
fields, vs the false `∀s` `WellFormedFlow`). -/
def HExistSegB (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
    (dt : ℝ) (ν : State (Var n)) : Prop :=
  ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → s ≤ dt → ΦL 0 = ν →
    (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
        HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
    (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL t x = ν x) →
    (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
    ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))

/-- **The bounded discharge — `HExistSegB` from `WellFormedFlowB`.** Same masking/coincidence argument as
`hExistSeg_of_wellFormedFlow`, but sourced from the HONEST bounded-`dt` domain-invariance: for a segment of
duration `s ≤ dt`, the left run masks the right coordinates (so `ΦL s ∈ domR`), and `WellFormedFlowB` at
`base = ΦL s` (also bounded by `s ≤ dt`) supplies the domain-staying right witness. This replaces the
`∀s` discharge (`hExistSeg_of_wellFormedFlow`, which needed the false `∀s` `WellFormedFlow`) with one that
rests only on what the tool actually Z3-checks. -/
theorem hExistSegB_of_wellFormedFlowB (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (dt : ℝ) (ν : State (Var n))
    (hwf : WellFormedFlowB fR lam domR dt)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hνdom : Formula.sat domR ν) :
    HExistSegB fL fR lam domL domR dt ν := by
  intro s ΦL hs0 hsdt hΦL0 _ hmaskL _
  have hΦLs_dom : Formula.sat domR (ΦL s) := by
    have heqon : Set.EqOn ν (ΦL s) domR.fv := by
      intro x hx
      exact (hmaskL s (right_mem_Icc.mpr hs0) x (hfrz x hx)).symm
    exact (Formula.coincidence domR heqon).mp hνdom
  obtain ⟨ΦR, hΦR0, hRder, hRmask, hRdom⟩ := hwf (ΦL s) hΦLs_dom s hs0 hsdt
  exact ⟨ΦR, hΦR0, hRder, hRmask, hRdom⟩

end RelCertifier
