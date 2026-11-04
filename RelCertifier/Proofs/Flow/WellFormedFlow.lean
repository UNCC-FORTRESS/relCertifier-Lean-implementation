/-
`HExistSeg` as a per-mode well-formedness property of the evolution domain.

`HExistSeg` (a domain-staying right run exists for the segment duration) follows from a property of
the right mode alone: from every in-domain start, its ODE has a domain-staying solution
(`WellFormedFlow`, or its duration-bounded form `WellFormedFlowB`). Because the left run freezes the
right coordinates, the right domain still holds at the end of the left run, and the per-mode property
supplies the right witness there (`hExistSeg_of_wellFormedFlow`, `hExistSegB_of_wellFormedFlowB`).
This is the existence half of the nonblocking clause of Assumption 1, stated per flow.
-/
import RelCertifier.Proofs.Encoding.BridgeDischarge

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- **Per-mode flow well-formedness.** From every start `base` in `domR` and for every duration
`s ≥ 0`, the right block's ODE has a solution `ΦR` on `[0, s]` with `ΦR 0 = base` that follows
`rightBlock fR lam`, keeps the non-right coordinates at their `base` values, and stays in `domR`
throughout. A property of the mode `(fR, lam, domR)` alone. -/
def WellFormedFlow (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n)) : Prop :=
  ∀ (base : State (Var n)), Formula.sat domR base → ∀ (s : ℝ), 0 ≤ s →
    ∃ ΦR : ℝ → State (Var n), ΦR 0 = base ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = base x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))

/-- **Duration-bounded per-mode flow well-formedness.** As `WellFormedFlow`, but only for durations
`0 ≤ s ≤ dt` (`dt` the segment span, `ε_R/λ`). The unbounded form fails for fields that drive a
bounded coordinate out of its domain over long times (e.g. `px' = vx > 0` with `px ≤ 15`), while
this form can hold over one segment. -/
def WellFormedFlowB (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (dt : ℝ) : Prop :=
  ∀ (base : State (Var n)), Formula.sat domR base → ∀ (s : ℝ), 0 ≤ s → s ≤ dt →
    ∃ ΦR : ℝ → State (Var n), ΦR 0 = base ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = base x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))

/-- `WellFormedFlow fR lam domR` implies `WellFormedFlowB fR lam domR dt` for every `dt`. -/
theorem WellFormedFlowB_of_WellFormedFlow (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR : Formula (Var n)) (dt : ℝ) (h : WellFormedFlow fR lam domR) :
    WellFormedFlowB fR lam domR dt := fun base hb s hs _ => h base hb s hs

/-- **`HExistSeg` from `WellFormedFlow` at an in-domain start.** If `WellFormedFlow fR lam domR`,
`domR` reads no coordinate the left block evolves (`hfrz`), and `ν ⊨ domR`, then
`HExistSeg fL fR lam domL domR ν`. The left run freezes the right coordinates, so `ΦL s` agrees
with `ν` on `domR.fv` and satisfies `domR`; `WellFormedFlow` at `base = ΦL s` gives the right
witness. -/
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

/-- **Duration-bounded segment witness existence**: `HExistSeg` restricted to left durations
`0 ≤ s ≤ dt`. For every left run `ΦL` of duration `s ≤ dt` from `ν` that stays in `domL`, a run of
`rightBlock fR lam` of duration `s` exists from the left run's end state `ΦL s` that stays in `domR`.
Segments last at most the span `dt`, so this is the existence the segment proofs need. -/
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

/-- **`HExistSegB` from `WellFormedFlowB`.** If `WellFormedFlowB fR lam domR dt`, `domR` reads no
coordinate the left block evolves (`hfrz`), and `ν ⊨ domR`, then `HExistSegB fL fR lam domL domR dt ν`,
by the argument of `hExistSeg_of_wellFormedFlow` restricted to durations `s ≤ dt`. -/
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
