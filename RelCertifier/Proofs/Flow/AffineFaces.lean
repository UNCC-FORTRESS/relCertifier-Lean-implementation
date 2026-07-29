/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L1c — affine-relaxation face invariance (the equilibrium-face class)

45 faces across 8 benchmarks have the affine self-damping shape: the field reaches
the face exactly at equilibrium (`x' = M − λ·x` with `M = λ·C` at the face `x ≤ C`,
e.g. watertank `Mid`'s `x' = 3(1 − 0.04x)` at `x = 25`), so the face is neither
strict (`Lie = 0` there) nor non-strict over any region (`Lie > 0` inside). The
UPPER-face lemma is `driven_bound_raw` (PicardBridge — the S3 driven-coordinate
bound); this file adds the LOWER mirror. Both feed the stratified existence consumer
as a final pass after the strict/growth/non-strict classes (the affine faces'
region conditioning is discharged by the already-proven classes, pointwise along
the curve).

Emitted query per face (same printer family): upper `UNSAT(region ∧ ẋ > M − λ·x)`
with `M ≤ λ·C`; lower `UNSAT(region ∧ ẋ < M − λ·x)` with `M ≥ λ·C`.

New leaf (imports `StratifiedFaces`); no upstream edits.
-/
import RelCertifier.Proofs.Flow.StratifiedFaces

namespace RelCertifier
open DL Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lower affine face** (mirror of `driven_bound_raw`): if along the curve
`odeField si ≥ M − λ·si` with `λ > 0` and `M ≥ λ·C`, then `si ≥ C` — via
`(C − si)·e^{λt}` being antitone. -/
theorem driven_bound_lo_raw {sys : ODESystem V} {r : ℝ} {Φ : ℝ → State V}
    (si : V) (lam M C : ℝ)
    (hlam : 0 < lam) (hC : lam * C ≤ M)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hdrive : ∀ t ∈ Set.Icc (0:ℝ) r, M - lam * (Φ t si) ≤ odeField sys (Φ t) si)
    (h0 : C ≤ Φ 0 si) :
    ∀ t ∈ Set.Icc (0:ℝ) r, C ≤ Φ t si := by
  set g : ℝ → ℝ := fun t => (C - Φ t si) * Real.exp (lam * t) with hg
  have hgd : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt g ((-(odeField sys (Φ t) si) + lam * (C - Φ t si))
        * Real.exp (lam * t)) (Set.Icc 0 r) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun u => C - Φ u si) (-(odeField sys (Φ t) si))
        (Set.Icc 0 r) t :=
      ((hasDerivWithinAt_pi.mp (hcurve t ht)) si).const_sub C
    have h2 : HasDerivWithinAt (fun u => Real.exp (lam * u)) (lam * Real.exp (lam * t))
        (Set.Icc 0 r) t := by
      have := (((hasDerivWithinAt_id t (Set.Icc 0 r)).const_mul lam).exp)
      simpa [mul_comm] using this
    have hm := h1.mul h2
    have heq : -(odeField sys (Φ t) si) * Real.exp (lam * t)
        + (C - Φ t si) * (lam * Real.exp (lam * t))
        = (-(odeField sys (Φ t) si) + lam * (C - Φ t si)) * Real.exp (lam * t) := by
      ring
    rw [← heq]; exact hm
  have hcont : ContinuousOn g (Set.Icc 0 r) := fun t ht => (hgd t ht).continuousWithinAt
  have hanti : AntitoneOn g (Set.Icc 0 r) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hcont (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact ((hgd x (Set.Ioo_subset_Icc_self hx)).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hxIcc := Set.Ioo_subset_Icc_self hx
      rw [((hgd x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
      have hexp : 0 < Real.exp (lam * x) := Real.exp_pos _
      have hdr := hdrive x hxIcc
      have : -(odeField sys (Φ x) si) + lam * (C - Φ x si) ≤ 0 := by
        nlinarith [hdr, hC]
      exact mul_nonpos_of_nonpos_of_nonneg this (le_of_lt hexp)
  intro t ht
  have hle := hanti (Set.left_mem_Icc.mpr (le_trans ht.1 ht.2)) ht ht.1
  simp only [hg, mul_zero, Real.exp_zero, mul_one] at hle
  have hexp : 0 < Real.exp (lam * t) := Real.exp_pos _
  have hle0 : (C - Φ t si) * Real.exp (lam * t) ≤ 0 := le_trans hle (by linarith [h0])
  have hneg : C - Φ t si ≤ 0 := by
    by_contra h; push_neg at h
    nlinarith [mul_pos h hexp, hle0]
  linarith [hneg]

end RelCertifier
