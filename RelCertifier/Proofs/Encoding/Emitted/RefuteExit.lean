/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Refutations, part 3: short-time flow existence and first-order exit

The analysis behind kind B (a component pushed out by the left flow). From a state `μ` in the
interior of the evolve domain, where a smooth function `G` is `≥ 0` and its Lie derivative along
the field is `> 0`, an integral curve of the field exists on a short interval `[0, t]`, `t > 0`
as small as asked, staying in the domain, at whose end `G > 0`:

* existence: Mathlib's C¹ local existence (`ContDiffAt.exists_forall_mem_closedBall_…`) for the
  polynomial field (`odeField_contDiff`, `Proofs/Flow/PicardBridge.lean`), as in
  `sem_ode_exists_local`;
* exit: `G ∘ Φ` has derivative `Lie sys G (Φ 0) > 0` within `[0, r]` at `0`
  (`hasDeriv_g_along_flow`), so its slope from `0` is eventually positive.

`curve_coord` reads a coordinate whose field is a constant `c` (`0` off the bound set, `1` for a
clock) along an integral curve: it moves by `c · s`.
-/
import RelCertifier.Proofs.Flow.PicardBridge

set_option autoImplicit false

namespace RelCertifier

open DL Set Metric Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A coordinate whose field is the constant `c` moves by `c · s` along an integral curve. -/
theorem curve_coord {sys : ODESystem V} {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Icc 0 r)) (x : V) (c : ℝ)
    (hx : ∀ y, odeField sys y x = c) : ∀ s ∈ Icc (0:ℝ) r, Φ s x = Φ 0 x + c * s := by
  have hcx : ∀ s ∈ Icc (0:ℝ) r,
      HasDerivWithinAt (fun u => Φ u x - c * u) 0 (Icc 0 r) s := by
    intro s hs
    have hpi : HasDerivWithinAt (fun u => Φ u x) (odeField sys (Φ s) x) (Icc 0 r) s :=
      (hasDerivWithinAt_pi.mp (hcurve s hs)) x
    rw [hx] at hpi
    have hlin : HasDerivWithinAt (fun u : ℝ => c * u) c (Icc 0 r) s := by
      simpa using (hasDerivWithinAt_id s (Icc 0 r)).const_mul c
    have h2 := hpi.sub hlin
    simp only [sub_self] at h2
    exact h2
  have hconst : ∀ s ∈ Icc (0:ℝ) r, Φ s x - c * s = Φ 0 x - c * 0 := by
    have hdiffOn : DifferentiableOn ℝ (fun u => Φ u x - c * u) (Icc 0 r) :=
      fun s hs => (hcx s hs).differentiableWithinAt
    have hd0 : ∀ s ∈ Ico (0:ℝ) r, derivWithin (fun u => Φ u x - c * u) (Icc 0 r) s = 0 := by
      intro s hs
      have hlt : (0:ℝ) < r := lt_of_le_of_lt hs.1 hs.2
      exact (hcx s ⟨hs.1, le_of_lt hs.2⟩).derivWithin
        ((uniqueDiffOn_Icc hlt) s ⟨hs.1, le_of_lt hs.2⟩)
    exact constant_of_derivWithin_zero hdiffOn hd0
  intro s hs
  have := hconst s hs
  linarith

/-- **Short-time existence with first-order exit.** -/
theorem exit_run {sys : ODESystem V} (hwf : sys.WellFormed) {dom : Formula V} {μ : State V}
    (hdom : {x | Formula.sat dom x} ∈ 𝓝 μ) {G : State V → ℝ} (hG : Differentiable ℝ G)
    (hG0 : 0 ≤ G μ) (hlie : 0 < Lie sys G μ) {T : ℝ} (hT : 0 < T) :
    ∃ t, 0 < t ∧ t ≤ T ∧ ∃ Φ : ℝ → State V, Φ 0 = μ ∧
      IsIntegralCurveOn Φ (fun _ => odeField sys) (Icc 0 t) ∧
      (∀ s ∈ Icc (0:ℝ) t, Formula.sat dom (Φ s)) ∧ 0 < G (Φ t) := by
  obtain ⟨α, hα0, ε, hε, hderiv⟩ :=
    ((odeField_contDiff sys).contDiffAt (x := μ) |>.of_le (by exact_mod_cast le_top)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have h0mem : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by constructor <;> linarith
  have hcont0 : ContinuousAt α 0 := (hderiv 0 h0mem).continuousAt
  have hpre : {t : ℝ | α t ∈ {x : State V | Formula.sat dom x}} ∈ 𝓝 (0 : ℝ) :=
    hcont0.preimage_mem_nhds (by simpa [hα0] using hdom)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  set r : ℝ := min (ε / 2) (δ / 2) with hr_def
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  have hcurve : IsIntegralCurveOn α (fun _ => odeField sys) (Icc 0 r) := by
    intro t ht
    have htioo : t ∈ Ioo (0 - ε) (0 + ε) := by
      constructor
      · linarith [ht.1]
      · linarith [min_le_left (ε/2) (δ/2), ht.2]
    exact (hderiv t htioo).hasDerivWithinAt
  have hdomr : ∀ t ∈ Icc (0:ℝ) r, Formula.sat dom (α t) := by
    intro t ht
    have htdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [min_le_right (ε/2) (δ/2), ht.2]
    exact hδsub htdist
  -- the slope of `G ∘ α` from `0` tends to the positive Lie derivative
  have hd := hasDeriv_g_along_flow hwf hG hcurve (t := 0) ⟨le_rfl, hrpos.le⟩
  rw [hα0] at hd
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp hd)
  rw [Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT hrpos] at hslope
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
      0 < slope (fun s => G (α s)) 0 t ∧ t < min r T ∧ 0 < t := by
    have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < min r T :=
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hrpos hT))
    have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
    exact ((hslope.eventually (lt_mem_nhds hlie)).and (h2.and h3))
  obtain ⟨t, hsl, htlt, htpos⟩ := hev.exists
  have htr : t ≤ r := le_of_lt (lt_of_lt_of_le htlt (min_le_left _ _))
  have htT : t ≤ T := le_of_lt (lt_of_lt_of_le htlt (min_le_right _ _))
  refine ⟨t, htpos, htT, α, hα0, hcurve.mono (Icc_subset_Icc_right htr),
    fun s hs => hdomr s ⟨hs.1, le_trans hs.2 htr⟩, ?_⟩
  rw [slope_def_field, hα0, sub_zero] at hsl
  have := (div_pos_iff_of_pos_right htpos).mp hsl
  linarith

end RelCertifier
