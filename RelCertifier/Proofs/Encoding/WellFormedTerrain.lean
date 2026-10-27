/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Assumption 1 for the terrain chain (`MUD → GRAVEL → PAVED`), proved once

The right models of the terrain chain (`rover_terrain_2to4`, `rover_terrain_4to6`,
`rover_terrain_6to12`) share one shape: three bands of the odometer `s` (`MUD` `0 ≤ s < s₁`,
`GRAVEL` `s₁ ≤ s < s₂`, `PAVED` `s ≥ s₂`), optionally with a cap `x_c ≤ c_q` on one
contraction coordinate `x_c' = k (c_q − x_c)` (the wheel-speed command `w` in `4to6`, the
motor torque state `u` in `6to12`), the odometer rate `s'` between `0` and `B` on the evolve
domain, the declared successors `MUD → {GRAVEL, MUD}`, `GRAVEL → {PAVED, GRAVEL}`,
`PAVED → {PAVED}`, and `ε_r = 1`. Since 2026-10-27 the four rover ladder rungs
(`rover_ladder_2to3`, `_3to6`, `_6to8`, `_8to12`: zones `STEEP`, `MODER`, `FLAT` with bands
`[0, 60)`, `[60, 140)`, `[140, ∞)`, no cap, `B = 8`) share the same shape and use it too.

`wellFormedR_terrain`: from the band facts and the existence of runs, `WellFormedR`.
Clause (ii) per band: the capped coordinate stays between its start and the set point (so
the band's cap is kept and implies the next band's, the set points being ordered), the
odometer does not decrease, and over one interval it grows by at most `B`, so a `MUD` run
ends below `s₁ + B ≤ s₂` (inside `MUD` or `GRAVEL`), a `GRAVEL` run ends in `GRAVEL` or
`PAVED`, and `PAVED` is forward invariant.

Clause (i) uses the explicit runs of affine cascades: `forcedSol k y₀ F` (variation of
constants, `y' = F t − k y`) and `intSol y₀ G` (`y' = G t`), and the comparison bounds
`forcedSol_between` (a forced contraction stays between its start and `F/k`) and
`mono_of_deriv_nonneg`. Z3-free.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
open DL DLCalTiming Set

/-! ## Explicit runs of affine cascades -/

/-- The solution of `y' = F t − k y`, `y 0 = y₀` (variation of constants). -/
noncomputable def forcedSol (k y0 : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(k * t)) * (y0 + ∫ τ in (0:ℝ)..t, Real.exp (k * τ) * F τ)

theorem forcedSol_zero (k y0 : ℝ) (F : ℝ → ℝ) : forcedSol k y0 F 0 = y0 := by
  simp [forcedSol]

theorem forcedSol_hasDerivAt (k y0 : ℝ) {F : ℝ → ℝ} (hF : Continuous F) (t : ℝ) :
    HasDerivAt (forcedSol k y0 F) (F t - k * forcedSol k y0 F t) t := by
  have hc : Continuous (fun τ => Real.exp (k * τ) * F τ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF
  have hI : HasDerivAt (fun u => y0 + ∫ τ in (0:ℝ)..u, Real.exp (k * τ) * F τ)
      (Real.exp (k * t) * F t) t :=
    (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add y0
  have hE : HasDerivAt (fun u => Real.exp (-(k * u))) (Real.exp (-(k * t)) * (-(k * 1))) t :=
    (((hasDerivAt_id t).const_mul k).neg).exp
  have hEE : Real.exp (-(k * t)) * Real.exp (k * t) = 1 := by
    rw [← Real.exp_add]; simp
  refine (hE.mul hI).congr_deriv ?_
  simp only [forcedSol]
  linear_combination (F t) * hEE

theorem forcedSol_continuous (k y0 : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (forcedSol k y0 F) :=
  continuous_iff_continuousAt.mpr fun t => (forcedSol_hasDerivAt k y0 hF t).continuousAt

/-- The integral `y₀ + ∫₀ᵗ G`, the solution of `y' = G t`. -/
noncomputable def intSol (y0 : ℝ) (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  y0 + ∫ τ in (0:ℝ)..t, G τ

theorem intSol_zero (y0 : ℝ) (G : ℝ → ℝ) : intSol y0 G 0 = y0 := by
  simp [intSol]

theorem intSol_hasDerivAt (y0 : ℝ) {G : ℝ → ℝ} (hG : Continuous G) (t : ℝ) :
    HasDerivAt (intSol y0 G) (G t) t :=
  (hG.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add y0

/-- A function with a nonnegative derivative on `[0, T]` does not decrease there. -/
theorem mono_of_deriv_nonneg {φ g : ℝ → ℝ} {T : ℝ} (hφ : ∀ t, HasDerivAt φ (g t) t)
    (hg : ∀ t ∈ Icc (0:ℝ) T, 0 ≤ g t) : ∀ t ∈ Icc (0:ℝ) T, φ 0 ≤ φ t := by
  have hmono : MonotoneOn φ (Icc 0 T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
      (fun t _ => (hφ t).continuousAt.continuousWithinAt)
      (fun t _ => (hφ t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hφ t).deriv]; exact hg t ⟨ht.1.le, ht.2.le⟩)
  intro t ht
  exact hmono ⟨le_refl 0, ht.1.trans ht.2⟩ ht ht.1

/-- **Upper comparison**: a forced contraction `y' = F t − k y` (`k > 0`) with `F ≤ hi` on
`[0, T]` stays at most `max y₀ (hi/k)` there. -/
theorem forced_le {φ F : ℝ → ℝ} {k hi T : ℝ} (hk : 0 < k)
    (hφ : ∀ t, HasDerivAt φ (F t - k * φ t) t) (hF : ∀ t ∈ Icc (0:ℝ) T, F t ≤ hi) :
    ∀ t ∈ Icc (0:ℝ) T, φ t ≤ max (φ 0) (hi / k) := by
  set g : ℝ → ℝ := fun t => (φ t - hi / k) * Real.exp (k * t) with hg
  have hgd : ∀ t, HasDerivAt g ((F t - hi) * Real.exp (k * t)) t := by
    intro t
    have hE : HasDerivAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1)) t :=
      ((hasDerivAt_id t).const_mul k).exp
    refine (((hφ t).sub_const (hi / k)).mul hE).congr_deriv ?_
    field_simp
    ring
  have hanti : AntitoneOn g (Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      (fun t _ => (hgd t).continuousAt.continuousWithinAt)
      (fun t _ => (hgd t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hgd t).deriv]
        have := hF t ⟨ht.1.le, ht.2.le⟩
        have he := Real.exp_pos (k * t)
        nlinarith)
  intro t ht
  have h := hanti ⟨le_refl 0, ht.1.trans ht.2⟩ ht ht.1
  simp only [hg, mul_zero, Real.exp_zero, mul_one] at h
  have he1 : 1 ≤ Real.exp (k * t) := Real.one_le_exp (by nlinarith [ht.1])
  by_cases hpos : φ t - hi / k ≤ 0
  · exact le_trans (by linarith) (le_max_right _ _)
  · have hpos := (not_le.mp hpos)
    have : φ t - hi / k ≤ (φ t - hi / k) * Real.exp (k * t) := by nlinarith
    exact le_trans (by linarith) (le_max_left _ _)

/-- **Lower comparison**: with `lo ≤ F` on `[0, T]`, the forced contraction stays at least
`min y₀ (lo/k)` there. -/
theorem forced_ge {φ F : ℝ → ℝ} {k lo T : ℝ} (hk : 0 < k)
    (hφ : ∀ t, HasDerivAt φ (F t - k * φ t) t) (hF : ∀ t ∈ Icc (0:ℝ) T, lo ≤ F t) :
    ∀ t ∈ Icc (0:ℝ) T, min (φ 0) (lo / k) ≤ φ t := by
  have hn : ∀ t, HasDerivAt (fun u => -φ u) ((-F t) - k * (-φ t)) t := fun t =>
    ((hφ t).neg).congr_deriv (by ring)
  have h := forced_le (F := fun t => -F t) (hi := -lo) hk hn (fun t ht => by
    have := hF t ht; linarith)
  intro t ht
  have h1 := h t ht
  rw [neg_div, max_neg_neg] at h1
  linarith

/-- **Both comparisons**: `lo ≤ F ≤ hi` on `[0, T]` keeps the forced contraction between
`min y₀ (lo/k)` and `max y₀ (hi/k)`. -/
theorem forcedSol_between (k y0 : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {lo hi T : ℝ}
    (hk : 0 < k) (hb : ∀ t ∈ Icc (0:ℝ) T, lo ≤ F t ∧ F t ≤ hi) :
    ∀ t ∈ Icc (0:ℝ) T,
      min y0 (lo / k) ≤ forcedSol k y0 F t ∧ forcedSol k y0 F t ≤ max y0 (hi / k) := by
  intro t ht
  have h1 := forced_ge hk (forcedSol_hasDerivAt k y0 hF) (fun t ht => (hb t ht).1) t ht
  have h2 := forced_le hk (forcedSol_hasDerivAt k y0 hF) (fun t ht => (hb t ht).2) t ht
  rw [forcedSol_zero] at h1 h2
  exact ⟨h1, h2⟩

/-! ## The band facts and Assumption 1 -/

variable {n : ℕ}

/-- The band facts of a terrain chain (indices: `Rv is` the odometer, `Rv ic` the capped
contraction coordinate). -/
structure TerrainWF (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n))
    (dom : Formula (Var n)) where
  m : ℕ → RMode (Var n)
  fR : ℕ → Fin n → Term (Var n)
  /-- the band boundaries and the odometer rate bound -/
  s1 : ℝ
  s2 : ℝ
  B : ℝ
  B0 : 0 ≤ B
  band : s1 + B ≤ s2
  /-- whether the guards carry the caps `x_c ≤ c_q` -/
  vcap : Prop
  is : Fin n
  ic : Fin n
  kc : ℝ
  kc0 : 0 ≤ kc
  cap : ℕ → ℝ
  cap01 : cap 0 ≤ cap 1
  cap12 : cap 1 ≤ cap 2
  modeAt : ∀ q < 3, G.modeAt q = some (m q)
  len : G.modes.length = 3
  sys_eq : ∀ q < 3, (m q).sys = rightBlock (fR q) (Term.const 1)
  dom_eq : ∀ q < 3, (m q).dom = dom
  fc : vcap → ∀ q < 3, ∀ s, Term.eval (fR q ic) s = kc * (cap q - s (Rv ic))
  fs : ∀ q < 3, ∀ s, Formula.sat dom s → 0 ≤ Term.eval (fR q is) s ∧ Term.eval (fR q is) s ≤ B
  g0 : ∀ x, Formula.sat (guard 0) x ↔
    (0 ≤ x (Rv is) ∧ x (Rv is) < s1) ∧ (vcap → x (Rv ic) ≤ cap 0)
  g1 : ∀ x, Formula.sat (guard 1) x ↔
    (s1 ≤ x (Rv is) ∧ x (Rv is) < s2) ∧ (vcap → x (Rv ic) ≤ cap 1)
  g2 : ∀ x, Formula.sat (guard 2) x ↔ s2 ≤ x (Rv is) ∧ (vcap → x (Rv ic) ≤ cap 2)
  e00 : REdge (Var n)
  e01 : REdge (Var n)
  e11 : REdge (Var n)
  e12 : REdge (Var n)
  e22 : REdge (Var n)
  e00_mem : e00 ∈ G.edgesFrom 0
  e01_mem : e01 ∈ G.edgesFrom 0
  e11_mem : e11 ∈ G.edgesFrom 1
  e12_mem : e12 ∈ G.edgesFrom 1
  e22_mem : e22 ∈ G.edgesFrom 2
  e00_tgt : e00.tgt = 0
  e01_tgt : e01.tgt = 1
  e11_tgt : e11.tgt = 1
  e12_tgt : e12.tgt = 2
  e22_tgt : e22.tgt = 2
  exists_run : ∀ q < 3, ∀ x, Formula.sat dom x → ∃ Φ, ODESol (m q).sys (m q).dom x 1 Φ

/-- **Assumption 1 for a terrain chain**, from its band facts (Z3-free). -/
theorem wellFormedR_terrain {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    {dom : Formula (Var n)} (W : TerrainWF G guard dom) : WellFormedR G guard 1 := by
  intro q hq m hm x hg hd _
  rw [W.len] at hq
  have hmq : m = W.m q := by
    have := W.modeAt q hq; rw [hm] at this; exact Option.some.inj this
  subst hmq
  refine ⟨W.exists_run q hq x (by rw [← W.dom_eq q hq]; exact hd), ?_⟩
  intro t Φ ht H
  rw [W.sys_eq q hq, W.dom_eq q hq] at H
  have hmemc := rightBlock_mem' (W.fR q) (Term.const 1) W.ic
  have hmems := rightBlock_mem' (W.fR q) (Term.const 1) W.is
  have hsup := H.rate_le hmems W.B (fun s hs => by rw [eval_unit_mul]; exact (W.fs q hq s hs).2)
  have hslo := H.mono hmems (fun s hs => by rw [eval_unit_mul]; exact (W.fs q hq s hs).1)
  have hr := H.hr
  have hBt : W.B * t ≤ W.B := by nlinarith [W.B0]
  have hcap : ∀ c, W.vcap → W.cap q ≤ c → x (Rv W.ic) ≤ c → Φ t (Rv W.ic) ≤ c := by
    intro c hv h1 h2
    have hb := H.linear_between hmemc W.kc (W.cap q) W.kc0
      (fun s _ => by rw [eval_unit_mul, W.fc hv q hq])
    exact le_trans hb.2 (max_le h2 h1)
  have band := W.band
  have c01 := W.cap01
  have c12 := W.cap12
  interval_cases q
  · -- MUD: ends below s₁ + B ≤ s₂, inside MUD or GRAVEL
    obtain ⟨⟨hs0, hs1⟩, hvc⟩ := (W.g0 x).mp hg
    by_cases h1 : Φ t (Rv W.is) < W.s1
    · refine ⟨W.e00, W.e00_mem, ?_⟩
      rw [W.e00_tgt, W.g0]
      exact ⟨⟨by linarith, h1⟩, fun h => hcap _ h le_rfl (hvc h)⟩
    · refine ⟨W.e01, W.e01_mem, ?_⟩
      rw [W.e01_tgt, W.g1]
      exact ⟨⟨by linarith, by linarith⟩, fun h => hcap _ h c01 (by linarith [hvc h])⟩
  · -- GRAVEL: inside GRAVEL or PAVED
    obtain ⟨⟨hs0, hs1⟩, hvc⟩ := (W.g1 x).mp hg
    by_cases h2 : Φ t (Rv W.is) < W.s2
    · refine ⟨W.e11, W.e11_mem, ?_⟩
      rw [W.e11_tgt, W.g1]
      exact ⟨⟨by linarith, h2⟩, fun h => hcap _ h le_rfl (hvc h)⟩
    · refine ⟨W.e12, W.e12_mem, ?_⟩
      rw [W.e12_tgt, W.g2]
      exact ⟨by linarith, fun h => hcap _ h c12 (by linarith [hvc h])⟩
  · -- PAVED: forward invariant
    obtain ⟨hs0, hvc⟩ := (W.g2 x).mp hg
    refine ⟨W.e22, W.e22_mem, ?_⟩
    rw [W.e22_tgt, W.g2]
    exact ⟨by linarith, fun h => hcap _ h le_rfl (hvc h)⟩

end RelCertifier
