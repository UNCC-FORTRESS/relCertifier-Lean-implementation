/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Wiring `hExist_rover` into `segment_faModal` — discharging the carried side-condition

`hExist_rover` (PicardBridge) constructs the right witness `ΦR` for the rover field shape. This file
threads it into `segment_faModal`'s `hExist` hypothesis, **removing** it from the carried
side-conditions for the rover-shape benchmarks.

The load-bearing seam is **cross-side masking**: `hExist_rover` needs the right's start `ΦL s` in the
slab. Two halves, both proven here:
1. *Preserved-by-disjointness* — `ΦL s (Rv j) = ν (Rv j)`, because `Rv j ∉ leftBlock.bound`
   (`Side.R ≠ Side.L`), so the left run's masking (an `hExist` premise) freezes the right's coords.
2. *Initial-in-slab* — `ν`'s right coords lie in the slab (the invariant-admissible start).
Together: the right starts in the slab ⟹ `hExist_rover` applies. This is the ∀∃ core (left runs;
right idles masked; then responds from its in-slab start).
-/
import RelCertifier.PicardBridge
import RelCertifier.Reify

namespace RelCertifier

open DL DLCalTiming Set

variable {n : ℕ}

/-- **Right coords are outside the left block's bound set** (`Side.R ≠ Side.L`). The disjointness that
freezes the right's variables during the left run. -/
theorem Rv_not_mem_leftBlock_bound (fL : Fin n → Term (Var n)) (j : Fin n) :
    Rv j ∉ (leftBlock fL).bound := by
  simp only [leftBlock, ODESystem.bound, List.map_map, List.mem_map, Function.comp]
  rintro ⟨i, _, hi⟩
  have hLR : (Side.L : Side) = Side.R := congrArg Prod.fst hi
  exact absurd hLR (by decide)

/-- **hExist discharged for `segment_faModal` (rover shape).** Proves the `hExist` hypothesis of
`segment_faModal` — no longer carried — from `hExist_rover` plus the cross-side masking seam. `vi`,`si`
are the right's velocity/position coords (`Rv _`, hence `∉ leftBlock.bound`, given as `hviL`/`hsiL`).
The growth bound is supplied as `hsmax` (the Z3-checkable coupling: the left staying in `domL` over
`[0,s]` bounds `s`, hence the right's `s`-growth `ν si + v_max·s ≤ S_max`). -/
theorem hExist_from_rover
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hwf : (rightBlock fR lam).WellFormed)
    (vi si : Var n) (k c vmax smax a : ℝ)
    (hfv : ∀ x : State (Var n), odeField (rightBlock fR lam) x vi = k * (c - x vi))
    (hfs : ∀ x : State (Var n), odeField (rightBlock fR lam) x si = x vi)
    (hother : ∀ (x : State (Var n)) j, j ≠ vi → j ≠ si →
        odeField (rightBlock fR lam) x j = 0)
    (hk : 0 < k) (hc0 : 0 < c) (hcv : c < vmax) (ha : 0 < a)
    (hviL : vi ∉ (leftBlock fL).bound) (hsiL : si ∉ (leftBlock fL).bound)
    (hdomsat : ∀ x : State (Var n),
        0 ≤ x vi → x vi ≤ vmax → 0 ≤ x si → x si ≤ smax → Formula.sat domR x)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hr₀le : max (k * (|c| + vmax + a)) (vmax + a) * r₀ ≤ a)
    (hνvi0 : 0 ≤ ν vi) (hνviv : ν vi ≤ vmax) (hνsi0 : 0 ≤ ν si)
    (hsmax : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) → ν si + vmax * s ≤ smax) :
    ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL t x = ν x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  intro s ΦL hs0 hΦL0 _ hmaskL hdomL
  -- the masking seam: the right's coords are frozen to their initial values by the left run
  have hωvi : ΦL s vi = ν vi := hmaskL s (right_mem_Icc.mpr hs0) vi hviL
  have hωsi : ΦL s si = ν si := hmaskL s (right_mem_Icc.mpr hs0) si hsiL
  have hZ3 : ΦL s si + vmax * s ≤ smax := by rw [hωsi]; exact hsmax s ΦL hs0 hdomL
  exact hExist_rover hwf vi si k c vmax smax a hfv hfs hother hk hc0 hcv ha hdomsat
    r₀ hr₀ hr₀le (ΦL s)
    (by rw [hωvi]; exact hνvi0) (by rw [hωvi]; exact hνviv) (by rw [hωsi]; exact hνsi0)
    s hs0 hZ3

/-- **hExist discharged for `segment_faModal` (cubic shape).** Same cross-side masking seam as
`hExist_from_rover` — **field-independent** (`hmaskL` + `Rv_not_mem_leftBlock_bound`, no field
reference) — but the inner witness is `hExist_cubic` (slab-Lipschitz, K/L discharged) instead of
`hExist_rover`. Confirms the seam transfers to the nonlinear (cubic) right-fields: the right's start
`ΦL s` is in the slab (right coords frozen to their in-slab initial values by the left run), so
`hExist_cubic` fires. This closes the 12 cubic's hExist into the tool. -/
theorem hExist_from_cubic
    (fL : Fin n → Term (Var n)) (rightSys : ODESystem (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hwf : rightSys.WellFormed)
    (vi psii si : Var n) (k c vmax lo hi smax : ℝ)
    (hfv : ∀ x : State (Var n), odeField rightSys x vi = k * (c - x vi))
    (hfpsi : ∀ x : State (Var n), odeField rightSys x psii = 1 * (0 - x psii))
    (hsge_box : ∀ x : State (Var n), (0 ≤ x vi ∧ x vi ≤ vmax ∧ lo ≤ x psii ∧ x psii ≤ hi) →
        0 ≤ odeField rightSys x si)
    (hsle_box : ∀ x : State (Var n), (0 ≤ x vi ∧ x vi ≤ vmax ∧ lo ≤ x psii ∧ x psii ≤ hi) →
        odeField rightSys x si ≤ vmax)
    (hk : 0 < k) (hc0 : 0 < c) (hcv : c < vmax) (hlo : lo < 0) (hhi : 0 < hi)
    (K L : NNReal) (c₀ : State (Var n)) (R a : ℝ) (ha : 0 < a)
    (hsindep : ∀ x : State (Var n), odeField rightSys x = odeField rightSys (Function.update x si 0))
    (hKcross : LipschitzOnWith K (odeField rightSys) (Metric.closedBall c₀ R))
    (hLcross : ∀ x ∈ Metric.closedBall c₀ R, ‖odeField rightSys x‖ ≤ (L : ℝ))
    (hsub : ∀ μ : State (Var n),
        (0 ≤ μ vi ∧ μ vi ≤ vmax ∧ lo ≤ μ psii ∧ μ psii ≤ hi ∧ 0 ≤ μ si) →
        Metric.closedBall (Function.update μ si 0) a ⊆ Metric.closedBall c₀ R)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hr₀le : (L : ℝ) * r₀ ≤ a)
    (hviL : vi ∉ (leftBlock fL).bound) (hpsiiL : psii ∉ (leftBlock fL).bound)
    (hsiL : si ∉ (leftBlock fL).bound)
    (hdomsat : ∀ x : State (Var n),
        (0 ≤ x vi ∧ x vi ≤ vmax ∧ lo ≤ x psii ∧ x psii ≤ hi ∧ 0 ≤ x si ∧ x si ≤ smax) →
        Formula.sat domR x)
    (hνv0 : 0 ≤ ν vi) (hνvv : ν vi ≤ vmax) (hνpl : lo ≤ ν psii) (hνph : ν psii ≤ hi) (hνs0 : 0 ≤ ν si)
    (hsmax : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) → ν si + vmax * s ≤ smax) :
    ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL t x = ν x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightSys,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ rightSys.bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  intro s ΦL hs0 hΦL0 _ hmaskL hdomL
  -- the field-independent masking seam: right coords frozen to ν during the left run
  have hωvi : ΦL s vi = ν vi := hmaskL s (right_mem_Icc.mpr hs0) vi hviL
  have hωpsi : ΦL s psii = ν psii := hmaskL s (right_mem_Icc.mpr hs0) psii hpsiiL
  have hωsi : ΦL s si = ν si := hmaskL s (right_mem_Icc.mpr hs0) si hsiL
  have hZ3 : ΦL s si + vmax * s ≤ smax := by rw [hωsi]; exact hsmax s ΦL hs0 hdomL
  exact hExist_cubic hwf vi psii si k c vmax lo hi smax hfv hfpsi hsge_box hsle_box
    hk hc0 hcv hlo hhi K L c₀ R a ha hsindep hKcross hLcross hsub r₀ hr₀ hr₀le hdomsat
    (ΦL s) (by rw [hωvi]; exact hνv0) (by rw [hωvi]; exact hνvv) (by rw [hωpsi]; exact hνpl)
    (by rw [hωpsi]; exact hνph) (by rw [hωsi]; exact hνs0) s hs0 hZ3

end RelCertifier



