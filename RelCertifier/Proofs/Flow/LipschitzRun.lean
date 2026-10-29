/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Runs of every duration for a globally Lipschitz field (Assumption 1, clause (i))

For a field that is globally `K`-Lipschitz (every affine field: the literature switched linear
systems `lit_gpt10_boost_converter`), a run of any duration `r ≥ 0` exists from every state,
inside any evolve domain that every state satisfies (the constant atom `0 ≤ 1`).

Proof: one uniform Picard step. From `ν`, on the ball of radius `a = ‖f ν‖ + 1` the field is
bounded by `L = ‖f ν‖ + K a` (Lipschitz), and `L · r₀ ≤ a` for `r₀ = 1 / (K + 1)` whatever
`ν` is (`‖f ν‖ ≤ a`). So `picard_isPL_of` gives a run of the uniform length `r₀` from every
state, `chainN` chains `⌈r / r₀⌉` of them, and `RunFor_unpack` reads the result as an `ODESol`.
Z3-free; the standard three axioms.
-/
import RelCertifier.Proofs.Flow.PicardBridge
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier

open DL DLCalTiming Set Metric

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **One uniform step.** From every state a run of length `1 / (K + 1)` exists (domain `tt`). -/
theorem runFor_step_of_lipschitz {sys : ODESystem V} {K : NNReal}
    (hLip : LipschitzWith K (odeField sys)) (ν : State V) :
    ∃ ν', RunFor sys Formula.tt (1 / ((K : ℝ) + 1)) ν ν' := by
  set a : ℝ := ‖odeField sys ν‖ + 1 with ha_def
  have ha : 0 < a := by positivity
  set Lr : ℝ := ‖odeField sys ν‖ + (K : ℝ) * a with hL_def
  have hL0 : 0 ≤ Lr := by positivity
  set L : NNReal := ⟨Lr, hL0⟩
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hr₀ : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  have hbound : ∀ x ∈ closedBall ν a, ‖odeField sys x‖ ≤ (L : ℝ) := by
    intro x hx
    have hd : dist x ν ≤ a := mem_closedBall.mp hx
    have h1 : ‖odeField sys x - odeField sys ν‖ ≤ (K : ℝ) * dist x ν := by
      rw [← dist_eq_norm]; exact hLip.dist_le_mul x ν
    have h2 : ‖odeField sys x‖ ≤ ‖odeField sys ν‖ + ‖odeField sys x - odeField sys ν‖ := by
      have := norm_add_le (odeField sys ν) (odeField sys x - odeField sys ν)
      rwa [add_sub_cancel] at this
    show ‖odeField sys x‖ ≤ Lr
    have h3 : (K : ℝ) * dist x ν ≤ (K : ℝ) * a := mul_le_mul_of_nonneg_left hd hK0
    linarith
  have hle : (L : ℝ) * (1 / ((K : ℝ) + 1)) ≤ a := by
    show Lr * (1 / ((K : ℝ) + 1)) ≤ a
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have : ‖odeField sys ν‖ ≤ a := by linarith
    nlinarith
  have hpl := picard_isPL_of K L ν a ha.le hLip hbound _ hr₀ hle
  obtain ⟨Φ, _, _, hrun⟩ := picard_to_RunFor (dom := Formula.tt) ν hr₀ hpl
    (fun _ _ _ _ _ => trivial)
  exact ⟨_, hrun⟩

/-- **Runs of every duration** for a globally Lipschitz well-formed field, inside an evolve
domain every state satisfies. -/
theorem exists_odeSol_of_lipschitz {sys : ODESystem V} (hwf : sys.WellFormed)
    {dom : Formula V} (hdom : ∀ x, Formula.sat dom x) {K : NNReal}
    (hLip : LipschitzWith K (odeField sys)) (ω : State V) (r : ℝ) (hr : 0 ≤ r) :
    ∃ Φ, ODESol sys dom ω r Φ := by
  have hK0 : (0 : ℝ) ≤ K := K.2
  set r₀ : ℝ := 1 / ((K : ℝ) + 1) with hr₀_def
  have hr₀ : 0 < r₀ := by positivity
  have hstep : ∀ ν, (fun _ : State V => True) ν →
      ∃ ν', (fun _ : State V => True) ν' ∧ RunFor sys Formula.tt r₀ ν ν' := by
    intro ν _
    obtain ⟨ν', h⟩ := runFor_step_of_lipschitz hLip ν
    exact ⟨ν', trivial, h⟩
  set N : ℕ := Nat.ceil (r / r₀) with hN
  have hrN : r ≤ (N : ℝ) * r₀ := by
    rw [hN]
    calc r = r / r₀ * r₀ := (div_mul_cancel₀ r (ne_of_gt hr₀)).symm
      _ ≤ (Nat.ceil (r / r₀) : ℝ) * r₀ :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (le_of_lt hr₀)
  obtain ⟨ν', hrun⟩ := chainN hr₀ (fun _ => True) hstep (fun _ _ => trivial) N r hr hrN ω trivial
  obtain ⟨Φ, h0, hder, hmask, _⟩ := RunFor_unpack hwf hrun
  exact ⟨Φ, ⟨hr, h0, hder, hmask, fun t _ => hdom (Φ t)⟩⟩

/-- **Per-coordinate affine bound ⟹ global Lipschitz.** If every coordinate of the field moves by
at most `K · dist` (an affine coordinate `Σ aⱼ xⱼ + b` with `Σ |aⱼ| ≤ K`), the field is
`K`-Lipschitz. A restatement of `odeField_lipschitz_of_perCoord` with the constant as a real. -/
theorem lipschitz_of_perCoord {sys : ODESystem V} (K : ℝ) (hK : 0 ≤ K)
    (hcoord : ∀ (i : V) (x y : State V),
      |odeField sys x i - odeField sys y i| ≤ K * dist x y) :
    LipschitzWith (Real.toNNReal K) (odeField sys) :=
  odeField_lipschitz_of_perCoord K hK hcoord

omit [DecidableEq V] in
/-- A coordinate moves by at most the sup distance. -/
theorem coord_sub_le_dist (x y : State V) (v : V) : |x v - y v| ≤ dist x y := by
  have := dist_le_pi_dist x y v
  rwa [Real.dist_eq] at this

omit [DecidableEq V] in
/-- **Two-coordinate affine bound.** `|a (x u − y u) + b (x v − y v)| ≤ (|a| + |b|) dist x y`. -/
theorem affine2_sub_le (a b : ℝ) (x y : State V) (u v : V) :
    |a * (x u - y u) + b * (x v - y v)| ≤ (|a| + |b|) * dist x y := by
  have hu := coord_sub_le_dist x y u
  have hv := coord_sub_le_dist x y v
  calc |a * (x u - y u) + b * (x v - y v)|
      ≤ |a * (x u - y u)| + |b * (x v - y v)| := abs_add_le _ _
    _ = |a| * |x u - y u| + |b| * |x v - y v| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * dist x y + |b| * dist x y := by
        gcongr
    _ = (|a| + |b|) * dist x y := by ring

variable {n : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- A run over the whole space that stays in `dom` is a run in `dom`. -/
theorem odeSol_of_tt {sys : ODESystem V} {dom : Formula V} {x : State V} {r : ℝ}
    {Φ : ℝ → State V} (H : ODESol sys Formula.tt x r Φ)
    (hd : ∀ t ∈ Icc (0 : ℝ) r, Formula.sat dom (Φ t)) : ODESol sys dom x r Φ :=
  ⟨H.hr, H.hΦ0, H.hder, H.hmask, hd⟩

/-- **Runs of every duration over the whole space** for a globally Lipschitz well-formed field
(the domain is checked afterwards, `odeSol_of_tt`). -/
theorem exists_odeSol_tt_of_lipschitz {sys : ODESystem V} (hwf : sys.WellFormed) {K : NNReal}
    (hLip : LipschitzWith K (odeField sys)) (ω : State V) (r : ℝ) (hr : 0 ≤ r) :
    ∃ Φ, ODESol sys Formula.tt ω r Φ :=
  exists_odeSol_of_lipschitz (dom := Formula.tt) hwf (fun _ => trivial) hLip ω r hr

/-- **The right block at unit stretch is Lipschitz** when every right field is: the left and
auxiliary coordinates are not bound (field `0`), the right ones are the fields themselves. -/
theorem lipschitz_rightBlock (fR : Fin n → Term (Var n)) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (j : Fin n) (x y : State (Var n)),
      |Term.eval (fR j) x - Term.eval (fR j) y| ≤ K * dist x y) :
    LipschitzWith (Real.toNNReal K) (odeField (rightBlock fR (Term.const 1))) := by
  apply odeField_lipschitz_of_perCoord K hK
  rintro ⟨s, j⟩ x y
  cases s with
  | R =>
    have hx := odeField_rightBlock_unit fR x j
    have hy := odeField_rightBlock_unit fR y j
    simp only [Rv] at hx hy
    rw [hx, hy]; exact h j x y
  | L =>
    have hnb : ((Side.L, j) : Var n) ∉ (rightBlock fR (Term.const 1)).bound := by
      simp [ODESystem.bound, rightBlock]
    simp only [odeField, if_neg hnb, sub_self, abs_zero]
    exact mul_nonneg hK dist_nonneg
  | Aux =>
    have hnb : ((Side.Aux, j) : Var n) ∉ (rightBlock fR (Term.const 1)).bound := by
      simp [ODESystem.bound, rightBlock]
    simp only [odeField, if_neg hnb, sub_self, abs_zero]
    exact mul_nonneg hK dist_nonneg

end RelCertifier
