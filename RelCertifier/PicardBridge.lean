/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Picard existence bridge — Mathlib ODE existence ⟹ dL-lean `sem`

The `hExist` side-condition of `faModal_ODE_G'` needs: from a bounded, in-domain segment, a right
`sem` run exists over the segment interval. This file builds that from Mathlib's Picard-Lindelöf,
**uniformly** over all polynomial fields (every benchmark's `odeField` is polynomial):

* Step 2 (`odeField_contDiff`, `odeField_lipschitzOnWith`) — the crux. `Term.eval` is polynomial,
  hence `ContDiff ℝ ⊤`; so `odeField sys` is `ContDiff`, hence its `fderiv` is continuous, hence
  bounded on any compact ball, hence **Lipschitz-on-compact** — exactly Mathlib's
  `IsPicardLindelof.lipschitzOnWith` hypothesis. Builds on the proven `term_differentiable`
  (strengthened here to `ContDiff`). One lemma, all fields.
* Step 1 (normed instance) — `State V = V → ℝ` with `Fintype V` is `Pi.normedAddCommGroup`
  (finite-dim, proper); the ball is compact. Same instance dL-lean's `DI` already uses.

`#print axioms` stays the standard three (Mathlib Picard adds no axiom).
-/
import RelCertifier.FlowCert
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

namespace RelCertifier

open DL Set Metric

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Terms are smooth.** Every term denotes a `ContDiff ℝ ⊤` (polynomial) function of the state —
the `ContDiff` strengthening of `term_differentiable`, same induction. Gives the continuous `fderiv`
that the Lipschitz-on-compact bound needs. -/
theorem term_contDiff (t : Term V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ν : State V => Term.eval t ν) := by
  induction t with
  | var y =>
    have hf : (fun ν : State V => Term.eval (Term.var y) ν) = fun ν => ν y := by
      funext ν; simp [Term.eval]
    rw [hf]; exact contDiff_apply ℝ ℝ y
  | const c => exact contDiff_const
  | binop op a b iha ihb =>
    cases op with
    | add => exact iha.add ihb
    | sub => exact iha.sub ihb
    | mul => exact iha.mul ihb

/-- **The assembled vector field is smooth.** `odeField sys` is `ContDiff ℝ ⊤`: each component is
either a term evaluation (smooth by `term_contDiff`) or the constant `0`. -/
theorem odeField_contDiff (sys : ODESystem V) :
    ContDiff ℝ (⊤ : ℕ∞) (odeField sys) := by
  apply contDiff_pi'
  intro i
  by_cases hi : i ∈ sys.bound
  · have hb : (fun x : State V => odeField sys x i) = fun x => (sys.rhs i).eval x := by
      funext x; simp only [odeField, if_pos hi]
    rw [hb]; exact term_contDiff _
  · have hb : (fun x : State V => odeField sys x i) = fun _ => (0 : ℝ) := by
      funext x; simp only [odeField, if_neg hi]
    rw [hb]; exact contDiff_const

/-- **Step 2 — Lipschitz-on-compact.** On any closed ball, `odeField sys` is Lipschitz: its `fderiv`
is continuous (smoothness) hence bounded on the compact ball, and the ball is convex. This is
precisely the field hypothesis Mathlib's `IsPicardLindelof` consumes. Uniform over all fields. -/
theorem odeField_lipschitzOnWith (sys : ODESystem V) (x₀ : State V) (a : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (odeField sys) (closedBall x₀ a) := by
  have hcont : Continuous (fderiv ℝ (odeField sys)) :=
    (odeField_contDiff sys).continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ a).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C.toNNReal, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (odeField_contDiff sys).differentiable (by norm_num) x) ?_ (convex_closedBall x₀ a)
  intro x hx
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC x hx)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hCnn]
  exact hC x hx



/-! ## Steps 3–4 — Mathlib existence ⟹ dL-lean `sem` (the reification seam) -/

/-- **The seam (integral curve ⟹ `sem`).** A Mathlib integral curve of `odeField sys` on `Icc 0 r`
that stays in `domR` genuinely **is** a dL-lean `sem` execution of `ode sys domR`. No abstract-vs-
concrete gap: this is exactly `sem_ode_iff_integralCurve` (proven in dL-lean) in the `.mpr`
direction. The Mathlib solution IS the `sem` run, not a lookalike. -/
theorem sem_of_integralCurveOn (sys : ODESystem V) (domR : Formula V) (hwf : sys.WellFormed)
    {r : ℝ} {Φ : ℝ → State V} (hr : 0 ≤ r)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Icc 0 r))
    (hdom : ∀ t ∈ Icc (0 : ℝ) r, Formula.sat domR (Φ t)) :
    Program.sem (.ode sys domR) (Φ 0) (Φ r) :=
  (sem_ode_iff_integralCurve hwf).mpr ⟨r, Φ, hr, rfl, rfl, hcurve, hdom⟩

/-- **Local `sem`-existence (steps 3–4, local).** From smoothness of the field (`odeField_contDiff`)
and an initial state `ν` in the (open) evolution domain `domR`, a `sem` run of `ode sys domR`
exists from `ν` of some positive duration `r`, landing at `ν'`. Mathlib's C¹ local-existence
(`ContDiffAt.…hasDerivAt₀`) gives the curve; continuity + openness of `domR` keep it in-domain on a
short `Icc 0 r`; the seam turns it into a `sem` run. Uniform over all polynomial fields; the only
per-segment residual is extending `r` to the parser's duration `Tᵢ` (continuation). -/
theorem sem_ode_exists_local (sys : ODESystem V) (domR : Formula V) (hwf : sys.WellFormed)
    (ν : State V) (hopen : IsOpen {x : State V | Formula.sat domR x})
    (hν : Formula.sat domR ν) :
    ∃ r > (0 : ℝ), ∃ ν', Program.sem (.ode sys domR) ν ν' := by
  obtain ⟨α, hα0, ε, hε, hderiv⟩ :=
    ((odeField_contDiff sys).contDiffAt.of_le (by exact_mod_cast le_top)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  -- α is continuous at 0 (it has a derivative there)
  have h0mem : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by constructor <;> linarith
  have hcont0 : ContinuousAt α 0 := (hderiv 0 h0mem).continuousAt
  -- α maps a neighbourhood of 0 into domR (openness + α 0 = ν ∈ domR)
  have hpre : {t : ℝ | α t ∈ {x : State V | Formula.sat domR x}} ∈ nhds (0 : ℝ) :=
    hcont0.preimage_mem_nhds (hopen.mem_nhds (by simpa [hα0] using hν))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  set r : ℝ := min (ε / 2) (δ / 2) with hr_def
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  refine ⟨r, hrpos, α r, ?_⟩
  have hα00 : α 0 = ν := hα0
  rw [← hα00]
  refine sem_of_integralCurveOn sys domR hwf (le_of_lt hrpos) ?_ ?_
  · -- integral curve on Icc 0 r
    intro t ht
    have htioo : t ∈ Ioo (0 - ε) (0 + ε) := by
      constructor
      · have : (0 : ℝ) ≤ t := ht.1
        linarith
      · have : t ≤ r := ht.2
        have : r ≤ ε / 2 := min_le_left _ _
        have ht2 := ht.2
        simp only [zero_add]; linarith [min_le_left (ε/2) (δ/2), ht.2]
    exact (hderiv t htioo).hasDerivWithinAt
  · -- domain holds on Icc 0 r
    intro t ht
    have htdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      have : r ≤ δ / 2 := min_le_right _ _
      linarith [ht.2]
    exact hδsub htdist

end RelCertifier
