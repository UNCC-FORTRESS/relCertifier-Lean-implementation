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

/-! ## Raw-curve strict positive-invariance (un-gated — the piece dL-lean leaves `sem`-gated)

`DI_strict` proves `g ≤ 0` along the flow but consumes a `sem` run — domain-membership *given*.
To *construct* a domain-staying witness (`hExist`), we need the same conclusion for a **raw** Picard
integral curve, before it is known to be a `sem` run. With a **global** strict-inflow hypothesis
(`g x = 0 → Lie < 0`, sound: strict avoids the `nonstrict_boundary_insufficient` t² trap), the
argument is `DI_strict`'s first-exit (`sSup` of the sublevel set) verbatim, minus the one `hdom`
step. Reuses the un-gated `hasDeriv_g_along_flow`. This is the v-face invariance the box needs. -/
theorem strict_inv_endpoint {sys : ODESystem V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, g x = 0 → Lie sys g x < 0)
    {r : ℝ} {Φ : ℝ → State V} (hr : 0 ≤ r)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinit : g (Φ 0) ≤ 0) : g (Φ r) ≤ 0 := by
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun t ht => hasDeriv_g_along_flow hwf hg hcurve ht
  have hcont : ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  by_contra hcon
  rw [not_le] at hcon
  set S : Set ℝ := Set.Icc 0 r ∩ (fun s => g (Φ s)) ⁻¹' Set.Iic 0 with hSdef
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have h0S : (0:ℝ) ∈ S :=
    ⟨Set.left_mem_Icc.mpr hr, by simp only [Set.mem_preimage, Set.mem_Iic]; exact hinit⟩
  have hSbdd : BddAbove S := ⟨r, fun t ht => ht.1.2⟩
  set s := sSup S with hsdef
  have hsS : s ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hSbdd
  have hsIcc : s ∈ Set.Icc 0 r := hsS.1
  have hsle0 : g (Φ s) ≤ 0 := hsS.2
  have hs_ub : ∀ t ∈ S, t ≤ s := fun t htS => le_csSup hSbdd htS
  clear_value s
  have hsr : s < r :=
    lt_of_le_of_ne hsIcc.2 (by rintro rfl; exact absurd hsle0 (not_le.mpr hcon))
  have hpos : ∀ t ∈ Set.Ioc s r, 0 < g (Φ t) := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 r := ⟨le_trans hsIcc.1 (le_of_lt ht.1), ht.2⟩
    have htnS : t ∉ S := fun htS => absurd (hs_ub t htS) (not_le.mpr ht.1)
    exact not_le.mp (fun h => htnS ⟨htIcc, h⟩)
  have hmem : s ∈ closure (Set.Ioc s r) := by
    rw [closure_Ioc (ne_of_lt hsr)]; exact Set.left_mem_Icc.mpr (le_of_lt hsr)
  haveI hneBot : (nhdsWithin s (Set.Ioc s r)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have hIocIcc : Set.Ioc s r ⊆ Set.Icc 0 r :=
    fun t ht => ⟨le_trans hsIcc.1 (le_of_lt ht.1), ht.2⟩
  have hge0 : 0 ≤ g (Φ s) := by
    have htend := (hcont s hsIcc).mono_left (nhdsWithin_mono s hIocIcc)
    exact ge_of_tendsto htend
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => le_of_lt (hpos t ht)))
  have hgeq0 : g (Φ s) = 0 := le_antisymm hsle0 hge0
  have hLie : Lie sys g (Φ s) < 0 := hbnd (Φ s) hgeq0
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv s hsIcc)).mono_left
    (nhdsWithin_mono s (fun t ht => ⟨hIocIcc ht, ne_of_gt ht.1⟩))
  have hslopepos : ∀ᶠ t in nhdsWithin s (Set.Ioc s r),
      0 < slope (fun t => g (Φ t)) s t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    exact div_pos (by rw [hgeq0]; simpa using hpos t ht) (by linarith [ht.1])
  exact absurd (ge_of_tendsto hslope (hslopepos.mono fun t h => le_of_lt h)) (not_le.mpr hLie)

/-- **Raw-curve strict invariance, all times.** Under global strict inflow, a raw integral curve
starting in `{g ≤ 0}` stays in `{g ≤ 0}` over the whole `Icc 0 r` — applying `strict_inv_endpoint`
to every sub-interval `[0,t]`. This is the un-gated positive-invariance `hExist` needs (v-face). -/
theorem strict_invariance_raw {sys : ODESystem V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, g x = 0 → Lie sys g x < 0)
    {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hinit : g (Φ 0) ≤ 0) :
    ∀ t ∈ Set.Icc (0:ℝ) r, g (Φ t) ≤ 0 := by
  intro t ht
  have hsub : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 t) :=
    fun u hu => (hcurve u ⟨hu.1, le_trans hu.2 ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2)
  exact strict_inv_endpoint hwf hg hbnd ht.1 hsub hinit


/-- **Raw-curve non-strict antitone invariance (un-gated).** If `Lie g ≤ 0` holds *along the curve*
(at every visited point), `g∘Φ` is non-increasing: `g (Φ t) ≤ g (Φ 0)`. This is `DI_nonstrict_domain`'s
`AntitoneOn` body, un-gated — sound because the hypothesis is `Lie ≤ 0` **along the curve**, not the
unsound boundary-only check (`nonstrict_boundary_insufficient`). The along-curve premise is supplied
by another invariant (e.g. the v-bound feeds the s growth-bound). -/
theorem nonstrict_antitone_raw {sys : ODESystem V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hlie : ∀ t ∈ Set.Icc (0:ℝ) r, Lie sys g (Φ t) ≤ 0) :
    ∀ t ∈ Set.Icc (0:ℝ) r, g (Φ t) ≤ g (Φ 0) := by
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun t ht => hasDeriv_g_along_flow hwf hg hcurve ht
  have hcont : ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  have hanti : AntitoneOn (fun s => g (Φ s)) (Set.Icc 0 r) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hcont (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      have hxIcc : x ∈ Set.Icc 0 r := Set.Ioo_subset_Icc_self hx
      exact ((hderiv x hxIcc).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hxIcc : x ∈ Set.Icc 0 r := Set.Ioo_subset_Icc_self hx
      rw [((hderiv x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
      exact hlie x hxIcc
  intro t ht
  exact hanti ⟨le_refl 0, le_trans ht.1 ht.2⟩ ht ht.1

/-- **Raw-curve linear growth bound (un-gated, clock-free).** A coordinate `sx` whose field value
stays `≤ M` along the curve satisfies the loose bound `Φ t sx ≤ Φ 0 sx + M·t`. Proof: `t ↦ Φ t sx − M·t`
has derivative `(odeField sys (Φ t) sx) − M ≤ 0`, so it is antitone. This is the growing-var (`s`-face)
bound — no clock: the time-dependent bound `s ≤ s₀ + v_max·t` is obtained directly, with `M = v_max`
the field-value bound from the v-invariance. Combined with the Z3 check `s₀ + v_max·Tᵢ ≤ S_max` it
gives `s ≤ S_max` over `[0,Tᵢ]`. -/
theorem growth_bound_raw {sys : ODESystem V} {r : ℝ} {Φ : ℝ → State V} (sx : V) (M : ℝ)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) r, odeField sys (Φ t) sx ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) r, Φ t sx ≤ Φ 0 sx + M * t := by
  have hsx : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun u => Φ u sx - M * u) (odeField sys (Φ t) sx - M) (Set.Icc 0 r) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun u => Φ u sx) (odeField sys (Φ t) sx) (Set.Icc 0 r) t :=
      (hasDerivWithinAt_pi.mp (hcurve t ht)) sx
    have h2 : HasDerivWithinAt (fun u => M * u) M (Set.Icc 0 r) t := by
      simpa using (hasDerivWithinAt_id t (Set.Icc 0 r)).const_mul M
    exact h1.sub h2
  have hcont : ContinuousOn (fun u => Φ u sx - M * u) (Set.Icc 0 r) :=
    fun t ht => (hsx t ht).continuousWithinAt
  have hanti : AntitoneOn (fun u => Φ u sx - M * u) (Set.Icc 0 r) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hcont (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      have hxIcc : x ∈ Set.Icc 0 r := Set.Ioo_subset_Icc_self hx
      exact ((hsx x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hxIcc : x ∈ Set.Icc 0 r := Set.Ioo_subset_Icc_self hx
      rw [((hsx x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
      linarith [hbound x hxIcc]
  intro t ht
  have := hanti ⟨le_refl 0, le_trans ht.1 ht.2⟩ ht ht.1
  simp only [mul_zero, sub_zero] at this
  linarith [this]


/-! ## Box composition — assembling the per-face raw invariances into `stays in domR` -/

/-- **Lie of an affine-in-one-coordinate function.** `Lie sys (fun y => a·yᵢ + b) x = a · (field)ᵢ`.
The `fderiv` of an affine coordinate map is `a • proj i`; `Lie_eq_fderiv` evaluates it on the field. -/
theorem lie_affine_coord (sys : ODESystem V) (hwf : sys.WellFormed) (i : V) (a b : ℝ)
    (x : State V) :
    Lie sys (fun y => a * y i + b) x = a * odeField sys x i := by
  rw [← Lie_eq_fderiv hwf]
  have hp : HasFDerivAt (fun y : State V => y i) (ContinuousLinearMap.proj i) x :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : V => ℝ) i x
  have h1 := (hp.const_mul a).add_const b
  rw [h1.fderiv]
  simp [ContinuousLinearMap.proj_apply]

/-- **Box positive-invariance (rover shape, un-gated).** For a raw integral curve of a system whose
field has the asymptotic/growing shape `v' = k(c−v)`, `s' = v` (field-value hypotheses `hfv`,`hfs`),
starting in the box `{0 ≤ v ≤ v_max, 0 ≤ s ≤ S_max}`, under the Z3-checkable parameter conditions
(`0<k`, `0<c<v_max`) and the Z3 growth bound (`s₀ + v_max·r ≤ S_max`), the curve **stays in the box**
over `[0,r]`. Assembles: `strict_invariance_raw` (both v-faces, strict inflow) + `growth_bound_raw`
(s upper, loose bound + Z3) + `nonstrict_antitone_raw` (s lower). The domain-staying half of
`hExist`, discharged — no subtangency, no `sem`-gating, no clock. -/
theorem box_invariance_rover {sys : ODESystem V} {r : ℝ} {Φ : ℝ → State V}
    (hwf : sys.WellFormed) (vi si : V) (k c vmax smax : ℝ)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hfv : ∀ x : State V, odeField sys x vi = k * (c - x vi))
    (hfs : ∀ x : State V, odeField sys x si = x vi)
    (hk : 0 < k) (hc0 : 0 < c) (hcv : c < vmax)
    (hv0lo : 0 ≤ Φ 0 vi) (hv0hi : Φ 0 vi ≤ vmax) (hs0lo : 0 ≤ Φ 0 si)
    (hZ3 : Φ 0 si + vmax * r ≤ smax) :
    ∀ t ∈ Set.Icc (0:ℝ) r,
      0 ≤ Φ t vi ∧ Φ t vi ≤ vmax ∧ 0 ≤ Φ t si ∧ Φ t si ≤ smax := by
  have hvmax0 : (0:ℝ) < vmax := lt_trans hc0 hcv
  have hvhi : ∀ t ∈ Set.Icc (0:ℝ) r, Φ t vi ≤ vmax := by
    have hmain := strict_invariance_raw (g := fun y => y vi - vmax) hwf (by fun_prop)
      (hbnd := ?_) hcurve (by simpa using hv0hi)
    · intro t ht; simpa using hmain t ht
    · intro x hx0
      have hxv : x vi = vmax := by linarith [hx0]
      have hlie : Lie sys (fun y => y vi - vmax) x = odeField sys x vi := by
        have heq : (fun y : State V => y vi - vmax) = (fun y => (1:ℝ) * y vi + (-vmax)) := by
          funext y; ring
        rw [heq]; simpa using lie_affine_coord sys hwf vi 1 (-vmax) x
      rw [hlie, hfv x, hxv]; nlinarith [hk, hcv]
  have hvlo : ∀ t ∈ Set.Icc (0:ℝ) r, 0 ≤ Φ t vi := by
    have hmain := strict_invariance_raw (g := fun y => -(y vi)) hwf (by fun_prop)
      (hbnd := ?_) hcurve (by simpa using hv0lo)
    · intro t ht; have h := hmain t ht; simpa using h
    · intro x hx0
      have hxv : x vi = 0 := by simpa using hx0
      have hlie : Lie sys (fun y => -(y vi)) x = - odeField sys x vi := by
        have heq : (fun y : State V => -(y vi)) = (fun y => (-1:ℝ) * y vi + 0) := by
          funext y; ring
        rw [heq]; simpa using lie_affine_coord sys hwf vi (-1) 0 x
      rw [hlie, hfv x, hxv]; nlinarith [hk, hc0]
  have hshi : ∀ t ∈ Set.Icc (0:ℝ) r, Φ t si ≤ smax := by
    have hgb := growth_bound_raw (sys := sys) si vmax hcurve
      (fun t ht => by rw [hfs (Φ t)]; exact hvhi t ht)
    intro t ht
    have hmono : vmax * t ≤ vmax * r := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hvmax0)
    linarith [hgb t ht, hmono, hZ3]
  have hslo : ∀ t ∈ Set.Icc (0:ℝ) r, 0 ≤ Φ t si := by
    have hmain := nonstrict_antitone_raw (g := fun y => -(y si)) hwf (by fun_prop) hcurve
      (fun t ht => by
        have hlie : Lie sys (fun y => -(y si)) (Φ t) = - odeField sys (Φ t) si := by
          have heq : (fun y : State V => -(y si)) = (fun y => (-1:ℝ) * y si + 0) := by
            funext y; ring
          rw [heq]; simpa using lie_affine_coord sys hwf si (-1) 0 (Φ t)
        rw [hlie, hfs (Φ t)]; simpa using hvlo t ht)
    intro t ht
    have h := hmain t ht
    have h2 : -(Φ t si) ≤ -(Φ 0 si) := by simpa using h
    linarith [h2, hs0lo]
  intro t ht
  exact ⟨hvlo t ht, hvhi t ht, hslo t ht, hshi t ht⟩

/-! ## Chaining — concatenating `sem` runs to reach the full parser duration `[0,Tᵢ]` -/

/-- **Gluing (`sem`-ode transitivity).** Two consecutive `sem` runs of `ode sys dom` compose into one
of the summed duration. Concatenate the integral curves `Φ` (on `[0,a]`) and `Ψ` (on `[0,b]`) into
`Θ t = if t ≤ a then Φ t else Ψ (t−a)`; the junction derivative matches via `HasDerivWithinAt.union`
(both sides evaluate the field at `ν = Φ a = Ψ 0`), interior points transfer by `nhdsWithin`
equality. Domain holds piecewise. This is the reusable core of the chaining that reaches `[0,Tᵢ]`. -/
theorem sem_ode_glue {sys : ODESystem V} {dom : Formula V} (hwf : sys.WellFormed)
    {ω ν μ : State V} (h1 : Program.sem (.ode sys dom) ω ν)
    (h2 : Program.sem (.ode sys dom) ν μ) :
    Program.sem (.ode sys dom) ω μ := by
  obtain ⟨a, Φ, ha, hΦ0, hΦa, hcΦ, hdΦ⟩ := (sem_ode_iff_integralCurve hwf).mp h1
  obtain ⟨b, Ψ, hb, hΨ0, hΨb, hcΨ, hdΨ⟩ := (sem_ode_iff_integralCurve hwf).mp h2
  set Θ : ℝ → State V := fun t => if t ≤ a then Φ t else Ψ (t - a) with hΘ
  have hΘle : ∀ t, t ≤ a → Θ t = Φ t := fun t ht => by simp only [hΘ, if_pos ht]
  have hΘa : Θ a = ν := by rw [hΘle a le_rfl]; exact hΦa
  have hΘeqΨ : ∀ t, a ≤ t → Θ t = Ψ (t - a) := by
    intro t ht
    rcases eq_or_lt_of_le ht with rfl | hlt
    · rw [hΘa, ← hΨ0]; simp
    · simp only [hΘ, if_neg (not_le.mpr hlt)]
  refine (sem_ode_iff_integralCurve hwf).mpr ⟨a + b, Θ, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [hΘle 0 ha]; exact hΦ0
  · rw [hΘeqΨ (a + b) (by linarith)]; simpa using hΨb
  · -- integral curve on Icc 0 (a+b)
    intro t ht
    have hLeft : t ≤ a → HasDerivWithinAt Θ (odeField sys (Θ t)) (Set.Icc 0 a) t := by
      intro hta
      have hc := (hcΦ t ⟨ht.1, hta⟩)
      rw [hΘle t hta]
      exact hc.congr (fun u hu => hΘle u hu.2) (hΘle t hta)
    have hRight : a ≤ t → HasDerivWithinAt Θ (odeField sys (Θ t)) (Set.Icc a (a + b)) t := by
      intro hat
      have htb : t - a ∈ Set.Icc (0:ℝ) b := ⟨by linarith, by linarith [ht.2]⟩
      have hΨt := hcΨ (t - a) htb
      have hshift : HasDerivWithinAt (fun u : ℝ => u - a) (1 : ℝ) (Set.Icc a (a + b)) t :=
        (hasDerivWithinAt_id t _).sub_const a
      have hmaps : Set.MapsTo (fun u : ℝ => u - a) (Set.Icc a (a + b)) (Set.Icc 0 b) :=
        fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hcomp := HasDerivWithinAt.scomp t hΨt hshift hmaps
      rw [one_smul] at hcomp
      rw [hΘeqΨ t hat]
      exact hcomp.congr (fun u hu => hΘeqΨ u hu.1) (hΘeqΨ t hat)
    rcases le_total t a with hta | hat
    · rcases eq_or_lt_of_le hta with rfl | hlt
      · have hu := (hLeft le_rfl).union (hRight le_rfl)
        rwa [Set.Icc_union_Icc_eq_Icc ha (by linarith)] at hu
      · refine (hLeft hta).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin.mpr ⟨Set.Iio a, isOpen_Iio, hlt,
          fun u hu => ⟨hu.2.1, le_of_lt hu.1⟩⟩
    · rcases eq_or_lt_of_le hat with rfl | hlt
      · have hu := (hLeft le_rfl).union (hRight le_rfl)
        rwa [Set.Icc_union_Icc_eq_Icc ha (by linarith)] at hu
      · refine (hRight hat).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin.mpr ⟨Set.Ioi a, isOpen_Ioi, hlt,
          fun u hu => ⟨le_of_lt hu.1, hu.2.2⟩⟩
  · -- domain holds on Icc 0 (a+b)
    intro t ht
    rcases le_total t a with hta | hat
    · rw [hΘle t hta]; exact hdΦ t ⟨ht.1, hta⟩
    · rw [hΘeqΨ t hat]; exact hdΨ (t - a) ⟨by linarith, by linarith [ht.2]⟩

/-- **Duration-explicit run.** `RunFor sys dom d ν ν'`: an integral curve of `odeField sys` of
duration **exactly** `d`, from `ν` to `ν'`, staying in `dom`. Exposes the duration (which `sem`
hides) so chaining can count steps. `RunFor → sem` and it composes additively. -/
def RunFor (sys : ODESystem V) (dom : Formula V) (d : ℝ) (ν ν' : State V) : Prop :=
  0 ≤ d ∧ ∃ Φ : ℝ → State V, Φ 0 = ν ∧ Φ d = ν' ∧
    IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 d) ∧
    (∀ t ∈ Set.Icc (0:ℝ) d, Formula.sat dom (Φ t))

theorem RunFor.toSem {sys : ODESystem V} {dom : Formula V} (hwf : sys.WellFormed)
    {d : ℝ} {ν ν' : State V} (h : RunFor sys dom d ν ν') :
    Program.sem (.ode sys dom) ν ν' := by
  obtain ⟨hd, Φ, h0, hd', hc, hdom⟩ := h
  exact (sem_ode_iff_integralCurve hwf).mpr ⟨d, Φ, hd, h0, hd', hc, hdom⟩

/-- **Zero run.** `RunFor 0 ν ν` (the constant curve on the singleton `{0}`). -/
theorem RunFor.zero {sys : ODESystem V} {dom : Formula V} {ν : State V}
    (hν : Formula.sat dom ν) : RunFor sys dom 0 ν ν := by
  refine ⟨le_rfl, fun _ => ν, rfl, rfl, ?_, ?_⟩
  · intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have : (Set.Icc (0:ℝ) 0) \ {0} = (∅ : Set ℝ) := by
      simp [Set.Icc_self]
    rw [this, nhdsWithin_empty]
    exact Filter.tendsto_bot
  · intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0; exact hν

/-- **Shorten.** A run of duration `d` restricts to any shorter duration `d' ≤ d`. -/
theorem RunFor.shorten {sys : ODESystem V} {dom : Formula V} {d d' : ℝ} {ν ν' : State V}
    (h : RunFor sys dom d ν ν') (hd' : 0 ≤ d') (hle : d' ≤ d) :
    ∃ ν'', RunFor sys dom d' ν ν'' := by
  obtain ⟨_, Φ, h0, _, hc, hdom⟩ := h
  refine ⟨Φ d', hd', Φ, h0, rfl, hc.mono (Set.Icc_subset_Icc_right hle), ?_⟩
  intro t ht; exact hdom t ⟨ht.1, le_trans ht.2 hle⟩

/-- **Additive gluing (duration-explicit).** `RunFor d₁ ν ν' → RunFor d₂ ν' ν'' → RunFor (d₁+d₂)`.
Same concatenation as `sem_ode_glue`, keeping the summed duration. -/
theorem RunFor.glue {sys : ODESystem V} {dom : Formula V} {a b : ℝ} {ω ν μ : State V}
    (h1 : RunFor sys dom a ω ν) (h2 : RunFor sys dom b ν μ) :
    RunFor sys dom (a + b) ω μ := by
  obtain ⟨ha, Φ, hΦ0, hΦa, hcΦ, hdΦ⟩ := h1
  obtain ⟨hb, Ψ, hΨ0, hΨb, hcΨ, hdΨ⟩ := h2
  set Θ : ℝ → State V := fun t => if t ≤ a then Φ t else Ψ (t - a) with hΘ
  have hΘle : ∀ t, t ≤ a → Θ t = Φ t := fun t ht => by simp only [hΘ, if_pos ht]
  have hΘa : Θ a = ν := by rw [hΘle a le_rfl]; exact hΦa
  have hΘeqΨ : ∀ t, a ≤ t → Θ t = Ψ (t - a) := by
    intro t ht
    rcases eq_or_lt_of_le ht with rfl | hlt
    · rw [hΘa, ← hΨ0]; simp
    · simp only [hΘ, if_neg (not_le.mpr hlt)]
  refine ⟨by linarith, Θ, by rw [hΘle 0 ha]; exact hΦ0,
    by rw [hΘeqΨ (a + b) (by linarith)]; simpa using hΨb, ?_, ?_⟩
  · intro t ht
    have hLeft : t ≤ a → HasDerivWithinAt Θ (odeField sys (Θ t)) (Set.Icc 0 a) t := by
      intro hta
      have hc := (hcΦ t ⟨ht.1, hta⟩)
      rw [hΘle t hta]
      exact hc.congr (fun u hu => hΘle u hu.2) (hΘle t hta)
    have hRight : a ≤ t → HasDerivWithinAt Θ (odeField sys (Θ t)) (Set.Icc a (a + b)) t := by
      intro hat
      have htb : t - a ∈ Set.Icc (0:ℝ) b := ⟨by linarith, by linarith [ht.2]⟩
      have hΨt := hcΨ (t - a) htb
      have hshift : HasDerivWithinAt (fun u : ℝ => u - a) (1 : ℝ) (Set.Icc a (a + b)) t :=
        (hasDerivWithinAt_id t _).sub_const a
      have hmaps : Set.MapsTo (fun u : ℝ => u - a) (Set.Icc a (a + b)) (Set.Icc 0 b) :=
        fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hcomp := HasDerivWithinAt.scomp t hΨt hshift hmaps
      rw [one_smul] at hcomp
      rw [hΘeqΨ t hat]
      exact hcomp.congr (fun u hu => hΘeqΨ u hu.1) (hΘeqΨ t hat)
    rcases le_total t a with hta | hat
    · rcases eq_or_lt_of_le hta with rfl | hlt
      · have hu := (hLeft le_rfl).union (hRight le_rfl)
        rwa [Set.Icc_union_Icc_eq_Icc ha (by linarith)] at hu
      · exact (hLeft hta).mono_of_mem_nhdsWithin
          (mem_nhdsWithin.mpr ⟨Set.Iio a, isOpen_Iio, hlt, fun u hu => ⟨hu.2.1, le_of_lt hu.1⟩⟩)
    · rcases eq_or_lt_of_le hat with rfl | hlt
      · have hu := (hLeft le_rfl).union (hRight le_rfl)
        rwa [Set.Icc_union_Icc_eq_Icc ha (by linarith)] at hu
      · exact (hRight hat).mono_of_mem_nhdsWithin
          (mem_nhdsWithin.mpr ⟨Set.Ioi a, isOpen_Ioi, hlt, fun u hu => ⟨le_of_lt hu.1, hu.2.2⟩⟩)
  · intro t ht
    rcases le_total t a with hta | hat
    · rw [hΘle t hta]; exact hdΦ t ⟨ht.1, hta⟩
    · rw [hΘeqΨ t hat]; exact hdΨ (t - a) ⟨by linarith, by linarith [ht.2]⟩

/-- **Chaining terminates (uniform step ⟹ any duration).** Given a uniform positive step `r₀` and a
step lemma (`hstep`: from any `P`-point a `RunFor r₀` run lands at another `P`-point — supplied by
Picard + `box_invariance_rover`), every duration `T ≤ n·r₀` is reachable from a `P`-point in `n`
steps. `⌈T/r₀⌉` steps cover `[0,T]` — the uniform `r₀` guarantees finitely many steps, not a
shrinking `ε`. This is the termination the chaining needs. -/
theorem chainN {sys : ODESystem V} {dom : Formula V} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (P : State V → Prop)
    (hstep : ∀ ν, P ν → ∃ ν', P ν' ∧ RunFor sys dom r₀ ν ν')
    (hP0 : ∀ ν, P ν → Formula.sat dom ν) :
    ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → T ≤ n * r₀ → ∀ ν, P ν → ∃ ν', RunFor sys dom T ν ν' := by
  intro n
  induction n with
  | zero =>
    intro T hT0 hTle ν hν
    have : T = 0 := le_antisymm (by simpa using hTle) hT0
    subst this
    exact ⟨ν, RunFor.zero (hP0 ν hν)⟩
  | succ m ih =>
    intro T hT0 hTle ν hν
    by_cases hTr : T ≤ r₀
    · obtain ⟨ν', _, hrun⟩ := hstep ν hν
      exact hrun.shorten hT0 hTr
    · push_neg at hTr
      obtain ⟨ν₁, hP1, hrun1⟩ := hstep ν hν
      have hTm : T - r₀ ≤ (m : ℝ) * r₀ := by
        have h2 : ((m : ℝ) + 1) * r₀ = (m : ℝ) * r₀ + r₀ := by ring
        have h3 : T ≤ ((m : ℝ) + 1) * r₀ := by exact_mod_cast hTle
        linarith [h2, h3]
      obtain ⟨ν', hrun2⟩ := ih (T - r₀) (by linarith) hTm ν₁ hP1
      refine ⟨ν', ?_⟩
      have := hrun1.glue hrun2
      rwa [add_sub_cancel] at this

/-! ## `hstep` — uniform-step existence (Picard ⟹ `RunFor`) -/

/-- **Picard ⟹ a `RunFor` curve.** Given `IsPicardLindelof` data for `odeField sys` at `ν` over
`[0,r₀]` (the `r = 0` differential form) and domain-membership for the resulting curve (supplied by
`box_invariance_rover`), a length-`r₀` integral curve from `ν` exists, staying in `dom`. Isolates the
`IsPicardLindelof → RunFor` mechanism; the uniform-constants construction of the `IsPicardLindelof`
data (from the field bound, uniform over the box since `v'=k(c−v)`,`s'=v` are `s`-independent) is the
remaining input. -/
theorem picard_to_RunFor {sys : ODESystem V} {dom : Formula V}
    (ν : State V) {a L K : NNReal} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpl : IsPicardLindelof (fun _ : ℝ => odeField sys) (tmin := 0) (tmax := r₀)
      ⟨0, Set.left_mem_Icc.mpr hr₀.le⟩ ν a 0 L K)
    (hdom : ∀ Φ : ℝ → State V, Φ 0 = ν →
      IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r₀) →
      ∀ t ∈ Set.Icc (0:ℝ) r₀, Formula.sat dom (Φ t)) :
    ∃ Φ : ℝ → State V, Φ 0 = ν ∧
      IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r₀) ∧
      RunFor sys dom r₀ ν (Φ r₀) := by
  obtain ⟨α, hα0, hαderiv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα00 : α 0 = ν := by simpa using hα0
  have hcurve : IsIntegralCurveOn α (fun _ => odeField sys) (Set.Icc 0 r₀) :=
    fun t ht => hαderiv t ht
  exact ⟨α, hα00, hcurve, hr₀.le, α, hα00, rfl, hcurve, hdom α hα00 hcurve⟩

/-- **Global Lipschitz for the affine rover field.** `v'=k(c−v)`, `s'=v` is affine, hence globally
`max(k,1)`-Lipschitz (per-coordinate: the v-equation is `k`-Lipschitz in `v`, the s-equation is
`1`-Lipschitz in `v`). Uniform `K` for the `IsPicardLindelof` construction — no compactness needed. -/
theorem odeField_lipschitz_rover {sys : ODESystem V} (vi si : V) (k c : ℝ) (hk : 0 ≤ k)
    (hfv : ∀ x : State V, odeField sys x vi = k * (c - x vi))
    (hfs : ∀ x : State V, odeField sys x si = x vi)
    (hother : ∀ (x : State V) i, i ≠ vi → i ≠ si → odeField sys x i = 0) :
    LipschitzWith (Real.toNNReal (max k 1)) (odeField sys) := by
  have hKnn : (0:ℝ) ≤ max k 1 := le_trans hk (le_max_left _ _)
  have hcoe : ((Real.toNNReal (max k 1) : NNReal) : ℝ) = max k 1 := Real.coe_toNNReal _ hKnn
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [hcoe]
  have hdxy : (0:ℝ) ≤ dist x y := dist_nonneg
  by_cases hvi : i = vi
  · rw [hvi, hfv, hfv, Real.dist_eq]
    have heq : k * (c - x vi) - k * (c - y vi) = k * (y vi - x vi) := by ring
    rw [heq, abs_mul, abs_of_nonneg hk]
    have h1 : |y vi - x vi| ≤ dist x y := by
      rw [← Real.dist_eq, dist_comm]; exact dist_le_pi_dist x y vi
    have h2 : k * |y vi - x vi| ≤ k * dist x y := by nlinarith [abs_nonneg (y vi - x vi)]
    nlinarith [le_max_left k 1, mul_le_mul_of_nonneg_right (le_max_left k 1) hdxy]
  · by_cases hsi : i = si
    · rw [hsi, hfs, hfs, Real.dist_eq]
      have h1 : |x vi - y vi| ≤ dist x y := by rw [← Real.dist_eq]; exact dist_le_pi_dist x y vi
      nlinarith [mul_le_mul_of_nonneg_right (le_max_right k 1) hdxy, h1]
    · rw [hother x i hvi hsi, hother y i hvi hsi, dist_self]
      positivity

end RelCertifier






