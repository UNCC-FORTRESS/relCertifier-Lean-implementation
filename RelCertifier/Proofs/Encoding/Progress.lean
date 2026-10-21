/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The progress certificate discharges reposition progress

`RepoProgress` (`CoverResp.lean`) asks, at a reposition node `q`, for a chain of right cycles
of `q` ending with a switch along a non-self exit. The tool's progress certificate
(`Trusted/ProgressEmit.lean`) gives it by a staged rate argument, and this file proves that:

* `cycle_growth`: along a run on which the field of `x` is at least `r`, `x` grows by `r`
  per unit time; `hits_line`: a coordinate that starts below `θ` and reaches it passes through
  `x = θ` (the intermediate value theorem); `keep_preserved`: a crossed threshold whose field is
  nonnegative at or below it stays crossed (the differential-invariant route of the cuts);
* `phase`: the cycles of one stage. From a cycle start (the right in `q`'s guard, the anchor
  and the stage's invariant at the merged state) the right either lands (an exit is enabled at
  a start already crossed, on the main coordinate's crossing line, or at a cycle end by
  Assumption 1) or reaches a cycle start with the stage's coordinate crossed; each cycle
  without crossing advances the coordinate by `r ε_R`, so the cycles are bounded;
* `repoProgress_one`, `repoProgress_two`: the certificate with one or two (upward) stages
  gives `RepoProgress`; `repoProgress_one_down` (with `cycle_decay`, `hits_line_down`,
  `phase_down`, `land_at_start_down`) the mirror for a single DOWNWARD stage, the only
  downward form the suite's records use (`vehicle_hypercert`).

Each cycle's run is Assumption 1's (from a guard state, duration `ε_R`); the anchor is kept by
the reposition flow certificate; the pruned exits are excluded by the right-only
non-connection certificate; the certificate's facts are read at the merged states of the run,
where the region `R` holds (implied by the anchor and, pre-joint, the left guard).
-/
import RelCertifier.Proofs.Encoding.CoverResp
import RelCertifier.Proofs.Encoding.RepoPrefix

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## Runs of the right alone -/

/-- A right coordinate is continuous along a right-only run. -/
theorem _root_.DLCalTiming.ODESol.coord_continuousOn {fR : Fin n → Term (Var n)}
    {domR : Formula (Var n)} {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (j : Fin n) :
    ContinuousOn (fun t => Φ t (Rv j)) (Icc 0 T) :=
  fun t ht => (H.hder t ht _ (rightBlock_mem' fR (Term.const 1) j)).continuousWithinAt

/-- The field of a right coordinate at a merged state is its value at the right part. -/
theorem eval_fR_merge {fR : Fin n → Term (Var n)} (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (j : Fin n) (ω₀ y ρ : State (Var n)) :
    Term.eval (fR j) (mergeLR ω₀ y ρ) = Term.eval (fR j) ρ := by
  refine Term.coincidence (fR j) (fun v hv => ?_)
  obtain ⟨i, rfl⟩ := hfR j hv
  exact mergeLR_R ω₀ _ _ i

/-- **Growth under a rate bound.** -/
theorem cycle_growth {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (j : Fin n) (r : ℝ)
    (hrate : ∀ t ∈ Icc (0 : ℝ) T, r ≤ Term.eval (fR j) (Φ t)) :
    ρ (Rv j) + r * T ≤ Φ T (Rv j) := by
  have hmem := rightBlock_mem' fR (Term.const 1) j
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => Φ u (Rv j) - r * u) (Term.eval (fR j) (Φ t) - r) (Icc 0 T) t := by
    intro t ht
    have h1 := H.hder t ht _ hmem
    rw [eval_unit_mul] at h1
    have h2 : HasDerivWithinAt (fun u : ℝ => r * u) r (Icc 0 T) t := by
      simpa using ((hasDerivAt_id t).const_mul r).hasDerivWithinAt
    exact h1.sub h2
  have hcont : ContinuousOn (fun u => Φ u (Rv j) - r * u) (Icc 0 T) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  have hmono : MonotoneOn (fun u => Φ u (Rv j) - r * u) (Icc 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcont (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have := hrate t (Ioo_subset_Icc_self ht)
      linarith
  have h := hmono ⟨le_rfl, H.hr⟩ ⟨H.hr, le_rfl⟩ H.hr
  simp only [H.hΦ0, mul_zero, sub_zero] at h
  linarith

/-- **The crossing line.** -/
theorem hits_line {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (j : Fin n) (θ : ℝ)
    (h0 : ρ (Rv j) < θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hθ : θ ≤ Φ t (Rv j)) :
    ∃ t' ∈ Icc (0 : ℝ) T, Φ t' (Rv j) = θ := by
  have hcont : ContinuousOn (fun u => Φ u (Rv j)) (Icc 0 t) :=
    (H.coord_continuousOn j).mono (Icc_subset_Icc le_rfl ht.2)
  obtain ⟨t', ht', hct⟩ := intermediate_value_Icc ht.1 hcont
    ⟨by simp only [H.hΦ0]; exact h0.le, hθ⟩
  exact ⟨t', ⟨ht'.1, ht'.2.trans ht.2⟩, hct⟩

/-- **Decay under a rate bound** (the mirror of `cycle_growth`): along a run on which the field
of `x` is at most `−r`, `x` falls by `r` per unit time. -/
theorem cycle_decay {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (j : Fin n) (r : ℝ)
    (hrate : ∀ t ∈ Icc (0 : ℝ) T, Term.eval (fR j) (Φ t) ≤ -r) :
    Φ T (Rv j) ≤ ρ (Rv j) - r * T := by
  have hmem := rightBlock_mem' fR (Term.const 1) j
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => Φ u (Rv j) + r * u) (Term.eval (fR j) (Φ t) + r) (Icc 0 T) t := by
    intro t ht
    have h1 := H.hder t ht _ hmem
    rw [eval_unit_mul] at h1
    have h2 : HasDerivWithinAt (fun u : ℝ => r * u) r (Icc 0 T) t := by
      simpa using ((hasDerivAt_id t).const_mul r).hasDerivWithinAt
    exact h1.add h2
  have hcont : ContinuousOn (fun u => Φ u (Rv j) + r * u) (Icc 0 T) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  have hanti : AntitoneOn (fun u => Φ u (Rv j) + r * u) (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have := hrate t (Ioo_subset_Icc_self ht)
      linarith
  have h := hanti ⟨le_rfl, H.hr⟩ ⟨H.hr, le_rfl⟩ H.hr
  simp only [H.hΦ0, mul_zero, add_zero] at h
  linarith

/-- **The crossing line, downward** (the mirror of `hits_line`): a coordinate that starts above
`θ` and reaches it passes through `x = θ`. -/
theorem hits_line_down {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (j : Fin n) (θ : ℝ)
    (h0 : θ < ρ (Rv j)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hθ : Φ t (Rv j) ≤ θ) :
    ∃ t' ∈ Icc (0 : ℝ) T, Φ t' (Rv j) = θ := by
  have hcont : ContinuousOn (fun u => Φ u (Rv j)) (Icc 0 t) :=
    (H.coord_continuousOn j).mono (Icc_subset_Icc le_rfl ht.2)
  obtain ⟨t', ht', hct⟩ := intermediate_value_Icc' ht.1 hcont
    ⟨hθ, by simp only [H.hΦ0]; exact h0.le⟩
  exact ⟨t', ⟨ht'.1, ht'.2.trans ht.2⟩, hct⟩

/-- A formula over both sides reads the same at `mergeLR (mergeLR y y w) (mergeLR y y w) μ` and
at `mergeLR y y μ`. -/
theorem sat_merge_merge {φ : Formula (Var n)} (hφ : φ.fv ⊆ range Lv ∪ range Rv)
    (y w μ : State (Var n)) :
    Formula.sat φ (mergeLR (mergeLR y y w) (mergeLR y y w) μ) ↔ Formula.sat φ (mergeLR y y μ) :=
  sat_of_agree hφ (fun i => by rw [mergeLR_L, mergeLR_L, mergeLR_L])
    (fun i => by rw [mergeLR_R, mergeLR_R])

/-! ## The node's context -/

section Node

variable (G : SearchGraph (Var n)) (fR : Fin n → Term (Var n)) (domL domR gL : Formula (Var n))
  (guard : ℕ → Formula (Var n)) (q : ℕ) (m : RMode (Var n)) (hm : G.modeAt q = some m)
  (hsys : m.sys = rightBlock fR (Term.const 1)) (hdomM : m.dom = domR)
  (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (hgL : gL.fv ⊆ range Lv) (hguardR : ∀ q', (guard q').fv ⊆ range Rv)
  (hgR : GuardsRight G) (hguards : ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
  (A : Formula (Var n)) (hAfv : A.fv ⊆ range Lv ∪ range Rv)
  (hAdom : ∀ y, Formula.sat A y → Formula.sat domL y ∧ Formula.sat domR y)
  (pre : Bool)
  (epsR : ℝ) (hε : 0 < epsR)
  -- the right clock: a coordinate of neither side (`RRespPC`'s clock, cap `ε_R`)
  (tr : Var n) (htrL : tr ∉ range Lv) (htrR : tr ∉ range Rv)
  (reg : Formula (Var n)) (hregR : reg.fv ⊆ range Rv)
  (hAreg : ∀ y, Formula.sat A y → Formula.sat reg y)
  (hex : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x →
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR x epsR Φ)
  (hcomp : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x → ∀ t Φ, t ≤ epsR →
    ODESol (rightBlock fR (Term.const 1)) domR x t Φ →
    ∃ e ∈ G.edgesFrom q, Formula.sat (guard e.tgt) (Φ t))
  (hboxD : ∀ σ ω, Formula.sat A σ → (pre = true → Formula.sat gL σ) →
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (Formula.and domL domR)) σ ω → Formula.sat A ω)
  (hpruneD : ∀ e ∈ G.edgesFrom q, e.pruned = true → ∀ σ ω, Formula.sat A σ →
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (Formula.and domL domR)) σ ω → ¬ Formula.sat e.guard ω)
  (R : Formula (Var n)) (hR : ∀ y, Formula.sat A y → (pre = true → Formula.sat gL y) →
    Formula.sat R y)

/-- The landing outcome (`RepoProgress`'s post): the chain ends with a switch along a non-self,
non-pruned exit, the anchor at the switch state, the left untouched. -/
def Landed (y ρ : State (Var n)) (q' : ℕ) (μ : State (Var n)) : Prop :=
  ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ q' = e.tgt ∧ SwitchLegal e μ ∧
    Formula.sat A (mergeLR y y μ) ∧ ∀ i, μ (Lv i) = ρ (Lv i)

/-- A cycle start: the right in `q`'s guard, the anchor and the stage's invariant `Kf` at the
merged state, the left untouched. -/
def CycleStart (Kf : Formula (Var n)) (y ρ μ : State (Var n)) : Prop :=
  Formula.sat (guard q) μ ∧ Formula.sat A (mergeLR y y μ) ∧ Formula.sat Kf (mergeLR y y μ) ∧
    ∀ i, μ (Lv i) = ρ (Lv i)

/-! ### The right clock is invisible to the landing and cycle-start facts -/

include hgR htrL htrR in
/-- A landing is insensitive to the right clock (the clocked end state carries it). -/
theorem landed_update_tr {y ρ : State (Var n)} {q' : ℕ} {μ : State (Var n)} (c : ℝ)
    (h : Landed G q A y ρ q' μ) : Landed G q A y ρ q' (Function.update μ tr c) := by
  obtain ⟨e, he, hneq, hnp, hq', hleg, hA, hL⟩ := h
  refine ⟨e, he, hneq, hnp, hq', (switchLegal_update hgR he htrR _ _).mpr hleg, ?_,
    fun i => (update_Lv_of_notMem htrL _ _ i).trans (hL i)⟩
  rw [mergeLR_update_R y y μ htrR c]; exact hA

include hguardR htrL htrR in
/-- A cycle start is insensitive to the right clock. -/
theorem cycleStart_update_tr {Kf : Formula (Var n)} {y ρ μ : State (Var n)} (c : ℝ)
    (h : CycleStart guard q A Kf y ρ μ) :
    CycleStart guard q A Kf y ρ (Function.update μ tr c) := by
  obtain ⟨hg, hA, hK, hL⟩ := h
  refine ⟨(sat_update_of_notMem (fun h => htrR (hguardR q h)) _ _).mpr hg, ?_, ?_,
    fun i => (update_Lv_of_notMem htrL _ _ i).trans (hL i)⟩
  · rw [mergeLR_update_R y y μ htrR c]; exact hA
  · rw [mergeLR_update_R y y μ htrR c]; exact hK

include hsys hdomM hfR hdomR htrR in
/-- The right clock is fresh for the node's flow. -/
theorem tr_notMem_ode_node : tr ∉ (Program.ode m.sys m.dom).fv := by
  intro h
  have hy := vars_ode_sub _ _ (Or.inl h)
  rw [hsys, hdomM] at hy
  rcases hy with (hy | hy) | hy
  · exact htrR (rightBlock_boundSet_sub fR (Term.const 1) hy)
  · exact htrR (rightBlock_readVars_sub fR (Term.const 1) hfR (by simp [Term.fv]) hy)
  · exact htrR (hdomR hy)

include hfR hdomL hdomR hgL hAfv hAdom hboxD hR in
/-- The merged run of a right-only run: the frozen-left program run to every time, with the
anchor and the region there. -/
theorem merged_run {y ρ : State (Var n)} (hyρ : ∀ i, y (Rv i) = ρ (Rv i))
    (hA : Formula.sat A y) (hgLy : pre = true → Formula.sat gL y)
    {T : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
        (Formula.and domL domR)) (mergeLR y y ρ) (mergeLR y y (Φ t)) ∧
      Formula.sat A (mergeLR y y (Φ t)) ∧ Formula.sat R (mergeLR y y (Φ t)) := by
  intro t ht
  have hAρ : Formula.sat A (mergeLR y y ρ) :=
    (sat_of_agree hAfv (y := y) (fun i => mergeLR_L y y ρ i)
      (fun i => by rw [mergeLR_R, hyρ i])).mpr hA
  have hgLρ : pre = true → Formula.sat gL (mergeLR y y ρ) := fun hp =>
    (sat_merge_L hgL y y ρ).mpr (hgLy hp)
  have hrun := right_sol_merge_joint hfR hdomL hdomR (ODESol_restrict H ht.1 ht.2) y y
    (hAdom y hA).1
  have hAt := hboxD _ _ hAρ hgLρ hrun
  exact ⟨hrun, hAt, hR _ hAt (fun hp => (sat_merge_L hgL y y _).mpr (hgLy hp))⟩

include hfR hdomL hdomR hgL hAfv hAdom hboxD hR in
/-- **A crossed threshold is kept** when the coordinate's field is nonnegative at or below it
on the region. -/
theorem keep_preserved (z : Fin n) (z₀ : ℝ)
    (hkeep : ∀ y, Formula.sat R y → y (Rv z) ≤ z₀ → 0 ≤ Term.eval (fR z) y)
    {y ρ : State (Var n)} (hyρ : ∀ i, y (Rv i) = ρ (Rv i))
    (hA : Formula.sat A y) (hgLy : pre = true → Formula.sat gL y)
    {T : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ)
    (h0 : z₀ ≤ ρ (Rv z)) : z₀ ≤ Φ T (Rv z) := by
  have hmr := merged_run fR domL domR gL hfR hdomL hdomR hgL A hAfv hAdom pre hboxD R hR hyρ
    hA hgLy H
  -- the merged run, with the region in its domain
  set D := Formula.and domL (Formula.and domR R) with hD
  obtain ⟨hr, h0', hder, hmask, -⟩ := right_sol_merge hfR hdomR H y y
  have HD : ODESol (rightBlock fR (Term.const 1)) D (mergeLR y y ρ) T
      (fun t => mergeLR y y (Φ t)) := by
    refine ⟨hr, h0', hder, hmask, fun t ht => ?_⟩
    obtain ⟨-, hAt, hRt⟩ := hmr t ht
    exact ⟨(hAdom _ hAt).1, (hAdom _ hAt).2, hRt⟩
  have hrunD : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1)) D)
      (mergeLR y y ρ) (mergeLR y y (Φ T)) := by
    rw [hD]
    exact (sem_rightBlock_frozen_iff hfR (by simp [Term.fv])).mpr
      (DLCalTiming.sem_ode_restrict HD H.hr le_rfl)
  have hinit : Term.eval (thrGe (Rv z) z₀) (mergeLR y y ρ) ≤ 0 := by
    simp [thrGe, Term.eval, AOp.interp, mergeLR_R]; linarith
  have hb := boxle_thrGe_R z z₀ (fun _ => Term.const 0) fR 1 zero_le_one D D (fun x h => h)
    (fun w hw hle => hkeep w hw.2.2 hle) hinit _ hrunD
  simp [thrGe, Term.eval, AOp.interp, mergeLR_R] at hb
  linarith

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex
  hcomp hboxD hpruneD hR in
/-- **The cycles of one stage.** Coordinate `z` crosses `z₀` upward at rate `rz` while below it
and while the stage's invariant `Kf` holds (`Kf` right-only, kept along runs from anchored
states); the main coordinate `j` lands on its line `θ` or at a start already crossed. From a
cycle start with `z₀ − z ≤ N · rz · ε_R`, within `N` cycles the right lands, or reaches a cycle
start with `z` crossed. The keep fact of `z` is needed only when `z` is not the landing
coordinate (a crossing of the landing coordinate lands at once). -/
theorem phase (j : Fin n) (θ : ℝ)
    (hline : ∀ y, Formula.sat R y → y (Rv j) = θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (hstart : ∀ y, Formula.sat R y → Formula.sat (guard q) y → θ ≤ y (Rv j) →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (z : Fin n) (z₀ rz : ℝ) (hrz : 0 < rz) (Kf : Formula (Var n)) (hKfv : Kf.fv ⊆ range Rv)
    (hKkeep : ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat A y →
      (pre = true → Formula.sat gL y) → Formula.sat Kf y →
      ∀ T Φ, ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ → Formula.sat Kf (mergeLR y y (Φ T)))
    (hrate : ∀ y, Formula.sat R y → Formula.sat Kf y → y (Rv z) < z₀ → rz ≤ Term.eval (fR z) y)
    (hkeep : (∀ y, Formula.sat R y → y (Rv z) ≤ z₀ → 0 ≤ Term.eval (fR z) y) ∨ (z = j ∧ z₀ = θ)) :
    ∀ (N : ℕ) (y ρ : State (Var n)), (∀ i, y (Rv i) = ρ (Rv i)) →
      (pre = true → Formula.sat gL y) → CycleStart guard q A Kf y ρ ρ →
      z₀ - ρ (Rv z) ≤ N * (rz * epsR) →
      RRespPC G tr epsR q (fun q' μ => Landed G q A y ρ q' μ ∨
        (q' = q ∧ CycleStart guard q A Kf y ρ μ ∧ z₀ ≤ μ (Rv z))) ρ := by
  have htrode := tr_notMem_ode_node fR domR m hsys hdomM hfR hdomR tr htrR
  have htrdom : tr ∉ m.dom.fv := ((notMem_ode_fv_iff _ _ _).mp htrode).2.2
  intro N
  induction N with
  | zero =>
      intro y ρ _ _ hcs hN
      simp only [CharP.cast_eq_zero, zero_mul] at hN
      exact rrespPC_stop (Or.inr ⟨rfl, hcs, by linarith⟩)
  | succ N ih =>
      intro y ρ hyρ hgLy hcs hN
      obtain ⟨hg, hA, hK, hL⟩ := hcs
      have hAy : Formula.sat A y :=
        (sat_of_agree hAfv (x := mergeLR y y ρ) (y := y) (fun i => mergeLR_L y y ρ i)
          (fun i => by rw [mergeLR_R, hyρ i])).mp hA
      have hKρ : Formula.sat Kf ρ := (sat_merge_R hKfv y y ρ).mp hK
      have hKy : Formula.sat Kf y :=
        (Formula.coincidence Kf (fun v hv => by
          obtain ⟨i, rfl⟩ := hKfv hv; exact hyρ i)).mpr hKρ
      have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR y y ρ).mp (hAdom _ hA).2
      -- the landing at the start, already crossed
      by_cases hx0 : θ ≤ ρ (Rv j)
      · have hRρ : Formula.sat R (mergeLR y y ρ) := hR _ hA (fun hp =>
          (sat_merge_L hgL y y ρ).mpr (hgLy hp))
        have hgρ : Formula.sat (guard q) (mergeLR y y ρ) :=
          (sat_merge_R (hguardR q) y y ρ).mpr hg
        obtain ⟨e, he, hneq, hnp, hge⟩ := hstart _ hRρ hgρ (by rw [mergeLR_R]; exact hx0)
        have hleg : SwitchLegal e ρ := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y ρ).mp hge
        have hdom : Formula.sat m.dom ρ := by rw [hdomM]; exact hρdom
        exact rrespPC_step hm he (sem_clockedSeg_zero m.sys m.dom tr epsR hε.le htrdom hdom)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR 0
            ⟨e, he, hneq, hnp, rfl, hleg, hA, hL⟩)))
      push Not at hx0
      -- one cycle
      obtain ⟨Φ, H⟩ := hex ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA))
      have hmr := merged_run fR domL domR gL hfR hdomL hdomR hgL A hAfv hAdom pre hboxD R hR
        hyρ hAy hgLy H
      have hHm : ODESol m.sys m.dom ρ epsR Φ := by rw [hsys, hdomM]; exact H
      -- the landing on the line within the cycle
      by_cases hcross : ∃ t ∈ Icc (0 : ℝ) epsR, θ ≤ Φ t (Rv j)
      · obtain ⟨t, ht, hθt⟩ := hcross
        obtain ⟨t', ht', hline'⟩ := hits_line H j θ hx0 ht hθt
        obtain ⟨-, hAt, hRt⟩ := hmr t' ht'
        obtain ⟨e, he, hneq, hnp, hge⟩ := hline _ hRt (by rw [mergeLR_R]; exact hline')
        have hleg : SwitchLegal e (Φ t') := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y _).mp hge
        exact rrespPC_step hm he
          (sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm ht'.1 ht'.2 ht'.2 htrode)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR t'
            ⟨e, he, hneq, hnp, rfl, hleg, hAt,
              fun i => (right_sol_left (ODESol_restrict H ht'.1 ht'.2) i).trans (hL i)⟩)))
      push Not at hcross
      -- the invariant along the cycle
      have hKt : ∀ t ∈ Icc (0 : ℝ) epsR, Formula.sat Kf (mergeLR y y (Φ t)) := fun t ht =>
        hKkeep y ρ hyρ hAy hgLy hKy t Φ (ODESol_restrict H ht.1 ht.2)
      -- the end of the cycle: a declared successor is enabled
      obtain ⟨-, hAe, hRe⟩ := hmr epsR ⟨hε.le, le_rfl⟩
      obtain ⟨e, he, hge⟩ := hcomp ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA)) epsR Φ le_rfl H
      have hleg : SwitchLegal e (Φ epsR) := by unfold SwitchLegal; rwa [hguards e he]
      have hflow := sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm H.hr le_rfl le_rfl htrode
      have hlegκ : SwitchLegal e (Function.update (Φ epsR) tr epsR) :=
        (switchLegal_update hgR he htrR _ _).mpr hleg
      have hLe : ∀ i, Φ epsR (Lv i) = ρ (Lv i) := fun i => (right_sol_left H i).trans (hL i)
      have hLeκ : ∀ i, Function.update (Φ epsR) tr epsR (Lv i) = ρ (Lv i) :=
        fun i => (update_Lv_of_notMem htrL _ _ i).trans (hLe i)
      by_cases hself : e.tgt = q
      · -- the self-loop: the next cycle start, with the measure decreased
        have hgnext : Formula.sat (guard q) (Φ epsR) := by rw [← hself]; exact hge
        have hKLR : Kf.fv ⊆ range Lv ∪ range Rv := fun v hv => Or.inr (hKfv hv)
        set y' := mergeLR y y (Φ epsR) with hy'
        have hgLy' : pre = true → Formula.sat gL y' := fun hp =>
          (sat_merge_L hgL y y _).mpr (hgLy hp)
        have hnext : CycleStart guard q A Kf y' (Φ epsR) (Φ epsR) :=
          ⟨hgnext, (sat_merge_merge hAfv y _ _).mpr hAe,
            (sat_merge_merge hKLR y _ _).mpr (hKt epsR ⟨hε.le, le_rfl⟩), fun _ => rfl⟩
        have hnextκ : CycleStart guard q A Kf y' (Function.update (Φ epsR) tr epsR)
            (Function.update (Φ epsR) tr epsR) := by
          obtain ⟨h1, h2, h3, -⟩ := cycleStart_update_tr guard q hguardR A tr htrL htrR epsR hnext
          exact ⟨h1, h2, h3, fun _ => rfl⟩
        have hgrow : z₀ - Φ epsR (Rv z) ≤ N * (rz * epsR) := by
          have hpos : (0 : ℝ) ≤ N * (rz * epsR) := by positivity
          by_cases hzend : z₀ ≤ Φ epsR (Rv z)
          · linarith
          push Not at hzend
          by_cases hz : ∃ t ∈ Icc (0 : ℝ) epsR, z₀ ≤ Φ t (Rv z)
          · -- crossed within the cycle: kept to its end (or it is the landing coordinate)
            exfalso
            obtain ⟨t, ht, hzt⟩ := hz
            rcases hkeep with hkeep | ⟨rfl, rfl⟩
            · have hsh := odeSol_shift H ht.1 ht.2 le_rfl
              have hmr' := hmr t ht
              have hAt' : Formula.sat A (mergeLR y y (Φ t)) := hmr'.2.1
              have hkept := keep_preserved fR domL domR gL hfR hdomL hdomR hgL A hAfv hAdom pre
                hboxD R hR z z₀ hkeep (y := mergeLR y y (Φ t)) (ρ := Φ t)
                (fun i => mergeLR_R y y _ i)
                ((sat_of_agree hAfv (y := mergeLR y y (Φ t)) (fun _ => rfl) (fun _ => rfl)).mp hAt')
                (fun hp => (sat_merge_L hgL y y _).mpr (hgLy hp)) hsh hzt
              simp only [add_sub_cancel] at hkept
              exact absurd hkept (not_le.mpr hzend)
            · exact absurd hzt (not_le.mpr (hcross t ht))
          · push Not at hz
            have hgr := cycle_growth H z rz (fun t ht => by
              obtain ⟨-, -, hRt⟩ := hmr t ht
              have := hrate _ hRt (hKt t ht) (by rw [mergeLR_R]; exact hz t ht)
              rwa [eval_fR_merge hfR] at this)
            have : (N.succ : ℝ) * (rz * epsR) = N * (rz * epsR) + rz * epsR := by
              push_cast; ring
            linarith
        have hgrowκ : z₀ - Function.update (Φ epsR) tr epsR (Rv z) ≤ N * (rz * epsR) := by
          rw [update_Rv_of_notMem htrR]; exact hgrow
        have hrest := ih y' (Function.update (Φ epsR) tr epsR)
          (fun i => by rw [hy', mergeLR_R, update_Rv_of_notMem htrR]) hgLy' hnextκ hgrowκ
        refine rrespPC_step hm he hflow hlegκ ?_
        rw [hself]
        refine rrespPC_mono ?_ hrest
        rintro q' μ (⟨e', he', hneq', hnp', rfl, hleg', hAμ, hμL⟩ | ⟨rfl, ⟨hg', hA', hK', hμL⟩, hz'⟩)
        · exact Or.inl ⟨e', he', hneq', hnp', rfl, hleg', (sat_merge_merge hAfv y _ _).mp hAμ,
            fun i => (hμL i).trans (hLeκ i)⟩
        · exact Or.inr ⟨rfl, ⟨hg', (sat_merge_merge hAfv y _ _).mp hA',
            (sat_merge_merge hKLR y _ _).mp hK', fun i => (hμL i).trans (hLeκ i)⟩, hz'⟩
      · -- a non-self successor: an exit (not pruned, by the non-connection certificate)
        have hnp : e.pruned = false := by
          by_contra hc
          have hp : e.pruned = true := by simpa using hc
          exact hpruneD e he hp _ _ hA (hmr epsR ⟨hε.le, le_rfl⟩).1
            ((switchLegal_merge hgR he y y).mpr hleg)
        exact rrespPC_step hm he hflow hlegκ
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR epsR
            ⟨e, he, hself, hnp, rfl, hleg, hAe, hLe⟩)))

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex
  hcomp hboxD hpruneD hR in
/-- **The cycles of one downward stage** (the mirror of `phase` for a single stage whose
coordinate is the landing one, the only downward form the suite's records use): `j` falls at
rate `r` while above `θ`; the right lands on the line `x = θ`, at a start already crossed
(`x ≤ θ`), or at a cycle end by Assumption 1; from a cycle start with `x − θ ≤ N · r · ε_R`,
within `N` cycles it lands or reaches a cycle start with `x` crossed. -/
theorem phase_down (j : Fin n) (θ : ℝ)
    (hline : ∀ y, Formula.sat R y → y (Rv j) = θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (hstart : ∀ y, Formula.sat R y → Formula.sat (guard q) y → y (Rv j) ≤ θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (r : ℝ) (hr : 0 < r)
    (hrate : ∀ y, Formula.sat R y → θ < y (Rv j) → Term.eval (fR j) y ≤ -r) :
    ∀ (N : ℕ) (y ρ : State (Var n)), (∀ i, y (Rv i) = ρ (Rv i)) →
      (pre = true → Formula.sat gL y) → CycleStart guard q A Formula.tt y ρ ρ →
      ρ (Rv j) - θ ≤ N * (r * epsR) →
      RRespPC G tr epsR q (fun q' μ => Landed G q A y ρ q' μ ∨
        (q' = q ∧ CycleStart guard q A Formula.tt y ρ μ ∧ μ (Rv j) ≤ θ)) ρ := by
  have htrode := tr_notMem_ode_node fR domR m hsys hdomM hfR hdomR tr htrR
  have htrdom : tr ∉ m.dom.fv := ((notMem_ode_fv_iff _ _ _).mp htrode).2.2
  intro N
  induction N with
  | zero =>
      intro y ρ _ _ hcs hN
      simp only [CharP.cast_eq_zero, zero_mul] at hN
      exact rrespPC_stop (Or.inr ⟨rfl, hcs, by linarith⟩)
  | succ N ih =>
      intro y ρ hyρ hgLy hcs hN
      obtain ⟨hg, hA, -, hL⟩ := hcs
      have hAy : Formula.sat A y :=
        (sat_of_agree hAfv (x := mergeLR y y ρ) (y := y) (fun i => mergeLR_L y y ρ i)
          (fun i => by rw [mergeLR_R, hyρ i])).mp hA
      have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR y y ρ).mp (hAdom _ hA).2
      -- the landing at the start, already crossed
      by_cases hx0 : ρ (Rv j) ≤ θ
      · have hRρ : Formula.sat R (mergeLR y y ρ) := hR _ hA (fun hp =>
          (sat_merge_L hgL y y ρ).mpr (hgLy hp))
        have hgρ : Formula.sat (guard q) (mergeLR y y ρ) :=
          (sat_merge_R (hguardR q) y y ρ).mpr hg
        obtain ⟨e, he, hneq, hnp, hge⟩ := hstart _ hRρ hgρ (by rw [mergeLR_R]; exact hx0)
        have hleg : SwitchLegal e ρ := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y ρ).mp hge
        have hdom : Formula.sat m.dom ρ := by rw [hdomM]; exact hρdom
        exact rrespPC_step hm he (sem_clockedSeg_zero m.sys m.dom tr epsR hε.le htrdom hdom)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR 0
            ⟨e, he, hneq, hnp, rfl, hleg, hA, hL⟩)))
      push Not at hx0
      -- one cycle
      obtain ⟨Φ, H⟩ := hex ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA))
      have hmr := merged_run fR domL domR gL hfR hdomL hdomR hgL A hAfv hAdom pre hboxD R hR
        hyρ hAy hgLy H
      have hHm : ODESol m.sys m.dom ρ epsR Φ := by rw [hsys, hdomM]; exact H
      -- the landing on the line within the cycle
      by_cases hcross : ∃ t ∈ Icc (0 : ℝ) epsR, Φ t (Rv j) ≤ θ
      · obtain ⟨t, ht, hθt⟩ := hcross
        obtain ⟨t', ht', hline'⟩ := hits_line_down H j θ hx0 ht hθt
        obtain ⟨-, hAt, hRt⟩ := hmr t' ht'
        obtain ⟨e, he, hneq, hnp, hge⟩ := hline _ hRt (by rw [mergeLR_R]; exact hline')
        have hleg : SwitchLegal e (Φ t') := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y _).mp hge
        exact rrespPC_step hm he
          (sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm ht'.1 ht'.2 ht'.2 htrode)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR t'
            ⟨e, he, hneq, hnp, rfl, hleg, hAt,
              fun i => (right_sol_left (ODESol_restrict H ht'.1 ht'.2) i).trans (hL i)⟩)))
      push Not at hcross
      -- the end of the cycle: a declared successor is enabled
      obtain ⟨-, hAe, -⟩ := hmr epsR ⟨hε.le, le_rfl⟩
      obtain ⟨e, he, hge⟩ := hcomp ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA)) epsR Φ le_rfl H
      have hleg : SwitchLegal e (Φ epsR) := by unfold SwitchLegal; rwa [hguards e he]
      have hflow := sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm H.hr le_rfl le_rfl htrode
      have hlegκ : SwitchLegal e (Function.update (Φ epsR) tr epsR) :=
        (switchLegal_update hgR he htrR _ _).mpr hleg
      have hLe : ∀ i, Φ epsR (Lv i) = ρ (Lv i) := fun i => (right_sol_left H i).trans (hL i)
      have hLeκ : ∀ i, Function.update (Φ epsR) tr epsR (Lv i) = ρ (Lv i) :=
        fun i => (update_Lv_of_notMem htrL _ _ i).trans (hLe i)
      by_cases hself : e.tgt = q
      · -- the self-loop: the next cycle start, with the measure decreased
        have hgnext : Formula.sat (guard q) (Φ epsR) := by rw [← hself]; exact hge
        set y' := mergeLR y y (Φ epsR) with hy'
        have hgLy' : pre = true → Formula.sat gL y' := fun hp =>
          (sat_merge_L hgL y y _).mpr (hgLy hp)
        have hnext : CycleStart guard q A Formula.tt y' (Φ epsR) (Φ epsR) :=
          ⟨hgnext, (sat_merge_merge hAfv y _ _).mpr hAe, trivial, fun _ => rfl⟩
        have hnextκ : CycleStart guard q A Formula.tt y' (Function.update (Φ epsR) tr epsR)
            (Function.update (Φ epsR) tr epsR) := by
          obtain ⟨h1, h2, h3, -⟩ := cycleStart_update_tr guard q hguardR A tr htrL htrR epsR hnext
          exact ⟨h1, h2, h3, fun _ => rfl⟩
        have hdecay : Φ epsR (Rv j) - θ ≤ N * (r * epsR) := by
          have hgr := cycle_decay H j r (fun t ht => by
            obtain ⟨-, -, hRt⟩ := hmr t ht
            have := hrate _ hRt (by rw [mergeLR_R]; exact hcross t ht)
            rwa [eval_fR_merge hfR] at this)
          have : (N.succ : ℝ) * (r * epsR) = N * (r * epsR) + r * epsR := by
            push_cast; ring
          linarith
        have hdecayκ : Function.update (Φ epsR) tr epsR (Rv j) - θ ≤ N * (r * epsR) := by
          rw [update_Rv_of_notMem htrR]; exact hdecay
        have hrest := ih y' (Function.update (Φ epsR) tr epsR)
          (fun i => by rw [hy', mergeLR_R, update_Rv_of_notMem htrR]) hgLy' hnextκ hdecayκ
        refine rrespPC_step hm he hflow hlegκ ?_
        rw [hself]
        refine rrespPC_mono ?_ hrest
        rintro q' μ (⟨e', he', hneq', hnp', rfl, hleg', hAμ, hμL⟩ | ⟨rfl, ⟨hg', hA', -, hμL⟩, hz'⟩)
        · exact Or.inl ⟨e', he', hneq', hnp', rfl, hleg', (sat_merge_merge hAfv y _ _).mp hAμ,
            fun i => (hμL i).trans (hLeκ i)⟩
        · exact Or.inr ⟨rfl, ⟨hg', (sat_merge_merge hAfv y _ _).mp hA', trivial,
            fun i => (hμL i).trans (hLeκ i)⟩, hz'⟩
      · -- a non-self successor: an exit (not pruned, by the non-connection certificate)
        have hnp : e.pruned = false := by
          by_contra hc
          have hp : e.pruned = true := by simpa using hc
          exact hpruneD e he hp _ _ hA (hmr epsR ⟨hε.le, le_rfl⟩).1
            ((switchLegal_merge hgR he y y).mpr hleg)
        exact rrespPC_step hm he hflow hlegκ
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR epsR
            ⟨e, he, hself, hnp, rfl, hleg, hAe, hLe⟩)))

end Node

end RelCertifier

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## The certificate with one or two stages gives `RepoProgress` -/

section Close

variable (G : SearchGraph (Var n)) (fR : Fin n → Term (Var n)) (domL domR gL : Formula (Var n))
  (guard : ℕ → Formula (Var n)) (q : ℕ) (m : RMode (Var n)) (hm : G.modeAt q = some m)
  (hsys : m.sys = rightBlock fR (Term.const 1)) (hdomM : m.dom = domR)
  (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (hgL : gL.fv ⊆ range Lv) (hguardR : ∀ q', (guard q').fv ⊆ range Rv)
  (hgR : GuardsRight G) (hguards : ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
  (A : ℕ → Formula (Var n)) (hAfv : (A q).fv ⊆ range Lv ∪ range Rv)
  (hAdom : ∀ y, Formula.sat (A q) y → Formula.sat domL y ∧ Formula.sat domR y)
  (pre : Bool) (epsR : ℝ) (hε : 0 < epsR)
  (tr : Var n) (htrL : tr ∉ range Lv) (htrR : tr ∉ range Rv)
  (reg : Formula (Var n)) (hregR : reg.fv ⊆ range Rv)
  (hAreg : ∀ y, Formula.sat (A q) y → Formula.sat reg y)
  (hex : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x →
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR x epsR Φ)
  (hcomp : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x → ∀ t Φ, t ≤ epsR →
    ODESol (rightBlock fR (Term.const 1)) domR x t Φ →
    ∃ e ∈ G.edgesFrom q, Formula.sat (guard e.tgt) (Φ t))
  (hboxD : ∀ σ ω, Formula.sat (A q) σ → (pre = true → Formula.sat gL σ) →
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (Formula.and domL domR)) σ ω → Formula.sat (A q) ω)
  (hpruneD : ∀ e ∈ G.edgesFrom q, e.pruned = true → ∀ σ ω, Formula.sat (A q) σ →
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (Formula.and domL domR)) σ ω → ¬ Formula.sat e.guard ω)
  (R : Formula (Var n)) (hR : ∀ y, Formula.sat (A q) y → (pre = true → Formula.sat gL y) →
    Formula.sat R y)
  (j : Fin n) (θ : ℝ)
  (hline : ∀ y, Formula.sat R y → y (Rv j) = θ →
    ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
  (hstart : ∀ y, Formula.sat R y → Formula.sat (guard q) y → θ ≤ y (Rv j) →
    ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)

include hm hdomM hdomR hgL hguardR hgR hguards hAdom hε htrL htrR hR hstart in
/-- A cycle start with the landing coordinate crossed lands at once. -/
theorem land_at_start {y ρ : State (Var n)} (hgLy : pre = true → Formula.sat gL y)
    {μ : State (Var n)} (hcs : CycleStart guard q (A q) Formula.tt y ρ μ) (hθ : θ ≤ μ (Rv j)) :
    RRespPC G tr epsR q (fun q' μ' => Landed G q (A q) y ρ q' μ') μ := by
  obtain ⟨hg, hA, -, hL⟩ := hcs
  have hRμ : Formula.sat R (mergeLR y y μ) := hR _ hA (fun hp =>
    (sat_merge_L hgL y y μ).mpr (hgLy hp))
  have hgμ : Formula.sat (guard q) (mergeLR y y μ) := (sat_merge_R (hguardR q) y y μ).mpr hg
  obtain ⟨e, he, hneq, hnp, hge⟩ := hstart _ hRμ hgμ (by rw [mergeLR_R]; exact hθ)
  have hleg : SwitchLegal e μ := by
    unfold SwitchLegal; rw [hguards e he]
    exact (sat_merge_R (hguardR e.tgt) y y μ).mp hge
  have hdom : Formula.sat m.dom μ := by
    rw [hdomM]; exact (sat_merge_R hdomR y y μ).mp (hAdom _ hA).2
  have htrdom : tr ∉ m.dom.fv := by rw [hdomM]; exact fun h => htrR (hdomR h)
  exact rrespPC_step hm he (sem_clockedSeg_zero m.sys m.dom tr epsR hε.le htrdom hdom)
    ((switchLegal_update hgR he htrR _ _).mpr hleg)
    (rrespPC_stop (landed_update_tr G q hgR (A q) tr htrL htrR 0
      ⟨e, he, hneq, hnp, rfl, hleg, hA, hL⟩))

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex hcomp hboxD
  hpruneD hR hline hstart in
/-- **One stage.** -/
theorem repoProgress_one (r : ℝ) (hr : 0 < r)
    (hrate : ∀ y, Formula.sat R y → y (Rv j) < θ → r ≤ Term.eval (fR j) y) :
    RepoProgress G tr epsR A gL (guard q) q pre := by
  intro ρ y hyρ hA hg hgLy
  have hA' : Formula.sat (A q) (mergeLR y y ρ) :=
    (sat_of_agree hAfv (x := y) (y := mergeLR y y ρ) (fun i => (mergeLR_L y y ρ i).symm)
      (fun i => by rw [mergeLR_R, hyρ i])).mp hA
  set N : ℕ := ⌈(θ - ρ (Rv j)) / (r * epsR)⌉₊ with hN
  have hbound : θ - ρ (Rv j) ≤ N * (r * epsR) := by
    have hpos : 0 < r * epsR := mul_pos hr hε
    have := Nat.le_ceil ((θ - ρ (Rv j)) / (r * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hph := phase G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp hboxD hpruneD R hR j θ hline hstart j θ r hr
    Formula.tt (by simp [Formula.fv]) (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun y hR' _ hlt => hrate y hR' hlt) (Or.inr ⟨rfl, rfl⟩) N y ρ hyρ hgLy
    ⟨hg, hA', trivial, fun _ => rfl⟩ hbound
  refine rrespPC_bind' hph ?_
  rintro q' μ (hland | ⟨hq', hcs, hθ⟩)
  · exact rrespPC_stop hland
  · subst q'
    exact land_at_start (G := G) (domL := domL) (domR := domR) (gL := gL) (guard := guard) (q := q)
      (m := m) (hm := hm)
      (hdomM := hdomM) (hdomR := hdomR) (hgL := hgL) (hguardR := hguardR) (hguards := hguards)
      (A := A) (hAdom := hAdom) (pre := pre) (epsR := epsR) (hε := hε) (hgR := hgR) (tr := tr) (htrL := htrL) (htrR := htrR) (R := R) (hR := hR) (j := j) (θ := θ)
      (hstart := hstart) hgLy hcs hθ

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex hcomp hboxD
  hpruneD hR hline hstart in
/-- **Two stages**: the helper coordinate `jh` first crosses `θh` (and stays crossed), then the
landing coordinate `j` rises at rate `r` to `θ`. -/
theorem repoProgress_two (r : ℝ) (hr : 0 < r) (jh : Fin n) (θh rh : ℝ) (hrh : 0 < rh)
    (hrate_h : ∀ y, Formula.sat R y → y (Rv jh) < θh → rh ≤ Term.eval (fR jh) y)
    (hkeep_h : ∀ y, Formula.sat R y → y (Rv jh) ≤ θh → 0 ≤ Term.eval (fR jh) y)
    (hrate : ∀ y, Formula.sat R y → θh ≤ y (Rv jh) → y (Rv j) < θ → r ≤ Term.eval (fR j) y) :
    RepoProgress G tr epsR A gL (guard q) q pre := by
  intro ρ y hyρ hA hg hgLy
  have hA' : Formula.sat (A q) (mergeLR y y ρ) :=
    (sat_of_agree hAfv (x := y) (y := mergeLR y y ρ) (fun i => (mergeLR_L y y ρ i).symm)
      (fun i => by rw [mergeLR_R, hyρ i])).mp hA
  -- stage 1: the helper crosses
  set N₁ : ℕ := ⌈(θh - ρ (Rv jh)) / (rh * epsR)⌉₊ with hN₁
  have hbound₁ : θh - ρ (Rv jh) ≤ N₁ * (rh * epsR) := by
    have hpos : 0 < rh * epsR := mul_pos hrh hε
    have := Nat.le_ceil ((θh - ρ (Rv jh)) / (rh * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hph₁ := phase G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp hboxD hpruneD R hR j θ hline hstart jh θh rh hrh
    Formula.tt (by simp [Formula.fv]) (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun y hR' _ hlt => hrate_h y hR' hlt) (Or.inl hkeep_h) N₁ y ρ hyρ hgLy
    ⟨hg, hA', trivial, fun _ => rfl⟩ hbound₁
  refine rrespPC_bind' hph₁ ?_
  rintro q' μ (hland | ⟨hq', ⟨hg₁, hA₁, -, hL₁⟩, hθh⟩)
  · exact rrespPC_stop hland
  subst q'
  -- stage 2: from the cycle start with the helper crossed
  set Kf : Formula (Var n) := Formula.cmp CompOp.le (Term.const θh) (Term.var (Rv jh)) with hKf
  have hKsat : ∀ w : State (Var n), Formula.sat Kf w ↔ θh ≤ w (Rv jh) := fun w => by
    simp [hKf, Formula.sat, CompOp.interp, Term.eval]
  have hKfv : Kf.fv ⊆ range Rv := by
    intro v hv
    simp only [hKf, Formula.fv, Term.fv, Set.empty_union, Set.mem_singleton_iff] at hv
    exact ⟨jh, hv.symm⟩
  set y' := mergeLR y y μ with hy'
  have hgLy' : pre = true → Formula.sat gL y' := fun hp => (sat_merge_L hgL y y μ).mpr (hgLy hp)
  have hKkeep : ∀ y₁ ρ₁, (∀ i, y₁ (Rv i) = ρ₁ (Rv i)) → Formula.sat (A q) y₁ →
      (pre = true → Formula.sat gL y₁) → Formula.sat Kf y₁ →
      ∀ T Φ, ODESol (rightBlock fR (Term.const 1)) domR ρ₁ T Φ →
        Formula.sat Kf (mergeLR y₁ y₁ (Φ T)) := by
    intro y₁ ρ₁ hyρ₁ hA₁' hgL₁ hK₁ T Φ H
    rw [hKsat, mergeLR_R]
    refine keep_preserved fR domL domR gL hfR hdomL hdomR hgL (A q) hAfv hAdom pre hboxD R hR jh
      θh hkeep_h hyρ₁ hA₁' hgL₁ H ?_
    rw [← hyρ₁ jh]
    exact (hKsat y₁).mp hK₁
  set N₂ : ℕ := ⌈(θ - μ (Rv j)) / (r * epsR)⌉₊ with hN₂
  have hbound₂ : θ - μ (Rv j) ≤ N₂ * (r * epsR) := by
    have hpos : 0 < r * epsR := mul_pos hr hε
    have := Nat.le_ceil ((θ - μ (Rv j)) / (r * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hcs₂ : CycleStart guard q (A q) Kf y' μ μ :=
    ⟨hg₁, (sat_merge_merge hAfv y μ μ).mpr hA₁,
      by rw [hKsat, mergeLR_R]; exact hθh, fun _ => rfl⟩
  have hph₂ := phase G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp hboxD hpruneD R hR j θ hline hstart j θ r hr
    Kf hKfv hKkeep (fun y₂ hR' hK' hlt => hrate y₂ hR' ((hKsat y₂).mp hK') hlt)
    (Or.inr ⟨rfl, rfl⟩) N₂ y' μ (fun i => by rw [hy', mergeLR_R]) hgLy' hcs₂ hbound₂
  refine rrespPC_bind' hph₂ ?_
  rintro q'' μ' (⟨e, he, hneq, hnp, hq'', hleg, hAμ, hμL⟩ | ⟨hq'', ⟨hg₂, hA₂, -, hL₂⟩, hθ⟩)
  · subst q''
    exact rrespPC_stop ⟨e, he, hneq, hnp, rfl, hleg, (sat_merge_merge hAfv y μ μ').mp hAμ,
      fun i => (hμL i).trans (hL₁ i)⟩
  · subst q''
    have hcs' : CycleStart guard q (A q) Formula.tt y ρ μ' :=
      ⟨hg₂, (sat_merge_merge hAfv y μ μ').mp hA₂, trivial, fun i => (hL₂ i).trans (hL₁ i)⟩
    exact land_at_start (G := G) (domL := domL) (domR := domR) (gL := gL) (guard := guard) (q := q)
      (m := m) (hm := hm)
      (hdomM := hdomM) (hdomR := hdomR) (hgL := hgL) (hguardR := hguardR) (hguards := hguards)
      (A := A) (hAdom := hAdom) (pre := pre) (epsR := epsR) (hε := hε) (hgR := hgR) (tr := tr) (htrL := htrL) (htrR := htrR) (R := R) (hR := hR) (j := j) (θ := θ)
      (hstart := hstart) hgLy hcs' hθ

include hm hdomM hdomR hgL hguardR hgR hguards hAdom hε htrL htrR hR in
/-- A cycle start with the landing coordinate crossed DOWNWARD lands at once (the mirror of
`land_at_start`; `hstart_down` is the landing at an already-crossed start, `x ≤ θ`). -/
theorem land_at_start_down
    (hstart_down : ∀ y, Formula.sat R y → Formula.sat (guard q) y → y (Rv j) ≤ θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    {y ρ : State (Var n)} (hgLy : pre = true → Formula.sat gL y)
    {μ : State (Var n)} (hcs : CycleStart guard q (A q) Formula.tt y ρ μ) (hθ : μ (Rv j) ≤ θ) :
    RRespPC G tr epsR q (fun q' μ' => Landed G q (A q) y ρ q' μ') μ := by
  obtain ⟨hg, hA, -, hL⟩ := hcs
  have hRμ : Formula.sat R (mergeLR y y μ) := hR _ hA (fun hp =>
    (sat_merge_L hgL y y μ).mpr (hgLy hp))
  have hgμ : Formula.sat (guard q) (mergeLR y y μ) := (sat_merge_R (hguardR q) y y μ).mpr hg
  obtain ⟨e, he, hneq, hnp, hge⟩ := hstart_down _ hRμ hgμ (by rw [mergeLR_R]; exact hθ)
  have hleg : SwitchLegal e μ := by
    unfold SwitchLegal; rw [hguards e he]
    exact (sat_merge_R (hguardR e.tgt) y y μ).mp hge
  have hdom : Formula.sat m.dom μ := by
    rw [hdomM]; exact (sat_merge_R hdomR y y μ).mp (hAdom _ hA).2
  have htrdom : tr ∉ m.dom.fv := by rw [hdomM]; exact fun h => htrR (hdomR h)
  exact rrespPC_step hm he (sem_clockedSeg_zero m.sys m.dom tr epsR hε.le htrdom hdom)
    ((switchLegal_update hgR he htrR _ _).mpr hleg)
    (rrespPC_stop (landed_update_tr G q hgR (A q) tr htrL htrR 0
      ⟨e, he, hneq, hnp, rfl, hleg, hA, hL⟩))

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex hcomp hboxD
  hpruneD hR hline in
/-- **One downward stage** (the mirror of `repoProgress_one`): the landing coordinate `j` falls
at rate `r` while above `θ`, lands on `x = θ` (`hline`) or at a start already below
(`hstart_down`). -/
theorem repoProgress_one_down (r : ℝ) (hr : 0 < r)
    (hstart_down : ∀ y, Formula.sat R y → Formula.sat (guard q) y → y (Rv j) ≤ θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (hrate : ∀ y, Formula.sat R y → θ < y (Rv j) → Term.eval (fR j) y ≤ -r) :
    RepoProgress G tr epsR A gL (guard q) q pre := by
  intro ρ y hyρ hA hg hgLy
  have hA' : Formula.sat (A q) (mergeLR y y ρ) :=
    (sat_of_agree hAfv (x := y) (y := mergeLR y y ρ) (fun i => (mergeLR_L y y ρ i).symm)
      (fun i => by rw [mergeLR_R, hyρ i])).mp hA
  set N : ℕ := ⌈(ρ (Rv j) - θ) / (r * epsR)⌉₊ with hN
  have hbound : ρ (Rv j) - θ ≤ N * (r * epsR) := by
    have hpos : 0 < r * epsR := mul_pos hr hε
    have := Nat.le_ceil ((ρ (Rv j) - θ) / (r * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hph := phase_down G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp hboxD hpruneD R hR j θ hline
    hstart_down r hr hrate N y ρ hyρ hgLy ⟨hg, hA', trivial, fun _ => rfl⟩ hbound
  refine rrespPC_bind' hph ?_
  rintro q' μ (hland | ⟨hq', hcs, hθ⟩)
  · exact rrespPC_stop hland
  · subst q'
    exact land_at_start_down (G := G) (domL := domL) (domR := domR) (gL := gL) (guard := guard)
      (q := q) (m := m) (hm := hm)
      (hdomM := hdomM) (hdomR := hdomR) (hgL := hgL) (hguardR := hguardR) (hguards := hguards)
      (A := A) (hAdom := hAdom) (pre := pre) (epsR := epsR) (hε := hε) (hgR := hgR) (tr := tr) (htrL := htrL) (htrR := htrR) (R := R) (hR := hR) (j := j) (θ := θ)
      hstart_down hgLy hcs hθ

end Close

end RelCertifier
