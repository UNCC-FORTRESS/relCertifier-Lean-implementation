/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_slow`: Assumption 1 of the right model — FALSE (model defect)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
Every mode is a constant rate `θ' = a` over the evolve domain `0 ≤ θ ≤ 1.2`.

**`WellFormedR` is false** (`arm_plateau_slow_wellFormedR_false`): the approach bands are
narrower than one control interval of their own rate.
* `ApproachA` (guard `0 ≤ θ ≤ 0.35`, `θ' = 0.5`, successors `[ApproachB, ApproachA]`): from
  `θ = 0.35` the run of duration 1 ends at `θ = 0.85`, outside `ApproachA` and `ApproachB`
  (`0.35 ≤ θ ≤ 0.5`) (`arm_plateau_slow_approachA_blocks`).
* `ApproachB` (guard `0.35 ≤ θ ≤ 0.5`, `θ' = 0.35`, successors `[ApproachC, ApproachB]`): from
  `θ = 0.5` the run of duration 1 ends at `θ = 0.85`, outside `ApproachB` and `ApproachC`
  (`0.5 ≤ θ ≤ 0.6`) (`arm_plateau_slow_approachB_blocks`).
The nominal controller has no enabled mode after such an interval. (The Theorem 3 responses
switch at the band boundaries inside the interval, so the certificate does not need the
assumption; the model as a sampled controller with period `ε_r` violates it.)

**`ApproachC` and `Hold` satisfy Assumption 1** (`arm_plateau_slow_wellFormedR_modes`,
Z3-free): `ApproachC` (style (b): a run ends in `[θ₀, θ₀ + 0.2] ⊆ [0.5, 0.8]`, inside
`ApproachC` or `Hold` `[0.6, 1.15)`) and `Hold` (style (a): frozen).
-/
import RelCertifier.InstancesV2.Modal.ArmPlateauSlow
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ArmPlateauSlow

open DL DLCalTiming DLRel Parse Set

theorem epsR_eq : epsR arm_plateau_slow_IRv2 = 1 := by
  simp [epsR, arm_plateau_slow_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- Along a run of mode `q` the angle moves at exactly its rate. -/
theorem run_exact (q : ℕ) (hq : q < 4) {x : State (Var 2)} {t : ℝ} {Φ : ℝ → State (Var 2)}
    (H : ODESol (modeW q).sys (modeW q).dom x t Φ) : Φ t (Rv 0) = x (Rv 0) + rate q * t := by
  have h1 := H.rate_le (memR q) (rate q) (fun s _ => by rw [eval_unit_mul, fR0_eval q hq])
  have h2 := H.rate_ge (memR q) (rate q) (fun s _ => by rw [eval_unit_mul, fR0_eval q hq])
  linarith

/-- The constant-rate run of mode `q` from `x`, for duration `ε`. -/
theorem run_exists (q : ℕ) (hq : q < 4) (x : State (Var 2)) (ε : ℝ) (hε : 0 ≤ ε)
    (hdom : ∀ t, 0 ≤ t → t ≤ ε → 0 ≤ x (Rv 0) + rate q * t ∧ x (Rv 0) + rate q * t ≤ 6/5) :
    ODESol (modeW q).sys (modeW q).dom x ε (trajJ x 0 (fun t => x (Rv 0) + rate q * t)) :=
  exists_rate_run (fR := fR q) (domR := domR) x 0 (rate q) (fR0_eval q hq)
    (fun i hi s => by
      match i, hi with
      | 1, _ => exact fR1_eval q hq s) ε hε
    (fun t ht hte => by
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact hdom t ht hte)

/-- **Assumption 1 at `ApproachC` and `Hold`** (Z3-free). -/
theorem arm_plateau_slow_wellFormedR_modes (q : ℕ) (hq2 : 2 ≤ q) (hq : q < 4) :
    WellFormedRMode Gr guardR (epsR arm_plateau_slow_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq x).mp hg
  refine ⟨⟨_, run_exists q hq x 1 (by norm_num) (fun t ht ht1 => ?_)⟩, ?_⟩
  · interval_cases q <;> simp [rate] at hgx ⊢ <;> constructor <;> nlinarith
  · intro t Φ ht H
    have hex := run_exact q hq H
    have ht0 := H.hr
    interval_cases q
    · -- ApproachC: ends in [θ₀, θ₀ + 0.2] ⊆ [0.5, 0.8]
      simp [rate] at hgx hex
      by_cases h06 : Φ t (Rv 0) ≤ 3/5
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guardR 2 (by norm_num) _).mpr
          (by norm_num; exact ⟨by nlinarith, h06⟩)⟩
      · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, by nlinarith⟩)⟩
    · -- Hold: frozen
      simp [rate] at hgx hex
      exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
        (by norm_num; rw [hex]; exact hgx)⟩

/-- A state with angle `θ` (every other variable 0). -/
noncomputable def xθ (θ : ℝ) : State (Var 2) := fun y => if y = Rv 0 then θ else 0

/-- **Assumption 1 fails at `ApproachA`**: from `θ = 0.35` the run of duration 1 ends at
`θ = 0.85`, outside the guards of `ApproachA` and `ApproachB`. -/
theorem arm_plateau_slow_approachA_blocks :
    ¬ WellFormedRMode Gr guardR (epsR arm_plateau_slow_IRv2) 0 := by
  rw [epsR_eq]
  have H := run_exists 0 (by norm_num) (xθ (7/20)) 1 (by norm_num)
    (fun t ht ht1 => by simp [xθ, rate]; constructor <;> linarith)
  refine not_wellFormedR_of_run (Gr_modeAt 0 (by norm_num)) ?_ ?_ le_rfl H ?_
  · show Formula.sat (hostGuard vs 2 Side.R (mR 0)) _
    rw [sat_guardR 0 (by norm_num)]; simp [xθ]; norm_num
  · show Formula.sat domR _
    rw [sat_domR]; simp [xθ]; norm_num
  · intro e he hsat
    have hl := edgesFrom_list he
    simp [edgeList] at hl
    rcases hl with ht | ht <;> rw [ht] at hsat
    · have := (sat_guardR 1 (by norm_num) _).mp hsat
      simp [xθ, rate] at this; linarith
    · have := (sat_guardR 0 (by norm_num) _).mp hsat
      simp [xθ, rate] at this; linarith

/-- **Assumption 1 fails at `ApproachB`**: from `θ = 0.5` the run of duration 1 ends at
`θ = 0.85`, outside the guards of `ApproachB` and `ApproachC`. -/
theorem arm_plateau_slow_approachB_blocks :
    ¬ WellFormedRMode Gr guardR (epsR arm_plateau_slow_IRv2) 1 := by
  rw [epsR_eq]
  have H := run_exists 1 (by norm_num) (xθ (1/2)) 1 (by norm_num)
    (fun t ht ht1 => by simp [xθ, rate]; constructor <;> linarith)
  refine not_wellFormedR_of_run (Gr_modeAt 1 (by norm_num)) ?_ ?_ le_rfl H ?_
  · show Formula.sat (hostGuard vs 2 Side.R (mR 1)) _
    rw [sat_guardR 1 (by norm_num)]; simp [xθ]; norm_num
  · show Formula.sat domR _
    rw [sat_domR]; simp [xθ]; norm_num
  · intro e he hsat
    have hl := edgesFrom_list he
    simp [edgeList] at hl
    rcases hl with ht | ht <;> rw [ht] at hsat
    · have := (sat_guardR 2 (by norm_num) _).mp hsat
      simp [xθ, rate] at this; linarith
    · have := (sat_guardR 1 (by norm_num) _).mp hsat
      simp [xθ, rate] at this; linarith

/-- **`arm_plateau_slow` violates Assumption 1** (a model defect: the approach bands are
left by one control interval of their own flow; see the module docstring). -/
theorem arm_plateau_slow_wellFormedR_false :
    ¬ WellFormedR Gr guardR (epsR arm_plateau_slow_IRv2) :=
  not_wellFormedR_of_mode (by simp [Gr]) arm_plateau_slow_approachA_blocks

end V2ArmPlateauSlow
end RelCertifier
