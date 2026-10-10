/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_crit`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
Every mode is a constant rate `θ' = a` over the evolve domain `0 ≤ θ ≤ 1.2`.

**`WellFormedR` holds** (`arm_plateau_crit_wellFormedR`, Z3-free). The planner is a SAMPLED
controller (the 2026-10-10 repair, `docs/SUITE-REDESIGN.md` §21): a ramp segment held for a
full interval can cross more than one band boundary, so the successor sets name every band a
sample can find: `ApproachA → [ApproachB, ApproachA, ApproachC, Hold]`,
`ApproachB → [ApproachC, ApproachB, Hold]`.

* `ApproachA` (`0 ≤ θ ≤ 0.35`, `θ' = 0.5`), style (b): a run ends in `[θ₀, θ₀ + 0.5] ⊆
  [0, 0.85]`, inside `ApproachA`, `ApproachB` (`[0.35, 0.5]`), `ApproachC` (`[0.5, 0.6]`) or
  `Hold` (`[0.6, 1.15)`), whichever band the end value lies in.
* `ApproachB` (`0.35 ≤ θ ≤ 0.5`, `θ' = 0.35`), style (b): ends in `[0.35, 0.85]`, inside
  `ApproachB`, `ApproachC` or `Hold`.
* `ApproachC` (style (b): ends in `[0.5, 0.8]`, inside `ApproachC` or `Hold`) and `Hold`
  (style (a): frozen).

Existence: the constant-rate run, inside `[0, 1.2]` for one interval from every band.
(Until 2026-10-10 the successor sets named only the next band, and the model was refuted
here: from `θ = 0.35` (`ApproachA`) and from `θ = 0.5` (`ApproachB`) the run of duration 1
ends at `θ = 0.85`, outside every declared successor's band.)
-/
import RelCertifier.InstancesV2.Modal.ArmPlateauCrit
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ArmPlateauCrit

open DL DLCalTiming DLRel Parse Set

theorem epsR_eq : epsR arm_plateau_crit_IRv2 = 1 := by
  simp [epsR, arm_plateau_crit_IRv2, hp10]

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

/-- **Assumption 1 at every mode** (Z3-free): each band's run ends in the band its end value
lies in, and that band is a declared successor. -/
theorem arm_plateau_crit_wellFormedR_mode (q : ℕ) (hq : q < 4) :
    WellFormedRMode Gr guardR (epsR arm_plateau_crit_IRv2) q := by
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
    · -- ApproachA: ends in [θ₀, θ₀ + 0.5] ⊆ [0, 0.85]
      simp [rate] at hgx hex
      by_cases h1 : Φ t (Rv 0) ≤ 7/20
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR 0 (by norm_num) _).mpr
          (by norm_num; exact ⟨by nlinarith, h1⟩)⟩
      by_cases h2 : Φ t (Rv 0) ≤ 1/2
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h2⟩)⟩
      by_cases h3 : Φ t (Rv 0) ≤ 3/5
      · exact ⟨edgeW 0 2, edge_mem 0 2 (by decide), (sat_guardR 2 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h3⟩)⟩
      · exact ⟨edgeW 0 3, edge_mem 0 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, by nlinarith⟩)⟩
    · -- ApproachB: ends in [θ₀, θ₀ + 0.35] ⊆ [0.35, 0.85]
      simp [rate] at hgx hex
      by_cases h2 : Φ t (Rv 0) ≤ 1/2
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by nlinarith, h2⟩)⟩
      by_cases h3 : Φ t (Rv 0) ≤ 3/5
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide), (sat_guardR 2 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h3⟩)⟩
      · exact ⟨edgeW 1 3, edge_mem 1 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, by nlinarith⟩)⟩
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

/-- **`arm_plateau_crit` satisfies Assumption 1** (every mode, Z3-free). -/
theorem arm_plateau_crit_wellFormedR :
    WellFormedR Gr guardR (epsR arm_plateau_crit_IRv2) := by
  intro q hq
  exact arm_plateau_crit_wellFormedR_mode q (by simpa [Gr] using hq)

end V2ArmPlateauCrit
end RelCertifier
