/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_refine`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`InstancesV2/Modal/RoverPatrolRefineGuarded.lean`), the lowered right guards, `ε_r = 1`.
The zones run `v' = c − v` (`c` = the zone cap 0.6, 0.9, 1.1, 1.5), `s' = v`, `a' = 0`
(no `STALL` mode in this file). Over one interval the odometer grows by at most `1.6` (the
evolve bound on `v`).
* `SLOW` (`0 ≤ s < 20`, `0.3 ≤ v ≤ 0.6`), style (b): ends in `SLOW` or `MEDIUM_ECO`.
* `MEDIUM_ECO` / `MEDIUM_BRISK` (`20 ≤ s < 50`, `0.3 ≤ v ≤ 0.9 / 1.1`), style (b): end in
  the zone itself or `FAST`.
* `FAST` (`s ≥ 50`, `0.3 ≤ v ≤ 1.5`), style (a).
Existence: the explicit zone runs (`flowR_run`). Z3-free.
-/
import RelCertifier.InstancesV2.Modal.RoverPatrolRefineGuarded
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolRefineGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolRefine

theorem epsR_eq : epsR rover_patrol_refine_IRv2 = 1 := by
  simp [epsR, rover_patrol_refine_IRv2, hp1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 20 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/5) := by
  rw [sat_guardR 0 (by norm_num)]; simp [loL, loQ, capL, capQ]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 2)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 11/10) := by
  rw [sat_guardR 2 (by norm_num)]; simp [loL, loQ, capL, capQ]

/-- **Assumption 1 for `rover_patrol_refine`**, every mode, Z3-free. -/
theorem rover_patrol_refine_wellFormedR :
    WellFormedR GrG guardR (epsR rover_patrol_refine_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨h4, rfl⟩ := GrG_modeAt_inv hm
  have hq5 := h4
  · refine ⟨?_, ?_⟩
    · obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q h4 1 zero_le_one x hd 1
      exact ⟨_, ⟨by norm_num, h0, hder, hmask, hdom⟩⟩
    intro t Φ ht H
    have hv := H.linear_between (rightBlock_mem' (fR q) (Term.const 1) 0) 1 (capL q)
      (by norm_num) (fun s _ => by rw [eval_unit_mul, fR0_eval q h4]; ring)
    have hsup := H.rate_le (rightBlock_mem' (fR q) (Term.const 1) 1) (8/5)
      (fun s hs => by rw [eval_unit_mul, fR1_eval q hq5]; exact ((sat_domR s).mp hs).2.1)
    have hslo := H.mono (rightBlock_mem' (fR q) (Term.const 1) 1)
      (fun s hs => by rw [eval_unit_mul, fR1_eval q hq5]; exact ((sat_domR s).mp hs).1)
    have hr := H.hr
    interval_cases q
    · -- SLOW
      obtain ⟨hs0, hs1, hv0, hv1⟩ := (sat_guardR0 x).mp hg
      have hc : capL 0 = 3/5 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      by_cases h20 : Φ t (Rv 1) < 20
      · exact ⟨edgeG 0 0, edgeG_mem 0 0 (by simp [edgeList]),
          (sat_guardR0 _).mpr ⟨by linarith, h20, by linarith [hv.1], hv.2⟩⟩
      · exact ⟨edgeG 0 1, edgeG_mem 0 1 (by simp [edgeList]),
          (sat_guardR1 _).mpr ⟨by linarith, by nlinarith, by linarith [hv.1], by linarith [hv.2]⟩⟩
    · -- MEDIUM_ECO
      obtain ⟨hs0, hs1, hv0, hv1⟩ := (sat_guardR1 x).mp hg
      have hc : capL 1 = 9/10 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      by_cases h50 : Φ t (Rv 1) < 50
      · exact ⟨edgeG 1 1, edgeG_mem 1 1 (by simp [edgeList]),
          (sat_guardR1 _).mpr ⟨by linarith, h50, by linarith [hv.1], hv.2⟩⟩
      · exact ⟨edgeG 1 3, edgeG_mem 1 3 (by simp [edgeList]),
          (sat_guardR3 _).mpr ⟨by linarith, by linarith [hv.1], by linarith [hv.2]⟩⟩
    · -- MEDIUM_BRISK
      obtain ⟨hs0, hs1, hv0, hv1⟩ := (sat_guardR2 x).mp hg
      have hc : capL 2 = 11/10 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      by_cases h50 : Φ t (Rv 1) < 50
      · exact ⟨edgeG 2 2, edgeG_mem 2 2 (by simp [edgeList]),
          (sat_guardR2 _).mpr ⟨by linarith, h50, by linarith [hv.1], hv.2⟩⟩
      · exact ⟨edgeG 2 3, edgeG_mem 2 3 (by simp [edgeList]),
          (sat_guardR3 _).mpr ⟨by linarith, by linarith [hv.1], by linarith [hv.2]⟩⟩
    · -- FAST
      obtain ⟨hs0, hv0, hv1⟩ := (sat_guardR3 x).mp hg
      have hc : capL 3 = 3/2 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      exact ⟨edgeG 3 3, edgeG_mem 3 3 (by simp [edgeList]),
        (sat_guardR3 _).mpr ⟨by linarith, by linarith [hv.1], hv.2⟩⟩

end V2RoverPatrolRefineGuarded
end RelCertifier
