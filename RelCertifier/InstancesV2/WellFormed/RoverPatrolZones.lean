/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`InstancesV2/Modal/RoverPatrolZonesGuarded.lean`), the lowered right guards, `ε_r = 1`.
The driving zones run `v' = c − v` (`c` = the zone cap 0.6, 0.9, 1.1, 1.5) and `s' = v`;
`STALL` runs `v' = −2 v`, `s' = v`. Over one interval the odometer grows by at most
`1.6` (the evolve bound on `v`).
* `SLOW` (`0 ≤ s < 20`, `0.3 ≤ v ≤ 0.6`), style (b): ends in `SLOW` or `MEDIUM_ECO`.
* `MEDIUM_ECO` / `MEDIUM_BRISK` (`20 ≤ s < 50`, `0.3 ≤ v ≤ 0.9 / 1.1`), style (b): end in
  the zone itself or `FAST`.
* `FAST` (`s ≥ 50`, `0.3 ≤ v ≤ 1.5`) and `STALL` (`v < 0.2`), style (a).
Existence: the explicit zone runs (`flowR_run`) and the explicit `STALL` decay. Z3-free.
-/
import RelCertifier.InstancesV2.Modal.RoverPatrolZonesGuarded
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolZonesGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolZones

theorem epsR_eq : epsR rover_patrol_zones_IRv2 = 1 := by
  simp [epsR, rover_patrol_zones_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem sat_guardR4 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 4)) x ↔
    x (Rv 0) < 1/5 := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp02, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fR0_stall (x : State (Var 3)) : Term.eval (fR 4 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The explicit `STALL` run: `v = v₀ e^{−2t}`, `s = s₀ + v₀ (1 − e^{−2t}) / 2`. -/
noncomputable def stallφ (ρ : State (Var 3)) : Fin 3 → ℝ → ℝ := fun i t =>
  if i = 0 then 0 + (ρ (Rv 0) - 0) * Real.exp (-(2 * t))
  else if i = 1 then ρ (Rv 1) + 0 * t + (ρ (Rv 0) - 0) * (1 - Real.exp (-(2 * t))) / 2
  else ρ (Rv i)

theorem stall_sol (ρ : State (Var 3)) (hdom : Formula.sat domR ρ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeW 4).sys (modeW 4).dom ρ τ (trajR ρ (stallφ ρ)) := by
  have hD := (sat_domR ρ).mp hdom
  refine explicit_sol ρ (stallφ ρ) τ hτ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [stallφ]
  · intro i t _ _
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [fR0_stall, trajR_R]
      have h := hasDerivAt_expApproach 2 0 (ρ (Rv 0)) t
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [fR1_eval 4 (by norm_num), trajR_R]
      have h := hasDerivAt_expIntegral 2 0 (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [fR2_eval 4 (by norm_num)]
      have hf : stallφ ρ 2 = fun _ => ρ (Rv 2) := by funext u; simp [stallφ]
      rw [hf]
      exact hasDerivAt_const t _
  · intro t ht _
    have he0 := Real.exp_pos (-(2 * t))
    have he1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    obtain ⟨h0, h1, h2⟩ := hD
    refine (sat_domR _).mpr ⟨?_, ?_, ?_⟩ <;> rw [trajR_R] <;> simp only [stallφ] <;> norm_num
      <;> nlinarith

/-- **Assumption 1 for `rover_patrol_zones`**, every mode, Z3-free. -/
theorem rover_patrol_zones_wellFormedR :
    WellFormedR GrG guardR (epsR rover_patrol_zones_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := GrG_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  by_cases h4 : q < 4
  · refine ⟨?_, ?_⟩
    · obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q h4 x hd 1
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
  · have : q = 4 := by omega
    subst this
    have hgx := (sat_guardR4 x).mp hg
    refine ⟨⟨_, stall_sol x hd 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hdn := H.linear_down (rightBlock_mem' (fR 4) (Term.const 1) 0) 2 0 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fR0_stall]) hdx.1
    exact ⟨edgeG 4 4, edgeG_mem 4 4 (by simp [edgeList]), (sat_guardR4 _).mpr (by linarith [hdn.2])⟩

end V2RoverPatrolZonesGuarded
end RelCertifier
