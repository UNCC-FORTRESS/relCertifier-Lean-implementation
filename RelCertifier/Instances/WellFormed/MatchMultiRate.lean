/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrPG` of the Theorem 3 instance
(`Instances/MatchMultiRateGuarded.lean`), the lowered right guards, `ε_r = 0.3` (the literal
is the suite_v2 file's, `InstancesV2/SameIR.lean`). Both guard sets are forward invariant
(style (a)): `DRIVE` (`0.2 ≤ v ≤ 1`, `v' = 1 − v`: `v` rises toward 1) and `STALL`
(`v < 0.2`, `v' = −2 v`: `v` decays); the odometer `s' = v ≥ 0` keeps `s ≥ 0`. Existence:
the explicit exponential runs (the instance's `driveEnd`; `stallEnd` below). Z3-free.
-/
import RelCertifier.Instances.MatchMultiRateGuarded
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace MatchMultiRateGuarded

open DL DLCalTiming DLRel Parse Set MatchMultiRateModal MatchMultiRatePruned

theorem hm03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hmm2 : Run.parseRat "-2" = some (-2 : ℚ) := by
  have h : parseQ "-2" = some (⟨-2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR match_multi_rate_IR = 3/10 := by
  simp [epsR, match_multi_rate_IR, hm03]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vsM 2 Side.R (mRM q)

theorem sat_guardSTALL (x : State (Var 2)) :
    Formula.sat (hostGuard vsM 2 Side.R (mRM 1)) x ↔ x (Rv 0) < 1/5 := by
  simp [hostGuard, mRM, match_multi_rate_IR, Run.lowerF, Run.lowerE, hm02, vsM,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fRM_stall0 (x : State (Var 2)) : Term.eval (fRM 1 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fRM, hostDyn, mRM, match_multi_rate_IR, vsM, Run.dynOf, Run.lowerE, hmm2,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fRM_stall1 (x : State (Var 2)) : Term.eval (fRM 1 1) x = x (Rv 0) := by
  simp [fRM, hostDyn, mRM, match_multi_rate_IR, vsM, Run.dynOf, Run.lowerE, hmm2,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The explicit `STALL` run: `v = v₀ e^{−2t}`, `s = s₀ + v₀ (1 − e^{−2t}) / 2`. -/
noncomputable def stallφ (ρ : State (Var 2)) : Fin 2 → ℝ → ℝ := fun i t =>
  if i = 0 then 0 + (ρ (Rv 0) - 0) * Real.exp (-(2 * t))
  else ρ (Rv 1) + 0 * t + (ρ (Rv 0) - 0) * (1 - Real.exp (-(2 * t))) / 2

theorem stall_sol (ρ : State (Var 2)) (hdom : Formula.sat domRM ρ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeM 1).sys (modeM 1).dom ρ τ (trajR ρ (stallφ ρ)) := by
  have hD := (sat_domRM ρ).mp hdom
  refine explicit_sol ρ (stallφ ρ) τ hτ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [stallφ]
  · intro i t _ _
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [fRM_stall0, trajR_R]
      have h := hasDerivAt_expApproach 2 0 (ρ (Rv 0)) t
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [fRM_stall1, trajR_R]
      have h := hasDerivAt_expIntegral 2 0 (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
  · intro t ht _
    have he0 := Real.exp_pos (-(2 * t))
    have he1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    refine (sat_domRM _).mpr ⟨?_, ?_, ?_⟩
    · rw [trajR_R]; simp only [stallφ]; norm_num; nlinarith [hD.1, hD.2.1]
    · rw [trajR_R]; simp only [stallφ]; norm_num; nlinarith [hD.2.1]
    · rw [trajR_R]; simp only [stallφ]; norm_num; nlinarith [hD.2.1, hD.2.2]

/-- **Assumption 1 for `match_multi_rate`**, every mode, Z3-free. -/
theorem match_multi_rate_wellFormedR :
    WellFormedR GrPG guardR (epsR match_multi_rate_IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  have hq2 : q < 2 := hq
  have hmq : m = modeM q := by
    have := GrPG_modeAt q hq2; rw [hm] at this; exact Option.some.inj this
  subst hmq
  interval_cases q
  · have hgx := (sat_guardDRIVE x).mp hg
    refine ⟨⟨_, drive_sol x hd hgx.2 (3/10) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hup := H.linear_up (rightBlock_mem' (fRM 0) (Term.const 1) 0) 1 1 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fRM0_eval 0 (by norm_num)]; simp [cstM]) hgx.2
    exact ⟨edgeG 0 0, List.mem_filter.mpr ⟨by simp [GrPG], by simp [edgeG]⟩,
      (sat_guardDRIVE _).mpr ⟨by linarith [hup.1], hup.2⟩⟩
  · have hgx := (sat_guardSTALL x).mp hg
    refine ⟨⟨_, stall_sol x hd (3/10) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hdn := H.linear_down (rightBlock_mem' (fRM 1) (Term.const 1) 0) 2 0 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fRM_stall0]) ((sat_domRM x).mp hd).2.1
    exact ⟨edgeG 1 1, List.mem_filter.mpr ⟨by simp [GrPG], by simp [edgeG]⟩,
      (sat_guardSTALL _).mpr (by linarith [hdn.2])⟩

end MatchMultiRateGuarded
end RelCertifier
