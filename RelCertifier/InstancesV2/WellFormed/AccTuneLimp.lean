/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_limp`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
`NORMAL` / `COMFORT` / `SPORT` (`20 ≤ v ≤ 36`, `v' = k (30 − v)`, `k = 0.5, 0.4, 0.6`) and
`DISENGAGE` (`v < 20`, `v' = −v/2`) are contractions whose guard sets are forward invariant
(style (a)). Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.InstancesV2.Modal.AccTuneLimp
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccTuneLimp

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR acc_tune_limp_IRv2 = 1 := by
  simp [epsR, acc_tune_limp_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

noncomputable def kR4 (q : ℕ) : ℝ := if q < 3 then kR q else 1/2
noncomputable def cR4 (q : ℕ) : ℝ := if q < 3 then 30 else 0

theorem fR0_all (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR4 q * (cR4 q - x (Rv 0)) := by
  by_cases h3 : q < 3
  · rw [fR0_eval q h3]; simp [kR4, cR4, h3]
  · have : q = 3 := by omega
    subst this
    simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, kR4, cR4]
    ring

theorem fRo_all (q : ℕ) (hq : q < 4) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  by_cases h3 : q < 3
  · match i, hi with
    | 1, _ => exact fR1_eval q h3 x
    | 2, _ => exact fR2_eval q h3 x
  · have : q = 3 := by omega
    subst this
    match i, hi with
    | 1, _ =>
      simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
        Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
        AOp.interp, Rv]
    | 2, _ =>
      simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
        Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
        AOp.interp, Rv]

theorem kR4_nonneg (q : ℕ) : 0 ≤ kR4 q := by
  unfold kR4; split_ifs
  · exact (kR_pos q).le
  · norm_num

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `acc_tune_limp`**, every mode, Z3-free. -/
theorem acc_tune_limp_wellFormedR : WellFormedR Gr guardR (epsR acc_tune_limp_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hcr : 0 ≤ cR4 q ∧ cR4 q ≤ 40 := by
    unfold cR4; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR4 q) (cR4 q) (kR4_nonneg q) (fR0_all q hq4)
      (fun i hi s => fRo_all q hq4 i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR4 q * (cR4 q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_all q hq4]
    have hb := H.linear_between (memR q) _ _ (kR4_nonneg q) hf
    have hgx := (sat_guardR q hq4 x).mp hg
    by_cases h3 : q < 3
    · -- the three engaged profiles: [20, 36] invariant (set point 30 inside)
      simp only [h3, if_true] at hgx
      simp only [cR4, h3, if_true] at hb
      refine ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide),
        (sat_guardR q hq4 _).mpr ?_⟩
      simp only [h3, if_true]
      exact ⟨le_trans (le_min hgx.1 (by norm_num)) hb.1,
        le_trans hb.2 (max_le hgx.2 (by norm_num))⟩
    · have : q = 3 := by omega
      subst this
      simp only [show ¬ (3:ℕ) < 3 from by norm_num, if_false] at hgx
      have hdn := H.linear_down (memR 3) _ _ (kR4_nonneg 3) hf
        (by simp [cR4]; linarith [hdx.1])
      refine ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR 3 hq4 _).mpr ?_⟩
      simp only [show ¬ (3:ℕ) < 3 from by norm_num, if_false]
      linarith [hdn.2]

end V2AccTuneLimp
end RelCertifier
