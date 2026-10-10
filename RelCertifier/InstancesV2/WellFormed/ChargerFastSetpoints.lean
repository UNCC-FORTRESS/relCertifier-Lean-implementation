/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
* `BULK` (`15 ≤ x < 80`, `x' = 0.1 (90 − x)`), style (b): a run ends in `[x₀, 90)`, inside
  `BULK` or `ABSORB` (`[80, 99)`).
* `ABSORB` (`80 ≤ x < 99`, `x' = 0.05 (100 − x)`), style (b): a run ends in `[x₀, 100)`,
  inside `ABSORB` or `FULL` (`x ≥ 99`).
* `FULL` (`x ≥ 99`, frozen) and `FAULT` (`x < 10`, `x' = −0.01 x`), style (a).
Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.InstancesV2.Modal.ChargerFastSetpoints
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ChargerFastSetpoints

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm001 : Run.parseRat "-0.01" = some (-(1:ℚ)/100) := by
  have h : parseQ "-0.01" = some (⟨-1, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR charger_fast_setpoints_IRv2 = 1 := by
  simp [epsR, charger_fast_setpoints_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

noncomputable def kR4 (q : ℕ) : ℝ := if q < 3 then kR q else 1/100
noncomputable def cR4 (q : ℕ) : ℝ := if q < 3 then cRc q else 0

theorem fR0_all (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR4 q * (cR4 q - x (Rv 0)) := by
  by_cases h3 : q < 3
  · rw [fR0_eval q h3]; simp [kR4, cR4, h3]
  · have : q = 3 := by omega
    subst this
    simp [fR, hostDyn, mR, charger_fast_setpoints_IRv2, vs, Run.dynOf, Run.lowerE, hpm001,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, kR4, cR4]
    ring

theorem fR1_all (q : ℕ) (hq : q < 4) (x : State (Var 2)) : Term.eval (fR q 1) x = 0 := by
  by_cases h3 : q < 3
  · exact fR1_eval q h3 x
  · have : q = 3 := by omega
    subst this
    simp [fR, hostDyn, mR, charger_fast_setpoints_IRv2, vs, Run.dynOf, Run.lowerE, hpm001,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_guardR3 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 3)) ν ↔ ν (Rv 0) < 10 := by
  simp [hostGuard, mR, charger_fast_setpoints_IRv2, Run.lowerF, Run.lowerE, hp100, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem kR4_nonneg (q : ℕ) : 0 ≤ kR4 q := by
  unfold kR4 kR; split_ifs <;> norm_num

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `charger_fast_setpoints`**, every mode, Z3-free. -/
theorem charger_fast_setpoints_wellFormedR :
    WellFormedR Gr guardR (epsR charger_fast_setpoints_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hcr : 0 ≤ cR4 q ∧ cR4 q ≤ 100 := by
    unfold cR4 cRc; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR4 q) (cR4 q) (kR4_nonneg q) (fR0_all q hq4)
      ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_all q hq4 s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR4 q * (cR4 q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_all q hq4]
    interval_cases q
    · -- BULK: ends in [x₀, 90), inside BULK or ABSORB
      have hgx := (sat_guardR 0 (by norm_num) x).mp hg
      simp only [if_true] at hgx
      have hup := H.linear_up (memR 0) _ _ (kR4_nonneg 0) hf (by simp [cR4, cRc]; linarith)
      have hlt := H.linear_lt (memR 0) _ _ hf (by simp [cR4, cRc]; linarith)
      simp [cR4, cRc] at hup hlt
      by_cases h80 : Φ t (Rv 0) < 80
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by linarith, h80⟩)⟩
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, by linarith⟩)⟩
    · -- ABSORB: ends in [x₀, 100), inside ABSORB or FULL
      have hgx := (sat_guardR 1 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 1) _ _ (kR4_nonneg 1) hf (by simp [cR4, cRc]; linarith)
      simp [cR4, cRc] at hup
      by_cases h99 : Φ t (Rv 0) < 99
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h99⟩)⟩
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide), (sat_guardR 2 (by norm_num) _).mpr
          (by norm_num; linarith)⟩
    · -- FULL: frozen
      have hgx := (sat_guardR 2 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 2) _ _ (kR4_nonneg 2) hf (by simp [cR4, cRc]; linarith)
      exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guardR 2 (by norm_num) _).mpr
        (by norm_num; linarith [hup.1])⟩
    · -- FAULT: [0, 10) invariant
      have hgx := (sat_guardR3 x).mp hg
      have hdn := H.linear_down (memR 3) _ _ (kR4_nonneg 3) hf (by simp [cR4]; linarith)
      exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR3 _).mpr (by linarith [hdn.2])⟩

end V2ChargerFastSetpoints
end RelCertifier
