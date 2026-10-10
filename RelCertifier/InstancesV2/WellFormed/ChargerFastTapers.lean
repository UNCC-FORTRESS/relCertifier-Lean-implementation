/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_tapers`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
* `BULK` (`15 ≤ x < 80`, `x' = 0.1 (100 − x)`), style (b): within one interval a run ends
  in `[x₀, 100 − (100 − x₀) e^{−0.1}] ⊆ [15, 99)` (the closed form at the run's duration
  `t ≤ 1`), inside `BULK` or `ABSORB_SLOW` (`[80, 99)`).
* `ABSORB_SLOW` / `ABSORB_FAST` (`80 ≤ x < 99`, `x' = k (100 − x)`), style (b): a run ends in
  `[x₀, 100)`, inside the mode itself or `FULL` (`x ≥ 99`).
* `FULL` (`x ≥ 99`, frozen) and `FAULT` (`x < 10`, `x' = −0.01 x`), style (a).
Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.InstancesV2.Modal.ChargerFastTapers
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ChargerFastTapers

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

theorem epsR_eq : epsR charger_fast_tapers_IRv2 = 1 := by
  simp [epsR, charger_fast_tapers_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

noncomputable def kR5 (q : ℕ) : ℝ := if q < 4 then kR q else 1/100
noncomputable def cR5 (q : ℕ) : ℝ := if q < 4 then 100 else 0

theorem fR0_all (q : ℕ) (hq : q < 5) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR5 q * (cR5 q - x (Rv 0)) := by
  by_cases h4 : q < 4
  · rw [fR0_eval q h4]; simp [kR5, cR5, h4]
  · have : q = 4 := by omega
    subst this
    simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hpm001,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, kR5, cR5]
    ring

theorem fR1_all (q : ℕ) (hq : q < 5) (x : State (Var 2)) : Term.eval (fR q 1) x = 0 := by
  by_cases h4 : q < 4
  · exact fR1_eval q h4 x
  · have : q = 4 := by omega
    subst this
    simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hpm001,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_guardR4 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 4)) ν ↔ ν (Rv 0) < 10 := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp100, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem kR5_nonneg (q : ℕ) : 0 ≤ kR5 q := by
  unfold kR5 kR; split_ifs <;> norm_num

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `charger_fast_tapers`**, every mode, Z3-free. -/
theorem charger_fast_tapers_wellFormedR :
    WellFormedR Gr guardR (epsR charger_fast_tapers_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hcr : 0 ≤ cR5 q ∧ cR5 q ≤ 100 := by
    unfold cR5; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR5 q) (cR5 q) (kR5_nonneg q) (fR0_all q hq5)
      ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_all q hq5 s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ ht H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR5 q * (cR5 q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_all q hq5]
    interval_cases q
    · -- BULK: ends in [x₀, 99) within one interval, inside BULK or ABSORB_SLOW
      have hgx := (sat_guardR 0 (by norm_num) x).mp hg
      simp only [if_true] at hgx
      have hup := H.linear_up (memR 0) _ _ (kR5_nonneg 0) hf (by simp [cR5]; linarith)
      have hex := H.linear_exact (memR 0) _ _ hf
      simp [cR5, kR5, kR] at hup hex
      have he := Real.add_one_le_exp (-(1/10 * t))
      have h99 : Φ t (Rv 0) < 99 := by
        rw [hex]; nlinarith [H.hr]
      by_cases h80 : Φ t (Rv 0) < 80
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by linarith, h80⟩)⟩
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h99⟩)⟩
    · -- ABSORB_SLOW: ends in [x₀, 100), inside itself or FULL
      have hgx := (sat_guardR 1 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 1) _ _ (kR5_nonneg 1) hf (by simp [cR5]; linarith)
      simp [cR5] at hup
      by_cases h99 : Φ t (Rv 0) < 99
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h99⟩)⟩
      · exact ⟨edgeW 1 3, edge_mem 1 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
          (by norm_num; linarith)⟩
    · -- ABSORB_FAST: the same
      have hgx := (sat_guardR 2 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 2) _ _ (kR5_nonneg 2) hf (by simp [cR5]; linarith)
      simp [cR5] at hup
      by_cases h99 : Φ t (Rv 0) < 99
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guardR 2 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h99⟩)⟩
      · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
          (by norm_num; linarith)⟩
    · -- FULL: frozen
      have hgx := (sat_guardR 3 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 3) _ _ (kR5_nonneg 3) hf (by simp [cR5]; linarith)
      exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
        (by norm_num; linarith [hup.1])⟩
    · -- FAULT: [0, 10) invariant
      have hgx := (sat_guardR4 x).mp hg
      have hdn := H.linear_down (memR 4) _ _ (kR5_nonneg 4) hf (by simp [cR5]; linarith)
      exact ⟨edgeW 4 4, edge_mem 4 4 (by decide), (sat_guardR4 _).mpr (by linarith [hdn.2])⟩

end V2ChargerFastTapers
end RelCertifier
