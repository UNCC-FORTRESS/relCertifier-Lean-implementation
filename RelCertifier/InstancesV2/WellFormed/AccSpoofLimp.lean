/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_limp`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
`NORMAL` / `ECO` / `SPORT` (`20 ≤ v < 40`, `v' = (c − v)/2` with `c = 30, 27, 33`) and
`DISENGAGE` (`v < 20`, `v' = −v/2`) are contractions whose guard sets are forward invariant
(style (a)). Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.InstancesV2.Modal.AccSpoofLimp
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccSpoofLimp

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR acc_spoof_limp_IRv2 = 1 := by
  simp [epsR, acc_spoof_limp_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- Set points of all four right modes (`DISENGAGE`: 0). -/
noncomputable def cR4 (q : ℕ) : ℝ := if q < 3 then cRc q else 0

theorem fR0_all (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = 1/2 * (cR4 q - x (Rv 0)) := by
  by_cases h3 : q < 3
  · rw [fR0_eval q h3]; simp [cR4, h3]
  · have : q = 3 := by omega
    subst this
    simp [fR, hostDyn, mR, acc_spoof_limp_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cR4]
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
      simp [fR, hostDyn, mR, acc_spoof_limp_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
        Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
        AOp.interp, Rv]
    | 2, _ =>
      simp [fR, hostDyn, mR, acc_spoof_limp_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
        Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
        AOp.interp, Rv]

theorem sat_guardR3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔ ν (Rv 0) < 20 := by
  simp [hostGuard, mR, acc_spoof_limp_IRv2, Run.lowerF, Run.lowerE, hp200, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `acc_spoof_limp`**, every mode, Z3-free. -/
theorem acc_spoof_limp_wellFormedR : WellFormedR Gr guardR (epsR acc_spoof_limp_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hcr : 0 ≤ cR4 q ∧ cR4 q ≤ 40 := by
    unfold cR4 cRc; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (1/2) (cR4 q) (by norm_num) (fR0_all q hq4)
      (fun i hi s => fRo_all q hq4 i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = 1/2 * (cR4 q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_all q hq4]
    have hb := H.linear_between (memR q) _ _ (by norm_num) hf
    by_cases h3 : q < 3
    · -- the three engaged profiles: [20, 40) invariant (set point inside)
      have hgx := (sat_guardR q h3 x).mp hg
      have hc : 20 ≤ cR4 q ∧ cR4 q < 40 := by
        unfold cR4 cRc; simp only [h3, if_true]; split_ifs <;> norm_num
      refine ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide),
        (sat_guardR q h3 _).mpr ⟨?_, ?_⟩⟩
      · exact le_trans (le_min hgx.1 hc.1) hb.1
      · exact lt_of_le_of_lt hb.2 (max_lt hgx.2 hc.2)
    · have : q = 3 := by omega
      subst this
      have hgx := (sat_guardR3 x).mp hg
      have hdn := H.linear_down (memR 3) _ _ (by norm_num) hf (by simp [cR4]; linarith [hdx.1])
      exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR3 _).mpr (by linarith [hdn.2])⟩

end V2AccSpoofLimp
end RelCertifier
