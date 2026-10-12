/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_twospeed`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant and of the stretches: over the right
automaton `Gr` of the Theorem 3 instance (`InstancesV2/Modal/WatertankTwospeed.lean`), the
lowered right guards, and `ε_r = 1` read from the file.

Both modes are contractions `x' = k (12.5 − x)` (`Fast` 0.6, `Slow` 0.2) inside the tank `[0, 25]`.
* Existence (i): the explicit exponential (`hwfB`, unit stretch).
* (ii), style (b) for `Fast` (`[2, 8)`): a run ends in `[x₀, 12.5)`, inside `Fast` or `Slow`
  (`x ≥ 8`); style (a) for `Slow`: `x ≥ 8` is forward invariant (12.5 approached from either
  side, the run stays above 8), the self-loop is enabled.
Z3-free.
-/
import RelCertifier.InstancesV2.Modal.WatertankTwospeed
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace V2WatertankTwospeed

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR watertank_twospeed_IRv2 = 1 := by
  simp [epsR, watertank_twospeed_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem fieldR (q : ℕ) (hq : q < 2) (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval q hq]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `watertank_twospeed`**, every mode, Z3-free. -/
theorem watertank_twospeed_wellFormedR : WellFormedR Gr guardR (epsR watertank_twospeed_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq2 x).mp hg
  refine ⟨?_, ?_⟩
  · exact exists_of_wellFormedFlowB (by norm_num) (hwfB' q hq2 1 zero_le_one 1) hd
  · intro t Φ _ H
    have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => fieldR q hq2 s
    have pick : ∀ t', (q, t') ∈ edgeList → t' < 2 →
        Formula.sat (hostGuard vs 2 Side.R (mR t')) (Φ t) →
        ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
      fun t' he _ hs => ⟨edgeW q t', edge_mem q t' he, hs⟩
    interval_cases q
    · -- Fast: a run ends in [x₀, 12.5), inside Fast or Slow
      simp only [if_true] at hgx
      have hup := H.linear_up (memR 0) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      have hlt := H.linear_lt (memR 0) _ _ hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hup hlt; norm_num at hup hlt
      by_cases h8 : Φ t (Rv 0) < 8
      · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by linarith, h8⟩))
      · exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; linarith))
    · -- Slow: x ≥ 8 is invariant (12.5 approached from below or above)
      norm_num at hgx
      by_cases hx : x (Rv 0) ≤ 25/2
      · have hup := H.linear_up (memR 1) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
        simp only [cRc] at hup; norm_num at hup
        exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; linarith))
      · replace hx := le_of_lt (not_le.mp hx)
        have hdn := H.linear_down (memR 1) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
        simp only [cRc] at hdn; norm_num at hdn
        exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; linarith [hdn.1]))

end V2WatertankTwospeed
end RelCertifier
