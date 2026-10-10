/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` of the
Theorem 3 instance (`InstancesV2/Modal/Watertank.lean`: the file's modes, flows, evolve
domain and `next` lists, every edge testing the entered mode's lowered guard), the lowered
right guards, and `ε_r = 1` read from the file.

Every mode is a contraction `x' = k (c − x)` (PumpOff: `x' = 0`) inside the tank `[0, 25]`.
* Existence (i): the explicit exponential (`hwfB`, unit stretch).
* (ii), style (b) for `Low` (`[2, 10)`, set point 12.5): a run ends in `[x₀, 12.5)`, inside
  `Low` or `MidEco` (`[10, 17)`); style (a) for the others: `MidEco` / `MidBoost` (`[10, 17)`,
  set point 17, approached from below, never reached), `High` (`x ≥ 17`, approached from
  above), `PumpOff` (`x < 2`, frozen) are forward invariant, the self-loop is enabled.
Z3-free.
-/
import RelCertifier.InstancesV2.Modal.Watertank
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace V2Watertank

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR watertank_IRv2 = 1 := by
  simp [epsR, watertank_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem fieldR (q : ℕ) (hq : q < 5) (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval q hq]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `watertank`**, every mode, Z3-free. -/
theorem watertank_wellFormedR : WellFormedR Gr guardR (epsR watertank_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq5 x).mp hg
  refine ⟨?_, ?_⟩
  · have hw := hwfB 2 q hq5 1
    rw [show lam 2 = 1 from by simp [lam]] at hw
    exact exists_of_wellFormedFlowB (by norm_num) hw hd
  · intro t Φ _ H
    have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => fieldR q hq5 s
    have hx0 := ((sat_domR x).mp hd).1
    have pick : ∀ t', (q, t') ∈ edgeList → t' < 5 →
        Formula.sat (hostGuard vs 2 Side.R (mR t')) (Φ t) →
        ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
      fun t' he _ hs => ⟨edgeW q t', edge_mem q t' he, hs⟩
    interval_cases q
    · -- Low: a run ends in [x₀, 12.5), inside Low or MidEco
      simp only [if_true] at hgx
      have hup := H.linear_up (memR 0) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      have hlt := H.linear_lt (memR 0) _ _ hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hup hlt; norm_num at hup hlt
      by_cases h10 : Φ t (Rv 0) < 10
      · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by linarith, h10⟩))
      · exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, by linarith⟩))
    · -- MidEco: [10, 17) is invariant (17 approached from below, never reached)
      norm_num at hgx
      have hup := H.linear_up (memR 1) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      have hlt := H.linear_lt (memR 1) _ _ hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hup hlt; norm_num at hup hlt
      exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
        (by norm_num; exact ⟨by linarith, hlt⟩))
    · -- MidBoost: the same
      norm_num at hgx
      have hup := H.linear_up (memR 2) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      have hlt := H.linear_lt (memR 2) _ _ hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hup hlt; norm_num at hup hlt
      exact pick 2 (by decide) (by norm_num) ((sat_guardR 2 (by norm_num) _).mpr
        (by norm_num; exact ⟨by linarith, hlt⟩))
    · -- High: x ≥ 17 is invariant (17 approached from above)
      norm_num at hgx
      have hdn := H.linear_down (memR 3) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hdn; norm_num at hdn
      exact pick 3 (by decide) (by norm_num) ((sat_guardR 3 (by norm_num) _).mpr
        (by norm_num; exact hdn.1))
    · -- PumpOff: frozen (k = 0)
      norm_num at hgx
      have hdn := H.linear_down (memR 4) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hdn; norm_num at hdn
      exact pick 4 (by decide) (by norm_num) ((sat_guardR 4 (by norm_num) _).mpr
        (by norm_num; linarith))

end V2Watertank
end RelCertifier
