/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf25_salt_tank_hold`: Assumption 1 of the right model (guards partition the level)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the genuine brine tank of the
CSF 2025 timed-attack case study (Fig. 8): `Inc` (`xp' = 0.03 (100 − xp)`, guard `xp < 35`) and
`Dec` (`xp' = 0.03 (25 − xp)`, guard `xp ≥ 35`), the global clock `t' = 1` (coordinate 1), the
padding coordinate 2 frozen, evolve domain `0 ≤ xp ≤ 300` (brine saturation), each mode a
successor of each.
* Existence (i): the field is affine, so a run of every length exists over the whole space
  (`exists_odeSol_tt_of_lipschitz`); along it the level stays between its start and the mode's
  set point (`ODESol.linear_between` on every prefix), both in `[0, 300]`, so the run is in the
  domain.
* Completeness (ii): the guards partition the level (`xp < 35` or `xp ≥ 35`), so every end state
  enables `Inc` or `Dec`, both declared successors of both modes. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Flow.LipschitzRun
import RelCertifier.InstancesV2.BenchIR.lit_csf25_salt_tank_hold

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2LitCsf25SaltTankHold

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.lit_csf25_salt_tank_hold_IRv2

/-! ## Parse pins -/

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp003 : Run.parseRat "0.03" = some ((3 : ℚ) / 100) := by
  have h : parseQ "0.03" = some (⟨3, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp100 : Run.parseRat "100.0" = some (100 : ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp35 : Run.parseRat "35.0" = some (35 : ℚ) := by
  have h : parseQ "35.0" = some (⟨350, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "300.0" = some (300 : ℚ) := by
  have h : parseQ "300.0" = some (⟨3000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.lit_csf25_salt_tank_hold_IRv2, hp10]

theorem nR_eq : nR IR = 2 := rfl

/-! ## The right fields, evaluated -/

/-- The set point of mode `q`: `100` for `Inc`, `25` for `Dec`. -/
noncomputable def sp (q : ℕ) : ℝ := if q = 0 then 100 else 25

theorem sp_bounds (q : ℕ) : 0 ≤ sp q ∧ sp q ≤ 300 := by
  unfold sp; split_ifs <;> norm_num

theorem fR_eval0 (q : ℕ) (hq : q < 2) (s : State (Var 3)) :
    Term.eval (fR IR 3 q 0) s = 3 / 100 * (sp q - s (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_csf25_salt_tank_hold_IRv2, Run.dynOf,
      Run.lowerE, hp003, hp100, hp25, hp10, hp00, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, sp]

theorem fR_eval1 (q : ℕ) (hq : q < 2) (s : State (Var 3)) : Term.eval (fR IR 3 q 1) s = 1 := by
  interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_csf25_salt_tank_hold_IRv2, Run.dynOf,
      Run.lowerE, hp003, hp100, hp25, hp10, hp00, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR_eval2 (q : ℕ) (hq : q < 2) (s : State (Var 3)) : Term.eval (fR IR 3 q 2) s = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_csf25_salt_tank_hold_IRv2, Run.dynOf,
      Run.lowerE, hp003, hp100, hp25, hp10, hp00, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

/-- The right block is `1`-Lipschitz (the level's field `0.03 (c − xp)`, the clock's `1`). -/
theorem lipR (q : ℕ) (hq : q < 2) :
    LipschitzWith (Real.toNNReal 1) (odeField (rightBlock (fR IR 3 q) (Term.const 1))) := by
  apply lipschitz_rightBlock (fR IR 3 q) 1 zero_le_one
  intro j x y
  have hd : (0 : ℝ) ≤ dist x y := dist_nonneg
  fin_cases j
  · show |Term.eval (fR IR 3 q 0) x - Term.eval (fR IR 3 q 0) y| ≤ 1 * dist x y
    rw [fR_eval0 q hq x, fR_eval0 q hq y]
    have h := coord_sub_le_dist x y (Rv 0)
    have he : 3 / 100 * (sp q - x (Rv 0)) - 3 / 100 * (sp q - y (Rv 0))
        = -(3 / 100) * (x (Rv 0) - y (Rv 0)) := by ring
    rw [he, abs_mul]
    have : |(-(3 / 100) : ℝ)| = 3 / 100 := by norm_num [abs_of_neg]
    rw [this]; nlinarith [abs_nonneg (x (Rv 0) - y (Rv 0))]
  · show |Term.eval (fR IR 3 q 1) x - Term.eval (fR IR 3 q 1) y| ≤ 1 * dist x y
    rw [fR_eval1 q hq x, fR_eval1 q hq y]; simp [hd]
  · show |Term.eval (fR IR 3 q 2) x - Term.eval (fR IR 3 q 2) y| ≤ 1 * dist x y
    rw [fR_eval2 q hq x, fR_eval2 q hq y]; simp [hd]

/-! ## Domain and guards -/

theorem sat_domR (s : State (Var 3)) :
    Formula.sat (domR IR 3) s ↔ 0 ≤ s (Rv 0) ∧ s (Rv 0) ≤ 300 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.lit_csf25_salt_tank_hold_IRv2, Run.lowerF,
    Run.lowerE, hp00, hp300, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR0 (s : State (Var 3)) : Formula.sat (guardR IR 3 0) s ↔ s (Rv 0) < 35 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_csf25_salt_tank_hold_IRv2, Run.lowerF,
    Run.lowerE, hp35, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR1 (s : State (Var 3)) : Formula.sat (guardR IR 3 1) s ↔ 35 ≤ s (Rv 0) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_csf25_salt_tank_hold_IRv2, Run.lowerF,
    Run.lowerE, hp35, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem inc_next (q : ℕ) (hq : q < 2) : "Inc" ∈ (mRof IR q).next := by
  interval_cases q <;> decide
theorem dec_next (q : ℕ) (hq : q < 2) : "Dec" ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem tgt_inc : tgtIdx IR "Inc" = 0 := by decide
theorem tgt_dec : tgtIdx IR "Dec" = 1 := by decide

/-- The level's entry of mode `q`'s right block. -/
theorem memR (q : ℕ) :
    (Rv 0, Term.binop .mul (Term.const 1) (fR IR 3 q 0)) ∈ rightBlock (fR IR 3 q) (Term.const 1) :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `lit_csf25_salt_tank_hold`**, every mode, over the bridge's automaton. -/
theorem lit_csf25_salt_tank_hold_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x _ hd _
  obtain ⟨hq2, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq2
  obtain ⟨d0, d1⟩ := (sat_domR x).mp hd
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, H⟩ := exists_odeSol_tt_of_lipschitz (rightBlock_wellFormed _ _) (lipR q hq2) x 1
      (by norm_num)
    refine ⟨Φ, odeSol_of_tt H (fun t ht => ?_)⟩
    have hb := (H.restrict ht.1 ht.2).linear_between (memR q) (3 / 100) (sp q) (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fR_eval0 q hq2])
    obtain ⟨s0, s1⟩ := sp_bounds q
    show Formula.sat (domR IR 3) (Φ t)
    rw [sat_domR]
    constructor
    · exact le_trans (le_min d0 s0) hb.1
    · exact le_trans hb.2 (max_le d1 s1)
  · intro t Φ _ _
    rcases lt_or_ge (Φ t (Rv 0)) 35 with h | h
    · refine ⟨edgeOf IR 3 pruned q "Inc", edge_mem_grOf (by rw [nR_eq]; exact hq2) (inc_next q hq2), ?_⟩
      simp only [edgeOf, tgt_inc]
      exact (sat_guardR0 _).mpr h
    · refine ⟨edgeOf IR 3 pruned q "Dec", edge_mem_grOf (by rw [nR_eq]; exact hq2) (dec_next q hq2), ?_⟩
      simp only [edgeOf, tgt_dec]
      exact (sat_guardR1 _).mpr h

end V2LitCsf25SaltTankHold
end RelCertifier
