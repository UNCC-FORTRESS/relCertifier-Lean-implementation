/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_lane_control`: Assumption 1 of the right model (style (b), exit into a `Coast` pair)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the permissive sampled
lane controller of the dRL case study: six modes, pairs of a follower action (`Accel`: `v_f' = 1`,
guard `v_f ≤ 9` and the safe distance; `Coast`: `v_f' = 0`; `Brake`: `v_f' = −1`, guard
`v_f ≥ 1`) and a leader action (`LAccel`: `v_l' = 1`, guard `v_l ≤ 9`; `LBrake`: `v_l' = −1`,
guard `v_l ≥ 1`), gap `d' = v_l − v_f`, evolve domain `0 ≤ v_f ≤ 10 ∧ 0 ≤ v_l ≤ 10`.
Existence: the explicit polynomial run (`trajRs_sol`), inside the domain for one period by
the guard's speed bounds. Completeness: at every end state `v_l ≤ 9` or `v_l ≥ 1`, so
`CoastLAccel` or `CoastLBrake` (both declared successors of every mode) is enabled. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.drl_lane_control

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2DrlLaneControl

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.drl_lane_control_IRv2

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1 : ℚ) / 2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm05 : Run.parseRat "-0.5" = some (-(1 : ℚ) / 2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp90 : Run.parseRat "9.0" = some (9 : ℚ) := by
  have h : parseQ "9.0" = some (⟨90, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.drl_lane_control_IRv2, hp10]

theorem nR_eq : nR IR = 6 := rfl

/-- The follower's acceleration of right mode `q` (`1, 1, 0, 0, −1, −1`). -/
noncomputable def af (q : ℕ) : ℝ := if q < 2 then 1 else if q < 4 then 0 else -1
/-- The leader's acceleration of right mode `q` (`1` for even `q`, `−1` for odd `q`). -/
noncomputable def al (q : ℕ) : ℝ := if q % 2 = 0 then 1 else -1

/-- The lowered right fields: `d' = v_l − v_f`, `v_f' = a_f`, `v_l' = a_l`. -/
theorem fR_eval (q : ℕ) (hq : q < 6) (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 q i) s =
      if i.val = 0 then s (Rv 2) - s (Rv 1) else if i.val = 1 then af q else al q := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.drl_lane_control_IRv2, Run.dynOf, Run.lowerE, hp00,
      hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, af, al]

theorem sat_domR (s : State (Var 3)) :
    Formula.sat (domR IR 3) s ↔
      (0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 10) ∧ (0 ≤ s (Rv 2) ∧ s (Rv 2) ≤ 10) := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.drl_lane_control_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

/-- The speed bounds every guard carries: the follower's by its action, the leader's by its. -/
theorem sat_guardR_speed (q : ℕ) (hq : q < 6) (s : State (Var 3))
    (hg : Formula.sat (guardR IR 3 q) s) :
    (q < 2 → s (Rv 1) ≤ 9) ∧ (4 ≤ q → 1 ≤ s (Rv 1)) ∧
      (q % 2 = 0 → s (Rv 2) ≤ 9) ∧ (q % 2 = 1 → 1 ≤ s (Rv 2)) := by
  interval_cases q <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.drl_lane_control_IRv2, Run.lowerF, Run.lowerE,
      hp00, hp05, hpm05, hp10, hp20, hp90, hp100, Run.resolveVar, List.findIdx?_cons,
      IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv] at hg ⊢ <;>
    simp_all

theorem sat_guardR2 (s : State (Var 3)) :
    Formula.sat (guardR IR 3 2) s ↔
      (0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 10) ∧ (0 ≤ s (Rv 2) ∧ s (Rv 2) ≤ 9) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.drl_lane_control_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp90, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guardR3 (s : State (Var 3)) :
    Formula.sat (guardR IR 3 3) s ↔
      (0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 10) ∧ (1 ≤ s (Rv 2) ∧ s (Rv 2) ≤ 10) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.drl_lane_control_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp10, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem coastA_next (q : ℕ) (hq : q < 6) : "CoastLAccel" ∈ (mRof IR q).next := by
  interval_cases q <;> decide
theorem coastB_next (q : ℕ) (hq : q < 6) : "CoastLBrake" ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem tgt_coastA : tgtIdx IR "CoastLAccel" = 2 := by decide
theorem tgt_coastB : tgtIdx IR "CoastLBrake" = 3 := by decide

/-- **Assumption 1 for `drl_lane_control`**, every mode, over the bridge's automaton. -/
theorem drl_lane_control_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq6, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq6
  have hdx := (sat_domR x).mp hd
  obtain ⟨hf9, hf1, hl9, hl1⟩ := sat_guardR_speed q hq6 x hg
  refine ⟨?_, ?_⟩
  · -- existence: the explicit polynomial run of one period
    have hd0 : ∀ t : ℝ, HasDerivAt
        (fun u : ℝ => x (Rv 0) + (x (Rv 2) - x (Rv 1)) * u + (al q - af q) * u ^ 2 / 2)
        ((x (Rv 2) + al q * t) - (x (Rv 1) + af q * t)) t := fun t => by
      have h1 : HasDerivAt (fun u : ℝ => x (Rv 0) + (x (Rv 2) - x (Rv 1)) * u)
          (x (Rv 2) - x (Rv 1)) t := by
        simpa using ((hasDerivAt_id t).const_mul (x (Rv 2) - x (Rv 1))).const_add (x (Rv 0))
      have h2 : HasDerivAt (fun u : ℝ => (al q - af q) * u ^ 2 / 2)
          ((al q - af q) * (2 * t ^ 1) / 2) t :=
        ((hasDerivAt_pow 2 t).const_mul (al q - af q)).div_const 2
      exact (h1.add h2).congr_deriv (by ring)
    refine ⟨_, trajRs_sol x (fun i t =>
        if i.val = 0 then x (Rv 0) + (x (Rv 2) - x (Rv 1)) * t + (al q - af q) * t ^ 2 / 2
        else if i.val = 1 then x (Rv 1) + af q * t else x (Rv 2) + al q * t) 1 (by norm_num)
        ?_ ?_ ?_⟩
    · intro i
      fin_cases i <;> simp
    · intro i t _ _
      rw [fR_eval q hq6]
      fin_cases i
      · simpa [trajRs_R] using hd0 t
      · simpa using ((hasDerivAt_id t).const_mul (af q)).const_add (x (Rv 1))
      · simpa using ((hasDerivAt_id t).const_mul (al q)).const_add (x (Rv 2))
    · intro t ht0 ht1
      change Formula.sat (domR IR 3) _
      rw [sat_domR]
      simp only [trajRs_R]
      norm_num
      obtain ⟨⟨hf0, hf10⟩, ⟨hl0, hl10⟩⟩ := hdx
      interval_cases q <;> norm_num [af, al] at hf9 hf1 hl9 hl1 ⊢ <;>
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith
  · -- completeness: `v_l ≤ 9` enables `CoastLAccel`, `v_l ≥ 1` enables `CoastLBrake`
    intro t Φ _ H
    have hend := (sat_domR _).mp H.end_dom
    by_cases hv : Φ t (Rv 2) ≤ 9
    · refine ⟨edgeOf IR 3 pruned q "CoastLAccel",
        edge_mem_grOf (by rw [nR_eq]; exact hq6) (coastA_next q hq6), ?_⟩
      simp only [edgeOf, tgt_coastA]
      rw [sat_guardR2]
      exact ⟨hend.1, hend.2.1, hv⟩
    · refine ⟨edgeOf IR 3 pruned q "CoastLBrake",
        edge_mem_grOf (by rw [nR_eq]; exact hq6) (coastB_next q hq6), ?_⟩
      simp only [edgeOf, tgt_coastB]
      rw [sat_guardR3]
      exact ⟨hend.1, by linarith, hend.2.2⟩

end V2DrlLaneControl
end RelCertifier
