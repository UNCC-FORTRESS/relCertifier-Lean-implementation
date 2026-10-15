/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_car_stop`: Assumption 1 of the right model (style (b), exit into `Coast`)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the permissive sampled
car controller of the dRL refinement example: `Accel` (`x' = v, v' = 1`, guard
`0 ≤ v ≤ 9 ∧ x + v²/2 ≤ 50`), `Coast` (`v' = 0`, guard `0 ≤ v ≤ 10`) and `Brake`
(`v' = −1`, guard `1 ≤ v ≤ 10`), evolve domain `0 ≤ v ≤ 10`. Existence: the explicit
polynomial run `x + v t + c t²/2`, `v + c t` (`trajRs_sol`), inside the domain for one period
by the guard's speed bounds. Completeness: `Coast`'s guard is the evolve domain, so every
run's end state enables the declared successor `Coast`. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.drl_car_stop

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2DrlCarStop

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.drl_car_stop_IRv2

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1 : ℚ) / 2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp90 : Run.parseRat "9.0" = some (9 : ℚ) := by
  have h : parseQ "9.0" = some (⟨90, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp500 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.drl_car_stop_IRv2, hp10]

theorem nR_eq : nR IR = 3 := rfl

/-- The acceleration of right mode `q`: `1`, `0`, `−1`. -/
noncomputable def cq (q : ℕ) : ℝ := if q = 0 then 1 else if q = 1 then 0 else -1

/-- The lowered right fields: `x' = v`, `v' = c_q`, the padding coordinate frozen. -/
theorem fR_eval (q : ℕ) (hq : q < 3) (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 q i) s = if i.val = 0 then s (Rv 1) else if i.val = 1 then cq q else 0 := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.drl_car_stop_IRv2, Run.dynOf, Run.lowerE, hp00,
      hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cq]

theorem sat_domR (s : State (Var 3)) :
    Formula.sat (domR IR 3) s ↔ 0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 10 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.drl_car_stop_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR_speed (q : ℕ) (hq : q < 3) (s : State (Var 3))
    (hg : Formula.sat (guardR IR 3 q) s) :
    (q = 0 → s (Rv 1) ≤ 9) ∧ (q = 2 → 1 ≤ s (Rv 1)) := by
  interval_cases q <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.drl_car_stop_IRv2, Run.lowerF, Run.lowerE,
      hp00, hp05, hp10, hp90, hp100, hp500, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
      ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv] at hg ⊢ <;>
    simp_all

theorem sat_guardR1 (s : State (Var 3)) :
    Formula.sat (guardR IR 3 1) s ↔ 0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 10 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.drl_car_stop_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem coast_next (q : ℕ) (hq : q < 3) : "Coast" ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem tgt_coast : tgtIdx IR "Coast" = 1 := by decide

/-- **Assumption 1 for `drl_car_stop`**, every mode, over the bridge's automaton. -/
theorem drl_car_stop_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq3
  have hdx := (sat_domR x).mp hd
  obtain ⟨hs0, hs2⟩ := sat_guardR_speed q hq3 x hg
  refine ⟨?_, ?_⟩
  · -- existence: the explicit polynomial run of one period
    have hd0 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => x (Rv 0) + x (Rv 1) * u + cq q * u ^ 2 / 2)
        (x (Rv 1) + cq q * t) t := fun t => by
      have h1 : HasDerivAt (fun u : ℝ => x (Rv 0) + x (Rv 1) * u) (x (Rv 1)) t := by
        simpa using ((hasDerivAt_id t).const_mul (x (Rv 1))).const_add (x (Rv 0))
      have h2 : HasDerivAt (fun u : ℝ => cq q * u ^ 2 / 2) (cq q * (2 * t ^ 1) / 2) t :=
        ((hasDerivAt_pow 2 t).const_mul (cq q)).div_const 2
      exact (h1.add h2).congr_deriv (by ring)
    refine ⟨_, trajRs_sol x (fun i t => if i.val = 0 then x (Rv 0) + x (Rv 1) * t + cq q * t ^ 2 / 2
        else if i.val = 1 then x (Rv 1) + cq q * t else x (Rv i)) 1 (by norm_num) ?_ ?_ ?_⟩
    · intro i
      fin_cases i <;> simp
    · intro i t _ _
      rw [fR_eval q hq3]
      fin_cases i
      · simpa [trajRs_R] using hd0 t
      · simpa using ((hasDerivAt_id t).const_mul (cq q)).const_add (x (Rv 1))
      · simpa using hasDerivAt_const t (x (Rv 2))
    · intro t ht0 ht1
      change Formula.sat (domR IR 3) _
      rw [sat_domR]
      simp only [trajRs_R]
      norm_num
      interval_cases q
      · have := hs0 rfl
        norm_num [cq]
        constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
      · norm_num [cq]
        exact hdx
      · have := hs2 rfl
        norm_num [cq]
        constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
  · -- completeness: the end state is in the domain, which is `Coast`'s guard
    intro t Φ _ H
    refine ⟨edgeOf IR 3 pruned q "Coast", edge_mem_grOf (by rw [nR_eq]; exact hq3) (coast_next q hq3), ?_⟩
    simp only [edgeOf, tgt_coast]
    rw [sat_guardR1, ← sat_domR]
    exact H.end_dom

end V2DrlCarStop
end RelCertifier
