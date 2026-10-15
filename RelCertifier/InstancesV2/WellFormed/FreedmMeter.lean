/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `freedm_meter`: Assumption 1 of the right model (style (b), exit into `GridD0R0`)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the free-source
controller `batS` of the FREEDM transformer with one battery `B` and the meter `E`: six battery
modes (`B' = r − d`, `E' = 0`, guard: one period keeps `B` in `[0, 10]`) and six grid modes
(`B' = 0`, `E' = d − r`, guard the evolve domain `0 ≤ B ≤ 10`), for demand `d ∈ {0, 1, 2}` and
renewable `r ∈ {0, 1}`. Existence: the explicit linear run (`trajRs_sol`), inside the domain for
one period by the battery guards. Completeness: `GridD0R0`'s guard is the evolve domain, so
every run's end state enables that declared successor. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.freedm_meter

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2FreedmMeter

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.freedm_meter_IRv2

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm10 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h] <;> norm_num
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h] <;> norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h] <;> norm_num
theorem hp90 : Run.parseRat "9.0" = some (9 : ℚ) := by
  have h : parseQ "9.0" = some (⟨90, 10⟩ : QF) := by decide
  simp [Run.parseRat, h] <;> norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h] <;> norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.freedm_meter_IRv2, hp10]

theorem nR_eq : nR IR = 12 := rfl

/-- The battery rate of right mode `q`: `r − d` for the battery modes `q < 6`, `0` on the grid. -/
noncomputable def cB (q : ℕ) : ℝ :=
  if q < 6 then ((q % 2 : ℕ) : ℝ) - ((q / 2 : ℕ) : ℝ) else 0
/-- The meter rate of right mode `q`: `0` on the battery, `d − r` on the grid. -/
noncomputable def cE (q : ℕ) : ℝ :=
  if q < 6 then 0 else (((q - 6) / 2 : ℕ) : ℝ) - (((q - 6) % 2 : ℕ) : ℝ)

/-- The lowered right fields: `B' = c_B`, `E' = c_E`, the padding coordinate frozen. -/
theorem fR_eval (q : ℕ) (hq : q < 12) (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 q i) s = if i.val = 0 then cB q else if i.val = 1 then cE q else 0 := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.freedm_meter_IRv2, Run.dynOf, Run.lowerE, hp00,
      hp10, hpm10, hp20, hpm20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, cB, cE] <;> norm_num [cB, cE]

theorem sat_domR (s : State (Var 3)) :
    Formula.sat (domR IR 3) s ↔ 0 ≤ s (Rv 0) ∧ s (Rv 0) ≤ 10 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.freedm_meter_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

/-- The battery guards bound one period of the mode's rate inside `[0, 10]`. -/
theorem sat_guardR_bounds (q : ℕ) (hq : q < 12) (s : State (Var 3))
    (hg : Formula.sat (guardR IR 3 q) s) :
    0 ≤ s (Rv 0) + cB q ∧ s (Rv 0) + cB q ≤ 10 := by
  interval_cases q <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.freedm_meter_IRv2, Run.lowerF, Run.lowerE,
      hp00, hp10, hp20, hp90, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
      ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv, cB] at hg ⊢ <;>
    constructor <;> linarith [hg.1, hg.2]

theorem sat_guardR6 (s : State (Var 3)) :
    Formula.sat (guardR IR 3 6) s ↔ 0 ≤ s (Rv 0) ∧ s (Rv 0) ≤ 10 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.freedm_meter_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp100, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem grid_next (q : ℕ) (hq : q < 12) : "GridD0R0" ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem tgt_grid : tgtIdx IR "GridD0R0" = 6 := by decide

/-- **Assumption 1 for `freedm_meter`**, every mode, over the bridge's automaton. -/
theorem freedm_meter_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq12, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq12
  have hdx := (sat_domR x).mp hd
  obtain ⟨hb0, hb1⟩ := sat_guardR_bounds q hq12 x hg
  refine ⟨?_, ?_⟩
  · -- existence: the explicit linear run of one period
    refine ⟨_, trajRs_sol x (fun i t => if i.val = 0 then x (Rv 0) + cB q * t
        else if i.val = 1 then x (Rv 1) + cE q * t else x (Rv i)) 1 (by norm_num) ?_ ?_ ?_⟩
    · intro i
      fin_cases i <;> simp
    · intro i t _ _
      rw [fR_eval q hq12]
      fin_cases i
      · simpa using ((hasDerivAt_id t).const_mul (cB q)).const_add (x (Rv 0))
      · simpa using ((hasDerivAt_id t).const_mul (cE q)).const_add (x (Rv 1))
      · simpa using hasDerivAt_const t (x (Rv 2))
    · intro t ht0 ht1
      change Formula.sat (domR IR 3) _
      rw [sat_domR]
      simp only [trajRs_R]
      norm_num
      constructor <;> nlinarith [hdx.1, hdx.2, hb0, hb1, ht0, ht1]
  · -- completeness: the end state is in the domain, which is `GridD0R0`'s guard
    intro t Φ _ H
    refine ⟨edgeOf IR 3 pruned q "GridD0R0",
      edge_mem_grOf (by rw [nR_eq]; exact hq12) (grid_next q hq12), ?_⟩
    simp only [edgeOf, tgt_grid]
    rw [sat_guardR6, ← sat_domR]
    exact H.end_dom

end V2FreedmMeter
end RelCertifier
