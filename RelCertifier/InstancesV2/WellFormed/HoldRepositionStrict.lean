/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hold_reposition_strict` (prelanding_demo): Assumption 1 of the right model

Stated directly over the generic bridge's automaton `grOf IR 3 pruned`: the lowered right
guards, `ε_R = 1`. `Up` (`y' = 1`, guard `y ≤ 0`, successors `Up`, `Hold`) and `Hold`
(`y' = 0`, guard `y ≥ 0`, successor `Hold`), evolve domain `y ≥ −10`; the padding coordinates have
field 0. Existence: the linear ascent from a start in the domain (`exists_rate_run`), the
constant run (`const_sol`). Completeness: along `Up` the two guards cover the line; along `Hold`
the level is frozen (`ODESol.const`), so `Hold`'s guard stays. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.hold_reposition_strict

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2HoldRepositionStrict

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.hold_reposition_strict_IRv2

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm10 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.hold_reposition_strict_IRv2, hp10]

theorem nR_eq : nR IR = 2 := rfl

theorem fR_up (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 0 i) s = if i.val = 0 then 1 else 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.hold_reposition_strict_IRv2, Run.dynOf, Run.lowerE,
      hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fR_hold (s : State (Var 3)) (i : Fin 3) : Term.eval (fR IR 3 1 i) s = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.hold_reposition_strict_IRv2, Run.dynOf, Run.lowerE,
      hp00, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_domR (s : State (Var 3)) : Formula.sat (domR IR 3) s ↔ -10 ≤ s (Rv 0) := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.hold_reposition_strict_IRv2, Run.lowerF,
    Run.lowerE, hpm10, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR0 (s : State (Var 3)) : Formula.sat (guardR IR 3 0) s ↔ s (Rv 0) ≤ 0 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.hold_reposition_strict_IRv2, Run.lowerF,
    Run.lowerE, hp00, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR1 (s : State (Var 3)) : Formula.sat (guardR IR 3 1) s ↔ 0 ≤ s (Rv 0) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.hold_reposition_strict_IRv2, Run.lowerF,
    Run.lowerE, hp00, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem up_next : "Up" ∈ (mRof IR 0).next := by decide
theorem hold_next0 : "Hold" ∈ (mRof IR 0).next := by decide
theorem hold_next1 : "Hold" ∈ (mRof IR 1).next := by decide
theorem tgt_up : tgtIdx IR "Up" = 0 := by decide
theorem tgt_hold : tgtIdx IR "Hold" = 1 := by decide

theorem memR (q : ℕ) :
    (Rv 0, Term.binop .mul (Term.const 1) (fR IR 3 q 0)) ∈ (modeOf IR 3 q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `hold_reposition_strict`**, every mode, over the bridge's automaton. -/
theorem hold_reposition_strict_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq2
  interval_cases q
  · -- Up: the linear ascent; the two guards cover the line
    have hd0 := (sat_domR x).mp hd
    refine ⟨⟨_, exists_rate_run x 0 1 (fun s => by rw [fR_up]; simp)
        (fun i hi s => by rw [fR_up, if_neg]; intro h; exact hi (Fin.ext h))
        1 (by norm_num) (fun t ht hte => ?_)⟩, fun t Φ _ _ => ?_⟩
    · show Formula.sat (domR IR 3) _
      rw [sat_domR, trajJ_j]; linarith
    · rcases le_total (Φ t (Rv 0)) 0 with h | h
      · refine ⟨edgeOf IR 3 pruned 0 "Up", edge_mem_grOf (by rw [nR_eq]; norm_num) up_next, ?_⟩
        simp only [edgeOf, tgt_up]
        exact (sat_guardR0 _).mpr h
      · refine ⟨edgeOf IR 3 pruned 0 "Hold", edge_mem_grOf (by rw [nR_eq]; norm_num) hold_next0, ?_⟩
        simp only [edgeOf, tgt_hold]
        exact (sat_guardR1 _).mpr h
  · -- Hold: the level is frozen
    have hg1 := (sat_guardR1 x).mp hg
    refine ⟨⟨_, const_sol (fun i s => fR_hold s i) hd (by norm_num)⟩, fun t Φ _ H => ?_⟩
    have hc := H.const (memR 1) (fun s _ => by rw [eval_unit_mul, fR_hold])
    refine ⟨edgeOf IR 3 pruned 1 "Hold", edge_mem_grOf (by rw [nR_eq]; norm_num) hold_next1, ?_⟩
    simp only [edgeOf, tgt_hold]
    rw [sat_guardR1, hc]
    exact hg1

end V2HoldRepositionStrict
end RelCertifier
