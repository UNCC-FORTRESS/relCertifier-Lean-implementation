/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_engine_cooling` (suite_v2): Assumption 1 of the right model

Stated directly over the generic bridge's automaton `grOf IR 3 pruned`: the lowered right
guards, `ε_R = 1`. The right model is the genuine controller of the NAHS 2025 engine cooling
system: `Cool` (`temp' = −0.5`, guard `temp ≥ 100`, the source's `temp > 100` closed, the
disclosed departure) and `Heat` (`temp' = 1`, guard `temp ≤ 100`), evolve domain `temp ≥ 0`;
the padding coordinates have field 0. Existence: the linear motion at the mode's rate
(`exists_rate_run`), in the domain since a cycle of `Cool` from `temp ≥ 100` stays above
`99.5`. Completeness, for EVERY run: the two guards cover the line (`temp ≥ 100` or
`temp ≤ 100`), and both modes declare both successors. Z3-free.

The suite file is the pre-landing demo `engine_cooling_prelanding` (`benchmarks/prelanding_demo`)
under its suite name; this proof is `WellFormed/EngineCoolingPrelanding.lean` with the names
changed (2026-10-30, batch 11).
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.lit_nahs25_engine_cooling

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2LitNahs25EngineCooling

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.lit_nahs25_engine_cooling_IRv2

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1 : ℚ) / 2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp1000 : Run.parseRat "100.0" = some (100 : ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.lit_nahs25_engine_cooling_IRv2, hp10]

theorem nR_eq : nR IR = 2 := rfl

/-- The lowered field of `Cool`: `temp' = 0 − 0.5`, the padding coordinates frozen. -/
theorem fR_cool (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 0 i) s = if i.val = 0 then -(1 / 2) else 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_nahs25_engine_cooling_IRv2, Run.dynOf, Run.lowerE,
      hp00, hp05, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

/-- The lowered field of `Heat`: `temp' = 1`, the padding coordinates frozen. -/
theorem fR_heat (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 1 i) s = if i.val = 0 then 1 else 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_nahs25_engine_cooling_IRv2, Run.dynOf, Run.lowerE,
      hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domR (s : State (Var 3)) : Formula.sat (domR IR 3) s ↔ 0 ≤ s (Rv 0) := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.lit_nahs25_engine_cooling_IRv2, Run.lowerF,
    Run.lowerE, hp00, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR0 (s : State (Var 3)) : Formula.sat (guardR IR 3 0) s ↔ 100 ≤ s (Rv 0) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_nahs25_engine_cooling_IRv2, Run.lowerF,
    Run.lowerE, hp1000, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR1 (s : State (Var 3)) : Formula.sat (guardR IR 3 1) s ↔ s (Rv 0) ≤ 100 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_nahs25_engine_cooling_IRv2, Run.lowerF,
    Run.lowerE, hp1000, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem cool_next (q : ℕ) (hq : q < 2) : "Cool" ∈ (mRof IR q).next := by
  interval_cases q <;> decide
theorem heat_next (q : ℕ) (hq : q < 2) : "Heat" ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem tgt_cool : tgtIdx IR "Cool" = 0 := by decide
theorem tgt_heat : tgtIdx IR "Heat" = 1 := by decide

/-- **Assumption 1 for `lit_nahs25_engine_cooling`**, every mode, over the bridge's automaton. -/
theorem lit_nahs25_engine_cooling_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq2
  -- completeness: the two guards cover the line, both successors declared everywhere
  have hcomp : ∀ (t : ℝ) (Φ : ℝ → State (Var 3)),
      ∃ e ∈ (grOf IR 3 pruned).edgesFrom q, Formula.sat (guardR IR 3 e.tgt) (Φ t) := by
    intro t Φ
    rcases le_total 100 (Φ t (Rv 0)) with h | h
    · refine ⟨edgeOf IR 3 pruned q "Cool", edge_mem_grOf (by rw [nR_eq]; exact hq2)
        (cool_next q hq2), ?_⟩
      simp only [edgeOf, tgt_cool]
      exact (sat_guardR0 _).mpr h
    · refine ⟨edgeOf IR 3 pruned q "Heat", edge_mem_grOf (by rw [nR_eq]; exact hq2)
        (heat_next q hq2), ?_⟩
      simp only [edgeOf, tgt_heat]
      exact (sat_guardR1 _).mpr h
  interval_cases q
  · -- Cool: the linear descent, above 99.5 within a cycle
    have hg0 := (sat_guardR0 x).mp hg
    refine ⟨⟨_, exists_rate_run x 0 (-(1 / 2)) (fun s => by rw [fR_cool]; simp)
        (fun i hi s => by rw [fR_cool, if_neg]; intro h; exact hi (Fin.ext h))
        1 (by norm_num) (fun t ht hte => ?_)⟩, fun t Φ _ _ => hcomp t Φ⟩
    show Formula.sat (domR IR 3) _
    rw [sat_domR, trajJ_j]; linarith
  · -- Heat: the linear ascent, above its start
    have hd0 := (sat_domR x).mp hd
    refine ⟨⟨_, exists_rate_run x 0 1 (fun s => by rw [fR_heat]; simp)
        (fun i hi s => by rw [fR_heat, if_neg]; intro h; exact hi (Fin.ext h))
        1 (by norm_num) (fun t ht hte => ?_)⟩, fun t Φ _ _ => hcomp t Φ⟩
    show Formula.sat (domR IR 3) _
    rw [sat_domR, trajJ_j]; linarith

end V2LitNahs25EngineCooling
end RelCertifier
