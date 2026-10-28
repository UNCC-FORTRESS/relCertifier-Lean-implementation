/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_salt_tank`: Assumption 1 of the right model (style (a), both modes invariant)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the genuine controller of
the brine tank: `On` (`xp' = 0.1 (25 − xp)`, guard `xp ≥ 25`) and `Off` (`xp' = 0`, guard
`xp < 25`, a strict atom), evolve domain the constant atom `0 ≤ 1` (the source's plant has no
state domain; the `xp ≥ 0` of the first install was dropped 2026-10-28); the padding
coordinates have field 0. Existence: `On`'s explicit exponential approach
`25 + (xp − 25) e^{−t/10}` (`exists_contract_run`), trivially in the domain; `Off`'s constant
run (`const_sol`). Completeness, for EVERY run (not only the explicit
one): along `On` the closed form of the linear coordinate (`ODESol.linear_down`) keeps
`xp ≥ 25`, so the end state enables the declared self-loop `On`; along `Off` the field
vanishes (`ODESol.const`), so `xp` keeps its start value and the end state enables `Off` (the
strict bound included). Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.lit_nahs25_salt_tank

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2LitNahs25SaltTank

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.lit_nahs25_salt_tank_IRv2

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp01 : Run.parseRat "0.1" = some ((1 : ℚ) / 10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.lit_nahs25_salt_tank_IRv2, hp10]

theorem nR_eq : nR IR = 2 := rfl

/-- The lowered field of `On`: `xp' = 0.1 (25 − xp)`, the padding coordinates frozen. -/
theorem fR_on (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 0 i) s = if i.val = 0 then 1 / 10 * (25 - s (Rv 0)) else 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_nahs25_salt_tank_IRv2, Run.dynOf, Run.lowerE,
      hp00, hp01, hp250, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

/-- The lowered field of `Off`: every coordinate frozen. -/
theorem fR_off (s : State (Var 3)) (i : Fin 3) : Term.eval (fR IR 3 1 i) s = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_nahs25_salt_tank_IRv2, Run.dynOf, Run.lowerE,
      hp00, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_domR_iff (s : State (Var 3)) : Formula.sat (domR IR 3) s ↔ (0 : ℝ) ≤ 1 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.lit_nahs25_salt_tank_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp10, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

/-- The evolve domain is the whole state space (the constant atom `0 ≤ 1`). -/
theorem sat_domR (s : State (Var 3)) : Formula.sat (domR IR 3) s :=
  (sat_domR_iff s).mpr zero_le_one

theorem sat_guardR0 (s : State (Var 3)) : Formula.sat (guardR IR 3 0) s ↔ 25 ≤ s (Rv 0) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_nahs25_salt_tank_IRv2, Run.lowerF, Run.lowerE,
    hp250, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_guardR1 (s : State (Var 3)) :
    Formula.sat (guardR IR 3 1) s ↔ s (Rv 0) < 25 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_nahs25_salt_tank_IRv2, Run.lowerF, Run.lowerE,
    hp250, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem on_next : "On" ∈ (mRof IR 0).next := by decide
theorem off_next : "Off" ∈ (mRof IR 1).next := by decide

theorem tgt_on : tgtIdx IR "On" = 0 := by decide
theorem tgt_off : tgtIdx IR "Off" = 1 := by decide

/-- The level coordinate's entry of mode `q`'s right block. -/
theorem memR (q : ℕ) :
    (Rv 0, Term.binop .mul (Term.const 1) (fR IR 3 q 0)) ∈ (modeOf IR 3 q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `lit_nahs25_salt_tank`**, every mode, over the bridge's automaton. -/
theorem lit_nahs25_salt_tank_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq2
  interval_cases q
  · -- On: the exponential approach to 25 from above
    have hg0 := (sat_guardR0 x).mp hg
    refine ⟨?_, ?_⟩
    · exact exists_contract_run x 0 (1 / 10) 25 (by norm_num)
        (fun s => by rw [fR_on]; simp)
        (fun i hi s => by rw [fR_on, if_neg]; intro h; exact hi (Fin.ext h))
        (fun _ _ _ => sat_domR _)
        1 (by norm_num)
    · intro t Φ _ H
      have hdn := H.linear_down (memR 0) (1 / 10) 25 (by norm_num)
        (fun s _ => by rw [eval_unit_mul, fR_on]; simp) hg0
      refine ⟨edgeOf IR 3 pruned 0 "On", edge_mem_grOf (by rw [nR_eq]; norm_num) on_next, ?_⟩
      simp only [edgeOf, tgt_on]
      exact (sat_guardR0 _).mpr hdn.1
  · -- Off: the level is frozen
    have hg1 := (sat_guardR1 x).mp hg
    refine ⟨?_, ?_⟩
    · exact ⟨_, const_sol (fun i s => fR_off s i) hd (by norm_num)⟩
    · intro t Φ _ H
      have hc := H.const (memR 1) (fun s _ => by rw [eval_unit_mul, fR_off])
      refine ⟨edgeOf IR 3 pruned 1 "Off", edge_mem_grOf (by rw [nR_eq]; norm_num) off_next, ?_⟩
      simp only [edgeOf, tgt_off]
      rw [sat_guardR1, hc]
      exact hg1

end V2LitNahs25SaltTank
end RelCertifier
