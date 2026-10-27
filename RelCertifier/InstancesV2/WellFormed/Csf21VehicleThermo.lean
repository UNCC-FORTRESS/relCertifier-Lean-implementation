/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `csf21_vehicle_thermo`: Assumption 1 of the right model (style (b), exit into `Coast*`)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the genuine car of the
CSF'21 sensor-attack example with its thermostat: six modes action × setting, `AccCool`,
`AccHeat`, `CoastCool`, `CoastHeat`, `BrkCool`, `BrkHeat` (indices `0..5`), field
`d' = −v`, `v' = c_q ∈ {1, 0, −1}`, `temp' = h_q ∈ {−1, 1}`, evolve domain `0 ≤ v ≤ 40`.
`Acc*` guards contain `0 ≤ v ≤ 39`, `Brk*` guards `1 ≤ v`, `Coast*` guards `0 ≤ v`, and
`Cool` asks `temp ≥ 20`, `Heat` asks `temp ≤ 20`. Existence: the explicit polynomial run
`d − v t − c t²/2`, `v + c t`, `temp + h t` (`trajRs_sol`), inside the domain for one period by
the guard's speed bounds. Completeness: the end state is in the domain, so `v ≥ 0` holds there,
and by a case split on its temperature it enables `CoastCool` (`temp ≥ 20`) or `CoastHeat`
(`temp ≤ 20`), both declared successors of every mode. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.csf21_vehicle_thermo

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Csf21VehicleThermo

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.csf21_vehicle_thermo_IRv2

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp390 : Run.parseRat "39.0" = some (39 : ℚ) := by
  have h : parseQ "39.0" = some (⟨390, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.csf21_vehicle_thermo_IRv2, hp10]

theorem nR_eq : nR IR = 6 := rfl

/-- The acceleration of right mode `q`: `1` (`Acc*`), `0` (`Coast*`), `−1` (`Brk*`). -/
noncomputable def cq (q : ℕ) : ℝ :=
  if q = 0 ∨ q = 1 then 1 else if q = 2 ∨ q = 3 then 0 else -1

/-- The thermostat rate of right mode `q`: `−1` (`*Cool`, even `q`), `1` (`*Heat`, odd `q`). -/
noncomputable def hq (q : ℕ) : ℝ :=
  if q = 0 ∨ q = 2 ∨ q = 4 then -1 else 1

/-- The lowered right fields: `d' = −v`, `v' = c_q`, `temp' = h_q`. -/
theorem fR_eval (q : ℕ) (hq6 : q < 6) (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 q i) s =
      if i.val = 0 then -s (Rv 1) else if i.val = 1 then cq q else hq q := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.csf21_vehicle_thermo_IRv2, Run.dynOf, Run.lowerE,
      hp00, hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cq, hq]

theorem sat_domR (s : State (Var 3)) :
    Formula.sat (domR IR 3) s ↔ 0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 40 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.csf21_vehicle_thermo_IRv2, Run.lowerF,
    Run.lowerE, hp00, hp400, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

/-- The speed bounds of the guards: `Acc*` needs `v ≤ 39`, `Brk*` needs `1 ≤ v`. -/
theorem sat_guardR_speed (q : ℕ) (hq6 : q < 6) (s : State (Var 3))
    (hg : Formula.sat (guardR IR 3 q) s) :
    ((q = 0 ∨ q = 1) → s (Rv 1) ≤ 39) ∧ ((q = 4 ∨ q = 5) → 1 ≤ s (Rv 1)) := by
  interval_cases q <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.csf21_vehicle_thermo_IRv2, Run.lowerF,
      Run.lowerE, hp00, hp10, hp20, hp40, hp200, hp390, hp400, Run.resolveVar,
      List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
      AOp.interp, Rv] at hg ⊢ <;>
    simp_all

/-- `CoastCool`'s guard: `0 ≤ v ∧ temp ≥ 20`. -/
theorem sat_guardR2 (s : State (Var 3)) :
    Formula.sat (guardR IR 3 2) s ↔ 0 ≤ s (Rv 1) ∧ 20 ≤ s (Rv 2) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.csf21_vehicle_thermo_IRv2, Run.lowerF,
    Run.lowerE, hp00, hp200, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

/-- `CoastHeat`'s guard: `0 ≤ v ∧ temp ≤ 20`. -/
theorem sat_guardR3 (s : State (Var 3)) :
    Formula.sat (guardR IR 3 3) s ↔ 0 ≤ s (Rv 1) ∧ s (Rv 2) ≤ 20 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.csf21_vehicle_thermo_IRv2, Run.lowerF,
    Run.lowerE, hp00, hp200, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem coastCool_next (q : ℕ) (hq6 : q < 6) : "CoastCool" ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem coastHeat_next (q : ℕ) (hq6 : q < 6) : "CoastHeat" ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem tgt_coastCool : tgtIdx IR "CoastCool" = 2 := by decide

theorem tgt_coastHeat : tgtIdx IR "CoastHeat" = 3 := by decide

/-- **Assumption 1 for `csf21_vehicle_thermo`**, every mode, over the bridge's automaton. -/
theorem csf21_vehicle_thermo_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q _ m hm x hg hd _
  obtain ⟨hq6, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq6
  have hdx := (sat_domR x).mp hd
  obtain ⟨hs0, hs2⟩ := sat_guardR_speed q hq6 x hg
  refine ⟨?_, ?_⟩
  · -- existence: the explicit polynomial run of one period
    have hd0 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => x (Rv 0) - x (Rv 1) * u - cq q * u ^ 2 / 2)
        (-(x (Rv 1) + cq q * t)) t := fun t => by
      have h1 : HasDerivAt (fun u : ℝ => x (Rv 0) - x (Rv 1) * u) (-x (Rv 1)) t := by
        simpa using ((hasDerivAt_id t).const_mul (x (Rv 1))).const_sub (x (Rv 0))
      have h2 : HasDerivAt (fun u : ℝ => cq q * u ^ 2 / 2) (cq q * (2 * t ^ 1) / 2) t :=
        ((hasDerivAt_pow 2 t).const_mul (cq q)).div_const 2
      exact (h1.sub h2).congr_deriv (by ring)
    refine ⟨_, trajRs_sol x (fun i t =>
        if i.val = 0 then x (Rv 0) - x (Rv 1) * t - cq q * t ^ 2 / 2
        else if i.val = 1 then x (Rv 1) + cq q * t else x (Rv 2) + hq q * t)
        1 (by norm_num) ?_ ?_ ?_⟩
    · intro i
      fin_cases i <;> simp
    · intro i t _ _
      rw [fR_eval q hq6]
      fin_cases i
      · simpa [trajRs_R] using hd0 t
      · simpa using ((hasDerivAt_id t).const_mul (cq q)).const_add (x (Rv 1))
      · simpa using ((hasDerivAt_id t).const_mul (hq q)).const_add (x (Rv 2))
    · intro t ht0 ht1
      change Formula.sat (domR IR 3) _
      rw [sat_domR]
      simp only [trajRs_R]
      norm_num
      interval_cases q
      · have := hs0 (Or.inl rfl)
        norm_num [cq]
        constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
      · have := hs0 (Or.inr rfl)
        norm_num [cq]
        constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
      · norm_num [cq]
        exact hdx
      · norm_num [cq]
        exact hdx
      · have := hs2 (Or.inl rfl)
        norm_num [cq]
        constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
      · have := hs2 (Or.inr rfl)
        norm_num [cq]
        constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
  · -- completeness: the end state is in the domain (`v ≥ 0`); by its temperature it enables
    -- `CoastCool` (`temp ≥ 20`) or `CoastHeat` (`temp ≤ 20`)
    intro t Φ _ H
    have hend := (sat_domR (Φ t)).mp H.end_dom
    rcases le_total 20 (Φ t (Rv 2)) with hT | hT
    · refine ⟨edgeOf IR 3 pruned q "CoastCool",
        edge_mem_grOf (by rw [nR_eq]; exact hq6) (coastCool_next q hq6), ?_⟩
      simp only [edgeOf, tgt_coastCool]
      exact (sat_guardR2 (Φ t)).mpr ⟨hend.1, hT⟩
    · refine ⟨edgeOf IR 3 pruned q "CoastHeat",
        edge_mem_grOf (by rw [nR_eq]; exact hq6) (coastHeat_next q hq6), ?_⟩
      simp only [edgeOf, tgt_coastHeat]
      exact (sat_guardR3 (Φ t)).mpr ⟨hend.1, hT⟩

end V2Csf21VehicleThermo
end RelCertifier
