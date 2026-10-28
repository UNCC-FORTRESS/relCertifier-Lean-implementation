/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `csf21_vehicle_bus`: Assumption 1 of the right model (style (b), exit into `Coast`)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the genuine car of the
internal-bus case study: twelve modes `xtA` / `xtT` (action `x ∈ {Acc, Coast, Brk}`, thermostat
`t ∈ {Cool, Heat}`, message type `A` / `T`), in file order `AccCoolA, AccCoolT, AccHeatA,
AccHeatT, CoastCoolA, CoastCoolT, CoastHeatA, CoastHeatT, BrkCoolA, BrkCoolT, BrkHeatA,
BrkHeatT`, with `d' = −v`, `v' = c_q ∈ {1, 0, −1}`, `temp' = h_q ∈ {−1, 1}` and the shared evolve
domain `0 ≤ v ≤ 40`. The `Acc` guards contain `0 ≤ v ≤ 39`, the `Brk` guards `v ≥ 1`, the
`Coast` guards `0 ≤ v ≤ 1` (the low-speed stand-in for braking to rest; 2026-10-28).
Existence: the explicit polynomial run `d − v t − c t²/2`, `v + c t`, `temp + h t`
(`trajRs_sol`), inside the domain for one period by the guard's speed bounds. Completeness: the
end state is in the domain, so `v ≥ 0`; `v ≤ 1` enables `CoastCoolA` (resp. `CoastHeatA`), whose
guard is `0 ≤ v ≤ 1`, and `v ≥ 1` enables `BrkCoolA` (resp. `BrkHeatA`), whose guard is
`v ≥ 1`; both are declared successors of every `Cool` (resp. `Heat`) mode, so every run's end
state enables a declared successor. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.csf21_vehicle_bus

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Csf21VehicleBus

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.csf21_vehicle_bus_IRv2

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
  simp [epsR, IR, Parse.csf21_vehicle_bus_IRv2, hp10]

theorem nR_eq : nR IR = 12 := rfl

/-- The acceleration of right mode `q`: `1` (`Acc`, `q < 4`), `0` (`Coast`, `4 ≤ q < 8`),
`−1` (`Brk`, `8 ≤ q`). -/
noncomputable def cq (q : ℕ) : ℝ := if q < 4 then 1 else if q < 8 then 0 else -1

/-- The temperature rate of right mode `q`: `−1` (`Cool`, `q % 4 < 2`), `1` (`Heat`). -/
noncomputable def hq (q : ℕ) : ℝ := if q % 4 < 2 then -1 else 1

/-- The lowered right fields: `d' = −v`, `v' = c_q`, `temp' = h_q`. -/
theorem fR_eval (q : ℕ) (hq12 : q < 12) (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 q i) s =
      if i.val = 0 then -s (Rv 1) else if i.val = 1 then cq q else hq q := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.csf21_vehicle_bus_IRv2, Run.dynOf, Run.lowerE, hp00,
      hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cq, hq]

theorem sat_domR (s : State (Var 3)) :
    Formula.sat (domR IR 3) s ↔ 0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 40 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.csf21_vehicle_bus_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp400, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

/-- The speed bounds of the guards: `v ≤ 39` in the `Acc` modes, `v ≥ 1` in the `Brk` modes. -/
theorem sat_guardR_speed (q : ℕ) (hq12 : q < 12) (s : State (Var 3))
    (hg : Formula.sat (guardR IR 3 q) s) :
    (q < 4 → s (Rv 1) ≤ 39) ∧ (8 ≤ q → 1 ≤ s (Rv 1)) := by
  interval_cases q <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.csf21_vehicle_bus_IRv2, Run.lowerF, Run.lowerE,
      hp00, hp10, hp20, hp40, hp200, hp390, hp400, Run.resolveVar, List.findIdx?_cons,
      IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv] at hg ⊢ <;>
    simp_all

/-- The guard of `CoastCoolA` (`q = 4`) and of `CoastHeatA` (`q = 6`) is `0 ≤ v ≤ 1`. -/
theorem sat_guardR_coastA (q : ℕ) (hq : q = 4 ∨ q = 6) (s : State (Var 3)) :
    Formula.sat (guardR IR 3 q) s ↔ 0 ≤ s (Rv 1) ∧ s (Rv 1) ≤ 1 := by
  rcases hq with rfl | rfl <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.csf21_vehicle_bus_IRv2, Run.lowerF, Run.lowerE,
      hp00, hp10, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, AOp.interp, Rv]

/-- The guard of `BrkCoolA` (`q = 8`) and of `BrkHeatA` (`q = 10`) is `v ≥ 1`. -/
theorem sat_guardR_brkA (q : ℕ) (hq : q = 8 ∨ q = 10) (s : State (Var 3)) :
    Formula.sat (guardR IR 3 q) s ↔ 1 ≤ s (Rv 1) := by
  rcases hq with rfl | rfl <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.csf21_vehicle_bus_IRv2, Run.lowerF, Run.lowerE,
      hp10, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, AOp.interp, Rv]

/-- The low-speed exit successor of right mode `q`: `CoastCoolA` for the `Cool` modes,
`CoastHeatA` for the `Heat` modes. -/
def succNm (q : ℕ) : String := if q % 4 < 2 then "CoastCoolA" else "CoastHeatA"

/-- The braking exit successor of right mode `q`: `BrkCoolA` for the `Cool` modes, `BrkHeatA`
for the `Heat` modes. -/
def brkNm (q : ℕ) : String := if q % 4 < 2 then "BrkCoolA" else "BrkHeatA"

theorem succ_next (q : ℕ) (hq12 : q < 12) : succNm q ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem brk_next (q : ℕ) (hq12 : q < 12) : brkNm q ∈ (mRof IR q).next := by
  interval_cases q <;> decide

theorem tgt_succ (q : ℕ) (hq12 : q < 12) : tgtIdx IR (succNm q) = 4 ∨ tgtIdx IR (succNm q) = 6 := by
  interval_cases q <;> decide

theorem tgt_brk (q : ℕ) (hq12 : q < 12) : tgtIdx IR (brkNm q) = 8 ∨ tgtIdx IR (brkNm q) = 10 := by
  interval_cases q <;> decide

/-- **Assumption 1 for `csf21_vehicle_bus`**, every mode, over the bridge's automaton. -/
theorem csf21_vehicle_bus_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq' m hm x hg hd _
  obtain ⟨hq12, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq12
  have hdx := (sat_domR x).mp hd
  obtain ⟨hs0, hs2⟩ := sat_guardR_speed q hq12 x hg
  refine ⟨?_, ?_⟩
  · -- existence: the explicit polynomial run of one period
    have hd0 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => x (Rv 0) - x (Rv 1) * u - cq q * u ^ 2 / 2)
        (-(x (Rv 1) + cq q * t)) t := fun t => by
      have h1 : HasDerivAt (fun u : ℝ => x (Rv 0) - x (Rv 1) * u) (-x (Rv 1)) t := by
        simpa using ((hasDerivAt_id t).const_mul (x (Rv 1))).const_sub (x (Rv 0))
      have h2 : HasDerivAt (fun u : ℝ => cq q * u ^ 2 / 2) (cq q * (2 * t ^ 1) / 2) t :=
        ((hasDerivAt_pow 2 t).const_mul (cq q)).div_const 2
      exact (h1.sub h2).congr_deriv (by ring)
    refine ⟨_, trajRs_sol x (fun i t => if i.val = 0 then x (Rv 0) - x (Rv 1) * t - cq q * t ^ 2 / 2
        else if i.val = 1 then x (Rv 1) + cq q * t else x (Rv 2) + hq q * t) 1 (by norm_num)
        ?_ ?_ ?_⟩
    · intro i
      fin_cases i <;> simp
    · intro i t _ _
      rw [fR_eval q hq12]
      fin_cases i
      · simpa [trajRs_R] using hd0 t
      · simpa using ((hasDerivAt_id t).const_mul (cq q)).const_add (x (Rv 1))
      · simpa using ((hasDerivAt_id t).const_mul (hq q)).const_add (x (Rv 2))
    · intro t ht0 ht1
      change Formula.sat (domR IR 3) _
      rw [sat_domR]
      simp only [trajRs_R]
      norm_num
      by_cases hA : q < 4
      · have := hs0 hA
        simp only [cq, if_pos hA]
        constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
      · by_cases hC : q < 8
        · simp only [cq, if_neg hA, if_pos hC]
          norm_num
          exact hdx
        · have := hs2 (by omega)
          simp only [cq, if_neg hA, if_neg hC]
          constructor <;> nlinarith [hdx.1, hdx.2, ht0, ht1, this]
  · -- completeness: the end state is in the domain (`v ≥ 0`); `v ≤ 1` enables the `Coast*A`
    -- successor, `v ≥ 1` the `Brk*A` successor
    intro t Φ _ H
    have hend := (sat_domR _).mp H.end_dom
    rcases le_total (Φ t (Rv 1)) 1 with hv | hv
    · refine ⟨edgeOf IR 3 pruned q (succNm q),
        edge_mem_grOf (by rw [nR_eq]; exact hq12) (succ_next q hq12), ?_⟩
      simp only [edgeOf]
      rw [sat_guardR_coastA _ (tgt_succ q hq12)]
      exact ⟨hend.1, hv⟩
    · refine ⟨edgeOf IR 3 pruned q (brkNm q),
        edge_mem_grOf (by rw [nR_eq]; exact hq12) (brk_next q hq12), ?_⟩
      simp only [edgeOf]
      rw [sat_guardR_brkA _ (tgt_brk q hq12)]
      exact hv

end V2Csf21VehicleBus
end RelCertifier
