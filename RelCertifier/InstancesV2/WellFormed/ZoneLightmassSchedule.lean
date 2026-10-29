/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `zone_lightmass_schedule`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three energy levels and their declared `next` lists), the lowered right guards, and `ε_r = 5`
read from the file.

The right model is the building-automation schedule in the reference zone: the zone temperature
`T` (coordinate 0) relaxes toward the level's set point, `T' = 0.02 (c − T)` (`COMFORT` `c = 21`,
`STANDBY` `c = 19`, `ECONOMY` `c = 16`), every level inside the comfort band `16 ≤ T ≤ 21` (the
band form of 2026-10-28; the domain was `[5, 30]` before); every level's guard is the same band.
* Existence (i), every level: the explicit exponential `c + (T₀ − c) e^{−k t}`
  (`exists_contract_run`; the padding coordinate 1 has field 0 and stays frozen),
  between `T₀` and `c`, both in `[16, 21]`.
* (ii), every level: every level declares every level, and every guard is the evolve domain
  `[16, 21]`, so the end state of any run (which lies in the domain) is in `COMFORT`'s guard.
Z3-free; modelled on `BmsChillerUndercharge.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.zone_lightmass_schedule

namespace RelCertifier
namespace V2ZoneLightmassSchedule

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["T"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := zone_lightmass_schedule_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp002 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp21 : Run.parseRat "21" = some (21 : ℚ) := by
  have h : parseQ "21" = some (⟨21, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp19 : Run.parseRat "19" = some (19 : ℚ) := by
  have h : parseQ "19" = some (⟨19, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp16 : Run.parseRat "16" = some (16 : ℚ) := by
  have h : parseQ "16" = some (⟨16, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp160 : Run.parseRat "16.0" = some (16 : ℚ) := by
  have h : parseQ "16.0" = some (⟨160, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp210 : Run.parseRat "21.0" = some (21 : ℚ) := by
  have h : parseQ "21.0" = some (⟨210, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The right fields, domain and guards, evaluated -/

/-- Relaxation rate of every level: 0.02 /min. -/
noncomputable def kR (_q : ℕ) : ℝ := 1/50

/-- Set points: `COMFORT` 21, `STANDBY` 19, `ECONOMY` 16. -/
noncomputable def cR (q : ℕ) : ℝ := if q = 0 then 21 else if q = 1 then 19 else 16

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, zone_lightmass_schedule_IRv2, vs, Run.dynOf, Run.lowerE, hp002,
      hp21, hp19, hp16, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR, cR]

/-- The padding coordinate 1 (not in `vs`): its right field lowers to 0. -/
theorem fRo_eval (q : ℕ) (hq : q < 3) (i : Fin 2) (hi : i ≠ 0) (x : State (Var 2)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | ⟨1, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, zone_lightmass_schedule_IRv2, vs, Run.dynOf, Run.lowerE, hp002,
        hp21, hp19, hp16, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
        Term.eval]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (16 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 21) := by
  simp only [domR, hostEvolve, mR, zone_lightmass_schedule_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp160, hp210, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (COMFORT 0, STANDBY 1, ECONOMY 2): every level
declares every level. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- Every level's guard, evaluated: `[16, 21]` (`COMFORT`'s is used). -/
theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ (16 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 21) := by
  simp [hostGuard, mR, zone_lightmass_schedule_IRv2, Run.lowerF, Run.lowerE, hp160, hp210, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR zone_lightmass_schedule_IRv2 = 5 := by
  simp [epsR, zone_lightmass_schedule_IRv2, hp50]

/-- **Assumption 1 for `zone_lightmass_schedule`**, every mode, Z3-free. -/
theorem zone_lightmass_schedule_wellFormedR :
    WellFormedR Gr guardR (epsR zone_lightmass_schedule_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hc : 16 ≤ cR q ∧ cR q ≤ 21 := by unfold cR; split_ifs <;> norm_num
  have hk : 0 ≤ kR q := by unfold kR; norm_num
  refine ⟨?_, ?_⟩
  · -- existence: the explicit exponential toward the set point, inside `[16, 21]`
    refine exists_contract_run x 0 (kR q) (cR q) hk (fR0_eval q hq3) ?_ ?_ 5 (by norm_num)
    · intro i hi s
      exact fRo_eval q hq3 i hi s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact ⟨le_trans (le_min hdx.1 hc.1) h1, le_trans h2 (max_le hdx.2 hc.2)⟩
  · -- the end state lies in the domain `[16, 21]`, which is `COMFORT`'s guard
    intro t Φ _ H
    obtain ⟨e16, e21⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW q 0, edge_mem q 0 (by interval_cases q <;> decide),
      (sat_guard0 _).mpr ⟨e16, e21⟩⟩

end V2ZoneLightmassSchedule
end RelCertifier

