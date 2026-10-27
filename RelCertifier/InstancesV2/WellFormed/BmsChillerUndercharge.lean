/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bms_chiller_undercharge`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three cooling levels and their declared `next` lists), the lowered right guards, and `ε_r = 1`
read from the file.

The right model is the pack's thermal strategy: the cell temperature `T` (coordinate 0) relaxes
toward the level's balance, `T' = k (c − T)` (`COAST` `k = 0.02`, `c = 50`; `CHILL_LO`
`k = 0.05`, `c = 30`; `CHILL_HI` `k = 0.05`, `c = 20`), every level inside `0 ≤ T ≤ 60`;
guards `COAST` `[0, 40]`, `CHILL_LO` and `CHILL_HI` `[20, 60]`.
* Existence (i), every level: the explicit exponential `c + (T₀ − c) e^{−k t}`
  (`exists_contract_run`; the padding coordinates 1 and 2 have field 0 and stay frozen),
  between `T₀` and `c`, both in `[0, 60]`.
* (ii), every level: every level declares every level, and `COAST`'s guard `[0, 40]` and
  `CHILL_HI`'s guard `[20, 60]` cover the evolve domain `[0, 60]`, so the end state of any run
  (which lies in the domain) is in `COAST`'s guard (end `≤ 40`) or in `CHILL_HI`'s (end `> 40`).
Z3-free; modelled on `TankDos3to1.lean` and `AccSpoofLimp.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.bms_chiller_undercharge

namespace RelCertifier
namespace V2BmsChillerUndercharge

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["T"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := bms_chiller_undercharge_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp002 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp50 : Run.parseRat "50" = some (50 : ℚ) := by
  have h : parseQ "50" = some (⟨50, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp30 : Run.parseRat "30" = some (30 : ℚ) := by
  have h : parseQ "30" = some (⟨30, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "20" = some (20 : ℚ) := by
  have h : parseQ "20" = some (⟨20, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp600 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- Relaxation rates: `COAST` 0.02, `CHILL_LO` and `CHILL_HI` 0.05. -/
noncomputable def kR (q : ℕ) : ℝ := if q = 0 then 1/50 else 1/20

/-- Balance temperatures: `COAST` 50, `CHILL_LO` 30, `CHILL_HI` 20. -/
noncomputable def cR (q : ℕ) : ℝ := if q = 0 then 50 else if q = 1 then 30 else 20

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, bms_chiller_undercharge_IRv2, vs, Run.dynOf, Run.lowerE, hp002,
      hp005, hp50, hp30, hp20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR, cR]

/-- The padding coordinates 1 and 2 (not in `vs`): their right field lowers to 0. -/
theorem fRo_eval (q : ℕ) (hq : q < 3) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | ⟨1, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, bms_chiller_undercharge_IRv2, vs, Run.dynOf, Run.lowerE, hp002,
        hp005, hp50, hp30, hp20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
        Term.eval]
  | ⟨2, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, bms_chiller_undercharge_IRv2, vs, Run.dynOf, Run.lowerE, hp002,
        hp005, hp50, hp30, hp20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
        Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60) := by
  simp only [domR, hostEvolve, mR, bms_chiller_undercharge_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (COAST 0, CHILL_LO 1, CHILL_HI 2): every level
declares every level. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- `COAST`'s guard, evaluated: `[0, 40]`. -/
theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔ (0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 40) := by
  simp [hostGuard, mR, bms_chiller_undercharge_IRv2, Run.lowerF, Run.lowerE, hp00, hp400, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `CHILL_HI`'s guard, evaluated: `[20, 60]`. -/
theorem sat_guard2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ (20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 60) := by
  simp [hostGuard, mR, bms_chiller_undercharge_IRv2, Run.lowerF, Run.lowerE, hp200, hp600, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR bms_chiller_undercharge_IRv2 = 1 := by
  simp [epsR, bms_chiller_undercharge_IRv2, hp10]

/-- **Assumption 1 for `bms_chiller_undercharge`**, every mode, Z3-free. -/
theorem bms_chiller_undercharge_wellFormedR :
    WellFormedR Gr guardR (epsR bms_chiller_undercharge_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hc : 0 ≤ cR q ∧ cR q ≤ 60 := by unfold cR; split_ifs <;> norm_num
  have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · -- existence: the explicit exponential toward the balance, inside `[0, 60]`
    refine exists_contract_run x 0 (kR q) (cR q) hk (fR0_eval q hq3) ?_ ?_ 1 (by norm_num)
    · intro i hi s
      exact fRo_eval q hq3 i hi s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact ⟨le_trans (le_min hdx.1 hc.1) h1, le_trans h2 (max_le hdx.2 hc.2)⟩
  · -- the end state lies in the domain `[0, 60] = [0, 40] ∪ [20, 60]`
    intro t Φ _ H
    obtain ⟨e0, e60⟩ := (sat_domR _).mp H.end_dom
    by_cases h40 : Φ t (Rv 0) ≤ 40
    · exact ⟨edgeW q 0, edge_mem q 0 (by interval_cases q <;> decide),
        (sat_guard0 _).mpr ⟨e0, h40⟩⟩
    · exact ⟨edgeW q 2, edge_mem q 2 (by interval_cases q <;> decide),
        (sat_guard2 _).mpr ⟨by linarith, e60⟩⟩

end V2BmsChillerUndercharge
end RelCertifier

