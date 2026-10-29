/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `canal_gate_notches`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
four gate notches and their declared `next` lists), the lowered right guards, and `ε_r = 10`
read from the file.

The right model is the notched gate schedule: the pool level `h` (coordinate 0) relaxes toward
the notch's level, `h' = 0.006 (c − h)` (`N100` `c = 1`, `N75` `c = 0.75`, `N50` `c = 0.5`,
`N25` `c = 0.25`), every notch inside `0 ≤ h ≤ 1.2`; guards `N100` `[0, 0.6)`, `N75` and `N50`
`[0, 1.2]`, `N25` `[0.7, 1.2]`.
* Existence (i), every notch: the explicit exponential `c + (h₀ − c) e^{−0.006 t}`
  (`exists_contract_run`; the padding coordinates 1 and 2 have field 0 and stay frozen),
  between `h₀` and `c`, both in `[0, 1.2]`.
* (ii), every notch: every notch declares every notch, and `N50`'s guard is the whole evolve
  domain `[0, 1.2]`, so the end state of any run (which lies in the domain) is in `N50`'s guard.
Z3-free; modelled on `TankDos3to1.lean` and `AccSpoofLimp.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.canal_gate_notches

namespace RelCertifier
namespace V2CanalGateNotches

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["h"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := canal_gate_notches_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp0006 : Run.parseRat "0.006" = some ((3:ℚ)/500) := by
  have h : parseQ "0.006" = some (⟨6, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp025 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp12 : Run.parseRat "1.2" = some ((6:ℚ)/5) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The right fields, domain and guards, evaluated -/

/-- Notch levels: `N100` 1, `N75` 0.75, `N50` 0.5, `N25` 0.25. -/
noncomputable def cR (q : ℕ) : ℝ :=
  if q = 0 then 1 else if q = 1 then 3/4 else if q = 2 then 1/2 else 1/4

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = 3/500 * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, canal_gate_notches_IRv2, vs, Run.dynOf, Run.lowerE, hp0006, hp1,
      hp075, hp05, hp025, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, cR]

/-- The padding coordinates 1 and 2 (not in `vs`): their right field lowers to 0. -/
theorem fRo_eval (q : ℕ) (hq : q < 4) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | ⟨1, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, canal_gate_notches_IRv2, vs, Run.dynOf, Run.lowerE, hp0006, hp1,
        hp075, hp05, hp025, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
        Term.eval]
  | ⟨2, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, canal_gate_notches_IRv2, vs, Run.dynOf, Run.lowerE, hp0006, hp1,
        hp075, hp05, hp025, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
        Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 6/5) := by
  simp only [domR, hostEvolve, mR, canal_gate_notches_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp12, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (N100 0, N75 1, N50 2, N25 3): every notch declares
every notch. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
   (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- `N50`'s guard, evaluated: the whole domain `[0, 1.2]`. -/
theorem sat_guard2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ (0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 6/5) := by
  simp [hostGuard, mR, canal_gate_notches_IRv2, Run.lowerF, Run.lowerE, hp00, hp12, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR canal_gate_notches_IRv2 = 10 := by
  simp [epsR, canal_gate_notches_IRv2, hp100]

/-- **Assumption 1 for `canal_gate_notches`**, every mode, Z3-free. -/
theorem canal_gate_notches_wellFormedR :
    WellFormedR Gr guardR (epsR canal_gate_notches_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hc : 0 ≤ cR q ∧ cR q ≤ 6/5 := by unfold cR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · -- existence: the explicit exponential toward the notch level, inside `[0, 1.2]`
    refine exists_contract_run x 0 (3/500) (cR q) (by norm_num) (fR0_eval q hq4) ?_ ?_ 10
      (by norm_num)
    · intro i hi s
      exact fRo_eval q hq4 i hi s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact ⟨le_trans (le_min hdx.1 hc.1) h1, le_trans h2 (max_le hdx.2 hc.2)⟩
  · -- the end state lies in the domain, which is `N50`'s guard
    intro t Φ _ H
    exact ⟨edgeW q 2, edge_mem q 2 (by interval_cases q <;> decide),
      (sat_guard2 _).mpr ((sat_domR _).mp H.end_dom)⟩

end V2CanalGateNotches
end RelCertifier

