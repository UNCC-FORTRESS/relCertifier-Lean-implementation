/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `compressor_station_recycle`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three unit levels and their declared `next` lists), the lowered right guards, and `ε_r = 1`
read from the file.

The right model is the station's control philosophy: suction pressure `ps` (coordinate 0) and
discharge pressure `pd` (coordinate 1) relax independently toward the level's equilibrium,
`ps' = 0.05 (62 − ps) − 0.2 n = 0.05 (cS − ps)`, `pd' = 0.05 (40 − pd) + 0.45 n = 0.05 (cP − pd)`
(`LOW` `n = 1`: `(58, 49)`, `MED` `n = 2`: `(54, 58)`, `HIGH` `n = 3`: `(50, 67)`), every level
inside the box `45 ≤ ps ≤ 62`, `40 ≤ pd ≤ 70`; coordinate 2 is the padding of the mode-choice
records (field 0, frozen). Guards: `LOW` `pd ≥ 60`, `MED` the box, `HIGH` `pd ≤ 66`.
* Existence (i), every level: the explicit exponentials on both axes (`trajRs_sol`), each
  between its start and its equilibrium, both inside the box.
* (ii), every level: every level declares every level, and `MED`'s guard is the evolve domain,
  so the end state of any run (which lies in the domain) is in `MED`'s guard.
Z3-free; modelled on `BmsChillerUndercharge.lean` and `GantrySpeedZones.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.compressor_station_recycle

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2CompressorStationRecycle

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["ps", "pd"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := compressor_station_recycle_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_62_0 : Run.parseRat "62.0" = some (62 : ℚ) := by
  have h : parseQ "62.0" = some (⟨620, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_2000 : Run.parseRat "0.2000" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2000" = some (⟨2000, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_40_0 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_4500 : Run.parseRat "0.4500" = some ((9:ℚ)/20) := by
  have h : parseQ "0.4500" = some (⟨4500, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_4000 : Run.parseRat "0.4000" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4000" = some (⟨4000, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_9000 : Run.parseRat "0.9000" = some ((9:ℚ)/10) := by
  have h : parseQ "0.9000" = some (⟨9000, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_6000 : Run.parseRat "0.6000" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6000" = some (⟨6000, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_3500 : Run.parseRat "1.3500" = some ((27:ℚ)/20) := by
  have h : parseQ "1.3500" = some (⟨13500, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_60_0 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_45_0 : Run.parseRat "45.0" = some (45 : ℚ) := by
  have h : parseQ "45.0" = some (⟨450, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_70_0 : Run.parseRat "70.0" = some (70 : ℚ) := by
  have h : parseQ "70.0" = some (⟨700, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_66_0 : Run.parseRat "66.0" = some (66 : ℚ) := by
  have h : parseQ "66.0" = some (⟨660, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- Suction equilibria: `LOW` 58, `MED` 54, `HIGH` 50. -/
noncomputable def cS (q : ℕ) : ℝ := if q = 0 then 58 else if q = 1 then 54 else 50

/-- Discharge equilibria: `LOW` 49, `MED` 58, `HIGH` 67. -/
noncomputable def cP (q : ℕ) : ℝ := if q = 0 then 49 else if q = 1 then 58 else 67

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = 1/20 * (cS q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, compressor_station_recycle_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_05, hp_62_0, hp_0_2000, hp_40_0, hp_0_4500, hp_0_4000, hp_0_9000, hp_0_6000, hp_1_3500, hp_60_0, hp_45_0, hp_70_0, hp_66_0, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cS] <;> ring

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 1/20 * (cP q - x (Rv 1)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, compressor_station_recycle_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_05, hp_62_0, hp_0_2000, hp_40_0, hp_0_4500, hp_0_4000, hp_0_9000, hp_0_6000, hp_1_3500, hp_60_0, hp_45_0, hp_70_0, hp_66_0, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cP] <;> ring

/-- The padding coordinate 2 (not in `vs`): its right field lowers to 0. -/
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) : Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, compressor_station_recycle_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_05, hp_62_0, hp_0_2000, hp_40_0, hp_0_4500, hp_0_4000, hp_0_9000, hp_0_6000, hp_1_3500, hp_60_0, hp_45_0, hp_70_0, hp_66_0, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (45 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 62 ∧ 40 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 70) := by
  simp only [domR, hostEvolve, mR, compressor_station_recycle_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_05, hp_62_0, hp_0_2000, hp_40_0, hp_0_4500, hp_0_4000, hp_0_9000, hp_0_6000, hp_1_3500, hp_60_0, hp_45_0, hp_70_0, hp_66_0, hp_1_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (LOW 0, MED 1, HIGH 2): every level declares every
level. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  have hlen : q < 3 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 3 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

/-- `MED`'s guard, evaluated: the box (the evolve domain). -/
theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (45 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 62 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 70) := by
  simp [hostGuard, mR, compressor_station_recycle_IRv2, Run.lowerF, Run.lowerE, hp_0_05, hp_62_0, hp_0_2000, hp_40_0, hp_0_4500, hp_0_4000, hp_0_9000, hp_0_6000, hp_1_3500, hp_60_0, hp_45_0, hp_70_0, hp_66_0, hp_1_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR compressor_station_recycle_IRv2 = 1 := by
  simp [epsR, compressor_station_recycle_IRv2, hp_1_0]

/-! ## Existence: the explicit run -/

/-- The run of level `q` from `x`: both pressures approach their equilibria, the padding
coordinate stays. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then cS q + (x (Rv 0) - cS q) * Real.exp (-(1/20 * t))
  else if i.val = 1 then cP q + (x (Rv 1) - cP q) * Real.exp (-(1/20 * t))
  else x (Rv 2)

theorem phi_zero (q : ℕ) (x : State (Var 3)) :
    phi q x 0 = fun t => cS q + (x (Rv 0) - cS q) * Real.exp (-(1/20 * t)) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 3)) :
    phi q x 1 = fun t => cP q + (x (Rv 1) - cP q) * Real.exp (-(1/20 * t)) := by
  funext t; simp [phi]

theorem phi_two (q : ℕ) (x : State (Var 3)) : phi q x 2 = fun _ => x (Rv 2) := by
  funext t; simp [phi]

theorem phi_init (q : ℕ) (x : State (Var 3)) (i : Fin 3) : phi q x i 0 = x (Rv i) := by
  match i with
  | 0 => rw [phi_zero]; simp
  | 1 => rw [phi_one]; simp
  | 2 => rw [phi_two]

theorem phi_der (q : ℕ) (hq : q < 3) (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, trajRs_R, phi_zero]
      exact hasDerivAt_expApproach (1/20) (cS q) (x (Rv 0)) t
  | 1 =>
      rw [fR1_eval q hq, trajRs_R, phi_one]
      exact hasDerivAt_expApproach (1/20) (cP q) (x (Rv 1)) t
  | 2 =>
      rw [fR2_eval q hq, phi_two]
      exact hasDerivAt_const _ _

theorem exists_run (q : ℕ) (hq : q < 3) (x : State (Var 3)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  have hS : 45 ≤ cS q ∧ cS q ≤ 62 := by unfold cS; split_ifs <;> norm_num
  have hP : 40 ≤ cP q ∧ cP q ≤ 70 := by unfold cP; split_ifs <;> norm_num
  refine ⟨_, trajRs_sol x (phi q x) ε hε (phi_init q x) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht _ => ?_)⟩
  obtain ⟨s1, s2⟩ := exp_approach_between (1/20) (cS q) (x (Rv 0)) t (by norm_num) ht
  obtain ⟨p1, p2⟩ := exp_approach_between (1/20) (cP q) (x (Rv 1)) t (by norm_num) ht
  rw [sat_domR, trajRs_R, trajRs_R, phi_zero, phi_one]
  exact ⟨le_trans (le_min a0 hS.1) s1, le_trans s2 (max_le a1 hS.2),
    le_trans (le_min b0 hP.1) p1, le_trans p2 (max_le b1 hP.2)⟩

/-- **Assumption 1 for `compressor_station_recycle`**, every mode, Z3-free. -/
theorem compressor_station_recycle_wellFormedR :
    WellFormedR Gr guardR (epsR compressor_station_recycle_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq3 x hd 1 (by norm_num), ?_⟩
  -- the end state lies in the evolve domain, which is `MED`'s guard
  intro t Φ _ H
  obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
  exact ⟨edgeW q 1, edge_mem q 1 (by interval_cases q <;> decide),
    (sat_guard1 _).mpr ⟨e0, e1, e2, e3⟩⟩

end V2CompressorStationRecycle
end RelCertifier
