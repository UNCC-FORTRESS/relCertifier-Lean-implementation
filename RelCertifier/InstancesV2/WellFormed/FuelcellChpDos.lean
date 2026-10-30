/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `fuelcell_chp_dos`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three current levels and their declared `next` lists), the lowered right guards, and `ε_r = 10`
read from the file.

The right model is the stack maker's operating protocol: the stack temperature `T`
(coordinate 0) relaxes toward the level's rise above the heating return `Tin` (coordinate 1,
constant), `T' = k ((Tin + r) − T)`, `k = 0.00833333` (time constant 120 s), `r = 12, 17, 22`
(`LOW`, `MED`, `HIGH`), every level inside the physical domain `0 ≤ T ≤ 100`, `0 ≤ Tin ≤ 100`;
coordinate 2 is the padding of the mode-choice records (field 0, frozen). Guards: `LOW`
`T < 60`, `MED` `50 < T < 80`, `HIGH` `T > 70`, each with the design range `40 ≤ Tin ≤ 56` and
the domain.
* Existence (i), every level: the explicit exponential `(Tin₀ + r) + (T₀ − Tin₀ − r) e^{−k t}`
  with `Tin` held (`trajRs_sol`), between `T₀` and `Tin₀ + r`. The design range is taken from the
  GUARD, not the domain: `Tin₀ ∈ [40, 56]` puts `Tin₀ + r ∈ [52, 78] ⊆ [0, 100]`, so the run stays
  inside `0 ≤ T ≤ 100` (in particular `T ≥ 0` under `LOW` and `T ≤ 100` under `HIGH`).
* (ii), every level: `Tin` is constant along every flow (`Tin' = 0`), so the end state keeps the
  start guard's `Tin ∈ [40, 56]`; every level declares every level, and the three guards cover
  `0 ≤ T ≤ 100` (`T < 60`, `[60, 80)`, `T ≥ 80`), so the end state of any run is in one of them.
Z3-free; modelled on `CompressorStationRecycle.lean` and `BmsChillerUndercharge.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.fuelcell_chp_dos

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2FuelcellChpDos

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["T", "Tin"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := fuelcell_chp_dos_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_00833333 : Run.parseRat "0.00833333" = some ((833333:ℚ)/100000000) := by
  have h : parseQ "0.00833333" = some (⟨833333, 100000000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_100 : Run.parseRat "100" = some (100 : ℚ) := by
  have h : parseQ "100" = some (⟨100, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_100_0 : Run.parseRat "100.0" = some (100 : ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_12 : Run.parseRat "12" = some (12 : ℚ) := by
  have h : parseQ "12" = some (⟨12, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_17 : Run.parseRat "17" = some (17 : ℚ) := by
  have h : parseQ "17" = some (⟨17, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_22 : Run.parseRat "22" = some (22 : ℚ) := by
  have h : parseQ "22" = some (⟨22, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_40_0 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_40 : Run.parseRat "40" = some (40 : ℚ) := by
  have h : parseQ "40" = some (⟨40, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_50_0 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_56 : Run.parseRat "56" = some (56 : ℚ) := by
  have h : parseQ "56" = some (⟨56, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_60_0 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_70_0 : Run.parseRat "70.0" = some (70 : ℚ) := by
  have h : parseQ "70.0" = some (⟨700, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_80_0 : Run.parseRat "80.0" = some (80 : ℚ) := by
  have h : parseQ "80.0" = some (⟨800, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_10_0 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The thermal rate `1 / 120` as written, `0.00833333`. -/
noncomputable def kR : ℝ := 833333 / 100000000

/-- The level's rise above the return: `LOW` 12, `MED` 17, `HIGH` 22. -/
noncomputable def rR (q : ℕ) : ℝ := if q = 0 then 12 else if q = 1 then 17 else 22

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR * ((x (Rv 1) + rR q) - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, fuelcell_chp_dos_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0, hp_100, hp_0_00833333, hp_100_0, hp_12, hp_17, hp_22, hp_40_0, hp_40, hp_50_0, hp_56, hp_60_0, hp_70_0, hp_80_0, hp_10_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, kR, rR] <;> ring

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) : Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, fuelcell_chp_dos_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0, hp_100, hp_0_00833333, hp_100_0, hp_12, hp_17, hp_22, hp_40_0, hp_40, hp_50_0, hp_56, hp_60_0, hp_70_0, hp_80_0, hp_10_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

/-- The padding coordinate 2 (not in `vs`): its right field lowers to 0. -/
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) : Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, fuelcell_chp_dos_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0, hp_100, hp_0_00833333, hp_100_0, hp_12, hp_17, hp_22, hp_40_0, hp_40, hp_50_0, hp_56, hp_60_0, hp_70_0, hp_80_0, hp_10_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 100 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 100) := by
  simp only [domR, hostEvolve, mR, fuelcell_chp_dos_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_0, hp_100, hp_0_00833333, hp_100_0, hp_12, hp_17, hp_22, hp_40_0, hp_40, hp_50_0, hp_56, hp_60_0, hp_70_0, hp_80_0, hp_10_0, Run.resolveVar, List.findIdx?_cons,
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

theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 60 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 56 ∧
        0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 100 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 100) := by
  simp [hostGuard, mR, fuelcell_chp_dos_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0, hp_100, hp_0_00833333, hp_100_0, hp_12, hp_17, hp_22, hp_40_0, hp_40, hp_50_0, hp_56, hp_60_0, hp_70_0, hp_80_0, hp_10_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (50 < ν (Rv 0) ∧ ν (Rv 0) < 80 ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 56 ∧
        0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 100 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 100) := by
  simp [hostGuard, mR, fuelcell_chp_dos_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0, hp_100, hp_0_00833333, hp_100_0, hp_12, hp_17, hp_22, hp_40_0, hp_40, hp_50_0, hp_56, hp_60_0, hp_70_0, hp_80_0, hp_10_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      (70 < ν (Rv 0) ∧ 40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 56 ∧
        0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 100 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 100) := by
  simp [hostGuard, mR, fuelcell_chp_dos_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0, hp_100, hp_0_00833333, hp_100_0, hp_12, hp_17, hp_22, hp_40_0, hp_40, hp_50_0, hp_56, hp_60_0, hp_70_0, hp_80_0, hp_10_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- Every right guard carries the design range of the return temperature. -/
theorem guard_Tin (q : ℕ) (hq : q < 3) (ν : State (Var 3)) (hg : Formula.sat (guardR q) ν) :
    40 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 56 := by
  interval_cases q
  · obtain ⟨_, h1, h2, _⟩ := (sat_guard0 ν).mp hg; exact ⟨h1, h2⟩
  · obtain ⟨_, _, h1, h2, _⟩ := (sat_guard1 ν).mp hg; exact ⟨h1, h2⟩
  · obtain ⟨_, h1, h2, _⟩ := (sat_guard2 ν).mp hg; exact ⟨h1, h2⟩

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR fuelcell_chp_dos_IRv2 = 10 := by
  simp [epsR, fuelcell_chp_dos_IRv2, hp_10_0]

/-! ## Existence: the explicit run -/

/-- The run of level `q` from `x`: `T` approaches `Tin₀ + r`, `Tin` and the padding stay. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then (x (Rv 1) + rR q) + (x (Rv 0) - (x (Rv 1) + rR q)) * Real.exp (-(kR * t))
  else if i.val = 1 then x (Rv 1)
  else x (Rv 2)

theorem phi_zero (q : ℕ) (x : State (Var 3)) :
    phi q x 0 = fun t =>
      (x (Rv 1) + rR q) + (x (Rv 0) - (x (Rv 1) + rR q)) * Real.exp (-(kR * t)) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 3)) : phi q x 1 = fun _ => x (Rv 1) := by
  funext t; simp [phi]

theorem phi_two (q : ℕ) (x : State (Var 3)) : phi q x 2 = fun _ => x (Rv 2) := by
  funext t; simp [phi]

theorem phi_init (q : ℕ) (x : State (Var 3)) (i : Fin 3) : phi q x i 0 = x (Rv i) := by
  match i with
  | 0 => rw [phi_zero]; simp
  | 1 => rw [phi_one]
  | 2 => rw [phi_two]

theorem phi_der (q : ℕ) (hq : q < 3) (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, trajRs_R, trajRs_R, phi_zero, phi_one]
      exact hasDerivAt_expApproach kR (x (Rv 1) + rR q) (x (Rv 0)) t
  | 1 =>
      rw [fR1_eval q hq, phi_one]
      exact hasDerivAt_const _ _
  | 2 =>
      rw [fR2_eval q hq, phi_two]
      exact hasDerivAt_const _ _

/-- The run of level `q` from a state with `Tin₀` in the design range (from the guard): it
stays between `T₀` and `Tin₀ + r ∈ [52, 78]`, inside `0 ≤ T ≤ 100`. -/
theorem exists_run (q : ℕ) (hq : q < 3) (x : State (Var 3)) (hd : Formula.sat domR x)
    (hTin : 40 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 56)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  obtain ⟨c0, c1⟩ := hTin
  have hr : 12 ≤ rR q ∧ rR q ≤ 22 := by unfold rR; split_ifs <;> norm_num
  have hk : 0 ≤ kR := by unfold kR; norm_num
  refine ⟨_, trajRs_sol x (phi q x) ε hε (phi_init q x) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht _ => ?_)⟩
  obtain ⟨s1, s2⟩ := exp_approach_between kR (x (Rv 1) + rR q) (x (Rv 0)) t hk ht
  rw [sat_domR, trajRs_R, trajRs_R, phi_zero, phi_one]
  exact ⟨le_trans (le_min a0 (by linarith)) s1, le_trans s2 (max_le a1 (by linarith)), b0, b1⟩

/-- **Assumption 1 for `fuelcell_chp_dos`**, every mode, Z3-free. -/
theorem fuelcell_chp_dos_wellFormedR :
    WellFormedR Gr guardR (epsR fuelcell_chp_dos_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  have hTin := guard_Tin q hq3 x hg
  refine ⟨exists_run q hq3 x hd hTin 10 (by norm_num), ?_⟩
  -- `Tin` is held, so the end state keeps the guard's design range; the three guards cover
  -- `0 ≤ T ≤ 100`; every level declares every level
  intro t Φ _ H
  obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
  have hc := H.const (rightBlock_mem' (fR q) (Term.const 1) 1) (fun s _ => by
    rw [eval_unit_mul, fR1_eval q hq3])
  have f0 : 40 ≤ Φ t (Rv 1) := by rw [hc]; exact hTin.1
  have f1 : Φ t (Rv 1) ≤ 56 := by rw [hc]; exact hTin.2
  by_cases h60 : Φ t (Rv 0) < 60
  · exact ⟨edgeW q 0, edge_mem q 0 (by interval_cases q <;> decide),
      (sat_guard0 _).mpr ⟨h60, f0, f1, e0, e1, e2, e3⟩⟩
  · by_cases h80 : Φ t (Rv 0) < 80
    · exact ⟨edgeW q 1, edge_mem q 1 (by interval_cases q <;> decide),
        (sat_guard1 _).mpr ⟨by linarith, h80, f0, f1, e0, e1, e2, e3⟩⟩
    · exact ⟨edgeW q 2, edge_mem q 2 (by interval_cases q <;> decide),
        (sat_guard2 _).mpr ⟨by linarith, f0, f1, e0, e1, e2, e3⟩⟩

end V2FuelcellChpDos
end RelCertifier
