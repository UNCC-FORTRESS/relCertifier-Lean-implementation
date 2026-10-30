/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `extruder_pe100_manualstart`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
four screw-speed steps and their declared `next` lists), the lowered right guards, and `ε_r = 1`
read from the file.

The right model is the extruder's automatic start-up sequence: the melt temperature `T`
(coordinate 0) relaxes toward the step's dissipation rise above the die-zone set temperature `p`
(coordinate 1, constant), `T' = k ((p + r) − T)`, `k = 0.5` (time constant 2 min),
`r = 1.33, 3.39, 8.64, 22.0` (`N1` to `N4`), every step inside the domain `130 ≤ T ≤ 300`,
`0 ≤ p ≤ 300`. Guards: `N1` `T < 186`, `N2` `186 ≤ T ≤ 206`, `N3` `206 < T ≤ 226`, `N4`
`T > 226`, each with the domain and the recipe range `180 ≤ p ≤ 220`.
* Existence (i), every step: the explicit exponential `(p₀ + r) + (T₀ − p₀ − r) e^{−k t}` with
  `p` held (`trajRs_sol`), between `T₀` and `p₀ + r`. The recipe range is taken from the GUARD,
  not the domain: `p₀ ∈ [180, 220]` puts `p₀ + r ∈ [181.33, 242] ⊆ [130, 300]`, so the run stays
  inside `130 ≤ T ≤ 300`.
* (ii), every step: `p` is constant along every flow (`p' = 0`), so the end state keeps the start
  guard's recipe range; every step declares every step, and the four guards cover
  `130 ≤ T ≤ 300` (`T < 186`, `[186, 206]`, `(206, 226]`, `T > 226`), so the end state of any run
  is in one of them.
Z3-free; modelled on `ReactorFeedWireless.lean` (dimension 2, no padding coordinate) and on the
guard-range argument of `FuelcellChpDos.lean` (in git history since 2026-10-30, batch 11).
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.extruder_pe100_manualstart

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ExtruderPe100Manualstart

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["T", "p"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := extruder_pe100_manualstart_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_33 : Run.parseRat "1.33" = some ((133:ℚ)/100) := by
  have h : parseQ "1.33" = some (⟨133, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_3_39 : Run.parseRat "3.39" = some ((339:ℚ)/100) := by
  have h : parseQ "3.39" = some (⟨339, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_8_64 : Run.parseRat "8.64" = some ((864:ℚ)/100) := by
  have h : parseQ "8.64" = some (⟨864, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_22_0 : Run.parseRat "22.0" = some (22 : ℚ) := by
  have h : parseQ "22.0" = some (⟨220, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_130 : Run.parseRat "130" = some (130 : ℚ) := by
  have h : parseQ "130" = some (⟨130, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_180 : Run.parseRat "180" = some (180 : ℚ) := by
  have h : parseQ "180" = some (⟨180, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_186 : Run.parseRat "186" = some (186 : ℚ) := by
  have h : parseQ "186" = some (⟨186, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_206 : Run.parseRat "206" = some (206 : ℚ) := by
  have h : parseQ "206" = some (⟨206, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_220 : Run.parseRat "220" = some (220 : ℚ) := by
  have h : parseQ "220" = some (⟨220, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_226 : Run.parseRat "226" = some (226 : ℚ) := by
  have h : parseQ "226" = some (⟨226, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_300 : Run.parseRat "300" = some (300 : ℚ) := by
  have h : parseQ "300" = some (⟨300, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The thermal rate `1 / 2` as written, `0.5`. -/
noncomputable def kR : ℝ := 1 / 2

/-- The step's dissipation rise above the die zone: `N1` 1.33, `N2` 3.39, `N3` 8.64, `N4` 22. -/
noncomputable def rR (q : ℕ) : ℝ :=
  if q = 0 then 133 / 100 else if q = 1 then 339 / 100 else if q = 2 then 864 / 100 else 22

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR * ((x (Rv 1) + rR q) - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, extruder_pe100_manualstart_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
      hp_0_5, hp_1_33, hp_3_39, hp_8_64, hp_22_0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR, rR] <;> ring

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) : Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, extruder_pe100_manualstart_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
      hp_0_5, hp_1_33, hp_3_39, hp_8_64, hp_22_0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (130 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 300 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 300) := by
  simp only [domR, hostEvolve, mR, extruder_pe100_manualstart_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0, hp_130, hp_300, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (N1 0, N2 1, N3 2, N4 3): every step declares every
step. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
   (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  have hlen : q < 4 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 4 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 186 ∧ 130 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 300 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 300 ∧
        180 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 220) := by
  simp [hostGuard, mR, extruder_pe100_manualstart_IRv2, Run.lowerF, Run.lowerE, hp_0, hp_130,
    hp_180, hp_186, hp_206, hp_220, hp_226, hp_300, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔
      (186 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 206 ∧ 130 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 300 ∧ 0 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 300 ∧ 180 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 220) := by
  simp [hostGuard, mR, extruder_pe100_manualstart_IRv2, Run.lowerF, Run.lowerE, hp_0, hp_130,
    hp_180, hp_186, hp_206, hp_220, hp_226, hp_300, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 2)) ν ↔
      (206 < ν (Rv 0) ∧ ν (Rv 0) ≤ 226 ∧ 130 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 300 ∧ 0 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 300 ∧ 180 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 220) := by
  simp [hostGuard, mR, extruder_pe100_manualstart_IRv2, Run.lowerF, Run.lowerE, hp_0, hp_130,
    hp_180, hp_186, hp_206, hp_220, hp_226, hp_300, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard3 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 3)) ν ↔
      (226 < ν (Rv 0) ∧ 130 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 300 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 300 ∧
        180 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 220) := by
  simp [hostGuard, mR, extruder_pe100_manualstart_IRv2, Run.lowerF, Run.lowerE, hp_0, hp_130,
    hp_180, hp_186, hp_206, hp_220, hp_226, hp_300, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- Every right guard carries the recipe range of the die-zone set temperature. -/
theorem guard_p (q : ℕ) (hq : q < 4) (ν : State (Var 2)) (hg : Formula.sat (guardR q) ν) :
    180 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 220 := by
  interval_cases q
  · obtain ⟨_, _, _, _, _, h1, h2⟩ := (sat_guard0 ν).mp hg; exact ⟨h1, h2⟩
  · obtain ⟨_, _, _, _, _, _, h1, h2⟩ := (sat_guard1 ν).mp hg; exact ⟨h1, h2⟩
  · obtain ⟨_, _, _, _, _, _, h1, h2⟩ := (sat_guard2 ν).mp hg; exact ⟨h1, h2⟩
  · obtain ⟨_, _, _, _, _, h1, h2⟩ := (sat_guard3 ν).mp hg; exact ⟨h1, h2⟩

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR extruder_pe100_manualstart_IRv2 = 1 := by
  simp [epsR, extruder_pe100_manualstart_IRv2, hp_1_0]

/-! ## Existence: the explicit run -/

/-- The run of step `q` from `x`: `T` approaches `p₀ + r`, `p` stays. -/
noncomputable def phi (q : ℕ) (x : State (Var 2)) (i : Fin 2) (t : ℝ) : ℝ :=
  if i.val = 0 then (x (Rv 1) + rR q) + (x (Rv 0) - (x (Rv 1) + rR q)) * Real.exp (-(kR * t))
  else x (Rv 1)

theorem phi_zero (q : ℕ) (x : State (Var 2)) :
    phi q x 0 = fun t =>
      (x (Rv 1) + rR q) + (x (Rv 0) - (x (Rv 1) + rR q)) * Real.exp (-(kR * t)) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 2)) : phi q x 1 = fun _ => x (Rv 1) := by
  funext t; simp [phi]

theorem phi_init (q : ℕ) (x : State (Var 2)) (i : Fin 2) : phi q x i 0 = x (Rv i) := by
  match i with
  | 0 => rw [phi_zero]; simp
  | 1 => rw [phi_one]

theorem phi_der (q : ℕ) (hq : q < 4) (x : State (Var 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, trajRs_R, trajRs_R, phi_zero, phi_one]
      exact hasDerivAt_expApproach kR (x (Rv 1) + rR q) (x (Rv 0)) t
  | 1 =>
      rw [fR1_eval q hq, phi_one]
      exact hasDerivAt_const _ _

/-- The run of step `q` from a state with `p₀` in the recipe range (from the guard): it stays
between `T₀` and `p₀ + r ∈ [181.33, 242]`, inside `130 ≤ T ≤ 300`. -/
theorem exists_run (q : ℕ) (hq : q < 4) (x : State (Var 2)) (hd : Formula.sat domR x)
    (hp : 180 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 220)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  obtain ⟨c0, c1⟩ := hp
  have hr : 133 / 100 ≤ rR q ∧ rR q ≤ 22 := by unfold rR; split_ifs <;> norm_num
  have hk : 0 ≤ kR := by unfold kR; norm_num
  refine ⟨_, trajRs_sol x (phi q x) ε hε (phi_init q x) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht _ => ?_)⟩
  obtain ⟨s1, s2⟩ := exp_approach_between kR (x (Rv 1) + rR q) (x (Rv 0)) t hk ht
  rw [sat_domR, trajRs_R, trajRs_R, phi_zero, phi_one]
  exact ⟨le_trans (le_min a0 (by linarith)) s1, le_trans s2 (max_le a1 (by linarith)), b0, b1⟩

/-- **Assumption 1 for `extruder_pe100_manualstart`**, every mode, Z3-free. -/
theorem extruder_pe100_manualstart_wellFormedR :
    WellFormedR Gr guardR (epsR extruder_pe100_manualstart_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  have hp := guard_p q hq4 x hg
  refine ⟨exists_run q hq4 x hd hp 1 (by norm_num), ?_⟩
  -- `p` is held, so the end state keeps the guard's recipe range; the four guards cover
  -- `130 ≤ T ≤ 300`; every step declares every step
  intro t Φ _ H
  obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
  have hc := H.const (rightBlock_mem' (fR q) (Term.const 1) 1) (fun s _ => by
    rw [eval_unit_mul, fR1_eval q hq4])
  have f0 : 180 ≤ Φ t (Rv 1) := by rw [hc]; exact hp.1
  have f1 : Φ t (Rv 1) ≤ 220 := by rw [hc]; exact hp.2
  by_cases h186 : Φ t (Rv 0) < 186
  · exact ⟨edgeW q 0, edge_mem q 0 (by interval_cases q <;> decide),
      (sat_guard0 _).mpr ⟨h186, e0, e1, e2, e3, f0, f1⟩⟩
  · by_cases h206 : Φ t (Rv 0) ≤ 206
    · exact ⟨edgeW q 1, edge_mem q 1 (by interval_cases q <;> decide),
        (sat_guard1 _).mpr ⟨by linarith, h206, e0, e1, e2, e3, f0, f1⟩⟩
    · by_cases h226 : Φ t (Rv 0) ≤ 226
      · exact ⟨edgeW q 2, edge_mem q 2 (by interval_cases q <;> decide),
          (sat_guard2 _).mpr ⟨by linarith, h226, e0, e1, e2, e3, f0, f1⟩⟩
      · exact ⟨edgeW q 3, edge_mem q 3 (by interval_cases q <;> decide),
          (sat_guard3 _).mpr ⟨by linarith, e0, e1, e2, e3, f0, f1⟩⟩

end V2ExtruderPe100Manualstart
end RelCertifier
