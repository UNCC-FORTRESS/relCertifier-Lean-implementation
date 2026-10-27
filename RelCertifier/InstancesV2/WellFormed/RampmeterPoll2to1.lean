/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rampmeter_poll_2to1`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
six metering rates and their declared `next` lists), the lowered right guards, and `ε_r = 20`
read from the file.

The right model is the polled ramp meter: the demand `kd` (coordinate 0, constant), the
upstream density `k1` (coordinate 1) and the downstream density `k` (coordinate 2), inside
`10 ≤ kd, k1 ≤ 27.5`, `14 ≤ k ≤ 42.5`. Rate `q` (`R1800`, `R1440`, `R1200`, `R960`, `R720`,
`R480`) admits the ramp level `r_q = 15, 12, 10, 8, 6, 4`: `kd' = 0`, `k1' = 0.02 (kd − k1)`,
`k' = 0.01 ((k1 + r_q) − k)`. The guards are density bands: `R1800` `k < 19`, `R1440`
`[19, 24)`, `R1200` `[24, 29)`, `R960` `[29, 34)`, `R720` `[34, 39)`, `R480` `k ≥ 39` (each with
the domain); `next` is the rate and its neighbours (`R1800` and `R1440` both reach
`R1800 … R1200`, `R720` and `R480` both reach `R960 … R480`).
* Existence (i): `kd` held, `k1` the variation-of-constants solution forced by `0.02 kd₀`
  (`forcedSol`), which stays in `[min k1₀ kd₀, max k1₀ kd₀] ⊆ [10, 27.5]`, and `k` the one
  forced by `0.01 (k1(t) + r_q) ∈ [0.01 (10 + r_q), 0.01 (27.5 + r_q)]`, which stays in
  `[min k₀ (10 + r_q), max k₀ (27.5 + r_q)] ⊆ [14, 42.5]` (`forcedSol_between`).
* (ii), every rate (style (b), exit): **the 20-second density envelope** (`k_envelope`). On
  the domain the field of `k` lies between `0.01 ((10 + r_q) − k)` and `0.01 ((27.5 + r_q) − k)`,
  so a run of duration `t ≤ 20` ends between the two exponential approaches
  `L + (k₀ − L) E` and `U + (k₀ − U) E` (`L = 10 + r_q`, `U = 27.5 + r_q`, `E = e^{−0.01 t}`,
  `0.8 ≤ 1 − 0.01 t ≤ E ≤ 1`; `contract_le` / `contract_ge`). A domain-wide rate bound is
  too coarse here (`R1440` could reach `R960`); the envelope is not: `R1800` ends below
  `42.5 − 23.5 · 0.8 = 23.7`, `R1440` below `39.5 − 15.5 · 0.8 = 27.1`, `R1200` in
  `[20, 37.5 − 8.5 · 0.8] = [20, 30.7]`, `R960` in `[18 + 11 · 0.8, 35.5] = [26.8, 35.5]`,
  `R720` in `[16 + 18 · 0.8, k₀] = [30.4, k₀]`, `R480` above `14 + 25 · 0.8 = 34`, each inside
  the bands of its declared successors.
Z3-free; modelled on `InsulinBasalCgmloss.lean` (band steps over levels) and
`FurnaceProgramTimebase.lean` (layout).
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.rampmeter_poll_2to1

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RampmeterPoll2to1

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["kd", "k1", "k"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := rampmeter_poll_2to1_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_01 : Run.parseRat "0.01" = some ((1:ℚ)/100) := by
  have h : parseQ "0.01" = some (⟨1, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_02 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_4 : Run.parseRat "4" = some (4 : ℚ) := by
  have h : parseQ "4" = some (⟨4, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_6 : Run.parseRat "6" = some (6 : ℚ) := by
  have h : parseQ "6" = some (⟨6, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_8 : Run.parseRat "8" = some (8 : ℚ) := by
  have h : parseQ "8" = some (⟨8, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_10 : Run.parseRat "10" = some (10 : ℚ) := by
  have h : parseQ "10" = some (⟨10, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_12 : Run.parseRat "12" = some (12 : ℚ) := by
  have h : parseQ "12" = some (⟨12, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_14 : Run.parseRat "14" = some (14 : ℚ) := by
  have h : parseQ "14" = some (⟨14, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_15 : Run.parseRat "15" = some (15 : ℚ) := by
  have h : parseQ "15" = some (⟨15, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_19 : Run.parseRat "19" = some (19 : ℚ) := by
  have h : parseQ "19" = some (⟨19, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_20 : Run.parseRat "20" = some (20 : ℚ) := by
  have h : parseQ "20" = some (⟨20, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_24 : Run.parseRat "24" = some (24 : ℚ) := by
  have h : parseQ "24" = some (⟨24, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_27_5 : Run.parseRat "27.5" = some ((55:ℚ)/2) := by
  have h : parseQ "27.5" = some (⟨275, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_29 : Run.parseRat "29" = some (29 : ℚ) := by
  have h : parseQ "29" = some (⟨29, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_34 : Run.parseRat "34" = some (34 : ℚ) := by
  have h : parseQ "34" = some (⟨34, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_39 : Run.parseRat "39" = some (39 : ℚ) := by
  have h : parseQ "39" = some (⟨39, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_42_5 : Run.parseRat "42.5" = some ((85:ℚ)/2) := by
  have h : parseQ "42.5" = some (⟨425, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- Rate `q`'s ramp level: `R1800` 15, `R1440` 12, `R1200` 10, `R960` 8, `R720` 6, `R480` 4. -/
noncomputable def rR : ℕ → ℝ
  | 0 => 15
  | 1 => 12
  | 2 => 10
  | 3 => 8
  | 4 => 6
  | _ => 4

theorem rR_bounds (q : ℕ) : 4 ≤ rR q ∧ rR q ≤ 15 := by
  unfold rR; split <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 6) (x : State (Var 3)) : Term.eval (fR q 0) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rampmeter_poll_2to1_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
      hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
      hp_34, hp_39, hp_42_5,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fR1_eval (q : ℕ) (hq : q < 6) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 1/50 * x (Rv 0) - 1/50 * x (Rv 1) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rampmeter_poll_2to1_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
      hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
      hp_34, hp_39, hp_42_5,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv] <;> ring

theorem fR2_eval (q : ℕ) (hq : q < 6) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 1/100 * (x (Rv 1) + rR q) - 1/100 * x (Rv 2) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rampmeter_poll_2to1_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
      hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
      hp_34, hp_39, hp_42_5,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, rR] <;> ring

theorem sat_domR (ν : State (Var 3)) :
    Formula.sat domR ν ↔
      (10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 55/2 ∧ 10 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 55/2 ∧ 14 ≤ ν (Rv 2) ∧
        ν (Rv 2) ≤ 85/2) := by
  simp only [domR, hostEvolve, mR, rampmeter_poll_2to1_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_0_01, hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14,
    hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29, hp_34, hp_39, hp_42_5, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (`R1800` 0, `R1440` 1, `R1200` 2, `R960` 3, `R720` 4,
`R480` 5). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3),
    (3, 4), (4, 3), (4, 4), (4, 5), (5, 3), (5, 4), (5, 5)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4, modeW 5]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 6) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 6 ∧ m = modeW q := by
  have hlen : q < 6 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 6 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

/-- `R1800`'s guard, evaluated. -/
theorem sat_g0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 2) < 19 ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 55/2 ∧ 10 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 55/2 ∧
        14 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 85/2) := by
  simp [hostGuard, mR, rampmeter_poll_2to1_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01,
    hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
    hp_34, hp_39, hp_42_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- `R1440`'s guard, evaluated. -/
theorem sat_g1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (19 ≤ ν (Rv 2) ∧ ν (Rv 2) < 24 ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 55/2 ∧ 10 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 55/2 ∧ 14 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 85/2) := by
  simp [hostGuard, mR, rampmeter_poll_2to1_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01,
    hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
    hp_34, hp_39, hp_42_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- `R1200`'s guard, evaluated. -/
theorem sat_g2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      (24 ≤ ν (Rv 2) ∧ ν (Rv 2) < 29 ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 55/2 ∧ 10 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 55/2 ∧ 14 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 85/2) := by
  simp [hostGuard, mR, rampmeter_poll_2to1_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01,
    hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
    hp_34, hp_39, hp_42_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- `R960`'s guard, evaluated. -/
theorem sat_g3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔
      (29 ≤ ν (Rv 2) ∧ ν (Rv 2) < 34 ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 55/2 ∧ 10 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 55/2 ∧ 14 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 85/2) := by
  simp [hostGuard, mR, rampmeter_poll_2to1_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01,
    hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
    hp_34, hp_39, hp_42_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- `R720`'s guard, evaluated. -/
theorem sat_g4 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 4)) ν ↔
      (34 ≤ ν (Rv 2) ∧ ν (Rv 2) < 39 ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 55/2 ∧ 10 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 55/2 ∧ 14 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 85/2) := by
  simp [hostGuard, mR, rampmeter_poll_2to1_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01,
    hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
    hp_34, hp_39, hp_42_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- `R480`'s guard, evaluated. -/
theorem sat_g5 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 5)) ν ↔
      (39 ≤ ν (Rv 2) ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 55/2 ∧ 10 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 55/2 ∧
        14 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 85/2) := by
  simp [hostGuard, mR, rampmeter_poll_2to1_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01,
    hp_0_02, hp_4, hp_6, hp_8, hp_10, hp_12, hp_14, hp_15, hp_19, hp_20, hp_24, hp_27_5, hp_29,
    hp_34, hp_39, hp_42_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR rampmeter_poll_2to1_IRv2 = 20 := by
  simp [epsR, rampmeter_poll_2to1_IRv2, hp_20]

/-! ## Existence: the explicit run -/

/-- The upstream density from `k1₀`, forced by the held demand `kd₀`. -/
noncomputable def k1Sol (kd0 k10 : ℝ) : ℝ → ℝ := forcedSol (1/50) k10 (fun _ => 1/50 * kd0)

theorem k1Sol_cont (kd0 k10 : ℝ) : Continuous (k1Sol kd0 k10) :=
  forcedSol_continuous _ _ continuous_const

theorem FK_cont (q : ℕ) (kd0 k10 : ℝ) : Continuous (fun u => 1/100 * (k1Sol kd0 k10 u + rR q)) :=
  continuous_const.mul ((k1Sol_cont kd0 k10).add continuous_const)

/-- The run of rate `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0)
  else if i.val = 1 then k1Sol (x (Rv 0)) (x (Rv 1)) t
  else forcedSol (1/100) (x (Rv 2)) (fun u => 1/100 * (k1Sol (x (Rv 0)) (x (Rv 1)) u + rR q)) t

theorem phi_zero (q : ℕ) (x : State (Var 3)) : phi q x 0 = fun _ => x (Rv 0) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 3)) : phi q x 1 = k1Sol (x (Rv 0)) (x (Rv 1)) := by
  funext t; simp [phi]

theorem phi_two (q : ℕ) (x : State (Var 3)) :
    phi q x 2 =
      forcedSol (1/100) (x (Rv 2)) (fun u => 1/100 * (k1Sol (x (Rv 0)) (x (Rv 1)) u + rR q)) := by
  funext t; simp [phi]

theorem phi_der (q : ℕ) (hq : q < 6) (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, phi_zero]
      exact hasDerivAt_const _ _
  | 1 =>
      rw [fR1_eval q hq, trajRs_R, trajRs_R, phi_zero, phi_one]
      exact (forcedSol_hasDerivAt (1/50) (x (Rv 1)) continuous_const t).congr_deriv rfl
  | 2 =>
      rw [fR2_eval q hq, trajRs_R, trajRs_R, phi_one, phi_two]
      exact (forcedSol_hasDerivAt (1/100) (x (Rv 2)) (FK_cont q (x (Rv 0)) (x (Rv 1))) t)

theorem k1Sol_box (kd0 k10 T : ℝ) (h0 : 10 ≤ kd0) (h1 : kd0 ≤ 55/2) (h2 : 10 ≤ k10)
    (h3 : k10 ≤ 55/2) : ∀ t ∈ Icc (0:ℝ) T, 10 ≤ k1Sol kd0 k10 t ∧ k1Sol kd0 k10 t ≤ 55/2 := by
  intro t ht
  have hb := forcedSol_between (1/50) k10 (F := fun _ => 1/50 * kd0) continuous_const
    (lo := 1/50 * kd0) (hi := 1/50 * kd0) (T := T) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩)
    t ht
  have e : (1/50 * kd0) / (1/50 : ℝ) = kd0 := by field_simp
  rw [e] at hb
  exact ⟨le_trans (le_min h2 h0) hb.1, le_trans hb.2 (max_le h3 h1)⟩

theorem exists_run (q : ℕ) (hq : q < 6) (x : State (Var 3)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, b0, b1, c0, c1⟩ := (sat_domR x).mp hd
  obtain ⟨r0, r1⟩ := rR_bounds q
  refine ⟨_, trajRs_sol x (phi q x) ε hε (fun i => ?_) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht hte => ?_)⟩
  · match i with
    | 0 => rw [phi_zero]
    | 1 => rw [phi_one]; exact forcedSol_zero _ _ _
    | 2 => rw [phi_two, forcedSol_zero]
  · have hK := forcedSol_between (1/100) (x (Rv 2)) (FK_cont q (x (Rv 0)) (x (Rv 1)))
      (lo := 1/100 * (10 + rR q)) (hi := 1/100 * (55/2 + rR q)) (T := ε) (by norm_num)
      (fun u hu => by
        have := k1Sol_box (x (Rv 0)) (x (Rv 1)) ε a0 a1 b0 b1 u hu
        show 1/100 * (10 + rR q) ≤ 1/100 * (k1Sol (x (Rv 0)) (x (Rv 1)) u + rR q) ∧
          1/100 * (k1Sol (x (Rv 0)) (x (Rv 1)) u + rR q) ≤ 1/100 * (55/2 + rR q)
        constructor <;> linarith [this.1, this.2]) t ⟨ht, hte⟩
    have e1 : 1/100 * (10 + rR q) / (1/100 : ℝ) = 10 + rR q := by field_simp
    have e2 : 1/100 * (55/2 + rR q) / (1/100 : ℝ) = 55/2 + rR q := by field_simp
    rw [e1, e2] at hK
    obtain ⟨d0, d1⟩ := k1Sol_box (x (Rv 0)) (x (Rv 1)) ε a0 a1 b0 b1 t ⟨ht, hte⟩
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R, phi_zero, phi_one, phi_two]
    exact ⟨a0, a1, d0, d1, le_trans (le_min c0 (by linarith)) hK.1,
      le_trans hK.2 (max_le c1 (by linarith))⟩

/-! ## The 20-second density envelope -/

/-- **Upper exponential comparison along a run**: a coordinate whose field is at most
`k (c − y)` on the domain ends below the exponential approach `c + (y₀ − c) e^{−k r}`. -/
theorem contract_le {sys : ODESystem (Var 3)} {dom : Formula (Var 3)} {x : State (Var 3)}
    {r : ℝ} {Φ : ℝ → State (Var 3)} (H : ODESol sys dom x r Φ) {y : Var 3} {f : Term (Var 3)}
    (hy : (y, f) ∈ sys) (k c : ℝ)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s ≤ k * (c - s y)) :
    Φ r y ≤ c + (x y - c) * Real.exp (-(k * r)) := by
  set g : ℝ → ℝ := fun t => (c - Φ t y) * Real.exp (k * t) with hg
  have hderiv : ∀ t ∈ Icc (0:ℝ) r,
      HasDerivWithinAt g ((k * (c - Φ t y) - Term.eval f (Φ t)) * Real.exp (k * t))
        (Icc 0 r) t := by
    intro t ht
    have h1 := H.hder t ht (y, f) hy
    have h2 : HasDerivWithinAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1))
        (Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul k).exp).hasDerivWithinAt
    exact ((h1.const_sub c).mul h2).congr_deriv (by ring)
  have hcont : ContinuousOn g (Icc 0 r) := fun t ht => (hderiv t ht).continuousWithinAt
  have hmono : MonotoneOn g (Icc 0 r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have := hf _ (H.hdom t (Ioo_subset_Icc_self ht))
      have he := Real.exp_pos (k * t)
      nlinarith
  have h := hmono ⟨le_refl 0, H.hr⟩ ⟨H.hr, le_refl r⟩ H.hr
  simp only [hg, mul_zero, Real.exp_zero, mul_one, H.hΦ0] at h
  have hexp : Real.exp (k * r) * Real.exp (-(k * r)) = 1 := by
    rw [← Real.exp_add]; simp
  have he := Real.exp_pos (-(k * r))
  have h' : (c - x y) * Real.exp (-(k * r)) ≤ c - Φ r y := by
    calc (c - x y) * Real.exp (-(k * r))
        ≤ ((c - Φ r y) * Real.exp (k * r)) * Real.exp (-(k * r)) :=
          mul_le_mul_of_nonneg_right h he.le
      _ = c - Φ r y := by rw [mul_assoc, hexp, mul_one]
  linarith

/-- **Lower exponential comparison along a run**: a coordinate whose field is at least
`k (c − y)` on the domain ends above the exponential approach `c + (y₀ − c) e^{−k r}`. -/
theorem contract_ge {sys : ODESystem (Var 3)} {dom : Formula (Var 3)} {x : State (Var 3)}
    {r : ℝ} {Φ : ℝ → State (Var 3)} (H : ODESol sys dom x r Φ) {y : Var 3} {f : Term (Var 3)}
    (hy : (y, f) ∈ sys) (k c : ℝ)
    (hf : ∀ s, Formula.sat dom s → k * (c - s y) ≤ Term.eval f s) :
    c + (x y - c) * Real.exp (-(k * r)) ≤ Φ r y := by
  set g : ℝ → ℝ := fun t => (Φ t y - c) * Real.exp (k * t) with hg
  have hderiv : ∀ t ∈ Icc (0:ℝ) r,
      HasDerivWithinAt g ((Term.eval f (Φ t) - k * (c - Φ t y)) * Real.exp (k * t))
        (Icc 0 r) t := by
    intro t ht
    have h1 := H.hder t ht (y, f) hy
    have h2 : HasDerivWithinAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1))
        (Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul k).exp).hasDerivWithinAt
    exact ((h1.sub_const c).mul h2).congr_deriv (by ring)
  have hcont : ContinuousOn g (Icc 0 r) := fun t ht => (hderiv t ht).continuousWithinAt
  have hmono : MonotoneOn g (Icc 0 r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have := hf _ (H.hdom t (Ioo_subset_Icc_self ht))
      have he := Real.exp_pos (k * t)
      nlinarith
  have h := hmono ⟨le_refl 0, H.hr⟩ ⟨H.hr, le_refl r⟩ H.hr
  simp only [hg, mul_zero, Real.exp_zero, mul_one, H.hΦ0] at h
  have hexp : Real.exp (k * r) * Real.exp (-(k * r)) = 1 := by
    rw [← Real.exp_add]; simp
  have he := Real.exp_pos (-(k * r))
  have h' : (x y - c) * Real.exp (-(k * r)) ≤ Φ r y - c := by
    calc (x y - c) * Real.exp (-(k * r))
        ≤ ((Φ r y - c) * Real.exp (k * r)) * Real.exp (-(k * r)) :=
          mul_le_mul_of_nonneg_right h he.le
      _ = Φ r y - c := by rw [mul_assoc, hexp, mul_one]
  linarith

theorem memK (q : ℕ) : (Rv 2, Term.binop .mul (Term.const 1) (fR q 2)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 2

/-- **Over one interval (at most 20 s) the density stays between the two exponential
approaches** to `10 + r_q` and `27.5 + r_q`, with a common factor `E ∈ [0.8, 1]`. -/
theorem k_envelope (q : ℕ) (hq : q < 6) (x : State (Var 3)) (t : ℝ) (Φ : ℝ → State (Var 3))
    (ht : t ≤ 20) (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    ∃ E : ℝ, 4/5 ≤ E ∧ E ≤ 1 ∧
      (10 + rR q) + (x (Rv 2) - (10 + rR q)) * E ≤ Φ t (Rv 2) ∧
      Φ t (Rv 2) ≤ (55/2 + rR q) + (x (Rv 2) - (55/2 + rR q)) * E := by
  have h0 := H.hr
  refine ⟨Real.exp (-(1/100 * t)), ?_, ?_, ?_, ?_⟩
  · have := Real.add_one_le_exp (-(1/100 * t)); linarith
  · rw [Real.exp_le_one_iff]; linarith
  · exact contract_ge H (memK q) (1/100) (10 + rR q) (fun s hs => by
      obtain ⟨a0, a1, b0, b1, c0, c1⟩ := (sat_domR s).mp hs
      show 1/100 * (10 + rR q - s (Rv 2)) ≤ Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) s
      rw [eval_unit_mul, fR2_eval q hq]; linarith)
  · exact contract_le H (memK q) (1/100) (55/2 + rR q) (fun s hs => by
      obtain ⟨a0, a1, b0, b1, c0, c1⟩ := (sat_domR s).mp hs
      show Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) s ≤ 1/100 * (55/2 + rR q - s (Rv 2))
      rw [eval_unit_mul, fR2_eval q hq]; linarith)

/-- **Assumption 1 for `rampmeter_poll_2to1`**, every mode, Z3-free. -/
theorem rampmeter_poll_2to1_wellFormedR :
    WellFormedR Gr guardR (epsR rampmeter_poll_2to1_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq6, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq6 x hd 20 (by norm_num), ?_⟩
  intro t Φ ht H
  obtain ⟨E, hE0, hE1, hlo, hhi⟩ := k_envelope q hq6 x t Φ ht H
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
  interval_cases q
  · -- R1800: from `k₀ < 19` the density ends below `42.5 − 23.5 · 0.8 = 23.7`
    have hg' := (sat_g0 x).mp hg
    simp only [rR] at hlo hhi
    have hk : Φ t (Rv 2) < 29 := by nlinarith [hg'.1]
    by_cases h1 : Φ t (Rv 2) < 19
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr ⟨h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 2) < 24
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
          (sat_g1 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 0 2, edge_mem 0 2 (by decide),
          (sat_g2 _).mpr ⟨by linarith, hk, e0, e1, e2, e3, e4, e5⟩⟩
  · -- R1440: from `k₀ < 24` the density ends below `39.5 − 15.5 · 0.8 = 27.1`
    have hg' := (sat_g1 x).mp hg
    simp only [rR] at hlo hhi
    have hk : Φ t (Rv 2) < 29 := by nlinarith [hg'.2.1]
    by_cases h1 : Φ t (Rv 2) < 19
    · exact ⟨edgeW 1 0, edge_mem 1 0 (by decide), (sat_g0 _).mpr ⟨h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 2) < 24
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
          (sat_g1 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
          (sat_g2 _).mpr ⟨by linarith, hk, e0, e1, e2, e3, e4, e5⟩⟩
  · -- R1200: from `[24, 29)` the density ends in `[20, 37.5 − 8.5 · 0.8] = [20, 30.7]`
    have hg' := (sat_g2 x).mp hg
    simp only [rR] at hlo hhi
    have hkl : 19 ≤ Φ t (Rv 2) := by nlinarith [hg'.1]
    have hku : Φ t (Rv 2) < 34 := by nlinarith [hg'.2.1]
    by_cases h1 : Φ t (Rv 2) < 24
    · exact ⟨edgeW 2 1, edge_mem 2 1 (by decide),
        (sat_g1 _).mpr ⟨hkl, h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 2) < 29
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide),
          (sat_g2 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide),
          (sat_g3 _).mpr ⟨by linarith, hku, e0, e1, e2, e3, e4, e5⟩⟩
  · -- R960: from `[29, 34)` the density ends in `[18 + 11 · 0.8, 35.5] = [26.8, 35.5]`
    have hg' := (sat_g3 x).mp hg
    simp only [rR] at hlo hhi
    have hkl : 24 ≤ Φ t (Rv 2) := by nlinarith [hg'.1]
    have hku : Φ t (Rv 2) < 39 := by nlinarith [hg'.2.1]
    by_cases h1 : Φ t (Rv 2) < 29
    · exact ⟨edgeW 3 2, edge_mem 3 2 (by decide),
        (sat_g2 _).mpr ⟨hkl, h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 2) < 34
      · exact ⟨edgeW 3 3, edge_mem 3 3 (by decide),
          (sat_g3 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 3 4, edge_mem 3 4 (by decide),
          (sat_g4 _).mpr ⟨by linarith, hku, e0, e1, e2, e3, e4, e5⟩⟩
  · -- R720: from `[34, 39)` the density ends in `[16 + 18 · 0.8, k₀] = [30.4, k₀]`
    have hg' := (sat_g4 x).mp hg
    simp only [rR] at hlo hhi
    have hkl : 29 ≤ Φ t (Rv 2) := by nlinarith [hg'.1]
    by_cases h1 : Φ t (Rv 2) < 34
    · exact ⟨edgeW 4 3, edge_mem 4 3 (by decide),
        (sat_g3 _).mpr ⟨hkl, h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 2) < 39
      · exact ⟨edgeW 4 4, edge_mem 4 4 (by decide),
          (sat_g4 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 4 5, edge_mem 4 5 (by decide),
          (sat_g5 _).mpr ⟨by linarith, e0, e1, e2, e3, e4, e5⟩⟩
  · -- R480: from `k₀ ≥ 39` the density ends above `14 + 25 · 0.8 = 34`
    have hg' := (sat_g5 x).mp hg
    simp only [rR] at hlo hhi
    have hkl : 29 ≤ Φ t (Rv 2) := by nlinarith [hg'.1]
    by_cases h1 : Φ t (Rv 2) < 34
    · exact ⟨edgeW 5 3, edge_mem 5 3 (by decide),
        (sat_g3 _).mpr ⟨hkl, h1, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 2) < 39
      · exact ⟨edgeW 5 4, edge_mem 5 4 (by decide),
          (sat_g4 _).mpr ⟨by linarith, h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 5 5, edge_mem 5 5 (by decide),
          (sat_g5 _).mpr ⟨by linarith, e0, e1, e2, e3, e4, e5⟩⟩

end V2RampmeterPoll2to1
end RelCertifier
