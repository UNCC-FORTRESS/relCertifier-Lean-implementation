/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `grid_ffr_dos`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three supervisor modes and their declared `next` lists), the lowered right guards, and
`ε_r = 0.1` read from the file.

The right model is the island grid with the FFR command delivered every cycle: the frequency
deviation `x` (coordinate 0), the lost infeed `d` (coordinate 1, constant), the activated FFR
share `a` (coordinate 2), inside `−2.5 ≤ x ≤ 1`, `0.05 ≤ d ≤ 0.3`, `0 ≤ a ≤ 1`. `NORMAL` and
`FFR` share the swing equation `x' = 6.25 (0.1 a − d) − 2.625 x`; `NORMAL` holds `a`, `FFR` ramps
it, `a' = 5 (1 − a)`; `TRIP` collapses the frequency, `x' = 0.5 (−2.5 − x)`. Guards (each with
the domain): `NORMAL` `x > −0.4 ∧ a ≤ 0`, `FFR` `x − 2a ≤ −0.4 ∧ x ≥ −1.5`, `TRIP` `x < −1.5`.
* Existence (i): in `NORMAL` and `FFR` the activation is the exponential approach
  `1 + (a₀ − 1) e^{−k t}` (`k = 0`, `5`), inside `[a₀, 1]`, and `x` the variation-of-constants
  solution forced by `0.625 a(t) − 6.25 d₀ ∈ [−1.875, 0.3125]` (`forcedSol`), which stays in
  `[min x₀ (−5/7), max x₀ (5/42)]` (`forcedSol_between`); in `TRIP` the exponential approach of
  `x` to `−2.5` (`exists_contract_run`).
* (ii): `NORMAL` keeps `a = 0` (frozen), and on `a = 0` the three guards cover the domain
  (`x > −0.4`, `[−1.5, −0.4]`, `x < −1.5`); `FFR` keeps `x − 2a ≤ −0.4` (non-strict
  superlevel barrier: its Lie derivative is `≤ 5.375 a − 6.25 d − 8.95 < 0` wherever
  `x − 2a ≥ −0.4`), so a run ends in `FFR` (`x ≥ −1.5`) or `TRIP` (`x < −1.5`); `TRIP` falls
  toward `−2.5` (`linear_down`) and stays below its start, below `−1.5`.
Z3-free; modelled on `FurnaceProgramTimebase.lean` and `FuelcellChpDos.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.grid_ffr_dos

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2GridFfrDos

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["x", "d", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := grid_ffr_dos_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_6_25 : Run.parseRat "6.25" = some ((25:ℚ)/4) := by
  have h : parseQ "6.25" = some (⟨625, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_2_625 : Run.parseRat "2.625" = some ((21:ℚ)/8) := by
  have h : parseQ "2.625" = some (⟨2625, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m0_4 : Run.parseRat "-0.4" = some ((-2:ℚ)/5) := by
  have h : parseQ "-0.4" = some (⟨-4, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m2_5 : Run.parseRat "-2.5" = some ((-5:ℚ)/2) := by
  have h : parseQ "-2.5" = some (⟨-25, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_2_0 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m1_5 : Run.parseRat "-1.5" = some ((-3:ℚ)/2) := by
  have h : parseQ "-1.5" = some (⟨-15, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_5 : Run.parseRat "5" = some (5 : ℚ) := by
  have h : parseQ "5" = some (⟨5, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_2_5 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- Activation rate: `FFR` 5; `NORMAL` and `TRIP` hold the activation (rate 0). -/
noncomputable def aK (q : ℕ) : ℝ := if q = 1 then 5 else 0

/-- The swing equation of `NORMAL` and `FFR`. -/
theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 0) x = 25/4 * (1/10 * x (Rv 2) - x (Rv 1)) - 21/8 * x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, grid_ffr_dos_IRv2, vs, Run.dynOf, Run.lowerE, hp_6_25, hp_0_1,
      hp_2_625, hp_0_0, hp_m0_4, hp_m2_5, hp_1_0, hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1,
      hp_0_5, hp_2_5, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

/-- The frequency collapse of `TRIP`. -/
theorem fR0_eval2 (x : State (Var 3)) :
    Term.eval (fR 2 0) x = 1/2 * (-5/2 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, grid_ffr_dos_IRv2, vs, Run.dynOf, Run.lowerE, hp_6_25, hp_0_1,
    hp_2_625, hp_0_0, hp_m0_4, hp_m2_5, hp_1_0, hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1,
    hp_0_5, hp_2_5, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
  ring

/-- The lost infeed is constant in every mode. -/
theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) : Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, grid_ffr_dos_IRv2, vs, Run.dynOf, Run.lowerE, hp_6_25, hp_0_1,
      hp_2_625, hp_0_0, hp_m0_4, hp_m2_5, hp_1_0, hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1,
      hp_0_5, hp_2_5, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

/-- The activation: `a' = aK q (1 − a)`. -/
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 2) x = aK q * (1 - x (Rv 2)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, grid_ffr_dos_IRv2, vs, Run.dynOf, Run.lowerE, hp_6_25, hp_0_1,
      hp_2_625, hp_0_0, hp_m0_4, hp_m2_5, hp_1_0, hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1,
      hp_0_5, hp_2_5, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, aK]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (-5/2 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1 ∧ 1/20 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 3/10 ∧ 0 ≤ x (Rv 2) ∧
        x (Rv 2) ≤ 1) := by
  simp only [domR, hostEvolve, mR, grid_ffr_dos_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_6_25, hp_0_1, hp_2_625, hp_0_0, hp_m0_4, hp_m2_5, hp_1_0,
    hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1, hp_0_5, hp_2_5, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
    AOp.interp, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, FFR 1, TRIP 2). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]

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
      (-2/5 < ν (Rv 0) ∧ ν (Rv 2) ≤ 0 ∧ -5/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 1 ∧ 1/20 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 3/10 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, grid_ffr_dos_IRv2, Run.lowerF, Run.lowerE, hp_6_25, hp_0_1, hp_2_625,
    hp_0_0, hp_m0_4, hp_m2_5, hp_1_0, hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1, hp_0_5,
    hp_2_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (ν (Rv 0) - 2 * ν (Rv 2) ≤ -2/5 ∧ -3/2 ≤ ν (Rv 0) ∧ -5/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 1 ∧
        1/20 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 3/10 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, grid_ffr_dos_IRv2, Run.lowerF, Run.lowerE, hp_6_25, hp_0_1, hp_2_625,
    hp_0_0, hp_m0_4, hp_m2_5, hp_1_0, hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1, hp_0_5,
    hp_2_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      (ν (Rv 0) < -3/2 ∧ -5/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 1 ∧ 1/20 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 3/10 ∧
        0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, grid_ffr_dos_IRv2, Run.lowerF, Run.lowerE, hp_6_25, hp_0_1, hp_2_625,
    hp_0_0, hp_m0_4, hp_m2_5, hp_1_0, hp_0_05, hp_0_3, hp_2_0, hp_m1_5, hp_5, hp_1, hp_0_5,
    hp_2_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR grid_ffr_dos_IRv2 = 1/10 := by
  simp [epsR, grid_ffr_dos_IRv2, hp_0_1]

/-! ## Existence: the explicit runs -/

/-- The activation of mode `q` from `a₀` (`NORMAL`, `TRIP`: held at `a₀`). -/
noncomputable def aSol (q : ℕ) (a0 t : ℝ) : ℝ := 1 + (a0 - 1) * Real.exp (-(aK q * t))

theorem aSol_cont (q : ℕ) (a0 : ℝ) : Continuous (aSol q a0) := by unfold aSol; fun_prop

/-- The forcing of the frequency deviation, `0.625 a(t) − 6.25 d₀`. -/
noncomputable def FX (q : ℕ) (x : State (Var 3)) (t : ℝ) : ℝ :=
  5/8 * aSol q (x (Rv 2)) t - 25/4 * x (Rv 1)

theorem FX_cont (q : ℕ) (x : State (Var 3)) : Continuous (FX q x) := by
  unfold FX; have := aSol_cont q (x (Rv 2)); fun_prop

/-- The run of `NORMAL` / `FFR` from `x`: `x` forced, `d` held, `a` the exponential approach. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then forcedSol (21/8) (x (Rv 0)) (FX q x) t
  else if i.val = 1 then x (Rv 1)
  else aSol q (x (Rv 2)) t

theorem phi_zero (q : ℕ) (x : State (Var 3)) :
    phi q x 0 = forcedSol (21/8) (x (Rv 0)) (FX q x) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 3)) : phi q x 1 = fun _ => x (Rv 1) := by
  funext t; simp [phi]

theorem phi_two (q : ℕ) (x : State (Var 3)) : phi q x 2 = aSol q (x (Rv 2)) := by
  funext t; simp [phi]

theorem phi_init (q : ℕ) (x : State (Var 3)) (i : Fin 3) : phi q x i 0 = x (Rv i) := by
  match i with
  | 0 => rw [phi_zero, forcedSol_zero]
  | 1 => rw [phi_one]
  | 2 => rw [phi_two]; simp [aSol]

theorem phi_der (q : ℕ) (hq : q < 2) (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq]
      simp only [trajRs_R, phi_zero, phi_one, phi_two]
      exact (forcedSol_hasDerivAt (21/8) (x (Rv 0)) (FX_cont q x) t).congr_deriv
        (by simp only [FX]; ring)
  | 1 =>
      rw [fR1_eval q (by omega), phi_one]
      exact hasDerivAt_const _ _
  | 2 =>
      rw [fR2_eval q (by omega)]
      simp only [trajRs_R, phi_two]
      exact hasDerivAt_expApproach (aK q) 1 (x (Rv 2)) t

theorem exists_run01 (q : ℕ) (hq : q < 2) (x : State (Var 3)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨x0l, x0u, d0l, d0u, a0l, a0u⟩ := (sat_domR x).mp hd
  have hk : 0 ≤ aK q := by unfold aK; split_ifs <;> norm_num
  have ha : ∀ t, 0 ≤ t → 0 ≤ aSol q (x (Rv 2)) t ∧ aSol q (x (Rv 2)) t ≤ 1 := by
    intro t ht
    obtain ⟨l, u⟩ := exp_approach_between (aK q) 1 (x (Rv 2)) t hk ht
    exact ⟨le_trans (le_min a0l zero_le_one) l, le_trans u (max_le a0u le_rfl)⟩
  refine ⟨_, trajRs_sol x (phi q x) ε hε (phi_init q x) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht hte => ?_)⟩
  have hT := forcedSol_between (21/8) (x (Rv 0)) (FX_cont q x)
    (lo := -15/8) (hi := 5/16) (T := ε) (by norm_num) (fun u hu => by
      obtain ⟨h1, h2⟩ := ha u hu.1
      show -15/8 ≤ 5/8 * aSol q (x (Rv 2)) u - 25/4 * x (Rv 1) ∧
        5/8 * aSol q (x (Rv 2)) u - 25/4 * x (Rv 1) ≤ 5/16
      constructor <;> linarith) t ⟨ht, hte⟩
  have e1 : (-15/8 : ℝ) / (21/8) = -5/7 := by norm_num
  have e2 : (5/16 : ℝ) / (21/8) = 5/42 := by norm_num
  rw [e1, e2] at hT
  obtain ⟨c0, c1⟩ := ha t ht
  rw [sat_domR]
  simp only [trajRs_R, phi_zero, phi_one, phi_two]
  exact ⟨le_trans (le_min x0l (by norm_num)) hT.1, le_trans hT.2 (max_le x0u (by norm_num)),
    d0l, d0u, c0, c1⟩

theorem exists_run2 (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 2) (Term.const 1)) domR x ε Φ := by
  obtain ⟨x0l, x0u, d0l, d0u, a0l, a0u⟩ := (sat_domR x).mp hd
  refine exists_contract_run x 0 (1/2) (-5/2) (by norm_num) fR0_eval2 (fun i hi s => ?_)
    (fun v hv1 hv2 => ?_) ε hε
  · match i, hi with
    | 0, h => exact absurd rfl h
    | 1, _ => exact fR1_eval 2 (by norm_num) s
    | 2, _ => rw [fR2_eval 2 (by norm_num) s]; simp [aK]
  · rw [sat_domR, trajJ_j, trajJ_Rv_ne x 0 _ 0 (by decide : (1 : Fin 3) ≠ 0),
      trajJ_Rv_ne x 0 _ 0 (by decide : (2 : Fin 3) ≠ 0)]
    exact ⟨le_trans (le_min x0l le_rfl) hv1, le_trans hv2 (max_le x0u (by norm_num)),
      d0l, d0u, a0l, a0u⟩

theorem exists_run (q : ℕ) (hq : q < 3) (x : State (Var 3)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  rcases (by omega : q < 2 ∨ q = 2) with h | rfl
  · exact exists_run01 q h x hd ε hε
  · exact exists_run2 x hd ε hε

/-! ## Successor-completeness: the run facts -/

theorem memR (q : ℕ) (i : Fin 3) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ i

/-- **`FFR` keeps its release line**: `x − 2a ≤ −0.4` is a non-strict superlevel barrier, the
Lie derivative `0.625 a − 6.25 d − 2.625 x − 10 (1 − a)` being negative wherever `x − 2a ≥ −0.4`
in the domain. -/
theorem ffr_keep {x : State (Var 3)} {r : ℝ} {Φ : ℝ → State (Var 3)}
    (H : ODESol (rightBlock (fR 1) (Term.const 1)) domR x r Φ)
    (h0 : x (Rv 0) - 2 * x (Rv 2) ≤ -2/5) : Φ r (Rv 0) - 2 * Φ r (Rv 2) ≤ -2/5 := by
  have hwf := rightBlock_wellFormed (fR 1) (Term.const 1)
  have hk : aK 1 = 5 := by simp [aK]
  have hbox := DI_nonstrict_superlevel (sys := rightBlock (fR 1) (Term.const 1)) (ψ := domR)
    (g := fun y => (1:ℝ) * y (Rv 0) + (-2) * y (Rv 2) + 2/5) hwf
    ((((differentiable_apply (Rv 0)).const_mul 1).add
      ((differentiable_apply (Rv 2)).const_mul (-2))).add_const (2/5))
    (fun y hy hge => by
      rw [lie_two_coord _ hwf (Rv 0) (Rv 2) 1 (-2) (2/5) y, odeField_rightBlock_unit,
        odeField_rightBlock_unit, fR0_eval 1 (by norm_num), fR2_eval 1 (by norm_num), hk]
      obtain ⟨_, _, h3, _, _, h6⟩ := (sat_domR y).mp hy
      linarith)
    (ν := x) (by linarith)
  have := hbox (Φ r) H.sem
  simp only at this
  linarith

/-- **Assumption 1 for `grid_ffr_dos`**, every mode, Z3-free. -/
theorem grid_ffr_dos_wellFormedR :
    WellFormedR Gr guardR (epsR grid_ffr_dos_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq3 x hd (1/10) (by norm_num), ?_⟩
  intro t Φ _ H
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
  interval_cases q
  · -- NORMAL: the activation stays 0; on `a = 0` the three guards cover the domain
    obtain ⟨-, g1, -, -, -, -, g6, -⟩ := (sat_guard0 x).mp hg
    have ha : Φ t (Rv 2) = x (Rv 2) := H.const (memR 0 2)
      (fun s _ => by rw [eval_unit_mul, fR2_eval 0 (by norm_num)]; simp [aK])
    by_cases h1 : -2/5 < Φ t (Rv 0)
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
        (sat_guard0 _).mpr ⟨h1, by linarith, e0, e1, e2, e3, e4, e5⟩⟩
    · by_cases h2 : Φ t (Rv 0) < -3/2
      · exact ⟨edgeW 0 2, edge_mem 0 2 (by decide),
          (sat_guard2 _).mpr ⟨h2, e0, e1, e2, e3, e4, e5⟩⟩
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
          (sat_guard1 _).mpr ⟨by linarith, by linarith, e0, e1, e2, e3, e4, e5⟩⟩
  · -- FFR: the release line is kept; FFR from -1.5, TRIP below
    obtain ⟨g0, -⟩ := (sat_guard1 x).mp hg
    have hk := ffr_keep H g0
    by_cases h2 : Φ t (Rv 0) < -3/2
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
        (sat_guard2 _).mpr ⟨h2, e0, e1, e2, e3, e4, e5⟩⟩
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
        (sat_guard1 _).mpr ⟨hk, by linarith, e0, e1, e2, e3, e4, e5⟩⟩
  · -- TRIP: the frequency falls toward -2.5 and stays below its start
    obtain ⟨g0, g1, -⟩ := (sat_guard2 x).mp hg
    have hu := H.linear_down (memR 2 0) (1/2) (-5/2) (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fR0_eval2]) g1
    exact ⟨edgeW 2 2, edge_mem 2 2 (by decide),
      (sat_guard2 _).mpr ⟨by linarith [hu.2], e0, e1, e2, e3, e4, e5⟩⟩

end V2GridFfrDos
end RelCertifier
