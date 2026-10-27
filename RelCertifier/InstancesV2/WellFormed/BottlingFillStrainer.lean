/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bottling_fill_strainer`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two phases and their declared `next` lists), the lowered right guards, and `ε_r = 0.005` read
from the file.

The right model is the validated filler: the filled volume `V` (coordinate 0) and the valve
opening `u` (coordinate 1), inside `0 ≤ V ≤ 1060`, `0 ≤ u ≤ 1`:
`FILL` (`V < 994`, `u ≥ 1`) `V' = 200 u`, `u' = 0`; `CLOSE` (`V ≥ 994`, `V + 8 u ≤ 1060`)
`V' = 200 u`, `u' = −25 u`.
* Existence (i): `FILL`: `u` frozen at `u₀ = 1` and `V = V₀ + 200 u₀ t`, at most `994 + 1`
  after `0.005`; `CLOSE`: `u = u₀ e^{−25 t}` and `V = (V₀ + 8 u₀) − 8 u₀ e^{−25 t}` (both
  exponential approaches, rate 25), so `V ∈ [V₀, V₀ + 8 u₀] ⊆ [994, 1060]`, `u ∈ [0, u₀]`.
* (ii): `FILL`: `u` stays `1` (`const`) and `V ≤ V₀ + 200 t < 995` (`rate_le`): `FILL` below
  994, `CLOSE` from 994 (`V + 8 u ≤ 1003`; style (b), exit); `CLOSE`: `V` does not fall
  (`mono`, `u ≥ 0`) and `V + 8 u` is conserved (`affine_const`), so its guard is kept
  (style (a)).
Z3-free; modelled on `FurnaceProgramTimebase.lean` and `MoldingPackCheckring.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.bottling_fill_strainer

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2BottlingFillStrainer

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["V", "u"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := bottling_fill_strainer_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_8_0 : Run.parseRat "8.0" = some (8 : ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_994_0 : Run.parseRat "994.0" = some (994 : ℚ) := by
  have h : parseQ "994.0" = some (⟨9940, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1060_0 : Run.parseRat "1060.0" = some (1060 : ℚ) := by
  have h : parseQ "1060.0" = some (⟨10600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_200 : Run.parseRat "200" = some (200 : ℚ) := by
  have h : parseQ "200" = some (⟨200, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp_25 : Run.parseRat "25" = some (25 : ℚ) := by
  have h : parseQ "25" = some (⟨25, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp_0_005 : Run.parseRat "0.005" = some ((1:ℚ)/200) := by
  have h : parseQ "0.005" = some (⟨5, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The volume rate, both phases: `V' = 200 u`. -/
theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 0) x = 200 * x (Rv 1) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, bottling_fill_strainer_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_1_0, hp_8_0, hp_994_0, hp_1060_0, hp_200, hp_25, hp_0_005,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

/-- `FILL`'s valve rate: `u' = 0`. -/
theorem fF1_eval (x : State (Var 2)) : Term.eval (fR 0 1) x = 0 := by
  simp [fR, hostDyn, mR, bottling_fill_strainer_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_1_0, hp_8_0, hp_994_0, hp_1060_0, hp_200, hp_25, hp_0_005,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

/-- `CLOSE`'s valve rate: `u' = (- 25) u`, the unary minus lowered as `0 − 25`. -/
theorem fC1_eval (x : State (Var 2)) : Term.eval (fR 1 1) x = -25 * x (Rv 1) := by
  simp [fR, hostDyn, mR, bottling_fill_strainer_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_1_0, hp_8_0, hp_994_0, hp_1060_0, hp_200, hp_25, hp_0_005,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1060 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 1) := by
  simp only [domR, hostEvolve, mR, bottling_fill_strainer_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_1_0, hp_8_0, hp_994_0, hp_1060_0, hp_200, hp_25, hp_0_005, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (FILL 0, CLOSE 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  have hlen : q < 2 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 2 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 994 ∧ 1 ≤ ν (Rv 1) ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 1060 ∧ 0 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 1) := by
  simp [hostGuard, mR, bottling_fill_strainer_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_1_0, hp_8_0, hp_994_0, hp_1060_0, hp_200, hp_25, hp_0_005, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔
      (994 ≤ ν (Rv 0) ∧ ν (Rv 0) + 8 * ν (Rv 1) ≤ 1060 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 1060 ∧
        0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 1) := by
  simp [hostGuard, mR, bottling_fill_strainer_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_1_0, hp_8_0, hp_994_0, hp_1060_0, hp_200, hp_25, hp_0_005, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR bottling_fill_strainer_IRv2 = 1/200 := by
  simp [epsR, bottling_fill_strainer_IRv2, hp_0_005]

/-! ## Existence: the explicit runs -/

/-- `FILL`'s volume from `V₀` at valve opening `u₀`. -/
noncomputable def VF (V0 u0 t : ℝ) : ℝ := V0 + t * (200 * u0)

/-- The run of `FILL` from `x`: `u` frozen, `V` linear. -/
noncomputable def phiF (x : State (Var 2)) (i : Fin 2) (t : ℝ) : ℝ :=
  if i.val = 0 then VF (x (Rv 0)) (x (Rv 1)) t else x (Rv 1)

theorem phiF_zero (x : State (Var 2)) : phiF x 0 = VF (x (Rv 0)) (x (Rv 1)) := by
  funext t; simp [phiF]

theorem phiF_one (x : State (Var 2)) : phiF x 1 = fun _ => x (Rv 1) := by
  funext t; simp [phiF]

theorem phiF_der (x : State (Var 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (phiF x i) (Term.eval (fR 0 i) (trajRs x (phiF x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval 0 (by norm_num), trajRs_R, phiF_zero, phiF_one]
      exact (hasDerivAt_mul_const (200 * x (Rv 1))).const_add (x (Rv 0))
  | 1 =>
      rw [fF1_eval, phiF_one]
      exact hasDerivAt_const t _

/-- `CLOSE`'s volume: the exponential approach to `V₀ + 8 u₀` at rate 25. -/
noncomputable def VC (V0 u0 t : ℝ) : ℝ :=
  (V0 + 8 * u0) + (V0 - (V0 + 8 * u0)) * Real.exp (-(25 * t))

/-- `CLOSE`'s valve opening: the exponential decay to 0 at rate 25. -/
noncomputable def uC (u0 t : ℝ) : ℝ := 0 + (u0 - 0) * Real.exp (-(25 * t))

/-- The run of `CLOSE` from `x`. -/
noncomputable def phiC (x : State (Var 2)) (i : Fin 2) (t : ℝ) : ℝ :=
  if i.val = 0 then VC (x (Rv 0)) (x (Rv 1)) t else uC (x (Rv 1)) t

theorem phiC_zero (x : State (Var 2)) : phiC x 0 = VC (x (Rv 0)) (x (Rv 1)) := by
  funext t; simp [phiC]

theorem phiC_one (x : State (Var 2)) : phiC x 1 = uC (x (Rv 1)) := by
  funext t; simp [phiC]

theorem phiC_der (x : State (Var 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (phiC x i) (Term.eval (fR 1 i) (trajRs x (phiC x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval 1 (by norm_num), trajRs_R, phiC_zero, phiC_one]
      exact (hasDerivAt_expApproach 25 (x (Rv 0) + 8 * x (Rv 1)) (x (Rv 0)) t).congr_deriv
        (by unfold uC; ring)
  | 1 =>
      rw [fC1_eval, trajRs_R, phiC_one]
      exact (hasDerivAt_expApproach 25 0 (x (Rv 1)) t).congr_deriv (by unfold uC; ring)

theorem exists_runF (x : State (Var 2)) (hg : Formula.sat (guardR 0) x) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x (1/200) Φ := by
  obtain ⟨g0, -, a0, -, b0, b1⟩ := (sat_guard0 x).mp hg
  refine ⟨_, trajRs_sol x (phiF x) (1/200) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phiF_der x i t) (fun t ht hte => ?_)⟩
  · match i with
    | 0 => simp [phiF, VF]
    | 1 => simp [phiF]
  · have hut : x (Rv 1) * t ≤ t := by nlinarith
    have hut0 : 0 ≤ x (Rv 1) * t := mul_nonneg b0 ht
    rw [sat_domR, trajRs_R, trajRs_R, phiF_zero, phiF_one]
    unfold VF
    refine ⟨by nlinarith, by nlinarith, b0, b1⟩

theorem exists_runC (x : State (Var 2)) (hg : Formula.sat (guardR 1) x) :
    ∃ Φ, ODESol (rightBlock (fR 1) (Term.const 1)) domR x (1/200) Φ := by
  obtain ⟨g0, g1, a0, a1, b0, b1⟩ := (sat_guard1 x).mp hg
  refine ⟨_, trajRs_sol x (phiC x) (1/200) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phiC_der x i t) (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiC, VC]
    | 1 => simp [phiC, uC]
  · obtain ⟨lV, uV⟩ := exp_approach_between 25 (x (Rv 0) + 8 * x (Rv 1)) (x (Rv 0)) t
      (by norm_num) ht
    obtain ⟨lu, uu⟩ := exp_approach_between 25 0 (x (Rv 1)) t (by norm_num) ht
    rw [sat_domR, trajRs_R, trajRs_R, phiC_zero, phiC_one]
    refine ⟨le_trans (le_min a0 (by linarith)) lV, le_trans uV (max_le a1 (by linarith)),
      le_trans (le_min b0 le_rfl) lu, le_trans uu (max_le b1 (by norm_num))⟩

theorem memR (q : ℕ) (i : Fin 2) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ i

/-- **Assumption 1 for `bottling_fill_strainer`**, every mode, Z3-free. -/
theorem bottling_fill_strainer_wellFormedR :
    WellFormedR Gr guardR (epsR bottling_fill_strainer_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- FILL: `u` stays 1, `V` rises by at most 1: FILL below 994, CLOSE from 994
    refine ⟨exists_runF x hg, ?_⟩
    intro t Φ ht H
    have hg0 := (sat_guard0 x).mp hg
    obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
    have hu : Φ t (Rv 1) = x (Rv 1) :=
      H.const (memR 0 1) (fun s _ => by rw [eval_unit_mul, fF1_eval])
    have hV : Φ t (Rv 0) ≤ x (Rv 0) + 200 * t :=
      H.rate_le (memR 0 0) 200 (fun s hs => by
        rw [eval_unit_mul, fR0_eval 0 (by norm_num)]
        have := (sat_domR s).mp hs
        linarith [this.2.2.2])
    by_cases h994 : Φ t (Rv 0) < 994
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
        (sat_guard0 _).mpr ⟨h994, by rw [hu]; exact hg0.2.1, e0, e1, e2, e3⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, by linarith [hg0.1], e0, e1, e2, e3⟩⟩
  · -- CLOSE: `V` does not fall and `V + 8 u` is conserved, so its guard is kept
    refine ⟨exists_runC x hg, ?_⟩
    intro t Φ _ H
    have hg1 := (sat_guard1 x).mp hg
    obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
    have hmono : x (Rv 0) ≤ Φ t (Rv 0) :=
      H.mono (memR 1 0) (fun s hs => by
        rw [eval_unit_mul, fR0_eval 1 (by norm_num)]
        have := (sat_domR s).mp hs
        linarith [this.2.2.1])
    have haff : 1 * Φ t (Rv 0) + 8 * Φ t (Rv 1) = 1 * x (Rv 0) + 8 * x (Rv 1) :=
      H.affine_const (memR 1 0) (memR 1 1) 1 8 (fun s _ => by
        rw [eval_unit_mul, eval_unit_mul, fR0_eval 1 (by norm_num), fC1_eval]; ring)
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
      (sat_guard1 _).mpr ⟨by linarith [hg1.1], by linarith [hg1.2.1], e0, e1, e2, e3⟩⟩

end V2BottlingFillStrainer
end RelCertifier
