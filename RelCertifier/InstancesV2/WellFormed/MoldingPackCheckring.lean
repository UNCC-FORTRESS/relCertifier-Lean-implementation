/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `molding_pack_checkring`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two phases and their declared `next` lists), the lowered right guards, and `ε_r = 0.05` read
from the file.

The right model is the validated cycle with a sealing check ring: the phase clock `t`
(coordinate 0, `t' = 1`), the nozzle pressure `x` (coordinate 1) and the cavity pressure `y`
(coordinate 2), inside `t ≥ 0`, `0 ≤ x, y ≤ 500`:
`HOLD` (`t < 5`) `x' = 10 (500 − x)`, `y' = 3 (x − y)`; `COOL` (`t ≥ 5`) `x' = −2 x`,
`y' = −0.3 y`.
* Existence (i): `HOLD`: the clock, the exponential approach of `x` to 500, and `y` the
  variation-of-constants solution forced by `3 x(t)` (`forcedSol`), which stays between `y₀`
  and the forcing's range `[0, 500]` (`forcedSol_between`); `COOL`: the clock and two
  exponential decays.
* (ii): `HOLD` ends in the domain, where `t < 5` is `HOLD`'s guard and `t ≥ 5` is `COOL`'s
  (style (b), exit); `COOL`: the clock does not fall, so `t ≥ 5` is kept (style (a)).
Z3-free; modelled on `TankDos3to1.lean` (forced coordinate) and `CompressorStationRecycle.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.molding_pack_checkring

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2MoldingPackCheckring

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["t", "x", "y"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := molding_pack_checkring_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_10_0 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_2_0 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_3_0 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_5_0 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_500_0 : Run.parseRat "500.0" = some (500 : ℚ) := by
  have h : parseQ "500.0" = some (⟨5000, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) : Term.eval (fR q 0) x = 1 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, molding_pack_checkring_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fH1_eval (x : State (Var 3)) : Term.eval (fR 0 1) x = 10 * (500 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, molding_pack_checkring_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fH2_eval (x : State (Var 3)) :
    Term.eval (fR 0 2) x = 3 * x (Rv 1) - 3 * x (Rv 2) := by
  simp [fR, hostDyn, mR, molding_pack_checkring_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

theorem fC1_eval (x : State (Var 3)) : Term.eval (fR 1 1) x = 2 * (0 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, molding_pack_checkring_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

theorem fC2_eval (x : State (Var 3)) : Term.eval (fR 1 2) x = 3/10 * (0 - x (Rv 2)) := by
  simp [fR, hostDyn, mR, molding_pack_checkring_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 500 ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 500) := by
  simp only [domR, hostEvolve, mR, molding_pack_checkring_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (HOLD 0, COOL 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  have hlen : q < 2 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 2 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 5 ∧ 0 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 500 ∧ 0 ≤ ν (Rv 2) ∧
        ν (Rv 2) ≤ 500) := by
  simp [hostGuard, mR, molding_pack_checkring_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (5 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 500 ∧ 0 ≤ ν (Rv 2) ∧
        ν (Rv 2) ≤ 500) := by
  simp [hostGuard, mR, molding_pack_checkring_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_3, hp_1_0, hp_10_0, hp_2_0, hp_3_0, hp_5_0, hp_500_0, hp_0_05, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR molding_pack_checkring_IRv2 = 1/20 := by
  simp [epsR, molding_pack_checkring_IRv2, hp_0_05]

/-! ## Existence: the explicit runs -/

/-- `HOLD`'s nozzle pressure from `x₀`. -/
noncomputable def xH (x0 t : ℝ) : ℝ := 500 + (x0 - 500) * Real.exp (-(10 * t))

theorem xH_cont (x0 : ℝ) : Continuous (xH x0) := by unfold xH; fun_prop

theorem FH_cont (x0 : ℝ) : Continuous (fun s => 3 * xH x0 s) :=
  continuous_const.mul (xH_cont x0)

/-- The run of `HOLD` from `x`. -/
noncomputable def phiH (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + t
  else if i.val = 1 then xH (x (Rv 1)) t
  else forcedSol 3 (x (Rv 2)) (fun s => 3 * xH (x (Rv 1)) s) t

/-- The run of `COOL` from `x`. -/
noncomputable def phiC (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + t
  else if i.val = 1 then 0 + (x (Rv 1) - 0) * Real.exp (-(2 * t))
  else 0 + (x (Rv 2) - 0) * Real.exp (-(3/10 * t))

theorem clock_der (a t : ℝ) : HasDerivAt (fun u => a + u) 1 t := by
  simpa using (hasDerivAt_id t).const_add a

theorem phiH_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiH x i) (Term.eval (fR 0 i) (trajRs x (phiH x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval 0 (by norm_num)]
      have hf : phiH x 0 = fun u => x (Rv 0) + u := by funext u; simp [phiH]
      rw [hf]; exact clock_der _ t
  | 1 =>
      rw [fH1_eval, trajRs_R]
      have hf : phiH x 1 = xH (x (Rv 1)) := by funext u; simp [phiH]
      rw [hf]
      exact hasDerivAt_expApproach 10 500 (x (Rv 1)) t
  | 2 =>
      rw [fH2_eval, trajRs_R, trajRs_R]
      have hf2 : phiH x 2 = forcedSol 3 (x (Rv 2)) (fun s => 3 * xH (x (Rv 1)) s) := by
        funext u; simp [phiH]
      have hf1 : phiH x 1 = xH (x (Rv 1)) := by funext u; simp [phiH]
      rw [hf2, hf1]
      exact (forcedSol_hasDerivAt 3 (x (Rv 2)) (FH_cont (x (Rv 1))) t).congr_deriv (by ring)

theorem phiC_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiC x i) (Term.eval (fR 1 i) (trajRs x (phiC x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval 1 (by norm_num)]
      have hf : phiC x 0 = fun u => x (Rv 0) + u := by funext u; simp [phiC]
      rw [hf]; exact clock_der _ t
  | 1 =>
      rw [fC1_eval, trajRs_R]
      have hf : phiC x 1 = fun u => 0 + (x (Rv 1) - 0) * Real.exp (-(2 * u)) := by
        funext u; simp [phiC]
      rw [hf]
      exact hasDerivAt_expApproach 2 0 (x (Rv 1)) t
  | 2 =>
      rw [fC2_eval, trajRs_R]
      have hf : phiC x 2 = fun u => 0 + (x (Rv 2) - 0) * Real.exp (-(3/10 * u)) := by
        funext u; simp [phiC]
      rw [hf]
      exact hasDerivAt_expApproach (3/10) 0 (x (Rv 2)) t

theorem xH_between (x0 t : ℝ) (h0 : 0 ≤ x0) (h1 : x0 ≤ 500) (ht : 0 ≤ t) :
    0 ≤ xH x0 t ∧ xH x0 t ≤ 500 := by
  obtain ⟨l, u⟩ := exp_approach_between 10 500 x0 t (by norm_num) ht
  exact ⟨le_trans (le_min h0 (by norm_num)) l, le_trans u (max_le h1 le_rfl)⟩

theorem exists_runH (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x ε Φ := by
  obtain ⟨t0, a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiH x) ε hε (fun i => ?_) (fun i t _ _ => phiH_der x i t)
    (fun t ht hte => ?_)⟩
  · match i with
    | 0 => simp [phiH]
    | 1 => simp [phiH, xH]
    | 2 => simp [phiH, forcedSol_zero]
  · have hy := forcedSol_between 3 (x (Rv 2)) (FH_cont (x (Rv 1)))
      (lo := 0) (hi := 1500) (T := ε) (by norm_num) (fun s hs => by
        have := xH_between (x (Rv 1)) s a0 a1 hs.1
        show 0 ≤ 3 * xH (x (Rv 1)) s ∧ 3 * xH (x (Rv 1)) s ≤ 1500
        constructor <;> linarith [this.1, this.2]) t ⟨ht, hte⟩
    obtain ⟨c0, c1⟩ := xH_between (x (Rv 1)) t a0 a1 ht
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiH, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    refine ⟨by linarith, c0, c1, ?_, ?_⟩
    · exact le_trans (le_min b0 (by norm_num)) hy.1
    · exact le_trans hy.2 (max_le b1 (by norm_num))

theorem exists_runC (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 1) (Term.const 1)) domR x ε Φ := by
  obtain ⟨t0, a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiC x) ε hε (fun i => ?_) (fun i t _ _ => phiC_der x i t)
    (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiC]
    | 1 => simp [phiC]
    | 2 => simp [phiC]
  · obtain ⟨l1, u1⟩ := exp_approach_between 2 0 (x (Rv 1)) t (by norm_num) ht
    obtain ⟨l2, u2⟩ := exp_approach_between (3/10) 0 (x (Rv 2)) t (by norm_num) ht
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiC, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    refine ⟨by linarith, le_trans (le_min a0 le_rfl) l1, le_trans u1 (max_le a1 (by norm_num)),
      le_trans (le_min b0 le_rfl) l2, le_trans u2 (max_le b1 (by norm_num))⟩

/-- **Assumption 1 for `molding_pack_checkring`**, every mode, Z3-free. -/
theorem molding_pack_checkring_wellFormedR :
    WellFormedR Gr guardR (epsR molding_pack_checkring_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- HOLD: ends in the domain; `t < 5` is HOLD, `t ≥ 5` is COOL
    refine ⟨exists_runH x hd (1/20) (by norm_num), ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    by_cases h5 : Φ t (Rv 0) < 5
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨h5, e0, e1, e2, e3, e4⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, e0, e1, e2, e3, e4⟩⟩
  · -- COOL: the clock does not fall, so `t ≥ 5` is kept
    refine ⟨exists_runC x hd (1/20) (by norm_num), ?_⟩
    intro t Φ _ H
    have hg1 := (sat_guard1 x).mp hg
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    have hmono := H.mono (rightBlock_mem' (fR 1) (Term.const 1) 0) (fun s _ => by
      rw [eval_unit_mul, fR0_eval 1 (by norm_num)]; norm_num)
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
      (sat_guard1 _).mpr ⟨by linarith [hg1.1], e0, e1, e2, e3, e4⟩⟩

end V2MoldingPackCheckring
end RelCertifier
