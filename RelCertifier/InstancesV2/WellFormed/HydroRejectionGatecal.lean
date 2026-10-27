/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hydro_rejection_gatecal`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two phases and their declared `next` lists), the lowered right guards, and `ε_r = 0.1` read
from the file.

The right model is the unit with the calibrated gate: the event clock `t` (coordinate 0,
`t' = 1`), the gate opening `g` (coordinate 1) and the speed deviation `w` (coordinate 2), inside
`t ≥ 0`, `0 ≤ g ≤ 1`, `−1 ≤ w ≤ 1`: `ONGRID` (`t < 20`, `|w| ≤ 0.004`) the droop governor
`g' = 0.25 ((0.85 − g) − 20 w)` with the speed held by the grid (`w' = 0`); `REJECT` (`t ≥ 20`)
`g' = 0.25 (0.1 − g)`, `w' = 0.125 ((g − 0.1) − w)`.
* Existence (i): `ONGRID`: the clock, `w` held, and the exponential approach of `g` to
  `0.85 − 20 w₀ ∈ [0.77, 0.93]`; `REJECT`: the clock, the approach of `g` to 0.1, and `w` the
  variation-of-constants solution forced by `0.125 (g(t) − 0.1) ∈ [−0.0125, 0.1125]`
  (`forcedSol`), which stays in `[min w₀ (−0.1), max w₀ 0.9] ⊆ [−1, 1]` (`forcedSol_between`).
* (ii): `ONGRID`: `w` is constant, the run ends in the domain, `t < 20` is `ONGRID`'s guard and
  `t ≥ 20` is `REJECT`'s (style (b), exit); `REJECT`: the clock does not fall (style (a)).
Z3-free; modelled on `MoldingPackCheckring.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.hydro_rejection_gatecal

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2HydroRejectionGatecal

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["t", "g", "w"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := hydro_rejection_gatecal_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_m0_004 : Run.parseRat "-0.004" = some ((-1:ℚ)/250) := by
  have h : parseQ "-0.004" = some (⟨-4, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m1_0 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_004 : Run.parseRat "0.004" = some ((1:ℚ)/250) := by
  have h : parseQ "0.004" = some (⟨4, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_125 : Run.parseRat "0.125" = some ((1:ℚ)/8) := by
  have h : parseQ "0.125" = some (⟨125, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_25 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_85 : Run.parseRat "0.85" = some ((17:ℚ)/20) := by
  have h : parseQ "0.85" = some (⟨85, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_20_0 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) : Term.eval (fR q 0) x = 1 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, hydro_rejection_gatecal_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fG1_eval (x : State (Var 3)) :
    Term.eval (fR 0 1) x = 1/4 * ((17/20 - 20 * x (Rv 2)) - x (Rv 1)) := by
  simp [fR, hostDyn, mR, hydro_rejection_gatecal_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

theorem fG2_eval (x : State (Var 3)) : Term.eval (fR 0 2) x = 0 := by
  simp [fR, hostDyn, mR, hydro_rejection_gatecal_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fJ1_eval (x : State (Var 3)) : Term.eval (fR 1 1) x = 1/4 * (1/10 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, hydro_rejection_gatecal_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

theorem fJ2_eval (x : State (Var 3)) :
    Term.eval (fR 1 2) x = 1/8 * (x (Rv 1) - 1/10) - 1/8 * x (Rv 2) := by
  simp [fR, hostDyn, mR, hydro_rejection_gatecal_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 1 ∧ -1 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 1) := by
  simp only [domR, hostEvolve, mR, hydro_rejection_gatecal_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (ONGRID 0, REJECT 1). -/
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
      (ν (Rv 0) < 20 ∧ -1/250 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1/250 ∧ 0 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 1 ∧ -1 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, hydro_rejection_gatecal_IRv2, Run.lowerF, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (20 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 1 ∧ -1 ≤ ν (Rv 2) ∧
        ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, hydro_rejection_gatecal_IRv2, Run.lowerF, Run.lowerE, hp_m0_004, hp_m1_0, hp_0_0, hp_0_004, hp_0_1, hp_0_125, hp_0_25, hp_0_85, hp_1_0, hp_20_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR hydro_rejection_gatecal_IRv2 = 1/10 := by
  simp [epsR, hydro_rejection_gatecal_IRv2, hp_0_1]

/-! ## Existence: the explicit runs -/

theorem clock_der (a t : ℝ) : HasDerivAt (fun u => a + u) 1 t := by
  simpa using (hasDerivAt_id t).const_add a

/-- The run of `ONGRID` from `x`: the clock, the gate's approach, the held speed. -/
noncomputable def phiG (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + t
  else if i.val = 1 then
    (17/20 - 20 * x (Rv 2)) + (x (Rv 1) - (17/20 - 20 * x (Rv 2))) * Real.exp (-(1/4 * t))
  else x (Rv 2)

/-- `REJECT`'s gate from `g₀`. -/
noncomputable def gJ (g0 t : ℝ) : ℝ := 1/10 + (g0 - 1/10) * Real.exp (-(1/4 * t))

theorem gJ_cont (g0 : ℝ) : Continuous (gJ g0) := by unfold gJ; fun_prop

theorem FJ_cont (g0 : ℝ) : Continuous (fun s => 1/8 * (gJ g0 s - 1/10)) :=
  continuous_const.mul ((gJ_cont g0).sub continuous_const)

/-- The run of `REJECT` from `x`. -/
noncomputable def phiJ (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + t
  else if i.val = 1 then gJ (x (Rv 1)) t
  else forcedSol (1/8) (x (Rv 2)) (fun s => 1/8 * (gJ (x (Rv 1)) s - 1/10)) t

theorem phiG_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiG x i) (Term.eval (fR 0 i) (trajRs x (phiG x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval 0 (by norm_num)]
      have hf : phiG x 0 = fun u => x (Rv 0) + u := by funext u; simp [phiG]
      rw [hf]; exact clock_der _ t
  | 1 =>
      rw [fG1_eval, trajRs_R, trajRs_R]
      have hf : phiG x 1 = fun u => (17/20 - 20 * x (Rv 2)) +
          (x (Rv 1) - (17/20 - 20 * x (Rv 2))) * Real.exp (-(1/4 * u)) := by
        funext u; simp [phiG]
      have hf2 : phiG x 2 = fun _ => x (Rv 2) := by funext u; simp [phiG]
      rw [hf, hf2]
      exact hasDerivAt_expApproach (1/4) (17/20 - 20 * x (Rv 2)) (x (Rv 1)) t
  | 2 =>
      rw [fG2_eval]
      have hf : phiG x 2 = fun _ => x (Rv 2) := by funext u; simp [phiG]
      rw [hf]; exact hasDerivAt_const _ _

theorem phiJ_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiJ x i) (Term.eval (fR 1 i) (trajRs x (phiJ x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval 1 (by norm_num)]
      have hf : phiJ x 0 = fun u => x (Rv 0) + u := by funext u; simp [phiJ]
      rw [hf]; exact clock_der _ t
  | 1 =>
      rw [fJ1_eval, trajRs_R]
      have hf : phiJ x 1 = gJ (x (Rv 1)) := by funext u; simp [phiJ]
      rw [hf]
      exact hasDerivAt_expApproach (1/4) (1/10) (x (Rv 1)) t
  | 2 =>
      rw [fJ2_eval, trajRs_R, trajRs_R]
      have hf2 : phiJ x 2 =
          forcedSol (1/8) (x (Rv 2)) (fun s => 1/8 * (gJ (x (Rv 1)) s - 1/10)) := by
        funext u; simp [phiJ]
      have hf1 : phiJ x 1 = gJ (x (Rv 1)) := by funext u; simp [phiJ]
      rw [hf2, hf1]
      exact (forcedSol_hasDerivAt (1/8) (x (Rv 2)) (FJ_cont (x (Rv 1))) t).congr_deriv (by ring)

theorem exists_runG (x : State (Var 3)) (hd : Formula.sat domR x)
    (hw : -1/250 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 1/250) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x ε Φ := by
  obtain ⟨t0, a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiG x) ε hε (fun i => ?_) (fun i t _ _ => phiG_der x i t)
    (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiG]
    | 1 => simp [phiG]
    | 2 => simp [phiG]
  · obtain ⟨l, u⟩ := exp_approach_between (1/4) (17/20 - 20 * x (Rv 2)) (x (Rv 1)) t
      (by norm_num) ht
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiG, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    refine ⟨by linarith, le_trans (le_min a0 (by linarith)) l,
      le_trans u (max_le a1 (by linarith)), b0, b1⟩

theorem exists_runJ (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 1) (Term.const 1)) domR x ε Φ := by
  obtain ⟨t0, a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiJ x) ε hε (fun i => ?_) (fun i t _ _ => phiJ_der x i t)
    (fun t ht hte => ?_)⟩
  · match i with
    | 0 => simp [phiJ]
    | 1 => simp [phiJ, gJ]
    | 2 => simp [phiJ, forcedSol_zero]
  · have gb : ∀ s, 0 ≤ s → 0 ≤ gJ (x (Rv 1)) s ∧ gJ (x (Rv 1)) s ≤ 1 := by
      intro s hs
      obtain ⟨l, u⟩ := exp_approach_between (1/4) (1/10) (x (Rv 1)) s (by norm_num) hs
      exact ⟨le_trans (le_min a0 (by norm_num)) l, le_trans u (max_le a1 (by norm_num))⟩
    have hy := forcedSol_between (1/8) (x (Rv 2)) (FJ_cont (x (Rv 1)))
      (lo := -(1/80)) (hi := 9/80) (T := ε) (by norm_num) (fun s hs => by
        have := gb s hs.1
        show -(1/80) ≤ 1/8 * (gJ (x (Rv 1)) s - 1/10) ∧ 1/8 * (gJ (x (Rv 1)) s - 1/10) ≤ 9/80
        constructor <;> linarith [this.1, this.2]) t ⟨ht, hte⟩
    obtain ⟨c0, c1⟩ := gb t ht
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiJ, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    have e1 : (-(1/80) : ℝ) / (1/8) = -(1/10) := by norm_num
    have e2 : ((9/80) : ℝ) / (1/8) = 9/10 := by norm_num
    rw [e1, e2] at hy
    refine ⟨by linarith, c0, c1, ?_, ?_⟩
    · exact le_trans (le_min b0 (by norm_num)) hy.1
    · exact le_trans hy.2 (max_le b1 (by norm_num))

/-- **Assumption 1 for `hydro_rejection_gatecal`**, every mode, Z3-free. -/
theorem hydro_rejection_gatecal_wellFormedR :
    WellFormedR Gr guardR (epsR hydro_rejection_gatecal_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- ONGRID: the speed is held, the run ends in the domain; `t < 20` ONGRID, else REJECT
    obtain ⟨-, w1, w2, -⟩ := (sat_guard0 x).mp hg
    refine ⟨exists_runG x hd ⟨w1, w2⟩ (1/10) (by norm_num), ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    have hw := H.const (rightBlock_mem' (fR 0) (Term.const 1) 2) (fun s _ => by
      rw [eval_unit_mul, fG2_eval])
    by_cases h20 : Φ t (Rv 0) < 20
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
        (sat_guard0 _).mpr ⟨h20, by rw [hw]; exact w1, by rw [hw]; exact w2, e0, e1, e2, e3, e4⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, e0, e1, e2, e3, e4⟩⟩
  · -- REJECT: the clock does not fall, so `t ≥ 20` is kept
    refine ⟨exists_runJ x hd (1/10) (by norm_num), ?_⟩
    intro t Φ _ H
    have hg1 := (sat_guard1 x).mp hg
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    have hmono := H.mono (rightBlock_mem' (fR 1) (Term.const 1) 0) (fun s _ => by
      rw [eval_unit_mul, fR0_eval 1 (by norm_num)]; norm_num)
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
      (sat_guard1 _).mpr ⟨by linarith [hg1.1], e0, e1, e2, e3, e4⟩⟩

end V2HydroRejectionGatecal
end RelCertifier
