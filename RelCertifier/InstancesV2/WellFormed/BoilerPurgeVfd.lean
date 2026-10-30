/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `boiler_purge_vfd`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two modes and their declared `next` lists), the lowered right guards, and `ε_r = 1` read from
the file.

The right model is the qualified cold start: the purge credit `v` (coordinate 0), the drum
pressure `p` (coordinate 1) and the transmitter offset `e` (coordinate 2, frozen, unused by the
reference), inside `v ≥ 0`, `−1 ≤ p ≤ 16`:
`PURGE` (`v < 5`) `v' = 0.01`, `p' = 0`, `e' = 0`; `FIRE` (`v ≥ 5`) `v' = 0`,
`p' = k (10 − p)` with `k = 0.000555555556` (time constant 30 min), `e' = 0`.
* Existence (i): `PURGE`: a linear clock-like credit and two frozen coordinates; `FIRE`: a frozen
  credit, the exponential approach of `p` to the set point 10, which stays between `p₀` and 10
  (`exp_approach_between`, inside `[−1, 16]`), and a frozen offset.
* (ii): `PURGE` ends in the domain, where `v < 5` is `PURGE`'s guard and `v ≥ 5` is `FIRE`'s
  (style (b), exit); `FIRE`: the credit does not fall, so `v ≥ 5` is kept (style (a)).
Z3-free; modelled on `MoldingPackCheckring.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.boiler_purge_vfd

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2BoilerPurgeVfd

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["v", "p", "e"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := boiler_purge_vfd_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_01 : Run.parseRat "0.01" = some ((1:ℚ)/100) := by
  have h : parseQ "0.01" = some (⟨1, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_5_0 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_10_0 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_16_0 : Run.parseRat "16.0" = some (16 : ℚ) := by
  have h : parseQ "16.0" = some (⟨160, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm1_0 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_k : Run.parseRat "0.000555555556" = some ((138888889:ℚ)/250000000000) := by
  have h : parseQ "0.000555555556" = some (⟨555555556, 1000000000000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-- The pressure loop's rate `0.000555555556`, as parsed. -/
noncomputable def kP : ℝ := (138888889:ℝ)/250000000000

theorem kP_nonneg : 0 ≤ kP := by unfold kP; norm_num

/-! ## The right fields, domain and guards, evaluated -/

theorem fP0_eval (x : State (Var 3)) : Term.eval (fR 0 0) x = 1/100 := by
  simp [fR, hostDyn, mR, boiler_purge_vfd_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
    hp_1_0, hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fP1_eval (x : State (Var 3)) : Term.eval (fR 0 1) x = 0 := by
  simp [fR, hostDyn, mR, boiler_purge_vfd_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
    hp_1_0, hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fP2_eval (x : State (Var 3)) : Term.eval (fR 0 2) x = 0 := by
  simp [fR, hostDyn, mR, boiler_purge_vfd_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
    hp_1_0, hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fF0_eval (x : State (Var 3)) : Term.eval (fR 1 0) x = 0 := by
  simp [fR, hostDyn, mR, boiler_purge_vfd_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
    hp_1_0, hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fF1_eval (x : State (Var 3)) : Term.eval (fR 1 1) x = kP * (10 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, boiler_purge_vfd_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
    hp_1_0, hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv, kP]

theorem fF2_eval (x : State (Var 3)) : Term.eval (fR 1 2) x = 0 := by
  simp [fR, hostDyn, mR, boiler_purge_vfd_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_01,
    hp_1_0, hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ -1 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 16) := by
  simp only [domR, hostEvolve, mR, boiler_purge_vfd_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_0_01, hp_1_0, hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k,
    Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (PURGE 0, FIRE 1). -/
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
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔ ν (Rv 0) < 5 := by
  simp [hostGuard, mR, boiler_purge_vfd_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01, hp_1_0,
    hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔ 5 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, boiler_purge_vfd_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_01, hp_1_0,
    hp_5_0, hp_10_0, hp_16_0, hpm1_0, hp_k, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR boiler_purge_vfd_IRv2 = 1 := by
  simp [epsR, boiler_purge_vfd_IRv2, hp_1_0]

/-! ## Existence: the explicit runs -/

/-- The run of `PURGE` from `x`: the credit rises at `0.01`, pressure and offset frozen. -/
noncomputable def phiP (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + 1/100 * t
  else if i.val = 1 then x (Rv 1)
  else x (Rv 2)

/-- The run of `FIRE` from `x`: credit and offset frozen, pressure approaching 10. -/
noncomputable def phiF (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0)
  else if i.val = 1 then 10 + (x (Rv 1) - 10) * Real.exp (-(kP * t))
  else x (Rv 2)

theorem lin_der (a c t : ℝ) : HasDerivAt (fun u => a + c * u) c t := by
  simpa using ((hasDerivAt_id t).const_mul c).const_add a

theorem phiP_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiP x i) (Term.eval (fR 0 i) (trajRs x (phiP x) t)) t := by
  match i with
  | 0 =>
      rw [fP0_eval]
      have hf : phiP x 0 = fun u => x (Rv 0) + 1/100 * u := by funext u; simp [phiP]
      rw [hf]; exact lin_der _ _ t
  | 1 =>
      rw [fP1_eval]
      have hf : phiP x 1 = fun _ => x (Rv 1) := by funext u; simp [phiP]
      rw [hf]; exact hasDerivAt_const t _
  | 2 =>
      rw [fP2_eval]
      have hf : phiP x 2 = fun _ => x (Rv 2) := by funext u; simp [phiP]
      rw [hf]; exact hasDerivAt_const t _

theorem phiF_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiF x i) (Term.eval (fR 1 i) (trajRs x (phiF x) t)) t := by
  match i with
  | 0 =>
      rw [fF0_eval]
      have hf : phiF x 0 = fun _ => x (Rv 0) := by funext u; simp [phiF]
      rw [hf]; exact hasDerivAt_const t _
  | 1 =>
      rw [fF1_eval, trajRs_R]
      have hf : phiF x 1 = fun u => 10 + (x (Rv 1) - 10) * Real.exp (-(kP * u)) := by
        funext u; simp [phiF]
      rw [hf]
      exact hasDerivAt_expApproach kP 10 (x (Rv 1)) t
  | 2 =>
      rw [fF2_eval]
      have hf : phiF x 2 = fun _ => x (Rv 2) := by funext u; simp [phiF]
      rw [hf]; exact hasDerivAt_const t _

theorem exists_runP (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, a2⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiP x) ε hε (fun i => ?_) (fun i t _ _ => phiP_der x i t)
    (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiP]
    | 1 => simp [phiP]
    | 2 => simp [phiP]
  · rw [sat_domR, trajRs_R, trajRs_R]
    simp only [phiP, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
    exact ⟨by linarith, a1, a2⟩

theorem exists_runF (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 1) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, a2⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiF x) ε hε (fun i => ?_) (fun i t _ _ => phiF_der x i t)
    (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiF]
    | 1 => simp [phiF]
    | 2 => simp [phiF]
  · obtain ⟨l1, u1⟩ := exp_approach_between kP 10 (x (Rv 1)) t kP_nonneg ht
    rw [sat_domR, trajRs_R, trajRs_R]
    simp only [phiF, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
    exact ⟨a0, le_trans (le_min a1 (by norm_num)) l1, le_trans u1 (max_le a2 (by norm_num))⟩

/-- **Assumption 1 for `boiler_purge_vfd`**, every mode, Z3-free. -/
theorem boiler_purge_vfd_wellFormedR :
    WellFormedR Gr guardR (epsR boiler_purge_vfd_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- PURGE: ends in the domain; `v < 5` is PURGE, `v ≥ 5` is FIRE
    refine ⟨exists_runP x hd 1 (by norm_num), ?_⟩
    intro t Φ _ H
    by_cases h5 : Φ t (Rv 0) < 5
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr h5⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_guard1 _).mpr (by linarith)⟩
  · -- FIRE: the credit does not fall, so `v ≥ 5` is kept
    refine ⟨exists_runF x hd 1 (by norm_num), ?_⟩
    intro t Φ _ H
    have hg1 := (sat_guard1 x).mp hg
    have hmono := H.mono (rightBlock_mem' (fR 1) (Term.const 1) 0) (fun s _ => by
      rw [eval_unit_mul, fF0_eval])
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guard1 _).mpr (by linarith)⟩

end V2BoilerPurgeVfd
end RelCertifier
