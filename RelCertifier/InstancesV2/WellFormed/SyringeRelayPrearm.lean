/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `syringe_relay_prearm`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
four relay phases and their declared `next` lists), the lowered right guards, and `ε_r = 0.1`
read from the file.

The right model is the relay with the original take-up: syringe volumes `v1`, `v2`
(coordinates 0, 1), the plasma concentration `C` (coordinate 2) and the second pump's plunger
take-up `b` (coordinate 3), inside `0 ≤ v1, v2 ≤ 50`, `0 ≤ C ≤ 1`, `0 ≤ b ≤ 1.2`. Every phase
moves the volumes and the take-up at constant rates and `C` toward its level:
`RUN1` (`v1 < 49.5`, `v2 ≤ 0`): `v1' = 0.05`, `C' = 0.29 (1 − C)`;
`TAKEUP2` (`v1 ≥ 49.5`, `b < 1`, `v2 ≤ 0`): `b' = 0.09`, `C' = −0.29 C`;
`RUN2` (`v1 ≥ 49.5`, `b ≥ 1`, `v2 < 49.5`): `v2' = 0.05`, `C' = 0.29 (1 − C)`;
`END` (`v1, v2 ≥ 49.5`): `C' = −0.29 C`; every other rate 0.
* Existence (i): the linear motions and the exponential of `C`; the moving coordinate starts
  below its threshold (`49.5`, resp. `1`) and moves by at most `0.005` (resp. `0.009`) in one
  interval, so it stays below `50` (resp. `1.2`).
* (ii): the frozen coordinates keep the guard's other atoms; the moving one either stays below
  its threshold (the same phase) or passes it (the next phase: `RUN1` to `TAKEUP2` if `b < 1`,
  else to `RUN2`; `TAKEUP2` to `RUN2`; `RUN2` to `END`); `END` is frozen but for `C`
  (style (a)).
Z3-free; modelled on `ElevatorStartDiscbrake.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.syringe_relay_prearm

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2SyringeRelayPrearm

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["v1", "v2", "C", "b"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := syringe_relay_prearm_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vs 4 Side.R (mR q)
noncomputable def domR : Formula (Var 4) := hostEvolve vs 4 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_09 : Run.parseRat "0.09" = some ((9:ℚ)/100) := by
  have h : parseQ "0.09" = some (⟨9, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_29 : Run.parseRat "0.29" = some ((29:ℚ)/100) := by
  have h : parseQ "0.29" = some (⟨29, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_2 : Run.parseRat "1.2" = some ((6:ℚ)/5) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_49_5 : Run.parseRat "49.5" = some ((99:ℚ)/2) := by
  have h : parseQ "49.5" = some (⟨495, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_50_0 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The rates of `v1`, `v2`, `b` per phase (RUN1 0, TAKEUP2 1, RUN2 2, END 3). -/
noncomputable def a1 (q : ℕ) : ℝ := if q = 0 then 1/20 else 0
noncomputable def a2 (q : ℕ) : ℝ := if q = 2 then 1/20 else 0
noncomputable def a4 (q : ℕ) : ℝ := if q = 1 then 9/100 else 0
/-- `C`'s level: 1 while a syringe infuses, 0 otherwise. -/
noncomputable def cC (q : ℕ) : ℝ := if q = 0 ∨ q = 2 then 1 else 0

theorem f0_eval (q : ℕ) (hq : q < 4) (x : State (Var 4)) : Term.eval (fR q 0) x = a1 q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, syringe_relay_prearm_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      a1]

theorem f1_eval (q : ℕ) (hq : q < 4) (x : State (Var 4)) : Term.eval (fR q 1) x = a2 q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, syringe_relay_prearm_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      a2]

theorem f2_eval (q : ℕ) (hq : q < 4) (x : State (Var 4)) :
    Term.eval (fR q 2) x = 29/100 * (cC q - x (Rv 2)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, syringe_relay_prearm_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cC] <;> ring

theorem f3_eval (q : ℕ) (hq : q < 4) (x : State (Var 4)) : Term.eval (fR q 3) x = a4 q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, syringe_relay_prearm_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      a4]

theorem sat_domR (ν : State (Var 4)) :
    Formula.sat domR ν ↔
      (0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 50 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 50 ∧ 0 ≤ ν (Rv 2) ∧
        ν (Rv 2) ≤ 1 ∧ 0 ≤ ν (Rv 3) ∧ ν (Rv 3) ≤ 6/5) := by
  simp only [domR, hostEvolve, mR, syringe_relay_prearm_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 4) :=
  { src := s, tgt := t, guard := hostGuard vs 4 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (RUN1 0, TAKEUP2 1, RUN2 2, END 3). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2), (2, 3), (3, 3)]

noncomputable def Gr : SearchGraph (Var 4) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 4)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  have hlen : q < 4 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 4 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_g0 (ν : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 99/2 ∧ ν (Rv 1) ≤ 0 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 50 ∧ 0 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 50 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1 ∧ 0 ≤ ν (Rv 3) ∧ ν (Rv 3) ≤ 6/5) := by
  simp [hostGuard, mR, syringe_relay_prearm_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g1 (ν : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR 1)) ν ↔
      (99/2 ≤ ν (Rv 0) ∧ ν (Rv 3) < 1 ∧ ν (Rv 1) ≤ 0 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 50 ∧
        0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 50 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1 ∧ 0 ≤ ν (Rv 3) ∧
        ν (Rv 3) ≤ 6/5) := by
  simp [hostGuard, mR, syringe_relay_prearm_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g2 (ν : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR 2)) ν ↔
      (99/2 ≤ ν (Rv 0) ∧ 1 ≤ ν (Rv 3) ∧ ν (Rv 1) < 99/2 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 50 ∧
        0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 50 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1 ∧ 0 ≤ ν (Rv 3) ∧
        ν (Rv 3) ≤ 6/5) := by
  simp [hostGuard, mR, syringe_relay_prearm_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g3 (ν : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR 3)) ν ↔
      (99/2 ≤ ν (Rv 0) ∧ 99/2 ≤ ν (Rv 1) ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 50 ∧ 0 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 50 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1 ∧ 0 ≤ ν (Rv 3) ∧ ν (Rv 3) ≤ 6/5) := by
  simp [hostGuard, mR, syringe_relay_prearm_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_0_05, hp_0_09, hp_0_29, hp_1_0, hp_1_2, hp_49_5, hp_50_0, hp_0_1, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 4) := hostGuard vs 4 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR syringe_relay_prearm_IRv2 = 1/10 := by
  simp [epsR, syringe_relay_prearm_IRv2, hp_0_1]

/-! ## Existence: the explicit run -/

theorem lin_der (a b t : ℝ) : HasDerivAt (fun u => a + b * u) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-- The run of phase `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 4)) (i : Fin 4) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + a1 q * t
  else if i.val = 1 then x (Rv 1) + a2 q * t
  else if i.val = 2 then cC q + (x (Rv 2) - cC q) * Real.exp (-(29/100 * t))
  else x (Rv 3) + a4 q * t

theorem phi_der (q : ℕ) (hq : q < 4) (x : State (Var 4)) (i : Fin 4) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [f0_eval q hq]
      have hf : phi q x 0 = fun u => x (Rv 0) + a1 q * u := by funext u; simp [phi]
      rw [hf]; exact lin_der _ _ t
  | 1 =>
      rw [f1_eval q hq]
      have hf : phi q x 1 = fun u => x (Rv 1) + a2 q * u := by funext u; simp [phi]
      rw [hf]; exact lin_der _ _ t
  | 2 =>
      rw [f2_eval q hq, trajRs_R]
      have hf : phi q x 2 = fun u => cC q + (x (Rv 2) - cC q) * Real.exp (-(29/100 * u)) := by
        funext u; simp [phi]
      rw [hf]; exact hasDerivAt_expApproach (29/100) (cC q) (x (Rv 2)) t
  | 3 =>
      rw [f3_eval q hq]
      have hf : phi q x 3 = fun u => x (Rv 3) + a4 q * u := by funext u; simp [phi]
      rw [hf]; exact lin_der _ _ t

/-- From a guard state of phase `q` the explicit run stays in the domain for one interval:
the moving coordinate starts below its threshold and moves by at most `0.005` (`0.009`). -/
theorem exists_run (q : ℕ) (hq : q < 4) (x : State (Var 4)) (hd : Formula.sat domR x)
    (h1 : a1 q = 0 ∨ x (Rv 0) < 99/2) (h2 : a2 q = 0 ∨ x (Rv 1) < 99/2)
    (h4 : a4 q = 0 ∨ x (Rv 3) < 1) :
    ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x (1/10) Φ := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := (sat_domR x).mp hd
  have r1 : 0 ≤ a1 q ∧ a1 q ≤ 1/20 := by unfold a1; split_ifs <;> norm_num
  have r2 : 0 ≤ a2 q ∧ a2 q ≤ 1/20 := by unfold a2; split_ifs <;> norm_num
  have r4 : 0 ≤ a4 q ∧ a4 q ≤ 9/100 := by unfold a4; split_ifs <;> norm_num
  have rc : 0 ≤ cC q ∧ cC q ≤ 1 := by unfold cC; split_ifs <;> norm_num
  refine ⟨_, trajRs_sol x (phi q x) (1/10) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phi_der q hq x i t) (fun t ht hte => ?_)⟩
  · match i with
    | 0 => simp [phi]
    | 1 => simp [phi]
    | 2 => simp [phi]
    | 3 => simp [phi]
  · obtain ⟨l, u⟩ := exp_approach_between (29/100) (cC q) (x (Rv 2)) t (by norm_num) ht
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R, trajRs_R]
    simp only [phi, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [e3, show (3:ℕ) ≠ 0 by norm_num, show (3:ℕ) ≠ 1 by norm_num,
      show (3:ℕ) ≠ 2 by norm_num, if_false]
    have m1 : a1 q * t ≤ 1/200 := by nlinarith
    have m2 : a2 q * t ≤ 1/200 := by nlinarith
    have m4 : a4 q * t ≤ 9/1000 := by nlinarith
    have p1 : 0 ≤ a1 q * t := mul_nonneg r1.1 ht
    have p2 : 0 ≤ a2 q * t := mul_nonneg r2.1 ht
    have p4 : 0 ≤ a4 q * t := mul_nonneg r4.1 ht
    refine ⟨by linarith, ?_, by linarith, ?_, le_trans (le_min d4 rc.1) l,
      le_trans u (max_le d5 rc.2), by linarith, ?_⟩
    · rcases h1 with h | h
      · rw [h]; linarith
      · linarith
    · rcases h2 with h | h
      · rw [h]; linarith
      · linarith
    · rcases h4 with h | h
      · rw [h]; linarith
      · linarith

theorem mem (q : ℕ) (i : Fin 4) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ i

/-- A coordinate whose rate is `0` in phase `q` is constant along the run. -/
theorem frozen0 {q : ℕ} (hq : q < 4) {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW q).sys (modeW q).dom x t Φ) (i : Fin 4)
    (hz : ∀ s, Term.eval (fR q i) s = 0) : Φ t (Rv i) = x (Rv i) :=
  H.const (mem q i) (fun s _ => by rw [eval_unit_mul, hz])

/-- A coordinate moving at the constant rate `a` is at `x + a t` at the run's end. -/
theorem linear_at {q : ℕ} {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW q).sys (modeW q).dom x t Φ) (i : Fin 4) (a : ℝ)
    (ha : ∀ s, Term.eval (fR q i) s = a) : Φ t (Rv i) = x (Rv i) + a * t := by
  have h1 := H.rate_le (mem q i) a (fun s _ => by rw [eval_unit_mul, ha])
  have h2 := H.rate_ge (mem q i) a (fun s _ => by rw [eval_unit_mul, ha])
  linarith

/-- **Assumption 1 for `syringe_relay_prearm`**, every mode, Z3-free. -/
theorem syringe_relay_prearm_wellFormedR :
    WellFormedR Gr guardR (epsR syringe_relay_prearm_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- RUN1: `v1` rises by 0.05 t; RUN1 below 49.5, else TAKEUP2 (b < 1) or RUN2 (b ≥ 1)
    have hg' := (sat_g0 x).mp hg
    refine ⟨exists_run 0 (by norm_num) x hd (Or.inr hg'.1) (Or.inl (by simp [a2]))
      (Or.inl (by simp [a4])), ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := (sat_domR _).mp H.end_dom
    have hv2 := frozen0 (by norm_num) H 1 (fun s => by rw [f1_eval 0 (by norm_num)]; simp [a2])
    by_cases h495 : Φ t (Rv 0) < 99/2
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr
        ⟨h495, by rw [hv2]; exact hg'.2.1, e0, e1, e2, e3, e4, e5, e6, e7⟩⟩
    · by_cases hb : Φ t (Rv 3) < 1
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_g1 _).mpr
          ⟨by linarith, hb, by rw [hv2]; exact hg'.2.1, e0, e1, e2, e3, e4, e5, e6, e7⟩⟩
      · exact ⟨edgeW 0 2, edge_mem 0 2 (by decide), (sat_g2 _).mpr
          ⟨by linarith, by linarith, by rw [hv2]; linarith [hg'.2.1], e0, e1, e2, e3, e4, e5,
            e6, e7⟩⟩
  · -- TAKEUP2: the take-up rises; TAKEUP2 below 1, else RUN2
    have hg' := (sat_g1 x).mp hg
    refine ⟨exists_run 1 (by norm_num) x hd (Or.inl (by simp [a1])) (Or.inl (by simp [a2]))
      (Or.inr hg'.2.1), ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := (sat_domR _).mp H.end_dom
    have hv1 := frozen0 (by norm_num) H 0 (fun s => by rw [f0_eval 1 (by norm_num)]; simp [a1])
    have hv2 := frozen0 (by norm_num) H 1 (fun s => by rw [f1_eval 1 (by norm_num)]; simp [a2])
    by_cases hb : Φ t (Rv 3) < 1
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr
        ⟨by rw [hv1]; exact hg'.1, hb, by rw [hv2]; exact hg'.2.2.1, e0, e1, e2, e3, e4, e5, e6,
          e7⟩⟩
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide), (sat_g2 _).mpr
        ⟨by rw [hv1]; exact hg'.1, by linarith, by rw [hv2]; linarith [hg'.2.2.1], e0, e1, e2,
          e3, e4, e5, e6, e7⟩⟩
  · -- RUN2: `v2` rises by 0.05 t; RUN2 below 49.5, else END
    have hg' := (sat_g2 x).mp hg
    refine ⟨exists_run 2 (by norm_num) x hd (Or.inl (by simp [a1])) (Or.inr hg'.2.2.1)
      (Or.inl (by simp [a4])), ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := (sat_domR _).mp H.end_dom
    have hv1 := frozen0 (by norm_num) H 0 (fun s => by rw [f0_eval 2 (by norm_num)]; simp [a1])
    have hb := frozen0 (by norm_num) H 3 (fun s => by rw [f3_eval 2 (by norm_num)]; simp [a4])
    by_cases h495 : Φ t (Rv 1) < 99/2
    · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr
        ⟨by rw [hv1]; exact hg'.1, by rw [hb]; exact hg'.2.1, h495, e0, e1, e2, e3, e4, e5, e6,
          e7⟩⟩
    · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_g3 _).mpr
        ⟨by rw [hv1]; exact hg'.1, by linarith, e0, e1, e2, e3, e4, e5, e6, e7⟩⟩
  · -- END: the volumes are frozen
    have hg' := (sat_g3 x).mp hg
    refine ⟨exists_run 3 (by norm_num) x hd (Or.inl (by simp [a1])) (Or.inl (by simp [a2]))
      (Or.inl (by simp [a4])), ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := (sat_domR _).mp H.end_dom
    have hv1 := frozen0 (by norm_num) H 0 (fun s => by rw [f0_eval 3 (by norm_num)]; simp [a1])
    have hv2 := frozen0 (by norm_num) H 1 (fun s => by rw [f1_eval 3 (by norm_num)]; simp [a2])
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_g3 _).mpr
      ⟨by rw [hv1]; exact hg'.1, by rw [hv2]; exact hg'.2.1, e0, e1, e2, e3, e4, e5, e6, e7⟩⟩

end V2SyringeRelayPrearm
end RelCertifier
