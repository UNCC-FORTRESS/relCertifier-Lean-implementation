/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `reactor_feed_wireless`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
four feed levels and their declared `next` lists), the lowered right guards, and `ε_r = 1`
read from the file.

The right model is the validated feed interlock of the exothermic reactor: the reactor
temperature `T` (coordinate 0) relaxes toward the level's rise above the cooling-water supply
temperature `p` (coordinate 1, constant), `T' = k ((p + r) − T)`, `k = 0.1` (time constant
10 min), `r = 4, 8, 12, 16` (`F1` to `F4`), every level inside `15 ≤ T ≤ 60`, `15 ≤ p ≤ 35`.
Guards: `F1` `T < 25`, `F2` `25 ≤ T < 35`, `F3` `35 ≤ T ≤ 45`, `F4` `T > 45` (each with the
domain).
* Existence (i), every level: the explicit exponential `(p₀ + r) + (T₀ − p₀ − r) e^{−k t}`
  with `p` held (`trajRs_sol`), between `T₀` and `p₀ + r ∈ [19, 51]`, inside the domain.
* (ii), every level: every level declares every level, and the four guards cover the domain
  (`T < 25`, `[25, 35)`, `[35, 45]`, `T > 45`), so the end state of any run (in the domain) is
  in one of them.
Z3-free; modelled on `FuelcellChpDos.lean` (at dimension 2, no padding coordinate).
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.reactor_feed_wireless

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ReactorFeedWireless

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["T", "p"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := reactor_feed_wireless_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_4_0 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_8_0 : Run.parseRat "8.0" = some (8 : ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_12_0 : Run.parseRat "12.0" = some (12 : ℚ) := by
  have h : parseQ "12.0" = some (⟨120, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_16_0 : Run.parseRat "16.0" = some (16 : ℚ) := by
  have h : parseQ "16.0" = some (⟨160, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_15_0 : Run.parseRat "15.0" = some (15 : ℚ) := by
  have h : parseQ "15.0" = some (⟨150, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_25_0 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_35_0 : Run.parseRat "35.0" = some (35 : ℚ) := by
  have h : parseQ "35.0" = some (⟨350, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_45_0 : Run.parseRat "45.0" = some (45 : ℚ) := by
  have h : parseQ "45.0" = some (⟨450, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_60_0 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The thermal rate `1 / 10` as written, `0.1`. -/
noncomputable def kR : ℝ := 1 / 10

/-- The level's rise above the cooling water: `F1` 4, `F2` 8, `F3` 12, `F4` 16. -/
noncomputable def rR (q : ℕ) : ℝ := if q = 0 then 4 else if q = 1 then 8 else if q = 2 then 12 else 16

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR * ((x (Rv 1) + rR q) - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, reactor_feed_wireless_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_1,
      hp_4_0, hp_8_0, hp_12_0, hp_16_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, kR, rR]

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) : Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, reactor_feed_wireless_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0, hp_0_1,
      hp_4_0, hp_8_0, hp_12_0, hp_16_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (15 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60 ∧ 15 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 35) := by
  simp only [domR, hostEvolve, mR, reactor_feed_wireless_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_15_0, hp_35_0, hp_60_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (F1 0, F2 1, F3 2, F4 3): every level declares every
level. -/
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
      (ν (Rv 0) < 25 ∧ 15 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 60 ∧ 15 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 35) := by
  simp [hostGuard, mR, reactor_feed_wireless_IRv2, Run.lowerF, Run.lowerE, hp_15_0, hp_25_0,
    hp_35_0, hp_45_0, hp_60_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔
      (25 ≤ ν (Rv 0) ∧ ν (Rv 0) < 35 ∧ 15 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 60 ∧ 15 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 35) := by
  simp [hostGuard, mR, reactor_feed_wireless_IRv2, Run.lowerF, Run.lowerE, hp_15_0, hp_25_0,
    hp_35_0, hp_45_0, hp_60_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 2)) ν ↔
      (35 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 45 ∧ 15 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 60 ∧ 15 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 35) := by
  simp [hostGuard, mR, reactor_feed_wireless_IRv2, Run.lowerF, Run.lowerE, hp_15_0, hp_25_0,
    hp_35_0, hp_45_0, hp_60_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard3 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 3)) ν ↔
      (45 < ν (Rv 0) ∧ 15 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 60 ∧ 15 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 35) := by
  simp [hostGuard, mR, reactor_feed_wireless_IRv2, Run.lowerF, Run.lowerE, hp_15_0, hp_25_0,
    hp_35_0, hp_45_0, hp_60_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR reactor_feed_wireless_IRv2 = 1 := by
  simp [epsR, reactor_feed_wireless_IRv2, hp_1_0]

/-! ## Existence: the explicit run -/

/-- The run of level `q` from `x`: `T` approaches `p₀ + r`, `p` stays. -/
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

theorem exists_run (q : ℕ) (hq : q < 4) (x : State (Var 2)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  have hr : 4 ≤ rR q ∧ rR q ≤ 16 := by unfold rR; split_ifs <;> norm_num
  have hk : 0 ≤ kR := by unfold kR; norm_num
  refine ⟨_, trajRs_sol x (phi q x) ε hε (phi_init q x) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht _ => ?_)⟩
  obtain ⟨s1, s2⟩ := exp_approach_between kR (x (Rv 1) + rR q) (x (Rv 0)) t hk ht
  rw [sat_domR, trajRs_R, trajRs_R, phi_zero, phi_one]
  exact ⟨le_trans (le_min a0 (by linarith)) s1, le_trans s2 (max_le a1 (by linarith)), b0, b1⟩

/-- **Assumption 1 for `reactor_feed_wireless`**, every mode, Z3-free. -/
theorem reactor_feed_wireless_wellFormedR :
    WellFormedR Gr guardR (epsR reactor_feed_wireless_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq4 x hd 1 (by norm_num), ?_⟩
  -- the four guards cover the domain; every level declares every level
  intro t Φ _ H
  obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
  by_cases h25 : Φ t (Rv 0) < 25
  · exact ⟨edgeW q 0, edge_mem q 0 (by interval_cases q <;> decide),
      (sat_guard0 _).mpr ⟨h25, e0, e1, e2, e3⟩⟩
  · by_cases h35 : Φ t (Rv 0) < 35
    · exact ⟨edgeW q 1, edge_mem q 1 (by interval_cases q <;> decide),
        (sat_guard1 _).mpr ⟨by linarith, h35, e0, e1, e2, e3⟩⟩
    · by_cases h45 : Φ t (Rv 0) ≤ 45
      · exact ⟨edgeW q 2, edge_mem q 2 (by interval_cases q <;> decide),
          (sat_guard2 _).mpr ⟨by linarith, h45, e0, e1, e2, e3⟩⟩
      · exact ⟨edgeW q 3, edge_mem q 3 (by interval_cases q <;> decide),
          (sat_guard3 _).mpr ⟨by linarith, e0, e1, e2, e3⟩⟩

end V2ReactorFeedWireless
end RelCertifier
