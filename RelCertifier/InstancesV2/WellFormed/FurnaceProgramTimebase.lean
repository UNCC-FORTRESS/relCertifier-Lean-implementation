/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `furnace_program_timebase`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three program segments and their declared `next` lists), the lowered right guards, and
`ε_r = 1` read from the file.

The right model is the validated heat-treatment program: the program set point `s`
(coordinate 0) and the load temperature `T` (coordinate 1), inside `20 ≤ s, T ≤ 900`. Every
segment moves the set point toward its target, `s' = a (c − s)` (`PREHEAT` `0.01`, 650;
`HEAT` `0.01`, 870; `SOAK` `0.1`, 870), and the load follows it, `T' = 0.2 (s − T)`. Guards:
`PREHEAT` `s < 640`, `HEAT` `640 ≤ s < 860`, `SOAK` `860 ≤ s ≤ 870` (each with the domain).
* Existence (i): the exponential approach of `s` (between `s₀` and its target, in the domain)
  and `T` the variation-of-constants solution forced by `0.2 s(t) ∈ [4, 180]` (`forcedSol`),
  which stays in `[min T₀ 20, max T₀ 900]` (`forcedSol_between`).
* (ii): the set point rises toward the segment's target (`linear_up`): `PREHEAT` ends in
  `[s₀, 650]`, inside `PREHEAT` (below 640) or `HEAT` (from 640; style (b), exit); `HEAT` ends
  in `[s₀, 870]`, inside `HEAT` or `SOAK` (style (b)); `SOAK` ends in `[860, 870]` (style (a)).
Z3-free; modelled on `MoldingPackCheckring.lean` and `TurbineStartupGearratio.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.furnace_program_timebase

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2FurnaceProgramTimebase

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["s", "T"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := furnace_program_timebase_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0_01 : Run.parseRat "0.01" = some ((1:ℚ)/100) := by
  have h : parseQ "0.01" = some (⟨1, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_2 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_20_0 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_640_0 : Run.parseRat "640.0" = some (640 : ℚ) := by
  have h : parseQ "640.0" = some (⟨6400, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_650_0 : Run.parseRat "650.0" = some (650 : ℚ) := by
  have h : parseQ "650.0" = some (⟨6500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_860_0 : Run.parseRat "860.0" = some (860 : ℚ) := by
  have h : parseQ "860.0" = some (⟨8600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_870_0 : Run.parseRat "870.0" = some (870 : ℚ) := by
  have h : parseQ "870.0" = some (⟨8700, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_900_0 : Run.parseRat "900.0" = some (900 : ℚ) := by
  have h : parseQ "900.0" = some (⟨9000, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- Set-point rates: `PREHEAT`, `HEAT` 0.01, `SOAK` 0.1. -/
noncomputable def aR (q : ℕ) : ℝ := if q = 2 then 1/10 else 1/100

/-- Set-point targets: `PREHEAT` 650, `HEAT` and `SOAK` 870. -/
noncomputable def cR (q : ℕ) : ℝ := if q = 0 then 650 else 870

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 0) x = aR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, furnace_program_timebase_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_01, hp_0_1, hp_0_2, hp_20_0, hp_640_0, hp_650_0, hp_860_0, hp_870_0, hp_900_0, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, aR, cR]

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 1/5 * x (Rv 0) - 1/5 * x (Rv 1) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, furnace_program_timebase_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_01, hp_0_1, hp_0_2, hp_20_0, hp_640_0, hp_650_0, hp_860_0, hp_870_0, hp_900_0, hp_1_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv] <;> ring

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (20 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 900 ∧ 20 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 900) := by
  simp only [domR, hostEvolve, mR, furnace_program_timebase_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_01, hp_0_1, hp_0_2, hp_20_0, hp_640_0, hp_650_0, hp_860_0, hp_870_0, hp_900_0, hp_1_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (PREHEAT 0, HEAT 1, SOAK 2). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  have hlen : q < 3 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 3 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 640 ∧ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 900 ∧ 20 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 900) := by
  simp [hostGuard, mR, furnace_program_timebase_IRv2, Run.lowerF, Run.lowerE, hp_0_01, hp_0_1, hp_0_2, hp_20_0, hp_640_0, hp_650_0, hp_860_0, hp_870_0, hp_900_0, hp_1_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔
      (640 ≤ ν (Rv 0) ∧ ν (Rv 0) < 860 ∧ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 900 ∧ 20 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 900) := by
  simp [hostGuard, mR, furnace_program_timebase_IRv2, Run.lowerF, Run.lowerE, hp_0_01, hp_0_1, hp_0_2, hp_20_0, hp_640_0, hp_650_0, hp_860_0, hp_870_0, hp_900_0, hp_1_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 2)) ν ↔
      (860 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 870 ∧ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 900 ∧ 20 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 900) := by
  simp [hostGuard, mR, furnace_program_timebase_IRv2, Run.lowerF, Run.lowerE, hp_0_01, hp_0_1, hp_0_2, hp_20_0, hp_640_0, hp_650_0, hp_860_0, hp_870_0, hp_900_0, hp_1_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR furnace_program_timebase_IRv2 = 1 := by
  simp [epsR, furnace_program_timebase_IRv2, hp_1_0]

/-! ## Existence: the explicit run -/

/-- The set point of segment `q` from `s₀`. -/
noncomputable def sSol (q : ℕ) (s0 t : ℝ) : ℝ := cR q + (s0 - cR q) * Real.exp (-(aR q * t))

theorem sSol_cont (q : ℕ) (s0 : ℝ) : Continuous (sSol q s0) := by unfold sSol; fun_prop

theorem FS_cont (q : ℕ) (s0 : ℝ) : Continuous (fun u => 1/5 * sSol q s0 u) :=
  continuous_const.mul (sSol_cont q s0)

/-- The run of segment `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 2)) (i : Fin 2) (t : ℝ) : ℝ :=
  if i.val = 0 then sSol q (x (Rv 0)) t
  else forcedSol (1/5) (x (Rv 1)) (fun u => 1/5 * sSol q (x (Rv 0)) u) t

theorem phi_zero (q : ℕ) (x : State (Var 2)) : phi q x 0 = sSol q (x (Rv 0)) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 2)) :
    phi q x 1 = forcedSol (1/5) (x (Rv 1)) (fun u => 1/5 * sSol q (x (Rv 0)) u) := by
  funext t; simp [phi]

theorem phi_der (q : ℕ) (hq : q < 3) (x : State (Var 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, trajRs_R, phi_zero]
      exact hasDerivAt_expApproach (aR q) (cR q) (x (Rv 0)) t
  | 1 =>
      rw [fR1_eval q hq, trajRs_R, trajRs_R, phi_zero, phi_one]
      exact (forcedSol_hasDerivAt (1/5) (x (Rv 1)) (FS_cont q (x (Rv 0))) t).congr_deriv
        (by ring)

theorem sSol_box (q : ℕ) (s0 t : ℝ) (h0 : 20 ≤ s0) (h1 : s0 ≤ 900) (ht : 0 ≤ t) :
    20 ≤ sSol q s0 t ∧ sSol q s0 t ≤ 900 := by
  have hc : 20 ≤ cR q ∧ cR q ≤ 900 := by unfold cR; split_ifs <;> norm_num
  have ha : 0 ≤ aR q := by unfold aR; split_ifs <;> norm_num
  obtain ⟨l, u⟩ := exp_approach_between (aR q) (cR q) s0 t ha ht
  exact ⟨le_trans (le_min h0 hc.1) l, le_trans u (max_le h1 hc.2)⟩

theorem exists_run (q : ℕ) (hq : q < 3) (x : State (Var 2)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phi q x) ε hε (fun i => ?_) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht hte => ?_)⟩
  · match i with
    | 0 => rw [phi_zero]; simp [sSol]
    | 1 => rw [phi_one, forcedSol_zero]
  · have hT := forcedSol_between (1/5) (x (Rv 1)) (FS_cont q (x (Rv 0)))
      (lo := 4) (hi := 180) (T := ε) (by norm_num) (fun u hu => by
        have := sSol_box q (x (Rv 0)) u a0 a1 hu.1
        show 4 ≤ 1/5 * sSol q (x (Rv 0)) u ∧ 1/5 * sSol q (x (Rv 0)) u ≤ 180
        constructor <;> linarith [this.1, this.2]) t ⟨ht, hte⟩
    have e1 : (4 : ℝ) / (1/5) = 20 := by norm_num
    have e2 : (180 : ℝ) / (1/5) = 900 := by norm_num
    rw [e1, e2] at hT
    obtain ⟨c0, c1⟩ := sSol_box q (x (Rv 0)) t a0 a1 ht
    rw [sat_domR, trajRs_R, trajRs_R, phi_zero, phi_one]
    exact ⟨c0, c1, le_trans (le_min b0 le_rfl) hT.1, le_trans hT.2 (max_le b1 le_rfl)⟩

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `furnace_program_timebase`**, every mode, Z3-free. -/
theorem furnace_program_timebase_wellFormedR :
    WellFormedR Gr guardR (epsR furnace_program_timebase_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq3 x hd 1 (by norm_num), ?_⟩
  intro t Φ _ H
  have hf : ∀ s, Formula.sat (modeW q).dom s →
      Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = aR q * (cR q - s (Rv 0)) :=
    fun s _ => by rw [eval_unit_mul, fR0_eval q hq3]
  have ha : 0 ≤ aR q := by unfold aR; split_ifs <;> norm_num
  obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
  interval_cases q
  · -- PREHEAT: rises toward 650 from below 640: PREHEAT below 640, HEAT from 640
    have hg0 := (sat_guard0 x).mp hg
    have hu := H.linear_up (memR 0) _ _ ha hf (by norm_num [cR]; linarith [hg0.1])
    rw [show cR 0 = 650 by norm_num [cR]] at hu
    by_cases h640 : Φ t (Rv 0) < 640
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨h640, e0, e1, e2, e3⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, by linarith, e0, e1, e2, e3⟩⟩
  · -- HEAT: rises toward 870 from [640, 860): HEAT below 860, SOAK from 860
    have hg1 := (sat_guard1 x).mp hg
    have hu := H.linear_up (memR 1) _ _ ha hf (by norm_num [cR]; linarith [hg1.2.1])
    rw [show cR 1 = 870 by norm_num [cR]] at hu
    by_cases h860 : Φ t (Rv 0) < 860
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith [hg1.1], h860, e0, e1, e2, e3⟩⟩
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
        (sat_guard2 _).mpr ⟨by linarith, by linarith, e0, e1, e2, e3⟩⟩
  · -- SOAK: inside [860, 870] the set point stays between its start and 870
    have hg2 := (sat_guard2 x).mp hg
    have hu := H.linear_up (memR 2) _ _ ha hf (by norm_num [cR]; linarith [hg2.2.1])
    rw [show cR 2 = 870 by norm_num [cR]] at hu
    exact ⟨edgeW 2 2, edge_mem 2 2 (by decide),
      (sat_guard2 _).mpr ⟨by linarith [hg2.1], hu.2, e0, e1, e2, e3⟩⟩

end V2FurnaceProgramTimebase
end RelCertifier
