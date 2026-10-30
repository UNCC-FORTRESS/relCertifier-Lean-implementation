/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `autoclave_liquid_steambank`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
four phases and their declared `next` lists), the lowered right guards, and `ε_r = 0.1` read
from the file.

The right model is the validated liquids cycle (four heating elements): the chamber temperature
`c` (coordinate 0), the load temperature `T` (coordinate 1) and the holding-time counter `t`
(coordinate 2), inside `20 ≤ c, T ≤ 138`, `t ≥ 0`. In every phase the load follows the chamber,
`T' = 0.1 (c − T)`; `HEAT` (`c < 122`, `t < 15`) `c' = 4`, `t' = 0`; `EQUIL`
(`122 ≤ c ≤ 124`, `T < 121`, `t < 15`) `c' = 0`, `t' = 0`; `EXPOSE` (`122 ≤ c ≤ 124`,
`T ≥ 121`, `t < 15`) `c' = 0`, `t' = 1`; `EXHAUST` (`t ≥ 15`) `c' = 0.1 (100 − c)`, `t' = 0`
(each guard with the domain).
* Existence (i): the chamber's closed form (`HEAT` the ramp `c₀ + 4 s`, which from `c₀ < 122`
  stays below `122.4` over `ε`; `EQUIL`, `EXPOSE` constant; `EXHAUST` the exponential approach
  to 100, between `c₀` and 100), the counter `t₀ + t' s`, and `T` the variation-of-constants
  solution forced by `0.1 c(s) ∈ [2, 13.8]` (`forcedSol`), which stays in
  `[min T₀ 20, max T₀ 138]` (`forcedSol_between`).
* (ii): `HEAT` (style (b), exit): the counter is constant (`t < 15` kept) and the chamber grows
  by at most `4 ε = 0.4` (`rate_le`), so it ends below 122 (`HEAT`) or in `[122, 124]`, where
  `T < 121` is `EQUIL` and `T ≥ 121` is `EXPOSE`; `EQUIL` (style (b)): chamber and counter
  constant, `T < 121` is `EQUIL`, `T ≥ 121` is `EXPOSE`; `EXPOSE` (style (b)): the chamber is
  constant, so on the run `T` is the linear coordinate `0.1 (c₀ − T)` and stays at or above
  `min T₀ c₀ ≥ 121` (`linear_between` on the domain pinned to `c = c₀`), so `t < 15` is
  `EXPOSE` and `t ≥ 15` is `EXHAUST`; `EXHAUST` (style (a)): the counter is constant, so
  `t ≥ 15` is kept.
Z3-free; modelled on `MoldingPackCheckring.lean` (forced coordinate) and
`FurnaceProgramTimebase.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.autoclave_liquid_steambank

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AutoclaveLiquidSteambank

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["c", "T", "t"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := autoclave_liquid_steambank_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

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
theorem hp_15_0 : Run.parseRat "15.0" = some (15 : ℚ) := by
  have h : parseQ "15.0" = some (⟨150, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_20_0 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_100_0 : Run.parseRat "100.0" = some (100 : ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_121_0 : Run.parseRat "121.0" = some (121 : ℚ) := by
  have h : parseQ "121.0" = some (⟨1210, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_122_0 : Run.parseRat "122.0" = some (122 : ℚ) := by
  have h : parseQ "122.0" = some (⟨1220, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_124_0 : Run.parseRat "124.0" = some (124 : ℚ) := by
  have h : parseQ "124.0" = some (⟨1240, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_138_0 : Run.parseRat "138.0" = some (138 : ℚ) := by
  have h : parseQ "138.0" = some (⟨1380, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

theorem fc0_eval (x : State (Var 3)) : Term.eval (fR 0 0) x = 4 := by
  simp [fR, hostDyn, mR, autoclave_liquid_steambank_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
    hp_0_1, hp_1_0, hp_4_0, hp_100_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp]

theorem fc1_eval (x : State (Var 3)) : Term.eval (fR 1 0) x = 0 := by
  simp [fR, hostDyn, mR, autoclave_liquid_steambank_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
    hp_0_1, hp_1_0, hp_4_0, hp_100_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp]

theorem fc2_eval (x : State (Var 3)) : Term.eval (fR 2 0) x = 0 := by
  simp [fR, hostDyn, mR, autoclave_liquid_steambank_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
    hp_0_1, hp_1_0, hp_4_0, hp_100_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp]

theorem fc3_eval (x : State (Var 3)) :
    Term.eval (fR 3 0) x = 1/10 * (100 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, autoclave_liquid_steambank_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
    hp_0_1, hp_1_0, hp_4_0, hp_100_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fT_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 1/10 * (x (Rv 0) - x (Rv 1)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, autoclave_liquid_steambank_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
      hp_0_1, hp_1_0, hp_4_0, hp_100_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

/-- The counter's rate: `1` in `EXPOSE`, `0` elsewhere. -/
noncomputable def tr (q : ℕ) : ℝ := if q = 2 then 1 else 0

theorem tr_nonneg (q : ℕ) : 0 ≤ tr q := by unfold tr; split_ifs <;> norm_num

theorem ft_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) : Term.eval (fR q 2) x = tr q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, autoclave_liquid_steambank_IRv2, vs, Run.dynOf, Run.lowerE, hp_0_0,
      hp_0_1, hp_1_0, hp_4_0, hp_100_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, tr]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (20 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 138 ∧ 20 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 138 ∧ 0 ≤ x (Rv 2)) := by
  simp only [domR, hostEvolve, mR, autoclave_liquid_steambank_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0_0, hp_20_0, hp_138_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (HEAT 0, EQUIL 1, EXPOSE 2, EXHAUST 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2), (2, 3), (3, 3)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  have hlen : q < 4 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 4 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 122 ∧ ν (Rv 2) < 15 ∧ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 138 ∧ 20 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 138 ∧ 0 ≤ ν (Rv 2)) := by
  simp [hostGuard, mR, autoclave_liquid_steambank_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_15_0,
    hp_20_0, hp_121_0, hp_122_0, hp_124_0, hp_138_0, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (122 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 124 ∧ ν (Rv 1) < 121 ∧ ν (Rv 2) < 15 ∧ 20 ≤ ν (Rv 0) ∧
        ν (Rv 0) ≤ 138 ∧ 20 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 138 ∧ 0 ≤ ν (Rv 2)) := by
  simp [hostGuard, mR, autoclave_liquid_steambank_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_15_0,
    hp_20_0, hp_121_0, hp_122_0, hp_124_0, hp_138_0, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      (122 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 124 ∧ 121 ≤ ν (Rv 1) ∧ ν (Rv 2) < 15 ∧ 20 ≤ ν (Rv 0) ∧
        ν (Rv 0) ≤ 138 ∧ 20 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 138 ∧ 0 ≤ ν (Rv 2)) := by
  simp [hostGuard, mR, autoclave_liquid_steambank_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_15_0,
    hp_20_0, hp_121_0, hp_122_0, hp_124_0, hp_138_0, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔
      (15 ≤ ν (Rv 2) ∧ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 138 ∧ 20 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 138 ∧
        0 ≤ ν (Rv 2)) := by
  simp [hostGuard, mR, autoclave_liquid_steambank_IRv2, Run.lowerF, Run.lowerE, hp_0_0, hp_15_0,
    hp_20_0, hp_121_0, hp_122_0, hp_124_0, hp_138_0, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR autoclave_liquid_steambank_IRv2 = 1/10 := by
  simp [epsR, autoclave_liquid_steambank_IRv2, hp_0_1]

/-! ## Existence: the explicit runs -/

/-- The chamber temperature of phase `q` from `c₀`: the ramp in `HEAT`, the exponential
approach to 100 in `EXHAUST`, held otherwise. -/
noncomputable def cS (q : ℕ) (c0 u : ℝ) : ℝ :=
  if q = 0 then c0 + 4 * u
  else if q = 3 then 100 + (c0 - 100) * Real.exp (-(1/10 * u))
  else c0

theorem cS_cont (q : ℕ) (c0 : ℝ) : Continuous (cS q c0) := by
  unfold cS; split_ifs <;> fun_prop

theorem FS_cont (q : ℕ) (c0 : ℝ) : Continuous (fun u => 1/10 * cS q c0 u) :=
  continuous_const.mul (cS_cont q c0)

/-- The run of phase `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (u : ℝ) : ℝ :=
  if i.val = 0 then cS q (x (Rv 0)) u
  else if i.val = 1 then forcedSol (1/10) (x (Rv 1)) (fun s => 1/10 * cS q (x (Rv 0)) s) u
  else x (Rv 2) + tr q * u

theorem phi_zero (q : ℕ) (x : State (Var 3)) : phi q x 0 = cS q (x (Rv 0)) := by
  funext u; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 3)) :
    phi q x 1 = forcedSol (1/10) (x (Rv 1)) (fun s => 1/10 * cS q (x (Rv 0)) s) := by
  funext u; simp [phi]

theorem phi_two (q : ℕ) (x : State (Var 3)) : phi q x 2 = fun u => x (Rv 2) + tr q * u := by
  funext u; simp [phi]

theorem phi_der (q : ℕ) (hq : q < 4) (x : State (Var 3)) (i : Fin 3) (u : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) u)) u := by
  match i with
  | 0 =>
      rw [phi_zero]
      interval_cases q
      · rw [fc0_eval]
        have hf : cS 0 (x (Rv 0)) = fun s => x (Rv 0) + 4 * s := by funext s; simp [cS]
        rw [hf]
        simpa using ((hasDerivAt_id u).const_mul (4:ℝ)).const_add (x (Rv 0))
      · rw [fc1_eval]
        have hf : cS 1 (x (Rv 0)) = fun _ => x (Rv 0) := by funext s; simp [cS]
        rw [hf]; exact hasDerivAt_const u _
      · rw [fc2_eval]
        have hf : cS 2 (x (Rv 0)) = fun _ => x (Rv 0) := by funext s; simp [cS]
        rw [hf]; exact hasDerivAt_const u _
      · rw [fc3_eval, trajRs_R, phi_zero]
        have hf : cS 3 (x (Rv 0)) = fun s => 100 + (x (Rv 0) - 100) * Real.exp (-(1/10 * s)) := by
          funext s; simp [cS]
        rw [hf]
        exact hasDerivAt_expApproach (1/10) 100 (x (Rv 0)) u
  | 1 =>
      rw [fT_eval q hq, trajRs_R, trajRs_R, phi_zero, phi_one]
      exact (forcedSol_hasDerivAt (1/10) (x (Rv 1)) (FS_cont q (x (Rv 0))) u).congr_deriv
        (by ring)
  | 2 =>
      rw [ft_eval q hq, phi_two]
      simpa using ((hasDerivAt_id u).const_mul (tr q)).const_add (x (Rv 2))

/-- The chamber stays in `[20, 138]` over `ε = 0.1` (in `HEAT` from below 122). -/
theorem cS_box (q : ℕ) (hq : q < 4) (c0 u : ℝ) (h0 : 20 ≤ c0) (h1 : c0 ≤ 138)
    (hh : q = 0 → c0 < 122) (hu : 0 ≤ u) (hue : u ≤ 1/10) :
    20 ≤ cS q c0 u ∧ cS q c0 u ≤ 138 := by
  interval_cases q
  · have h := hh rfl
    have e : cS 0 c0 u = c0 + 4 * u := by simp [cS]
    rw [e]; constructor <;> linarith
  · have e : cS 1 c0 u = c0 := by simp [cS]
    rw [e]; exact ⟨h0, h1⟩
  · have e : cS 2 c0 u = c0 := by simp [cS]
    rw [e]; exact ⟨h0, h1⟩
  · have e : cS 3 c0 u = 100 + (c0 - 100) * Real.exp (-(1/10 * u)) := by simp [cS]
    obtain ⟨l, r⟩ := exp_approach_between (1/10) 100 c0 u (by norm_num) hu
    rw [e]
    exact ⟨le_trans (le_min h0 (by norm_num)) l, le_trans r (max_le h1 (by norm_num))⟩

theorem exists_run (q : ℕ) (hq : q < 4) (x : State (Var 3)) (hd : Formula.sat domR x)
    (hh : q = 0 → x (Rv 0) < 122) :
    ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x (1/10) Φ := by
  obtain ⟨a0, a1, b0, b1, t0⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phi q x) (1/10) (by norm_num) (fun i => ?_)
    (fun i u _ _ => phi_der q hq x i u) (fun u hu hue => ?_)⟩
  · match i with
    | 0 => rw [phi_zero]; interval_cases q <;> simp [cS]
    | 1 => rw [phi_one, forcedSol_zero]
    | 2 => rw [phi_two]; simp
  · -- the forcing `0.1 c(s)` stays in `[2, 13.8]`
    have hT := forcedSol_between (1/10) (x (Rv 1)) (FS_cont q (x (Rv 0)))
      (lo := 2) (hi := 138/10) (T := 1/10) (by norm_num) (fun s hs => by
        have := cS_box q hq (x (Rv 0)) s a0 a1 hh hs.1 hs.2
        show 2 ≤ 1/10 * cS q (x (Rv 0)) s ∧ 1/10 * cS q (x (Rv 0)) s ≤ 138/10
        constructor <;> linarith [this.1, this.2]) u ⟨hu, hue⟩
    have e1 : (2 : ℝ) / (1/10) = 20 := by norm_num
    have e2 : (138/10 : ℝ) / (1/10) = 138 := by norm_num
    rw [e1, e2] at hT
    obtain ⟨c0, c1⟩ := cS_box q hq (x (Rv 0)) u a0 a1 hh hu hue
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R, phi_zero, phi_one, phi_two]
    exact ⟨c0, c1, le_trans (le_min b0 le_rfl) hT.1, le_trans hT.2 (max_le b1 le_rfl),
      add_nonneg t0 (mul_nonneg (tr_nonneg q) hu)⟩

theorem memR (q : ℕ) (i : Fin 3) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ i

/-! ## Completeness: the end states -/

/-- `EXPOSE`'s load stays at or above `min T₀ c₀`: the chamber is held along the run, so on the
domain pinned to `c = c₀` the load is the linear coordinate `0.1 (c₀ − T)`. -/
theorem expose_T (x : State (Var 3)) {r : ℝ} {Φ : ℝ → State (Var 3)}
    (H : ODESol (modeW 2).sys domR x r Φ) : min (x (Rv 1)) (x (Rv 0)) ≤ Φ r (Rv 1) := by
  have hc : ∀ u ∈ Icc (0:ℝ) r, Φ u (Rv 0) = x (Rv 0) := fun u hu =>
    (H.restrict hu.1 hu.2).const (memR 2 0) (fun s _ => by rw [eval_unit_mul, fc2_eval])
  have H' : ODESol (modeW 2).sys
      (Formula.and domR (Formula.cmp .eq (Term.var (Rv 0)) (Term.const (x (Rv 0))))) x r Φ :=
    ⟨H.hr, H.hΦ0, H.hder, H.hmask, fun u hu => ⟨H.hdom u hu, by
      simp [Formula.sat, CompOp.interp, Term.eval, hc u hu]⟩⟩
  exact (H'.linear_between (memR 2 1) (1/10) (x (Rv 0)) (by norm_num) (fun s hs => by
    have hs2 : s (Rv 0) = x (Rv 0) := by
      simpa [Formula.sat, CompOp.interp, Term.eval] using hs.2
    rw [eval_unit_mul, fT_eval 2 (by norm_num), hs2])).1

/-- **Assumption 1 for `autoclave_liquid_steambank`**, every mode, Z3-free. -/
theorem autoclave_liquid_steambank_wellFormedR :
    WellFormedR Gr guardR (epsR autoclave_liquid_steambank_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- HEAT: the counter is held, the chamber grows by at most 0.4: HEAT below 122, then
    -- EQUIL (T < 121) or EXPOSE (T ≥ 121) inside [122, 124]
    have hg0 := (sat_guard0 x).mp hg
    refine ⟨exists_run 0 (by norm_num) x hd (fun _ => hg0.1), ?_⟩
    intro r Φ hr H
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    have ht := H.const (memR 0 2) (fun s _ => by
      rw [eval_unit_mul, ft_eval 0 (by norm_num)]; simp [tr])
    have hc := H.rate_le (memR 0 0) 4 (fun s _ => by rw [eval_unit_mul, fc0_eval])
    have h15 : Φ r (Rv 2) < 15 := by rw [ht]; exact hg0.2.1
    by_cases h122 : Φ r (Rv 0) < 122
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
        (sat_guard0 _).mpr ⟨h122, h15, e0, e1, e2, e3, e4⟩⟩
    · have h124 : Φ r (Rv 0) ≤ 124 := by linarith [hg0.1]
      by_cases h121 : Φ r (Rv 1) < 121
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
          (sat_guard1 _).mpr ⟨by linarith, h124, h121, h15, e0, e1, e2, e3, e4⟩⟩
      · exact ⟨edgeW 0 2, edge_mem 0 2 (by decide),
          (sat_guard2 _).mpr ⟨by linarith, h124, by linarith, h15, e0, e1, e2, e3, e4⟩⟩
  · -- EQUIL: chamber and counter held: EQUIL (T < 121) or EXPOSE (T ≥ 121)
    have hg1 := (sat_guard1 x).mp hg
    refine ⟨exists_run 1 (by norm_num) x hd (fun h => absurd h (by norm_num)), ?_⟩
    intro r Φ hr H
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    have ht := H.const (memR 1 2) (fun s _ => by
      rw [eval_unit_mul, ft_eval 1 (by norm_num)]; simp [tr])
    have hc := H.const (memR 1 0) (fun s _ => by rw [eval_unit_mul, fc1_eval])
    have hc0 : 122 ≤ Φ r (Rv 0) := by rw [hc]; exact hg1.1
    have hc1 : Φ r (Rv 0) ≤ 124 := by rw [hc]; exact hg1.2.1
    have h15 : Φ r (Rv 2) < 15 := by rw [ht]; exact hg1.2.2.2.1
    by_cases h121 : Φ r (Rv 1) < 121
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
        (sat_guard1 _).mpr ⟨hc0, hc1, h121, h15, e0, e1, e2, e3, e4⟩⟩
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
        (sat_guard2 _).mpr ⟨hc0, hc1, by linarith, h15, e0, e1, e2, e3, e4⟩⟩
  · -- EXPOSE: chamber held, load kept at or above 121: EXPOSE (t < 15) or EXHAUST (t ≥ 15)
    have hg2 := (sat_guard2 x).mp hg
    refine ⟨exists_run 2 (by norm_num) x hd (fun h => absurd h (by norm_num)), ?_⟩
    intro r Φ hr H
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    have hc := H.const (memR 2 0) (fun s _ => by rw [eval_unit_mul, fc2_eval])
    have hc0 : 122 ≤ Φ r (Rv 0) := by rw [hc]; exact hg2.1
    have hc1 : Φ r (Rv 0) ≤ 124 := by rw [hc]; exact hg2.2.1
    have hT : 121 ≤ Φ r (Rv 1) :=
      le_trans (le_min hg2.2.2.1 (by linarith [hg2.1])) (expose_T x H)
    by_cases h15 : Φ r (Rv 2) < 15
    · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide),
        (sat_guard2 _).mpr ⟨hc0, hc1, hT, h15, e0, e1, e2, e3, e4⟩⟩
    · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide),
        (sat_guard3 _).mpr ⟨by linarith, e0, e1, e2, e3, e4⟩⟩
  · -- EXHAUST: the counter is held, so `t ≥ 15` is kept
    have hg3 := (sat_guard3 x).mp hg
    refine ⟨exists_run 3 (by norm_num) x hd (fun h => absurd h (by norm_num)), ?_⟩
    intro r Φ hr H
    obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
    have ht := H.const (memR 3 2) (fun s _ => by
      rw [eval_unit_mul, ft_eval 3 (by norm_num)]; simp [tr])
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide),
      (sat_guard3 _).mpr ⟨by rw [ht]; exact hg3.1, e0, e1, e2, e3, e4⟩⟩

end V2AutoclaveLiquidSteambank
end RelCertifier
