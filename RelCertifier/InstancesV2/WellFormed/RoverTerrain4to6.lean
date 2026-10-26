/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_4to6`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (the file's three terrains `MUD`, `GRAVEL`, `PAVED` and
their declared `next` lists), the lowered right guards, `ε_r = 1`. The right is the
soil-level rover (the chain's 4-coordinate model; motor torque `u` and heave `zh` pinned):
per terrain `T`, `v' = μ_T (w − v) − r_T v − zs`, `s' = v`, `w' = 3 (c_T − w)`,
`zs' = 2 (Z_T − zs)`, `u' = zh' = 0`; the guards are the odometer bands `[0, 5)`, `[5, 12)`,
`[12, ∞)` with the wheel cap `w ≤ c_T` (`c_T` = 0.25, 0.45, 0.7).
`wellFormedR_terrain` (clause (ii): the cap is kept by the contraction `w' = 3 (c_T − w)` and
`0 ≤ s' = v ≤ 0.8`, so a `MUD` run ends in `MUD` or `GRAVEL`, a `GRAVEL` run in `GRAVEL` or
`PAVED`, `PAVED` is forward invariant). Existence: the explicit run of the affine cascade
`w, zs → v → s` (`forcedSol`, `intSol`), kept in the evolve box by the comparison bounds
(`forcedSol_between`: `w` between its start and `c_T`, `zs` between its start and `Z_T`, `v`
between `min v₀ ((0.15 μ_T − 0.12)/(μ_T + r_T)) ≥ 0` and `max v₀ (0.8 μ_T/(μ_T + r_T)) ≤ 0.8`).
Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_terrain_4to6
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverTerrain4to6Pins

open Parse

/-! Parse pins of the numerals the right guards, fields and domain of `rover_terrain_4to6` write. -/

theorem gp_0 : Run.parseRat "0" = some (0:ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_03 : Run.parseRat "0.03" = some ((3:ℚ)/100) := by
  have h : parseQ "0.03" = some (⟨3, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_12 : Run.parseRat "0.12" = some ((3:ℚ)/25) := by
  have h : parseQ "0.12" = some (⟨12, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_15 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_25 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_4 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_45 : Run.parseRat "0.45" = some ((9:ℚ)/20) := by
  have h : parseQ "0.45" = some (⟨45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_7 : Run.parseRat "0.7" = some ((7:ℚ)/10) := by
  have h : parseQ "0.7" = some (⟨7, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_8 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2 : Run.parseRat "2" = some (2:ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2_5 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3 : Run.parseRat "3" = some (3:ℚ) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_4_0 : Run.parseRat "4.0" = some (4:ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_5_0 : Run.parseRat "5.0" = some (5:ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_8_0 : Run.parseRat "8.0" = some (8:ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_12_0 : Run.parseRat "12.0" = some (12:ℚ) := by
  have h : parseQ "12.0" = some (⟨120, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num


end RoverTerrain4to6Pins

namespace RoverTerrain4to6Modal

open DL DLCalTiming DLRel Parse Set RoverTerrain4to6Pins

def vsR : List String := ["v", "s", "w", "zs", "u", "zh"]

def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRR (q : ℕ) : Parse.PMode := rover_terrain_4to6_IRv2.R.modes.getD q dummyR

noncomputable def fRR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vsR 6 Side.R (mRR q)

noncomputable def domRR : Formula (Var 6) := hostEvolve vsR 6 Side.R (mRR 0)

noncomputable def modeR (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

/-- The terrain constants: wheel set point `c_T`, traction stiffness `μ_T`, drag `r_T`,
equilibrium sinkage `Z_T`. -/
noncomputable def cT (q : ℕ) : ℝ := if q = 0 then 1/4 else if q = 1 then 9/20 else 7/10
noncomputable def muT (q : ℕ) : ℝ := if q = 0 then 5/2 else if q = 1 then 4 else 8
noncomputable def rT (q : ℕ) : ℝ := if q = 0 then 2/5 else if q = 1 then 3/20 else 1/20
noncomputable def ZT (q : ℕ) : ℝ := if q = 0 then 1/10 else if q = 1 then 3/100 else 0

theorem fRR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 0) x = muT q * (x (Rv 2) - x (Rv 0)) - rT q * x (Rv 0) - x (Rv 3) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_4to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT, muT, rT, ZT]

theorem fRR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_4to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT, muT, rT, ZT]

theorem fRR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 2) x = 3 * (cT q - x (Rv 2)) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_4to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT, muT, rT, ZT]

theorem fRR3_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 3) x = 2 * (ZT q - x (Rv 3)) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_4to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT, muT, rT, ZT]

theorem fRR4_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 4) x = 0 := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_4to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT, muT, rT, ZT]

theorem fRR5_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 5) x = 0 := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_4to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT, muT, rT, ZT]

theorem sat_domRR (x : State (Var 6)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 4/5 ∧ 0 ≤ x (Rv 1) ∧ 3/20 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 4/5 ∧
      0 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/25 ∧ 3/20 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 4/5 ∧
      0 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 1/2) := by
  simp only [domRR, hostEvolve, mRR, rover_terrain_4to6_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

end RoverTerrain4to6Modal

namespace RoverTerrain4to6Guarded

open DL DLCalTiming DLRel Parse Set RoverTerrain4to6Modal RoverTerrain4to6Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 6 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 6)) : Formula.sat (hostGuard vsR 6 Side.R (mRR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 5 ∧ x (Rv 2) ≤ 1/4) := by
  simp [hostGuard, mRR, rover_terrain_4to6_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0,
    vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]
  try norm_num

theorem sat_guardR1 (x : State (Var 6)) : Formula.sat (hostGuard vsR 6 Side.R (mRR 1)) x ↔
    (5 ≤ x (Rv 1) ∧ x (Rv 1) < 12 ∧ x (Rv 2) ≤ 9/20) := by
  simp [hostGuard, mRR, rover_terrain_4to6_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0,
    vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]
  try norm_num

theorem sat_guardR2 (x : State (Var 6)) : Formula.sat (hostGuard vsR 6 Side.R (mRR 2)) x ↔
    (12 ≤ x (Rv 1) ∧ x (Rv 2) ≤ 7/10) := by
  simp [hostGuard, mRR, rover_terrain_4to6_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_03, gp_0_05, gp_0_1, gp_0_12, gp_0_15, gp_0_25, gp_0_4, gp_0_45, gp_0_5, gp_0_7, gp_0_8, gp_1_0, gp_2, gp_2_5, gp_3, gp_4_0, gp_5_0, gp_8_0, gp_12_0,
    vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]
  try norm_num

/-! ## The explicit runs (the affine cascade `w, zs → v → s`) -/

/-- The terrain's speed decay rate `μ_T + r_T`. -/
noncomputable def kT (q : ℕ) : ℝ := muT q + rT q

/-- The numeric facts the comparison bounds use. -/
theorem consts (q : ℕ) (hq : q < 3) :
    1/4 ≤ cT q ∧ cT q ≤ 7/10 ∧ 0 ≤ ZT q ∧ ZT q ≤ 3/25 ∧ 0 < kT q ∧ 0 ≤ muT q ∧
      0 ≤ (muT q * (3/20) - 3/25) / kT q ∧ muT q * (4/5) / kT q ≤ 4/5 := by
  interval_cases q <;> norm_num [cT, ZT, kT, muT, rT]

noncomputable def φw (q : ℕ) (ρ : State (Var 6)) : ℝ → ℝ :=
  forcedSol 3 (ρ (Rv 2)) (fun _ => 3 * cT q)

noncomputable def φz (q : ℕ) (ρ : State (Var 6)) : ℝ → ℝ :=
  forcedSol 2 (ρ (Rv 3)) (fun _ => 2 * ZT q)

noncomputable def φv (q : ℕ) (ρ : State (Var 6)) : ℝ → ℝ :=
  forcedSol (kT q) (ρ (Rv 0)) (fun τ => muT q * φw q ρ τ - φz q ρ τ)

noncomputable def φs (q : ℕ) (ρ : State (Var 6)) : ℝ → ℝ := intSol (ρ (Rv 1)) (φv q ρ)

theorem φw_cont (q : ℕ) (ρ : State (Var 6)) : Continuous (φw q ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φz_cont (q : ℕ) (ρ : State (Var 6)) : Continuous (φz q ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φvF_cont (q : ℕ) (ρ : State (Var 6)) :
    Continuous (fun τ => muT q * φw q ρ τ - φz q ρ τ) :=
  (continuous_const.mul (φw_cont q ρ)).sub (φz_cont q ρ)

theorem φv_cont (q : ℕ) (ρ : State (Var 6)) : Continuous (φv q ρ) :=
  forcedSol_continuous _ _ (φvF_cont q ρ)

/-- The run: every right coordinate along its explicit law (`u`, `zh` frozen). -/
noncomputable def φR (q : ℕ) (ρ : State (Var 6)) (i : Fin 6) : ℝ → ℝ :=
  if i = 0 then φv q ρ else if i = 1 then φs q ρ else if i = 2 then φw q ρ
  else if i = 3 then φz q ρ else fun _ => ρ (Rv i)

theorem φR_zero (q : ℕ) (ρ : State (Var 6)) (i : Fin 6) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φv, φs, φw, φz, forcedSol_zero, intSol_zero]

theorem φR_der (q : ℕ) (hq : q < 3) (ρ : State (Var 6)) (i : Fin 6) (t : ℝ) :
    HasDerivAt (φR q ρ i) (Term.eval (fRR q i) (trajRs ρ (φR q ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fRR0_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.zero_eta, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt (kT q) (ρ (Rv 0)) (φvF_cont q ρ) t).congr_deriv ?_
    simp only [φv, kT]; ring
  · rw [fRR1_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.mk_one, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont q ρ) t
  · rw [fRR2_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 3 (ρ (Rv 2)) continuous_const t).congr_deriv ?_
    simp only [φw]; ring
  · rw [fRR3_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 2 (ρ (Rv 3)) continuous_const t).congr_deriv ?_
    simp only [φz]; ring
  · rw [fRR4_eval q hq]
    simp only [φR, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · rw [fRR5_eval q hq]
    simp only [φR, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _

/-- The run stays in the evolve box over one control interval. -/
theorem φR_dom (q : ℕ) (hq : q < 3) (ρ : State (Var 6)) (hρ : Formula.sat domRR ρ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hv0, hv1, hs0, hw0, hw1, hz0, hz1, hu0, hu1, hh0, hh1⟩ := (sat_domRR ρ).mp hρ
  obtain ⟨hc0, hc1, hZ0, hZ1, hk, hmu, hlo, hhi⟩ := consts q hq
  have hw : ∀ τ ∈ Icc (0:ℝ) 1, 3/20 ≤ φw q ρ τ ∧ φw q ρ τ ≤ 4/5 := by
    intro τ hτ
    have h := forcedSol_between 3 (ρ (Rv 2)) (F := fun _ => 3 * cT q) continuous_const
      (lo := 3 * cT q) (hi := 3 * cT q) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    have he : 3 * cT q / 3 = cT q := by ring
    rw [he] at h
    exact ⟨le_trans (le_min hw0 (by linarith)) h.1, le_trans h.2 (max_le hw1 (by linarith))⟩
  have hz : ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φz q ρ τ ∧ φz q ρ τ ≤ 3/25 := by
    intro τ hτ
    have h := forcedSol_between 2 (ρ (Rv 3)) (F := fun _ => 2 * ZT q) continuous_const
      (lo := 2 * ZT q) (hi := 2 * ZT q) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    have he : 2 * ZT q / 2 = ZT q := by ring
    rw [he] at h
    exact ⟨le_trans (le_min hz0 hZ0) h.1, le_trans h.2 (max_le hz1 hZ1)⟩
  have hv : ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 4/5 := by
    intro τ hτ
    have h := forcedSol_between (kT q) (ρ (Rv 0)) (φvF_cont q ρ)
      (lo := muT q * (3/20) - 3/25) (hi := muT q * (4/5)) hk (fun s hs => by
        obtain ⟨a0, a1⟩ := hw s hs
        obtain ⟨b0, b1⟩ := hz s hs
        constructor <;> nlinarith) τ hτ
    exact ⟨le_trans (le_min hv0 hlo) h.1, le_trans h.2 (max_le hv1 hhi)⟩
  have hs : 0 ≤ φs q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 1)) (φv_cont q ρ) τ)
      (fun τ hτ => (hv τ hτ).1) t ht
    simp only [intSol_zero] at h
    simp only [φs]; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true,
    Fin.reduceEq, if_false]
  exact ⟨(hv t ht).1, (hv t ht).2, hs, (hw t ht).1, (hw t ht).2, (hz t ht).1, (hz t ht).2,
    hu0, hu1, hh0, hh1⟩

theorem epsR_eq : epsR rover_terrain_4to6_IRv2 = 1 := by
  simp [epsR, rover_terrain_4to6_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vsR 6 Side.R (mRR q)

noncomputable def WF : TerrainWF GrG guardR domRR where
  m := modeR
  fR := fRR
  s1 := 5
  s2 := 12
  B := 4/5
  B0 := by norm_num
  band := by norm_num
  vcap := True
  is := 1
  ic := 2
  kc := 3
  kc0 := by norm_num
  cap := cT
  cap01 := by norm_num [cT]
  cap12 := by norm_num [cT]
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fc := fun _ q hq s => fRR2_eval q hq s
  fs := fun q hq s hs => by
    have h := (sat_domRR s).mp hs
    rw [fRR1_eval q hq]; exact ⟨h.1, h.2.1⟩
  g0 := fun x => by rw [guardR, sat_guardR0]; simp [cT, and_assoc]
  g1 := fun x => by rw [guardR, sat_guardR1]; simp [cT, and_assoc]
  g2 := fun x => by rw [guardR, sat_guardR2]; simp [cT]
  e00 := edgeG 0 0
  e01 := edgeG 0 1
  e11 := edgeG 1 1
  e12 := edgeG 1 2
  e22 := edgeG 2 2
  e00_mem := edgeG_mem 0 0 (by simp [GrG])
  e01_mem := edgeG_mem 0 1 (by simp [GrG])
  e11_mem := edgeG_mem 1 1 (by simp [GrG])
  e12_mem := edgeG_mem 1 2 (by simp [GrG])
  e22_mem := edgeG_mem 2 2 (by simp [GrG])
  e00_tgt := rfl
  e01_tgt := rfl
  e11_tgt := rfl
  e12_tgt := rfl
  e22_tgt := rfl
  exists_run := fun q hq x hx =>
    ⟨_, trajRs_sol x (φR q x) 1 (by norm_num) (φR_zero q x) (fun i t _ _ => φR_der q hq x i t)
      (fun t h0 h1 => φR_dom q hq x hx t ⟨h0, h1⟩)⟩

/-- **Assumption 1 for `rover_terrain_4to6`**, every mode, Z3-free. -/
theorem rover_terrain_4to6_wellFormedR :
    WellFormedR GrG guardR (epsR rover_terrain_4to6_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_terrain WF

end RoverTerrain4to6Guarded

end RelCertifier
