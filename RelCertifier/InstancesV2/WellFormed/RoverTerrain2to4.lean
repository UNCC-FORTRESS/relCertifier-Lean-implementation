/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_2to4`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (the file's three terrains `MUD`, `GRAVEL`, `PAVED` and
their declared `next` lists), the lowered right guards, `ε_r = 1`. The right is the no-slip
plan (the chain's 2-coordinate model; wheel speed `w` and sinkage `zs` pinned): per terrain
`T`, `v' = 3 (c_T − v)` (`c_T` = 0.25, 0.45, 0.7), `s' = v`, `w' = zs' = 0`; the guards are
the odometer bands `[0, 5)`, `[5, 12)`, `[12, ∞)` only (no cap). The evolve domain is
`0 ≤ v ≤ 0.8`, `s ≥ 0`, `0.05 ≤ w ≤ 0.8` (the wheel floor), `0 ≤ zs ≤ 0.12`.
`wellFormedR_terrain` (clause (ii): `0 ≤ s' = v ≤ 0.8`, so a `MUD` run ends in `MUD` or
`GRAVEL`, a `GRAVEL` run in `GRAVEL` or `PAVED`, `PAVED` is forward invariant). Existence: the
explicit run `v → c_T` exponentially (`forcedSol`, kept between its start and `c_T`), `s` its
integral (`intSol`), `w`, `zs` frozen. Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_terrain_2to4
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverTerrain2to4Pins

open Parse

/-! Parse pins of the numerals the right guards, fields and domain of `rover_terrain_2to4` write. -/

theorem gp_0 : Run.parseRat "0" = some (0:ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_12 : Run.parseRat "0.12" = some ((3:ℚ)/25) := by
  have h : parseQ "0.12" = some (⟨12, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_25 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_45 : Run.parseRat "0.45" = some ((9:ℚ)/20) := by
  have h : parseQ "0.45" = some (⟨45, 100⟩ : QF) := by decide
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

theorem gp_3 : Run.parseRat "3" = some (3:ℚ) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_5_0 : Run.parseRat "5.0" = some (5:ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_12_0 : Run.parseRat "12.0" = some (12:ℚ) := by
  have h : parseQ "12.0" = some (⟨120, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num


end RoverTerrain2to4Pins

namespace RoverTerrain2to4Modal

open DL DLCalTiming DLRel Parse Set RoverTerrain2to4Pins

def vsR : List String := ["v", "s", "w", "zs"]

def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRR (q : ℕ) : Parse.PMode := rover_terrain_2to4_IRv2.R.modes.getD q dummyR

noncomputable def fRR (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vsR 4 Side.R (mRR q)

noncomputable def domRR : Formula (Var 4) := hostEvolve vsR 4 Side.R (mRR 0)

noncomputable def modeR (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

/-- The terrain's speed set point `c_T`. -/
noncomputable def cT (q : ℕ) : ℝ := if q = 0 then 1/4 else if q = 1 then 9/20 else 7/10

theorem fRR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRR q 0) x = 3 * (cT q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_2to4_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT]

theorem fRR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_2to4_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT]

theorem fRR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRR q 2) x = 0 := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_2to4_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT]

theorem fRR3_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fRR q 3) x = 0 := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_terrain_2to4_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cT]

theorem sat_domRR (x : State (Var 4)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 4/5 ∧ 0 ≤ x (Rv 1) ∧ 1/20 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 4/5 ∧
      0 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 3/25) := by
  simp only [domRR, hostEvolve, mRR, rover_terrain_2to4_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

end RoverTerrain2to4Modal

namespace RoverTerrain2to4Guarded

open DL DLCalTiming DLRel Parse Set RoverTerrain2to4Modal RoverTerrain2to4Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 4) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 4 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 4) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 4)) : Formula.sat (hostGuard vsR 4 Side.R (mRR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 5) := by
  simp [hostGuard, mRR, rover_terrain_2to4_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0,
    vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]
  try norm_num

theorem sat_guardR1 (x : State (Var 4)) : Formula.sat (hostGuard vsR 4 Side.R (mRR 1)) x ↔
    (5 ≤ x (Rv 1) ∧ x (Rv 1) < 12) := by
  simp [hostGuard, mRR, rover_terrain_2to4_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0,
    vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]
  try norm_num

theorem sat_guardR2 (x : State (Var 4)) : Formula.sat (hostGuard vsR 4 Side.R (mRR 2)) x ↔
    12 ≤ x (Rv 1) := by
  simp [hostGuard, mRR, rover_terrain_2to4_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_12, gp_0_25, gp_0_45, gp_0_7, gp_0_8, gp_1_0, gp_3, gp_5_0, gp_12_0,
    vsR, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]
  try norm_num

/-! ## The explicit runs -/

theorem consts (q : ℕ) (hq : q < 3) : 1/4 ≤ cT q ∧ cT q ≤ 7/10 := by
  interval_cases q <;> norm_num [cT]

noncomputable def φv (q : ℕ) (ρ : State (Var 4)) : ℝ → ℝ :=
  forcedSol 3 (ρ (Rv 0)) (fun _ => 3 * cT q)

noncomputable def φs (q : ℕ) (ρ : State (Var 4)) : ℝ → ℝ := intSol (ρ (Rv 1)) (φv q ρ)

theorem φv_cont (q : ℕ) (ρ : State (Var 4)) : Continuous (φv q ρ) :=
  forcedSol_continuous _ _ continuous_const

/-- The run: `v`, `s` along their explicit laws, `w`, `zs` frozen. -/
noncomputable def φR (q : ℕ) (ρ : State (Var 4)) (i : Fin 4) : ℝ → ℝ :=
  if i = 0 then φv q ρ else if i = 1 then φs q ρ else fun _ => ρ (Rv i)

theorem φR_zero (q : ℕ) (ρ : State (Var 4)) (i : Fin 4) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φv, φs, forcedSol_zero, intSol_zero]

theorem φR_der (q : ℕ) (hq : q < 3) (ρ : State (Var 4)) (i : Fin 4) (t : ℝ) :
    HasDerivAt (φR q ρ i) (Term.eval (fRR q i) (trajRs ρ (φR q ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fRR0_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.zero_eta, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 3 (ρ (Rv 0)) continuous_const t).congr_deriv ?_
    simp only [φv]; ring
  · rw [fRR1_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.mk_one, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont q ρ) t
  · rw [fRR2_eval q hq]
    simp only [φR, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _
  · rw [fRR3_eval q hq]
    simp only [φR, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _

/-- The run stays in the evolve box over one control interval. -/
theorem φR_dom (q : ℕ) (hq : q < 3) (ρ : State (Var 4)) (hρ : Formula.sat domRR ρ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hv0, hv1, hs0, hw0, hw1, hz0, hz1⟩ := (sat_domRR ρ).mp hρ
  obtain ⟨hc0, hc1⟩ := consts q hq
  have hv : ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 4/5 := by
    intro τ hτ
    have h := forcedSol_between 3 (ρ (Rv 0)) (F := fun _ => 3 * cT q) continuous_const
      (lo := 3 * cT q) (hi := 3 * cT q) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    have he : 3 * cT q / 3 = cT q := by ring
    rw [he] at h
    exact ⟨le_trans (le_min hv0 (by linarith)) h.1, le_trans h.2 (max_le hv1 (by linarith))⟩
  have hs : 0 ≤ φs q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 1)) (φv_cont q ρ) τ)
      (fun τ hτ => (hv τ hτ).1) t ht
    simp only [intSol_zero] at h
    simp only [φs]; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true,
    Fin.reduceEq, if_false]
  exact ⟨(hv t ht).1, (hv t ht).2, hs, hw0, hw1, hz0, hz1⟩

theorem epsR_eq : epsR rover_terrain_2to4_IRv2 = 1 := by
  simp [epsR, rover_terrain_2to4_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 4) := hostGuard vsR 4 Side.R (mRR q)

noncomputable def WF : TerrainWF GrG guardR domRR where
  m := modeR
  fR := fRR
  s1 := 5
  s2 := 12
  B := 4/5
  B0 := by norm_num
  band := by norm_num
  vcap := False
  is := 1
  ic := 0
  kc := 3
  kc0 := by norm_num
  cap := cT
  cap01 := by norm_num [cT]
  cap12 := by norm_num [cT]
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fc := fun h => h.elim
  fs := fun q hq s hs => by
    have h := (sat_domRR s).mp hs
    rw [fRR1_eval q hq]; exact ⟨h.1, h.2.1⟩
  g0 := fun x => by rw [guardR, sat_guardR0]; simp
  g1 := fun x => by rw [guardR, sat_guardR1]; simp
  g2 := fun x => by rw [guardR, sat_guardR2]; simp
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

/-- **Assumption 1 for `rover_terrain_2to4`**, every mode, Z3-free. -/
theorem rover_terrain_2to4_wellFormedR :
    WellFormedR GrG guardR (epsR rover_terrain_2to4_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_terrain WF

end RoverTerrain2to4Guarded

end RelCertifier
