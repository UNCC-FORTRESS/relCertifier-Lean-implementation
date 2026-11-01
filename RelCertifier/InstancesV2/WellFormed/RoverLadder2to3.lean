/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_2to3`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (the file's three route zones `STEEP`, `MODER`, `FLAT`
and their declared `next` lists), the lowered right guards, `ε_r = 1`. The right is the
canonical rover's point model `L2` (the hierarchy's level 2; the heading `ψ` frozen at its
start value, rate 0): per zone `v' = (c_q − v)/2` toward the zone's set point `c_q`
(3, 5, 6.5 m/s), `s' = v`, `ψ' = 0`; the guards are the odometer zones `[0, 60)`, `[60, 140)`,
`[140, ∞)`; the evolve box is the validity box shared by both sides, `0 ≤ v ≤ 8`, `s ≥ 0`,
`|ψ| ≤ 0.6`.
`wellFormedR_terrain` (the shared three-band lemma, no caps: `0 ≤ s' = v ≤ 8`, so a `STEEP`
run ends below `60 + 8 ≤ 140`, inside `STEEP` or `MODER`, a `MODER` run in `MODER` or `FLAT`,
`FLAT` is forward invariant). Existence: the explicit run (`forcedSol` for `v`, between its
start and `c_q`; `intSol` for `s`, nondecreasing; `ψ` frozen at its start value, inside the
box). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_ladder_2to3
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverLadder2to3Pins

open Parse

/-! Parse pins of the numerals the right guards, fields and domain of `rover_ladder_2to3`
write. -/

theorem gp_0 : Run.parseRat "0" = some (0:ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_6 : Run.parseRat "-0.6" = some (-(3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3_0 : Run.parseRat "3.0" = some (3:ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_5_0 : Run.parseRat "5.0" = some (5:ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_6_5 : Run.parseRat "6.5" = some ((13:ℚ)/2) := by
  have h : parseQ "6.5" = some (⟨65, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_8_0 : Run.parseRat "8.0" = some (8:ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_60_0 : Run.parseRat "60.0" = some (60:ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_140_0 : Run.parseRat "140.0" = some (140:ℚ) := by
  have h : parseQ "140.0" = some (⟨1400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

end RoverLadder2to3Pins

namespace RoverLadder2to3Modal

open DL DLCalTiming DLRel Parse Set RoverLadder2to3Pins

def vsR : List String := ["v", "s", "psi"]

def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRR (q : ℕ) : Parse.PMode := rover_ladder_2to3_IRv2.R.modes.getD q dummyR

noncomputable def fRR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsR 3 Side.R (mRR q)

noncomputable def domRR : Formula (Var 3) := hostEvolve vsR 3 Side.R (mRR 0)

noncomputable def modeR (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

/-- The zones' speed set points `c_q` (`STEEP` 3, `MODER` 5, `FLAT` 6.5 m/s). -/
noncomputable def cZ (q : ℕ) : ℝ := if q = 0 then 3 else if q = 1 then 5 else 13/2

theorem fRR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRR q 0) x = 1/2 * (cZ q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_2to3_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_5, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0,
      gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cZ]

theorem fRR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_2to3_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_5, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0,
      gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem fRR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRR q 2) x = 0 := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_2to3_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_5, gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0,
      gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_domRR (x : State (Var 3)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8 ∧ 0 ≤ x (Rv 1) ∧ -(3/5) ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/5) := by
  simp only [domRR, hostEvolve, mRR, rover_ladder_2to3_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0,
    gp_6_5, gp_8_0, gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

end RoverLadder2to3Modal

namespace RoverLadder2to3Guarded

open DL DLCalTiming DLRel Parse Set RoverLadder2to3Modal RoverLadder2to3Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 3 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vsR 3 Side.R (mRR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 60) := by
  simp [hostGuard, mRR, rover_ladder_2to3_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vsR 3 Side.R (mRR 1)) x ↔
    (60 ≤ x (Rv 1) ∧ x (Rv 1) < 140) := by
  simp [hostGuard, mRR, rover_ladder_2to3_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vsR 3 Side.R (mRR 2)) x ↔
    140 ≤ x (Rv 1) := by
  simp [hostGuard, mRR, rover_ladder_2to3_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

/-! ## The explicit runs -/

theorem cZ_bounds (q : ℕ) (hq : q < 3) : 3 ≤ cZ q ∧ cZ q ≤ 13/2 := by
  interval_cases q <;> norm_num [cZ]

noncomputable def φv (q : ℕ) (ρ : State (Var 3)) : ℝ → ℝ :=
  forcedSol (1/2) (ρ (Rv 0)) (fun _ => 1/2 * cZ q)

noncomputable def φs (q : ℕ) (ρ : State (Var 3)) : ℝ → ℝ := intSol (ρ (Rv 1)) (φv q ρ)

theorem φv_cont (q : ℕ) (ρ : State (Var 3)) : Continuous (φv q ρ) :=
  forcedSol_continuous _ _ continuous_const

/-- The run: `v` toward the zone's set point, `s` its integral, `ψ` frozen. -/
noncomputable def φR (q : ℕ) (ρ : State (Var 3)) (i : Fin 3) : ℝ → ℝ :=
  if i = 0 then φv q ρ else if i = 1 then φs q ρ else fun _ => ρ (Rv i)

theorem φR_zero (q : ℕ) (ρ : State (Var 3)) (i : Fin 3) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φv, φs, forcedSol_zero, intSol_zero]

theorem φR_der (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (φR q ρ i) (Term.eval (fRR q i) (trajRs ρ (φR q ρ) t)) t := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · rw [fRR0_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.zero_eta, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt (1/2) (ρ (Rv 0)) continuous_const t).congr_deriv ?_
    simp only [φv]; ring
  · rw [fRR1_eval q hq]
    simp only [trajRs_R, φR]
    simp only [Fin.isValue, Fin.mk_one, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φv_cont q ρ) t
  · rw [fRR2_eval q hq]
    simp only [φR, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, if_false]
    exact hasDerivAt_const t _

/-- The run stays in the evolve box over one control interval. -/
theorem φR_dom (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hρ : Formula.sat domRR ρ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hv0, hv1, hs0, hp0, hp1⟩ := (sat_domRR ρ).mp hρ
  obtain ⟨hc0, hc1⟩ := cZ_bounds q hq
  have hv : ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8 := by
    intro τ hτ
    have h := forcedSol_between (1/2) (ρ (Rv 0)) (F := fun _ => 1/2 * cZ q) continuous_const
      (lo := 1/2 * cZ q) (hi := 1/2 * cZ q) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    have he : 1/2 * cZ q / (1/2) = cZ q := by ring
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
  exact ⟨(hv t ht).1, (hv t ht).2, hs, hp0, hp1⟩

theorem epsR_eq : epsR rover_ladder_2to3_IRv2 = 1 := by
  simp [epsR, rover_ladder_2to3_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vsR 3 Side.R (mRR q)

noncomputable def WF : TerrainWF GrG guardR domRR where
  m := modeR
  fR := fRR
  s1 := 60
  s2 := 140
  B := 8
  B0 := by norm_num
  band := by norm_num
  vcap := False
  is := 1
  ic := 0
  kc := 0
  kc0 := le_rfl
  cap := fun _ => 0
  cap01 := le_rfl
  cap12 := le_rfl
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

/-- **Assumption 1 for `rover_ladder_2to3`**, every mode, Z3-free. -/
theorem rover_ladder_2to3_wellFormedR :
    WellFormedR GrG guardR (epsR rover_ladder_2to3_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_terrain WF

end RoverLadder2to3Guarded

end RelCertifier
