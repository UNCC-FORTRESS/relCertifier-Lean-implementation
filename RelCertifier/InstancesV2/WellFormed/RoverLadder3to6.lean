/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_3to6`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` (the file's three route zones `STEEP`, `MODER`, `FLAT`
and their declared `next` lists), the lowered right guards, `ε_r = 1`. The right is the
canonical rover's level `L3` (speed, odometer, heading error; pitch `θ`, heave `z` and roll `φ`
pinned at 0): per zone `v' = (c_q − v)/2` toward the zone's set point `c_q` (3, 5, 6.5 m/s),
`s' = v (1 − ψ²/2)`, `ψ' = −ψ`, `θ' = z' = φ' = 0`; the guards are the odometer zones
`[0, 60)`, `[60, 140)`, `[140, ∞)`; the evolve box `0 ≤ v ≤ 8`, `s ≥ 0`, `|ψ| ≤ 0.6`,
`θ = z = φ = 0`.
`wellFormedR_terrain` (the shared three-band lemma, no caps: `0 ≤ s' ≤ 8` on the box, so a
`STEEP` run ends below `60 + 8 ≤ 140`, inside `STEEP` or `MODER`, a `MODER` run in `MODER` or
`FLAT`, `FLAT` is forward invariant). Existence: the explicit run (`forcedSol` for `v`,
between its start and `c_q`, and for `ψ`, between its start and 0; `intSol` for `s`,
nondecreasing; `θ`, `z`, `φ` frozen). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_ladder_3to6
import RelCertifier.Proofs.Encoding.WellFormedTerrain

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverLadder3to6Pins

open Parse

/-! Parse pins of the numerals the right guards, fields and domain of `rover_ladder_3to6`
write. -/

theorem gp_0 : Run.parseRat "0" = some (0:ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1 : Run.parseRat "1" = some (1:ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m1 : Run.parseRat "-1" = some (-1:ℚ) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
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

end RoverLadder3to6Pins

namespace RoverLadder3to6Modal

open DL DLCalTiming DLRel Parse Set RoverLadder3to6Pins

def vsR : List String := ["v", "s", "psi", "theta_p", "z", "phi_r"]

def dummyR : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRR (q : ℕ) : Parse.PMode := rover_ladder_3to6_IRv2.R.modes.getD q dummyR

noncomputable def fRR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vsR 6 Side.R (mRR q)

noncomputable def domRR : Formula (Var 6) := hostEvolve vsR 6 Side.R (mRR 0)

noncomputable def modeR (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fRR q) (Term.const 1), dom := domRR, weight := 1 }

/-- The zones' speed set points `c_q` (`STEEP` 3, `MODER` 5, `FLAT` 6.5 m/s). -/
noncomputable def cZ (q : ℕ) : ℝ := if q = 0 then 3 else if q = 1 then 5 else 13/2

theorem fRR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 0) x = 1/2 * (cZ q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_3to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0,
      gp_6_5, gp_8_0, gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, cZ]

theorem fRR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 1) x = x (Rv 0) * (1 - 1/2 * (x (Rv 2) * x (Rv 2))) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_3to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0,
      gp_6_5, gp_8_0, gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fRR q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRR, hostDyn, mRR, rover_ladder_3to6_IRv2, vsR, Run.dynOf,
      Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0,
      gp_6_5, gp_8_0, gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRR_pinned (q : ℕ) (hq : q < 3) (x : State (Var 6)) (i : Fin 6) (h0 : i ≠ 0)
    (h1 : i ≠ 1) (h2 : i ≠ 2) : Term.eval (fRR q i) x = 0 := by
  fin_cases i
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  all_goals
    interval_cases q <;>
      simp [fRR, hostDyn, mRR, rover_ladder_3to6_IRv2, vsR, Run.dynOf,
        Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_5, gp_0_6, gp_m0_6, gp_1_0, gp_3_0, gp_5_0,
        gp_6_5, gp_8_0, gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons, List.finRange,
        ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRR (x : State (Var 6)) : Formula.sat domRR x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8 ∧ 0 ≤ x (Rv 1) ∧ -(3/5) ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/5 ∧
      0 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 0 ∧ 0 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 0 ∧
      0 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 0) := by
  simp only [domRR, hostEvolve, mRR, rover_ladder_3to6_IRv2, vsR]
  simp [Run.lowerF, Run.lowerE, gp_0, gp_1, gp_m1, gp_0_0, gp_0_5, gp_0_6, gp_m0_6, gp_1_0,
    gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  try norm_num
  try tauto

end RoverLadder3to6Modal

namespace RoverLadder3to6Guarded

open DL DLCalTiming DLRel Parse Set RoverLadder3to6Modal RoverLadder3to6Pins

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
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 60) := by
  simp [hostGuard, mRR, rover_ladder_3to6_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

theorem sat_guardR1 (x : State (Var 6)) : Formula.sat (hostGuard vsR 6 Side.R (mRR 1)) x ↔
    (60 ≤ x (Rv 1) ∧ x (Rv 1) < 140) := by
  simp [hostGuard, mRR, rover_ladder_3to6_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

theorem sat_guardR2 (x : State (Var 6)) : Formula.sat (hostGuard vsR 6 Side.R (mRR 2)) x ↔
    140 ≤ x (Rv 1) := by
  simp [hostGuard, mRR, rover_ladder_3to6_IRv2, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_5,
    gp_1_0, gp_3_0, gp_5_0, gp_6_5, gp_8_0, gp_60_0, gp_140_0, vsR, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]
  try norm_num

/-! ## The explicit runs -/

theorem cZ_bounds (q : ℕ) (hq : q < 3) : 3 ≤ cZ q ∧ cZ q ≤ 13/2 := by
  interval_cases q <;> norm_num [cZ]

/-- The heading-weighted odometer rate `v (1 − ψ²/2)` lies in `[0, 8]` on the box. -/
theorem odo_rate (v a : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 8) (ha0 : -(3/5) ≤ a) (ha1 : a ≤ 3/5) :
    0 ≤ v * (1 - 1/2 * (a * a)) ∧ v * (1 - 1/2 * (a * a)) ≤ 8 := by
  have ha2 : a * a ≤ 9/25 := by nlinarith
  have hk0 : 0 ≤ 1 - 1/2 * (a * a) := by nlinarith
  have hk1 : 1 - 1/2 * (a * a) ≤ 1 := by nlinarith [mul_self_nonneg a]
  exact ⟨mul_nonneg hv0 hk0, by nlinarith [mul_le_mul_of_nonneg_left hk1 hv0]⟩

noncomputable def φv (q : ℕ) (ρ : State (Var 6)) : ℝ → ℝ :=
  forcedSol (1/2) (ρ (Rv 0)) (fun _ => 1/2 * cZ q)

noncomputable def φps (ρ : State (Var 6)) : ℝ → ℝ := forcedSol 1 (ρ (Rv 2)) (fun _ => 0)

noncomputable def φsF (q : ℕ) (ρ : State (Var 6)) : ℝ → ℝ :=
  fun τ => φv q ρ τ * (1 - 1/2 * (φps ρ τ * φps ρ τ))

noncomputable def φs (q : ℕ) (ρ : State (Var 6)) : ℝ → ℝ := intSol (ρ (Rv 1)) (φsF q ρ)

theorem φv_cont (q : ℕ) (ρ : State (Var 6)) : Continuous (φv q ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φps_cont (ρ : State (Var 6)) : Continuous (φps ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φsF_cont (q : ℕ) (ρ : State (Var 6)) : Continuous (φsF q ρ) := by
  have h1 := φv_cont q ρ
  have h2 := φps_cont ρ
  unfold φsF
  fun_prop

/-- The run: `v` toward the zone's set point, `ψ` decaying, `s` the integral of the
odometer rate, `θ`, `z`, `φ` frozen. -/
noncomputable def φR (q : ℕ) (ρ : State (Var 6)) (i : Fin 6) : ℝ → ℝ :=
  if i = 0 then φv q ρ else if i = 1 then φs q ρ else if i = 2 then φps ρ
  else fun _ => ρ (Rv i)

theorem φR_zero (q : ℕ) (ρ : State (Var 6)) (i : Fin 6) : φR q ρ i 0 = ρ (Rv i) := by
  fin_cases i <;> simp [φR, φv, φs, φps, forcedSol_zero, intSol_zero]

theorem φR_der (q : ℕ) (hq : q < 3) (ρ : State (Var 6)) (i : Fin 6) (t : ℝ) :
    HasDerivAt (φR q ρ i) (Term.eval (fRR q i) (trajRs ρ (φR q ρ) t)) t := by
  by_cases h0 : i = 0
  · subst h0
    rw [fRR0_eval q hq]
    simp only [trajRs_R, φR, if_true]
    refine (forcedSol_hasDerivAt (1/2) (ρ (Rv 0)) continuous_const t).congr_deriv ?_
    simp only [φv]; ring
  by_cases h1 : i = 1
  · subst h1
    rw [fRR1_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.mk_one, if_true, Fin.reduceEq, if_false]
    exact intSol_hasDerivAt _ (φsF_cont q ρ) t
  by_cases h2 : i = 2
  · subst h2
    rw [fRR2_eval q hq]
    simp only [trajRs_R, φR, Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    refine (forcedSol_hasDerivAt 1 (ρ (Rv 2)) continuous_const t).congr_deriv ?_
    simp only [φps]; ring
  rw [fRR_pinned q hq _ i h0 h1 h2]
  simp only [φR, h0, h1, h2, if_false]
  exact hasDerivAt_const t _

/-- The run stays in the evolve box over one control interval. -/
theorem φR_dom (q : ℕ) (hq : q < 3) (ρ : State (Var 6)) (hρ : Formula.sat domRR ρ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Formula.sat domRR (trajRs ρ (φR q ρ) t) := by
  obtain ⟨hv0, hv1, hs0, hp0, hp1, h30, h31, h40, h41, h50, h51⟩ := (sat_domRR ρ).mp hρ
  obtain ⟨hc0, hc1⟩ := cZ_bounds q hq
  have hv : ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φv q ρ τ ∧ φv q ρ τ ≤ 8 := by
    intro τ hτ
    have h := forcedSol_between (1/2) (ρ (Rv 0)) (F := fun _ => 1/2 * cZ q) continuous_const
      (lo := 1/2 * cZ q) (hi := 1/2 * cZ q) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    have he : 1/2 * cZ q / (1/2) = cZ q := by ring
    rw [he] at h
    exact ⟨le_trans (le_min hv0 (by linarith)) h.1, le_trans h.2 (max_le hv1 (by linarith))⟩
  have hps : ∀ τ ∈ Icc (0:ℝ) 1, -(3/5) ≤ φps ρ τ ∧ φps ρ τ ≤ 3/5 := by
    intro τ hτ
    have h := forcedSol_between 1 (ρ (Rv 2)) (F := fun _ => (0:ℝ)) continuous_const
      (lo := 0) (hi := 0) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
    simp only [zero_div] at h
    exact ⟨le_trans (le_min hp0 (by norm_num)) h.1, le_trans h.2 (max_le hp1 (by norm_num))⟩
  have hs : 0 ≤ φs q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 1)) (φsF_cont q ρ) τ)
      (fun τ hτ => (odo_rate _ _ (hv τ hτ).1 (hv τ hτ).2 (hps τ hτ).1 (hps τ hτ).2).1) t ht
    simp only [intSol_zero] at h
    simp only [φs]; linarith
  rw [sat_domRR]
  simp only [trajRs_R, φR, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, if_true,
    Fin.reduceEq, if_false]
  exact ⟨(hv t ht).1, (hv t ht).2, hs, (hps t ht).1, (hps t ht).2, h30, h31, h40, h41, h50, h51⟩

theorem epsR_eq : epsR rover_ladder_3to6_IRv2 = 1 := by
  simp [epsR, rover_ladder_3to6_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vsR 6 Side.R (mRR q)

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
    obtain ⟨h0, h1, _, h3, h4, _⟩ := (sat_domRR s).mp hs
    rw [fRR1_eval q hq]; exact odo_rate _ _ h0 h1 h3 h4
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

/-- **Assumption 1 for `rover_ladder_3to6`**, every mode, Z3-free. -/
theorem rover_ladder_3to6_wellFormedR :
    WellFormedR GrG guardR (epsR rover_ladder_3to6_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_terrain WF

end RoverLadder3to6Guarded

end RelCertifier
