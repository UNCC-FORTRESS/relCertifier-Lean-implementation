/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_6to8`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverTerrain6to8Guarded.lean`), the lowered right guards, `ε_r = 1` (the literal is the
suite_v2 file's, `InstancesV2/SameIR.lean`). A terrain ladder with speed caps, `s' = v (1 − ψ²/2 − 0.3 θ²)` (since 2026-10-26):
`wellFormedR_ladder` (style (b) for `STEEP`, `MODER`, (a) for `FLAT`); existence from the
instance's explicit ladder runs (`LR.sol`). Z3-free. (GENERATED from one template.)
-/
import RelCertifier.InstancesV2.BenchIR.rover_terrain_6to8
import RelCertifier.Proofs.Encoding.WellFormedLadder

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverTerrain6to8Pins

open Parse

/-! Parse pins of the numerals the guards and fields of `rover_terrain_6to8` write (the `GuardedPins` lemmas this file uses, local). -/

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
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

theorem gp_0_65 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_4 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

end RoverTerrain6to8Pins

namespace RoverTerrain6to8Modal

open DL DLCalTiming DLRel Parse Set

def vsU : List String := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]

def dummyU : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRU (q : ℕ) : Parse.PMode := rover_terrain_6to8_IRv2.R.modes.getD q dummyU

noncomputable def fRU (q : ℕ) : Fin 8 → Term (Var 8) := hostDyn vsU 8 Side.R (mRU q)

noncomputable def domRU : Formula (Var 8) := hostEvolve vsU 8 Side.R (mRU 0)

noncomputable def modeU (q : ℕ) : RMode (Var 8) :=
  { sys := rightBlock (fRU q) (Term.const 1), dom := domRU, weight := 1 }

theorem hu030 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hu050 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hu065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hu3 : Run.parseRat "3" = some 3 := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hum1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hu0 : Run.parseRat "0" = some 0 := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hu00 : Run.parseRat "0.0" = some 0 := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hu08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hum05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hu015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hum10 : Run.parseRat "-1.0" = some (-1) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hu11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hup1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hup05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num

theorem hup03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num

noncomputable def cstU (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem fRU0_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 0) x = 3 * (cstU q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cstU]

theorem fRU1_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 1) x = x (Rv 0) * ((1 - 1/2 * (x (Rv 2) * x (Rv 2))) - 3/10 * (x (Rv 4) * x (Rv 4))) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU2_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 2) x = -1 * x (Rv 2) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU3_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 3) x = 0 := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU4_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 4) x = -1 * x (Rv 4) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU5_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 5) x = 0 := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU6_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 6) x = -1 * x (Rv 6) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fRU7_eval (q : ℕ) (hq : q < 3) (x : State (Var 8)) :
    Term.eval (fRU q 7) x = -1 * x (Rv 7) := by
  interval_cases q <;>
    simp [fRU, hostDyn, mRU, rover_terrain_6to8_IRv2, vsU, Run.dynOf,
      Run.lowerE, hu3, hu030, hu050, hu065, hum1, hu0, hup1, hup05, hup03, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRU (x : State (Var 8)) : Formula.sat domRU x ↔
    (-(1:ℝ) ≤ x (Rv 3) ∧ x (Rv 3) ≤ 11/10 ∧ -(1:ℝ) ≤ x (Rv 5) ∧ x (Rv 5) ≤ 11/10 ∧
     -(1:ℝ)/2 ≤ x (Rv 7) ∧ x (Rv 7) ≤ 3/20 ∧ -(1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 3/20 ∧
     0 ≤ x (Rv 1) ∧ -(1:ℝ)/2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 3/20 ∧ 0 ≤ x (Rv 0) ∧
     x (Rv 0) ≤ 4/5 ∧ -(1:ℝ) ≤ x (Rv 6) ∧ x (Rv 6) ≤ 3/20) := by
  simp only [domRU, hostEvolve, mRU, rover_terrain_6to8_IRv2, vsU]
  simp [Run.lowerF, Run.lowerE, hum05, hu015, hu00, hu08, hum10, hu11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end RoverTerrain6to8Modal

namespace RoverTerrain6to8Guarded

open DL DLCalTiming DLRel Parse Set RoverTerrain6to8Modal RoverTerrain6to8Pins

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := hostGuard vsU 8 Side.R (mRU tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 8) :=
  { modes := [modeU 0, modeU 1, modeU 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeU q) := by
  interval_cases q <;> rfl

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRU, rover_terrain_6to8_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRU, rover_terrain_6to8_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRU, rover_terrain_6to8_IRv2, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cstU_eq (q : ℕ) : cstU q = ladC q := rfl

/-- Decay rates (`ψ, θ, …` decay `e^{−t}`, the pinned coordinates frozen). -/
noncomputable def dR : Fin 8 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 1]

noncomputable def φo (ρ : State (Var 8)) (i : Fin 8) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run. -/
noncomputable def kapT (ρ : State (Var 8)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem φo_bounds (ρ : State (Var 8)) (hρ : Formula.sat domRU ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) := by
  have h2l : -(1:ℝ)/2 ≤ ρ (Rv 2) := by rw [sat_domRU] at hρ; tauto
  have h2h : ρ (Rv 2) ≤ 3/20 := by rw [sat_domRU] at hρ; tauto
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (by simp [dR]) ht
  have h4l : -(1:ℝ)/2 ≤ ρ (Rv 4) := by rw [sat_domRU] at hρ; tauto
  have h4h : ρ (Rv 4) ≤ 3/20 := by rw [sat_domRU] at hρ; tauto
  have b4 := decay_between (ρ (Rv 4)) (dR 4) t (by simp [dR]) ht
  simp only [φo]
  exact ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1, le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b4.1, le_trans b4.2 (max_le h4h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 8)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 8)) (hρ : Formula.sat domRU ρ) {t : ℝ} (ht : 0 ≤ t) :
    7/10 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem hfoR (q : ℕ) (hq : q < 3) (ρ : State (Var 8)) (i : Fin 8) (h0 : i ≠ 0) (h1 : i ≠ 1)
    (t : ℝ) : HasDerivAt (φo ρ i) (Term.eval (fRU q i) (trajR ρ (phiK φo kapT q ρ) t)) t := by
  have hf : φo ρ i = fun u => ρ (Rv i) * Real.exp (-(dR i * u)) := rfl
  have hd := hasDerivAt_decay (ρ (Rv i)) (dR i) t
  rw [hf]
  convert hd using 1
  fin_cases i
  · exact absurd rfl h0
  · exact absurd rfl h1
  all_goals
    simp only [Fin.reduceFinMk, Fin.isValue]
    first
      | (rw [fRU2_eval q hq]) | (rw [fRU3_eval q hq]) | (rw [fRU4_eval q hq]) | (rw [fRU5_eval q hq]) | (rw [fRU6_eval q hq]) | (rw [fRU7_eval q hq])
    simp [trajR_R, phiK, φo, dR]

noncomputable def LR : LadderRun GrG domRU :=
  LadderRun.ofKappa GrG domRU modeU fRU φo kapT (7/10) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRU0_eval q hq, cstU_eq])
    (fun ρ i _ _ => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => hfoR q hq ρ i h0 h1 t)
    (fun q hq ρ _ t _ => by
      rw [fRU1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRU ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (7/10) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (by fin_cases k <;> simp [dR]) ht
      rw [sat_domRU]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRU ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

theorem epsR_eq : epsR rover_terrain_6to8_IRv2 = 1 := by
  simp [epsR, rover_terrain_6to8_IRv2, gp_1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 8) := hostGuard vsU 8 Side.R (mRU q)

noncomputable def WF : LadderWF GrG guardR domRU where
  m := modeU
  fR := fRU
  vcap := True
  i0 := 0
  i1 := 1
  modeAt := GrG_modeAt
  len := rfl
  sys_eq := fun _ _ => rfl
  dom_eq := fun _ _ => rfl
  fv := fun q hq s => by rw [fRU0_eval q hq, cstU_eq]
  fs := fun q hq s hs => by
    have h0 : 0 ≤ s (Rv 0) := by rw [sat_domRU] at hs; tauto
    have h1 : s (Rv 0) ≤ 4/5 := by rw [sat_domRU] at hs; tauto
    have hp2l : -(1:ℝ)/2 ≤ s (Rv 2) := by rw [sat_domRU] at hs; tauto
    have hp2h : s (Rv 2) ≤ 3/20 := by rw [sat_domRU] at hs; tauto
    have hp4l : -(1:ℝ)/2 ≤ s (Rv 4) := by rw [sat_domRU] at hs; tauto
    have hp4h : s (Rv 4) ≤ 3/20 := by rw [sat_domRU] at hs; tauto
    rw [fRU1_eval q hq]
    exact odo_rate2 _ _ _ h0 h1 (by linarith) (by linarith) (by linarith) (by linarith)
  g0 := fun x => by rw [guardR, sat_guardR0]; simp [and_assoc]
  g1 := fun x => by rw [guardR, sat_guardR1]; simp [and_assoc]
  g2 := fun x => by rw [guardR, sat_guardR2]; simp
  e00 := edgeG 0 0
  e01 := edgeG 0 1
  e11 := edgeG 1 1
  e12 := edgeG 1 2
  e22 := edgeG 2 2
  e00_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e01_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e11_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e12_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e22_mem := List.mem_filter.mpr ⟨by simp [GrG], by simp [edgeG]⟩
  e00_tgt := rfl
  e01_tgt := rfl
  e11_tgt := rfl
  e12_tgt := rfl
  e22_tgt := rfl
  exists_run := LR.exists_run GrG_modeAt

/-- **Assumption 1 for `rover_terrain_6to8`**, every mode, Z3-free. -/
theorem rover_terrain_6to8_wellFormedR :
    WellFormedR GrG guardR (epsR rover_terrain_6to8_IRv2) := by
  rw [epsR_eq]; exact wellFormedR_ladder WF

end RoverTerrain6to8Guarded

end RelCertifier
