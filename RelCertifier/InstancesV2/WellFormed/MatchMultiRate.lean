/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrPG` of the Theorem 3 instance
(`Instances/MatchMultiRateGuarded.lean`), the lowered right guards, `ε_r = 0.3` (the literal
is the suite_v2 file's, `InstancesV2/SameIR.lean`). Both guard sets are forward invariant
(style (a)): `DRIVE` (`0.2 ≤ v ≤ 1`, `v' = 1 − v`: `v` rises toward 1) and `STALL`
(`v < 0.2`, `v' = −2 v`: `v` decays); the odometer `s' = v ≥ 0` keeps `s ≥ 0`. Existence:
the explicit exponential runs (the instance's `driveEnd`; `stallEnd` below). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.match_multi_rate
import RelCertifier.Proofs.Encoding.WellFormedR

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace MatchMultiRateModal

open DL DLCalTiming DLRel Parse Set

def vsM : List String := ["v", "s"]

def dummyM : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRM (q : ℕ) : Parse.PMode := match_multi_rate_IRv2.R.modes.getD q dummyM

noncomputable def fRM (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsM 2 Side.R (mRM q)

noncomputable def domRM : Formula (Var 2) := hostEvolve vsM 2 Side.R (mRM 0)

noncomputable def modeM (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRM q) (Term.const 1), dom := domRM, weight := 1 }

/-! ## Parse pins -/

theorem hm10 : Run.parseRat "1.0" = some (1) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm3 : Run.parseRat "3" = some (3) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm2 : Run.parseRat "2" = some (2) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm4 : Run.parseRat "4" = some (4) := by
  have h : parseQ "4" = some (⟨4, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hm115 : Run.parseRat "1.15" = some ((23:ℚ)/20) := by
  have h : parseQ "1.15" = some (⟨115, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Field and shape pins -/

noncomputable def cstM (q : ℕ) : ℝ := if q = 0 then 1 else if q = 1 then 1 else 1

theorem fRM0_eval (q : ℕ) (hq : q < 1) (x : State (Var 2)) :
    Term.eval (fRM q 0) x = 1 * (cstM q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fRM, hostDyn, mRM, match_multi_rate_IRv2, vsM, Run.dynOf,
      Run.lowerE, hm10, hm3, hm2, hm1, hm4, hm01, hm0, hm00, hm115, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstM]

theorem fRM1_eval (q : ℕ) (hq : q < 1) (x : State (Var 2)) :
    Term.eval (fRM q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fRM, hostDyn, mRM, match_multi_rate_IRv2, vsM, Run.dynOf,
      Run.lowerE, hm10, hm3, hm2, hm1, hm4, hm01, hm0, hm00, hm115, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRM (x : State (Var 2)) : Formula.sat domRM x ↔
    (0 ≤ x (Rv 1) ∧ 0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ (23:ℝ)/20) := by
  simp only [domRM, hostEvolve, mRM, match_multi_rate_IRv2, vsM]
  simp [Run.lowerF, Run.lowerE, hm00, hm115,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end MatchMultiRateModal

namespace MatchMultiRateGuarded

open DL DLCalTiming DLRel Parse Set MatchMultiRateModal

/-- The declared edge `st → tgt` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (st tgt : ℕ) : REdge (Var 2) :=
  { src := st, tgt := tgt, guard := hostGuard vsM 2 Side.R (mRM tgt), pruned := false }

noncomputable def GrPG : SearchGraph (Var 2) :=
  { modes := [modeM 0, modeM 1], edges := [edgeG 0 0, edgeG 0 1, edgeG 1 1] }

theorem GrPG_modeAt (q : ℕ) (hq : q < 2) : GrPG.modeAt q = some (modeM q) := by
  interval_cases q <;> rfl

theorem hm02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- `DRIVE`'s guard, evaluated (`0.2 ≤ v ≤ 1`). -/
theorem sat_guardDRIVE (x : State (Var 2)) :
    Formula.sat (hostGuard vsM 2 Side.R (mRM 0)) x ↔ 1/5 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1 := by
  simp [hostGuard, mRM, match_multi_rate_IRv2, Run.lowerF, Run.lowerE, hm02, hm10, vsM,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

noncomputable def driveEnd (ρ : State (Var 2)) (t : ℝ) : State (Var 2) :=
  fun x => if x = Rv 0 then 1 - (1 - ρ (Rv 0)) * Real.exp (-t)
    else if x = Rv 1 then ρ (Rv 1) + t - (1 - ρ (Rv 0)) * (1 - Real.exp (-t)) else ρ x

theorem driveEnd_R0 (ρ : State (Var 2)) (t : ℝ) :
    driveEnd ρ t (Rv 0) = 1 - (1 - ρ (Rv 0)) * Real.exp (-t) := by simp [driveEnd]

theorem driveEnd_R1 (ρ : State (Var 2)) (t : ℝ) :
    driveEnd ρ t (Rv 1) = ρ (Rv 1) + t - (1 - ρ (Rv 0)) * (1 - Real.exp (-t)) := by
  simp [driveEnd, show (Rv 1 : Var 2) ≠ Rv 0 from by simp [Rv, Prod.ext_iff]]

theorem driveEnd_ne (ρ : State (Var 2)) (t : ℝ) {x : Var 2} (h0 : x ≠ Rv 0) (h1 : x ≠ Rv 1) :
    driveEnd ρ t x = ρ x := by simp [driveEnd, h0, h1]

theorem drive_sem (ρ : State (Var 2)) (hdom : Formula.sat domRM ρ) (hw1 : ρ (Rv 0) ≤ 1)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Program.sem (Program.ode (modeM 0).sys (modeM 0).dom) ρ (driveEnd ρ τ) := by
  have hD := (sat_domRM ρ).mp hdom
  refine ⟨τ, fun t => driveEnd ρ t, hτ, ?_, rfl, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp [driveEnd]
    · by_cases h1 : x = Rv 1
      · subst h1; simp [driveEnd_R1]
      · exact driveEnd_ne ρ 0 h0 h1
  · intro t ht p hp
    simp only [modeM, rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hexp : HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-t) * (-1))
        (Set.Icc 0 τ) t := by
      have := (hasDerivAt_id t).neg.exp
      simpa using this.hasDerivWithinAt
    fin_cases i
    · show HasDerivWithinAt (fun u => driveEnd ρ u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRM 0 0)) (driveEnd ρ t)) _ t
      simp only [Term.eval, AOp.interp]
      rw [fRM0_eval 0 (by norm_num), driveEnd_R0]
      have h := (hexp.const_mul (1 - ρ (Rv 0))).const_sub 1
      refine (h.congr (fun y _ => driveEnd_R0 ρ y) (driveEnd_R0 ρ t)).congr_deriv ?_
      simp [cstM]
    · show HasDerivWithinAt (fun u => driveEnd ρ u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRM 0 1)) (driveEnd ρ t)) _ t
      simp only [Term.eval, AOp.interp]
      rw [fRM1_eval 0 (by norm_num), driveEnd_R0]
      have hid := hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)
      have h := ((hid.const_add (ρ (Rv 1))).sub ((hexp.const_sub 1).const_mul (1 - ρ (Rv 0))))
      refine (h.congr (fun y _ => by rw [driveEnd_R1]; simp) (by rw [driveEnd_R1]; simp)).congr_deriv
        ?_
      simp
  · intro t ht x hx
    have h0 : x ≠ Rv 0 := by
      rintro rfl; exact hx (by simp [modeM, rightBlock, ODESystem.bound])
    have h1 : x ≠ Rv 1 := by
      rintro rfl; exact hx (by simp [modeM, rightBlock, ODESystem.bound])
    exact driveEnd_ne ρ t h0 h1
  · intro t ht
    have he0 := Real.exp_pos (-t)
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    have hlin : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
    refine (sat_domRM _).mpr ⟨?_, ?_, ?_⟩
    · show 0 ≤ driveEnd ρ t (Rv 1)
      rw [driveEnd_R1]
      nlinarith [hD.1, hD.2.1]
    · show 0 ≤ driveEnd ρ t (Rv 0)
      rw [driveEnd_R0]; nlinarith [hD.2.1]
    · show driveEnd ρ t (Rv 0) ≤ 23/20
      rw [driveEnd_R0]; nlinarith [hD.2.1]

/-- The instance's explicit `DRIVE` run (`drive_sem`), with its duration kept. -/
theorem drive_sol (ρ : State (Var 2)) (hdom : Formula.sat domRM ρ) (hw1 : ρ (Rv 0) ≤ 1)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeM 0).sys (modeM 0).dom ρ τ (fun t => driveEnd ρ t) := by
  have hD := (sat_domRM ρ).mp hdom
  refine ⟨hτ, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp [driveEnd]
    · by_cases h1 : x = Rv 1
      · subst h1; simp [driveEnd_R1]
      · exact driveEnd_ne ρ 0 h0 h1
  · intro t ht p hp
    simp only [modeM, rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hexp : HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-t) * (-1))
        (Set.Icc 0 τ) t := by
      have := (hasDerivAt_id t).neg.exp
      simpa using this.hasDerivWithinAt
    fin_cases i
    · show HasDerivWithinAt (fun u => driveEnd ρ u (Rv 0))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRM 0 0)) (driveEnd ρ t)) _ t
      simp only [Term.eval, AOp.interp]
      rw [fRM0_eval 0 (by norm_num), driveEnd_R0]
      have h := (hexp.const_mul (1 - ρ (Rv 0))).const_sub 1
      refine (h.congr (fun y _ => driveEnd_R0 ρ y) (driveEnd_R0 ρ t)).congr_deriv ?_
      simp [cstM]
    · show HasDerivWithinAt (fun u => driveEnd ρ u (Rv 1))
        (Term.eval (Term.binop AOp.mul (Term.const 1) (fRM 0 1)) (driveEnd ρ t)) _ t
      simp only [Term.eval, AOp.interp]
      rw [fRM1_eval 0 (by norm_num), driveEnd_R0]
      have hid := hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)
      have h := ((hid.const_add (ρ (Rv 1))).sub ((hexp.const_sub 1).const_mul (1 - ρ (Rv 0))))
      refine (h.congr (fun y _ => by rw [driveEnd_R1]; simp) (by rw [driveEnd_R1]; simp)).congr_deriv
        ?_
      simp
  · intro t ht x hx
    have h0 : x ≠ Rv 0 := by
      rintro rfl; exact hx (by simp [modeM, rightBlock, ODESystem.bound])
    have h1 : x ≠ Rv 1 := by
      rintro rfl; exact hx (by simp [modeM, rightBlock, ODESystem.bound])
    exact driveEnd_ne ρ t h0 h1
  · intro t ht
    have he0 := Real.exp_pos (-t)
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    have hlin : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
    refine (sat_domRM _).mpr ⟨?_, ?_, ?_⟩
    · show 0 ≤ driveEnd ρ t (Rv 1)
      rw [driveEnd_R1]
      nlinarith [hD.1, hD.2.1]
    · show 0 ≤ driveEnd ρ t (Rv 0)
      rw [driveEnd_R0]; nlinarith [hD.2.1]
    · show driveEnd ρ t (Rv 0) ≤ 23/20
      rw [driveEnd_R0]; nlinarith [hD.2.1]

theorem hm03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hmm2 : Run.parseRat "-2" = some (-2 : ℚ) := by
  have h : parseQ "-2" = some (⟨-2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR match_multi_rate_IRv2 = 3/10 := by
  simp [epsR, match_multi_rate_IRv2, hm03]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vsM 2 Side.R (mRM q)

theorem sat_guardSTALL (x : State (Var 2)) :
    Formula.sat (hostGuard vsM 2 Side.R (mRM 1)) x ↔ x (Rv 0) < 1/5 := by
  simp [hostGuard, mRM, match_multi_rate_IRv2, Run.lowerF, Run.lowerE, hm02, vsM,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fRM_stall0 (x : State (Var 2)) : Term.eval (fRM 1 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fRM, hostDyn, mRM, match_multi_rate_IRv2, vsM, Run.dynOf, Run.lowerE, hmm2,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fRM_stall1 (x : State (Var 2)) : Term.eval (fRM 1 1) x = x (Rv 0) := by
  simp [fRM, hostDyn, mRM, match_multi_rate_IRv2, vsM, Run.dynOf, Run.lowerE, hmm2,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The explicit `STALL` run: `v = v₀ e^{−2t}`, `s = s₀ + v₀ (1 − e^{−2t}) / 2`. -/
noncomputable def stallφ (ρ : State (Var 2)) : Fin 2 → ℝ → ℝ := fun i t =>
  if i = 0 then 0 + (ρ (Rv 0) - 0) * Real.exp (-(2 * t))
  else ρ (Rv 1) + 0 * t + (ρ (Rv 0) - 0) * (1 - Real.exp (-(2 * t))) / 2

theorem stall_sol (ρ : State (Var 2)) (hdom : Formula.sat domRM ρ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeM 1).sys (modeM 1).dom ρ τ (trajR ρ (stallφ ρ)) := by
  have hD := (sat_domRM ρ).mp hdom
  refine explicit_sol ρ (stallφ ρ) τ hτ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [stallφ]
  · intro i t _ _
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [fRM_stall0, trajR_R]
      have h := hasDerivAt_expApproach 2 0 (ρ (Rv 0)) t
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [fRM_stall1, trajR_R]
      have h := hasDerivAt_expIntegral 2 0 (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
  · intro t ht _
    have he0 := Real.exp_pos (-(2 * t))
    have he1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    refine (sat_domRM _).mpr ⟨?_, ?_, ?_⟩
    · rw [trajR_R]; simp only [stallφ]; norm_num; nlinarith [hD.1, hD.2.1]
    · rw [trajR_R]; simp only [stallφ]; norm_num; nlinarith [hD.2.1]
    · rw [trajR_R]; simp only [stallφ]; norm_num; nlinarith [hD.2.1, hD.2.2]

/-- **Assumption 1 for `match_multi_rate`**, every mode, Z3-free. -/
theorem match_multi_rate_wellFormedR :
    WellFormedR GrPG guardR (epsR match_multi_rate_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  have hq2 : q < 2 := hq
  have hmq : m = modeM q := by
    have := GrPG_modeAt q hq2; rw [hm] at this; exact Option.some.inj this
  subst hmq
  interval_cases q
  · have hgx := (sat_guardDRIVE x).mp hg
    refine ⟨⟨_, drive_sol x hd hgx.2 (3/10) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hup := H.linear_up (rightBlock_mem' (fRM 0) (Term.const 1) 0) 1 1 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fRM0_eval 0 (by norm_num)]; simp [cstM]) hgx.2
    exact ⟨edgeG 0 0, List.mem_filter.mpr ⟨by simp [GrPG], by simp [edgeG]⟩,
      (sat_guardDRIVE _).mpr ⟨by linarith [hup.1], hup.2⟩⟩
  · have hgx := (sat_guardSTALL x).mp hg
    refine ⟨⟨_, stall_sol x hd (3/10) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hdn := H.linear_down (rightBlock_mem' (fRM 1) (Term.const 1) 0) 2 0 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fRM_stall0]) ((sat_domRM x).mp hd).2.1
    exact ⟨edgeG 1 1, List.mem_filter.mpr ⟨by simp [GrPG], by simp [edgeG]⟩,
      (sat_guardSTALL _).mpr (by linarith [hdn.2])⟩

end MatchMultiRateGuarded

end RelCertifier
