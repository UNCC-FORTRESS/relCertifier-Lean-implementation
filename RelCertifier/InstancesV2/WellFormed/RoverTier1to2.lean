/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_tier_1to2`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/RoverTier1to2Guarded.lean`), the lowered right guards, `ε_r = 0.3` (the
literal is the suite_v2 file's, `InstancesV2/SameIR.lean`). Both modes run `v' = a`,
`s' = v`, `a' = 0` with `a ∈ [0.5, 1]` on the evolve domain, so `v` only grows.
* `ACCEL` (`0.3 ≤ v < 0.6`), style (b): a run ends at `v ≥ v₀ ≥ 0.3`, inside `ACCEL` or
  `COAST` (`v ≥ 0.6`).
* `COAST` (`v ≥ 0.6`), style (a): forward invariant.
Existence: the instance's explicit polynomial run (`runEnd`). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_tier_1to2
import RelCertifier.Proofs.Encoding.WellFormedR

set_option maxHeartbeats 12800000
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverTier1to2Modal

open DL DLCalTiming DLRel Parse Set

def vsQ : List String := ["v", "s", "a"]

def dummyQ : Parse.PMode := ⟨"", [], .tt, .tt, []⟩

def mRQ (q : ℕ) : Parse.PMode := rover_tier_1to2_IRv2.R.modes.getD q dummyQ

noncomputable def fRQ (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsQ 3 Side.R (mRQ q)

noncomputable def domRQ : Formula (Var 3) := hostEvolve vsQ 3 Side.R (mRQ 0)

noncomputable def modeQ (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fRQ q) (Term.const 1), dom := domRQ, weight := 1 }

theorem hq0 : Run.parseRat "0" = some (0) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq1 : Run.parseRat "1" = some (1) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hq10 : Run.parseRat "1.0" = some (1) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq00 : Run.parseRat "0.0" = some (0) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hq06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fRQ0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fRQ q 0) x = x (Rv 2) := by
  interval_cases q <;>
    · simp [fRQ, hostDyn, mRQ, rover_tier_1to2_IRv2, vsQ, Run.dynOf,
      Run.lowerE, hq0, hq1, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRQ1_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fRQ q 1) x = x (Rv 0) := by
  interval_cases q <;>
    · simp [fRQ, hostDyn, mRQ, rover_tier_1to2_IRv2, vsQ, Run.dynOf,
      Run.lowerE, hq0, hq1, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRQ2_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fRQ q 2) x = 0 := by
  interval_cases q <;>
    · simp [fRQ, hostDyn, mRQ, rover_tier_1to2_IRv2, vsQ, Run.dynOf,
      Run.lowerE, hq0, hq1, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem sat_domRQ (x : State (Var 3)) : Formula.sat domRQ x ↔
    ((1:ℝ)/2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 1 ∧ 0 ≤ x (Rv 1) ∧ 0 ≤ x (Rv 0)) := by
  simp only [domRQ, hostEvolve, mRQ, rover_tier_1to2_IRv2, vsQ]
  simp [Run.lowerF, Run.lowerE, hq05, hq10, hq00,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

end RoverTier1to2Modal

namespace RoverTier1to2Guarded

open DL DLCalTiming DLRel Parse Set RoverTier1to2Modal

/-- The declared edge `st → tgt` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsQ 3 Side.R (mRQ tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeQ 0, modeQ 1],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 0, edgeG 1 1] }

theorem GrG_modeAt (q : ℕ) (hq : q < 2) : GrG.modeAt q = some (modeQ q) := by
  interval_cases q <;> rfl

theorem GrG_len : GrG.modes.length = 2 := rfl

theorem edgeG_mem (st tgt : ℕ) (hst : st < 2) (htgt : tgt < 2) :
    edgeG st tgt ∈ GrG.edgesFrom st := by
  refine List.mem_filter.mpr ⟨?_, by simp [edgeG]⟩
  interval_cases st <;> interval_cases tgt <;> simp [GrG]

/-- The right guards, evaluated (`ACCEL`: `0.3 ≤ v < 0.6`; `COAST`: `v ≥ 0.6`). -/
theorem sat_guardRQ (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Formula.sat (hostGuard vsQ 3 Side.R (mRQ q)) x ↔
      (if q = 0 then 3/10 ≤ x (Rv 0) ∧ x (Rv 0) < 3/5 else 3/5 ≤ x (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mRQ, rover_tier_1to2_IRv2, Run.lowerF, Run.lowerE, hq03, hq06, vsQ,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

noncomputable def runEnd (ρ : State (Var 3)) (τ : ℝ) : State (Var 3) :=
  fun x => if x = Rv 0 then ρ (Rv 0) + ρ (Rv 2) * τ
    else if x = Rv 1 then ρ (Rv 1) + ρ (Rv 0) * τ + ρ (Rv 2) * τ ^ 2 / 2 else ρ x

theorem runEnd_ne (ρ : State (Var 3)) (τ : ℝ) {x : Var 3} (h0 : x ≠ Rv 0) (h1 : x ≠ Rv 1) :
    runEnd ρ τ x = ρ x := by simp [runEnd, h0, h1]

theorem runEnd_R0 (ρ : State (Var 3)) (τ : ℝ) : runEnd ρ τ (Rv 0) = ρ (Rv 0) + ρ (Rv 2) * τ := by
  simp [runEnd]

theorem runEnd_R1 (ρ : State (Var 3)) (τ : ℝ) :
    runEnd ρ τ (Rv 1) = ρ (Rv 1) + ρ (Rv 0) * τ + ρ (Rv 2) * τ ^ 2 / 2 := by
  simp [runEnd, show (Rv 1 : Var 3) ≠ Rv 0 from by simp [Rv, Prod.ext_iff]]

theorem runEnd_R2 (ρ : State (Var 3)) (τ : ℝ) : runEnd ρ τ (Rv 2) = ρ (Rv 2) :=
  runEnd_ne ρ τ (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])

/-- The explicit solution is a run of either right mode, for any duration. -/
theorem run_sol (q : ℕ) (hq : q < 2) (ρ : State (Var 3)) (hdom : Formula.sat domRQ ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeQ q).sys (modeQ q).dom ρ τ (fun t => runEnd ρ t) := by
  have hD := (sat_domRQ ρ).mp hdom
  refine ⟨hτ, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp [runEnd]
    · by_cases h1 : x = Rv 1
      · subst h1; simp [runEnd_R1]
      · exact runEnd_ne ρ 0 h0 h1
  · intro t ht p hp
    simp only [modeQ, rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    fin_cases i
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨0, by norm_num⟩))
          (runEnd ρ t) = ρ (Rv 2) := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨0, by norm_num⟩ = fRQ q 0 from rfl, fRQ0_eval q hq, runEnd_R2]
        ring
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => ρ (Rv 0) + ρ (Rv 2) * u) (ρ (Rv 2) * 1)
          (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (ρ (Rv 2))).const_add (ρ (Rv 0))
      rw [mul_one] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [runEnd_R0]
      · simp [runEnd_R0]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨1, by norm_num⟩))
          (runEnd ρ t) = ρ (Rv 0) + ρ (Rv 2) * t := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨1, by norm_num⟩ = fRQ q 1 from rfl, fRQ1_eval q hq, runEnd_R0]
        ring
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => ρ (Rv 1) + ρ (Rv 0) * u + ρ (Rv 2) * u ^ 2 / 2)
          (ρ (Rv 0) * 1 + ρ (Rv 2) * (2 * t ^ 1 * 1) / 2) (Set.Icc 0 τ) t := by
        have hu := hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)
        exact ((hu.const_mul (ρ (Rv 0))).const_add (ρ (Rv 1))).add
          (((hu.pow 2).const_mul (ρ (Rv 2))).div_const 2)
      have he : ρ (Rv 0) * 1 + ρ (Rv 2) * (2 * t ^ 1 * 1) / 2 = ρ (Rv 0) + ρ (Rv 2) * t := by
        ring
      rw [he] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [runEnd_R1]
      · simp [runEnd_R1]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨2, by norm_num⟩))
          (runEnd ρ t) = 0 := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨2, by norm_num⟩ = fRQ q 2 from rfl, fRQ2_eval q hq]
        ring
      simp only [heval]
      refine HasDerivWithinAt.congr (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (ρ (Rv 2)))
        ?_ ?_
      · intro y _; simp [runEnd_R2]
      · simp [runEnd_R2]
  · intro t ht x hx
    have h0 : x ≠ Rv 0 := by
      rintro rfl
      exact hx (List.mem_map.mpr ⟨(Rv 0, _), List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩,
        rfl⟩)
    have h1 : x ≠ Rv 1 := by
      rintro rfl
      exact hx (List.mem_map.mpr ⟨(Rv 1, _), List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩,
        rfl⟩)
    exact runEnd_ne ρ t h0 h1
  · intro t ht
    refine (sat_domRQ _).mpr ?_
    simp only [runEnd_R2, runEnd_R1, runEnd_R0]
    obtain ⟨ha1, ha2, hs, hv⟩ := hD
    have ht0 := ht.1
    refine ⟨ha1, ha2, ?_, ?_⟩
    · have : 0 ≤ ρ (Rv 0) * t := mul_nonneg hv ht0
      have : 0 ≤ ρ (Rv 2) * t ^ 2 / 2 := by positivity
      linarith
    · have : 0 ≤ ρ (Rv 2) * t := mul_nonneg (by linarith) ht0
      linarith

theorem epsR_eq : epsR rover_tier_1to2_IRv2 = 3/10 := by
  simp [epsR, rover_tier_1to2_IRv2, hq03]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vsQ 3 Side.R (mRQ q)

/-- **Assumption 1 for `rover_tier_1to2`**, every mode, Z3-free. -/
theorem rover_tier_1to2_wellFormedR :
    WellFormedR GrG guardR (epsR rover_tier_1to2_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  rw [GrG_len] at hq
  have hmq : m = modeQ q := by
    have := GrG_modeAt q hq; rw [hm] at this; exact Option.some.inj this
  subst hmq
  refine ⟨⟨_, run_sol q hq x hd (3/10) (by norm_num)⟩, ?_⟩
  intro t Φ _ H
  have hmono := H.mono (rightBlock_mem' (fRQ q) (Term.const 1) 0) (fun s hs => by
    rw [eval_unit_mul, fRQ0_eval q hq]
    have := ((sat_domRQ s).mp hs).1; linarith)
  have hgx := (sat_guardRQ q hq x).mp hg
  interval_cases q
  · simp only [if_true] at hgx
    by_cases h06 : Φ t (Rv 0) < 3/5
    · exact ⟨edgeG 0 0, edgeG_mem 0 0 (by norm_num) (by norm_num),
        (sat_guardRQ 0 (by norm_num) _).mpr (by simp only [if_true]; exact ⟨by linarith, h06⟩)⟩
    · exact ⟨edgeG 0 1, edgeG_mem 0 1 (by norm_num) (by norm_num),
        (sat_guardRQ 1 (by norm_num) _).mpr (by norm_num; linarith)⟩
  · norm_num at hgx
    exact ⟨edgeG 1 1, edgeG_mem 1 1 (by norm_num) (by norm_num),
      (sat_guardRQ 1 (by norm_num) _).mpr (by norm_num; linarith)⟩

end RoverTier1to2Guarded

end RelCertifier
