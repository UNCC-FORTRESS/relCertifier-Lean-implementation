/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_refine`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`InstancesV2/Modal/RoverPatrolRefineGuarded.lean`), the lowered right guards, `ε_r = 1`.
The zones run `v' = c − v` (`c` = the zone cap 0.6, 0.9, 1.1, 1.5), `s' = v`, `a' = 0`
(no `STALL` mode in this file). Over one interval the odometer grows by at most `1.6` (the
evolve bound on `v`).
* `SLOW` (`0 ≤ s < 20`, `0.3 ≤ v ≤ 0.6`), style (b): ends in `SLOW` or `MEDIUM_ECO`.
* `MEDIUM_ECO` / `MEDIUM_BRISK` (`20 ≤ s < 50`, `0.3 ≤ v ≤ 0.9 / 1.1`), style (b): end in
  the zone itself or `FAST`.
* `FAST` (`s ≥ 50`, `0.3 ≤ v ≤ 1.5`), style (a).
Existence: the explicit zone runs (`flowR_run`). Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.rover_patrol_refine
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolRefine

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle


def vs : List String := ["v", "s", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := rover_patrol_refine_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp0_48 : Run.parseRat "0.48" = some ((12/25 : ℚ)) := by
  have h : parseQ "0.48" = some (⟨48, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_72 : Run.parseRat "0.72" = some ((18/25 : ℚ)) := by
  have h : parseQ "0.72" = some (⟨72, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_88 : Run.parseRat "0.88" = some ((22/25 : ℚ)) := by
  have h : parseQ "0.88" = some (⟨88, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_2 : Run.parseRat "1.2" = some ((6/5 : ℚ)) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_8 : Run.parseRat "0.8" = some ((4/5 : ℚ)) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_95 : Run.parseRat "0.95" = some ((19/20 : ℚ)) := by
  have h : parseQ "0.95" = some (⟨95, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_05 : Run.parseRat "1.05" = some ((21/20 : ℚ)) := by
  have h : parseQ "1.05" = some (⟨105, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_25 : Run.parseRat "1.25" = some ((5/4 : ℚ)) := by
  have h : parseQ "1.25" = some (⟨125, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm0_95 : Run.parseRat "-0.95" = some ((-19/20 : ℚ)) := by
  have h : parseQ "-0.95" = some (⟨-95, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm1_55 : Run.parseRat "-1.55" = some ((-31/20 : ℚ)) := by
  have h : parseQ "-1.55" = some (⟨-155, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm1_95 : Run.parseRat "-1.95" = some ((-39/20 : ℚ)) := by
  have h : parseQ "-1.95" = some (⟨-195, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm2_75 : Run.parseRat "-2.75" = some ((-11/4 : ℚ)) := by
  have h : parseQ "-2.75" = some (⟨-275, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_1 : Run.parseRat "1.1" = some ((11/10 : ℚ)) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_3 : Run.parseRat "1.3" = some ((13/10 : ℚ)) := by
  have h : parseQ "1.3" = some (⟨13, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_1 : Run.parseRat "0.1" = some ((1/10 : ℚ)) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp2_5 : Run.parseRat "2.5" = some ((5/2 : ℚ)) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp5_0 : Run.parseRat "5.0" = some ((5 : ℚ)) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_35 : Run.parseRat "0.35" = some ((7/20 : ℚ)) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_6 : Run.parseRat "0.6" = some ((3/5 : ℚ)) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_9 : Run.parseRat "0.9" = some ((9/10 : ℚ)) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_5 : Run.parseRat "1.5" = some ((3/2 : ℚ)) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm2_0 : Run.parseRat "-2.0" = some ((-2 : ℚ)) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp2_0 : Run.parseRat "2.0" = some ((2 : ℚ)) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_0 : Run.parseRat "0.0" = some ((0 : ℚ)) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_6 : Run.parseRat "1.6" = some ((8/5 : ℚ)) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp20_0 : Run.parseRat "20.0" = some ((20 : ℚ)) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp50_0 : Run.parseRat "50.0" = some ((50 : ℚ)) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_3 : Run.parseRat "0.3" = some ((3/10 : ℚ)) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0_5 : Run.parseRat "0.5" = some ((1/2 : ℚ)) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hpm0_5 : Run.parseRat "-0.5" = some ((-1/2 : ℚ)) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1_0 : Run.parseRat "1.0" = some ((1 : ℚ)) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp0 : Run.parseRat "0" = some ((0 : ℚ)) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

def loQ : ℕ → ℚ
  | 0 => 0 | 1 => 20 | 2 => 20 | _ => 50
def capQ : ℕ → ℚ
  | 0 => 3/5 | 1 => 9/10 | 2 => 11/10 | _ => 3/2
noncomputable def loL (l : ℕ) : ℝ := (loQ l : ℝ)
noncomputable def capL (l : ℕ) : ℝ := (capQ l : ℝ)
theorem cap_bounds (l : ℕ) (hl : l < 4) : 3/5 ≤ capL l ∧ capL l ≤ 3/2 := by
  interval_cases l <;> norm_num [capL, capQ]

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = capL q - x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv,
      capL, capQ]

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_refine_IRv2, vs, Run.dynOf, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8/5 ∧ 0 ≤ x (Rv 1) ∧ -2 ≤ x (Rv 2) ∧
      x (Rv 2) ≤ 2) := by
  simp only [domR, hostEvolve, mR, rover_patrol_refine_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp0_48, hp0_72, hp0_88, hp1_2, hp0_8, hp0_95, hp1_05, hp1_25, hpm0_95, hpm1_55, hpm1_95, hpm2_75, hp1_1, hp1_3, hp0_1, hp2_5, hp5_0, hp0_35, hp0_6, hp0_9, hp1_5, hpm2_0, hp2_0, hp0_0, hp1_6, hp20_0, hp50_0, hp0_3, hp0_5, hpm0_5, hp1_0, hp0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared transitions, as indices (`SLOW` 0, `MEDIUM_ECO` 1, `MEDIUM_BRISK` 2,
`FAST` 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 0), (1, 3), (1, 1), (2, 3), (2, 2), (3, 3)]

/-! ## Existence: each zone's flow, explicitly, at any rate `k ≥ 0`

`v(t) = c + (v₀ − c) e^{−k t}` (a convex combination of `v₀` and the command `c`, inside
`[0, 1.6]`), `s(t) = s₀ + k c t + (v₀ − c)(1 − e^{−k t}) = s₀ + v₀ (1 − e^{−kt}) +
c (k t − 1 + e^{−k t}) ≥ s₀` (no odometer wall), `a` frozen (the reference has no lag). The
joint pieces run at the cover's λ = 9/4, the right-only repositions at rate 1. -/

noncomputable def ex (k t : ℝ) : ℝ := Real.exp (-(k * t))

noncomputable def solR (c k : ℝ) (b : State (Var 3)) (t : ℝ) : State (Var 3) := fun x =>
  if x = Rv 0 then c + (b (Rv 0) - c) * ex k t
  else if x = Rv 1 then b (Rv 1) + k * c * t + (b (Rv 0) - c) * (1 - ex k t)
  else b x

theorem solR_0 (c k : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c k b t (Rv 0) = c + (b (Rv 0) - c) * ex k t := by simp [solR]
theorem solR_1 (c k : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c k b t (Rv 1) = b (Rv 1) + k * c * t + (b (Rv 0) - c) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (c k : ℝ) (b : State (Var 3)) (t : ℝ) {x : Var 3} (h0 : x ≠ Rv 0)
    (h1 : x ≠ Rv 1) : solR c k b t x = b x := by
  simp [solR, h0, h1]

theorem ex_hasDeriv (k t : ℝ) : HasDerivAt (ex k) (-k * ex k t) t := by
  have h := ((hasDerivAt_id t).const_mul k).neg.exp
  have h' : HasDerivAt (ex k) (Real.exp (-(k * id t)) * (-(k * 1))) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring
theorem ex_zero (k : ℝ) : ex k 0 = 1 := by simp [ex]
theorem ex_pos (k t : ℝ) : 0 < ex k t := Real.exp_pos _
theorem ex_le_one {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) : ex k t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; nlinarith
theorem ex_ge (k t : ℝ) : 1 - k * t ≤ ex k t := by
  unfold ex; have := Real.add_one_le_exp (-(k * t)); linarith

theorem solR_stays (q : ℕ) (hq : q < 4) (k : ℝ) (hk : 0 ≤ k) (b : State (Var 3))
    (hb : Formula.sat domR b) {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR (capL q) k b t) := by
  rw [sat_domR] at hb ⊢
  obtain ⟨h0, h1, h2, h3, h4⟩ := hb
  have hc := cap_bounds q hq
  have he0 := ex_pos k t
  have he1 := ex_le_one hk ht
  have he2 := ex_ge k t
  have hkt : 0 ≤ k * t := mul_nonneg hk ht
  rw [solR_0, solR_1, solR_other _ _ _ _ (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, h3, h4⟩

theorem rightBlock_bound_mem (q : ℕ) (k : ℝ) (i : Fin 3) :
    Rv i ∈ (rightBlock (fR q) (Term.const k)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- **The explicit run of a zone at rate `k`** (any duration `s`, from any envelope state). -/
theorem flowR_run (q : ℕ) (hq : q < 4) (k : ℝ) (hk : 0 ≤ k) (b : State (Var 3))
    (hb : Formula.sat domR b) (s : ℝ) :
    solR (capL q) k b 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const k),
          HasDerivWithinAt (fun u => solR (capL q) k b u p.1) (p.2.eval (solR (capL q) k b t))
            (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const k)).bound →
        solR (capL q) k b t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (solR (capL q) k b t)) := by
  set c := capL q with hcdef
  refine ⟨?_, ?_, ?_, fun t ht => solR_stays q hq k hk b hb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero]; ring
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero]; ring
    exact solR_other c k b 0 h0 h1
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hd := ex_hasDeriv k t
    fin_cases i
    · have h := (((hd.const_mul (b (Rv 0) - c)).const_add c)).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c k b u (Rv 0)) = fun u => c + (b (Rv 0) - c) * ex k u := by
        funext u; exact solR_0 c k b u
      show HasDerivWithinAt (fun u => solR c k b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const k) (fR q 0)) (solR c k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR0_eval q hq, solR_0]
      exact h.congr_deriv (by rw [← hcdef]; ring)
    · have h := ((((hasDerivAt_id t).const_mul (k * c)).const_add (b (Rv 1))).add
        ((hd.const_sub 1).const_mul (b (Rv 0) - c))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c k b u (Rv 1)) =
          fun u => (b (Rv 1) + k * c * id u) + (b (Rv 0) - c) * (1 - ex k u) := by
        funext u; rw [solR_1]; rfl
      show HasDerivWithinAt (fun u => solR c k b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const k) (fR q 1)) (solR c k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR1_eval q hq, solR_0]
      exact h.congr_deriv (by ring)
    · have hcurve : (fun u => solR c k b u (Rv 2)) = fun _ => b (Rv 2) := by
        funext u
        exact solR_other c k b u (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])
      show HasDerivWithinAt (fun u => solR c k b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const k) (fR q 2)) (solR c k b t)) (Icc 0 s) t
      rw [hcurve]
      simp only [Term.eval, AOp.interp]
      rw [fR2_eval q hq, mul_zero]
      exact hasDerivWithinAt_const t _ _
  · intro t _ x hx
    refine solR_other c k b t (fun h => hx ?_) (fun h => hx ?_)
    · rw [h]; exact rightBlock_bound_mem q k 0
    · rw [h]; exact rightBlock_bound_mem q k 1

end V2RoverPatrolRefine

namespace V2RoverPatrolRefineGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolRefine


/-! ## The guarded right graph -/

noncomputable def edgeG (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_modeAt (q : ℕ) (hq : q < 4) : GrG.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrG_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : GrG.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])

theorem edgeG_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeG s t ∈ GrG.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 1)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 9/10) := by
  simp [hostGuard, mR, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0, hp50_0,
    hp0_3, hp0_6, hp0_9, hp1_1, hp1_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR3 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 3)) x ↔
    (50 ≤ x (Rv 1) ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/2) := by
  simp [hostGuard, mR, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0, hp50_0,
    hp0_3, hp0_6, hp0_9, hp1_1, hp1_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- The zone guards: `lo ≤ s < hi` (no ceiling in `FAST`), `0.3 ≤ v ≤ cap`. -/
theorem sat_guardR (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) x ↔
      (loL q ≤ x (Rv 1) ∧ (q < 3 → x (Rv 1) < (if q = 0 then 20 else 50)) ∧
        3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ capL q) := by
  interval_cases q <;>
    simp [hostGuard, mR, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0,
      hp50_0, hp0_3, hp0_6, hp0_9, hp1_1, hp1_5, vs, Run.resolveVar, List.findIdx?_cons,
      IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc, loL,
      loQ, capL, capQ]


theorem epsR_eq : epsR rover_patrol_refine_IRv2 = 1 := by
  simp [epsR, rover_patrol_refine_IRv2, hp1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 20 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/5) := by
  rw [sat_guardR 0 (by norm_num)]; simp [loL, loQ, capL, capQ]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 2)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 11/10) := by
  rw [sat_guardR 2 (by norm_num)]; simp [loL, loQ, capL, capQ]

/-- **Assumption 1 for `rover_patrol_refine`**, every mode, Z3-free. -/
theorem rover_patrol_refine_wellFormedR :
    WellFormedR GrG guardR (epsR rover_patrol_refine_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨h4, rfl⟩ := GrG_modeAt_inv hm
  have hq5 := h4
  · refine ⟨?_, ?_⟩
    · obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q h4 1 zero_le_one x hd 1
      exact ⟨_, ⟨by norm_num, h0, hder, hmask, hdom⟩⟩
    intro t Φ ht H
    have hv := H.linear_between (rightBlock_mem' (fR q) (Term.const 1) 0) 1 (capL q)
      (by norm_num) (fun s _ => by rw [eval_unit_mul, fR0_eval q h4]; ring)
    have hsup := H.rate_le (rightBlock_mem' (fR q) (Term.const 1) 1) (8/5)
      (fun s hs => by rw [eval_unit_mul, fR1_eval q hq5]; exact ((sat_domR s).mp hs).2.1)
    have hslo := H.mono (rightBlock_mem' (fR q) (Term.const 1) 1)
      (fun s hs => by rw [eval_unit_mul, fR1_eval q hq5]; exact ((sat_domR s).mp hs).1)
    have hr := H.hr
    interval_cases q
    · -- SLOW
      obtain ⟨hs0, hs1, hv0, hv1⟩ := (sat_guardR0 x).mp hg
      have hc : capL 0 = 3/5 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      by_cases h20 : Φ t (Rv 1) < 20
      · exact ⟨edgeG 0 0, edgeG_mem 0 0 (by simp [edgeList]),
          (sat_guardR0 _).mpr ⟨by linarith, h20, by linarith [hv.1], hv.2⟩⟩
      · exact ⟨edgeG 0 1, edgeG_mem 0 1 (by simp [edgeList]),
          (sat_guardR1 _).mpr ⟨by linarith, by nlinarith, by linarith [hv.1], by linarith [hv.2]⟩⟩
    · -- MEDIUM_ECO
      obtain ⟨hs0, hs1, hv0, hv1⟩ := (sat_guardR1 x).mp hg
      have hc : capL 1 = 9/10 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      by_cases h50 : Φ t (Rv 1) < 50
      · exact ⟨edgeG 1 1, edgeG_mem 1 1 (by simp [edgeList]),
          (sat_guardR1 _).mpr ⟨by linarith, h50, by linarith [hv.1], hv.2⟩⟩
      · exact ⟨edgeG 1 3, edgeG_mem 1 3 (by simp [edgeList]),
          (sat_guardR3 _).mpr ⟨by linarith, by linarith [hv.1], by linarith [hv.2]⟩⟩
    · -- MEDIUM_BRISK
      obtain ⟨hs0, hs1, hv0, hv1⟩ := (sat_guardR2 x).mp hg
      have hc : capL 2 = 11/10 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      by_cases h50 : Φ t (Rv 1) < 50
      · exact ⟨edgeG 2 2, edgeG_mem 2 2 (by simp [edgeList]),
          (sat_guardR2 _).mpr ⟨by linarith, h50, by linarith [hv.1], hv.2⟩⟩
      · exact ⟨edgeG 2 3, edgeG_mem 2 3 (by simp [edgeList]),
          (sat_guardR3 _).mpr ⟨by linarith, by linarith [hv.1], by linarith [hv.2]⟩⟩
    · -- FAST
      obtain ⟨hs0, hv0, hv1⟩ := (sat_guardR3 x).mp hg
      have hc : capL 3 = 3/2 := by norm_num [capL, capQ]
      rw [hc, min_eq_left hv1, max_eq_right hv1] at hv
      exact ⟨edgeG 3 3, edgeG_mem 3 3 (by simp [edgeList]),
        (sat_guardR3 _).mpr ⟨by linarith, by linarith [hv.1], hv.2⟩⟩

end V2RoverPatrolRefineGuarded
end RelCertifier
