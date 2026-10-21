/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`InstancesV2/Modal/RoverPatrolZonesGuarded.lean`), the lowered right guards, `ε_r = 1`.
The driving zones run `v' = c − v` (`c` = the zone cap 0.6, 0.9, 1.1, 1.5) and `s' = v`;
`STALL` runs `v' = −2 v`, `s' = v`. Over one interval the odometer grows by at most
`1.6` (the evolve bound on `v`).
* `SLOW` (`0 ≤ s < 20`, `0.3 ≤ v ≤ 0.6`), style (b): ends in `SLOW` or `MEDIUM_ECO`.
* `MEDIUM_ECO` / `MEDIUM_BRISK` (`20 ≤ s < 50`, `0.3 ≤ v ≤ 0.9 / 1.1`), style (b): end in
  the zone itself or `FAST`.
* `FAST` (`s ≥ 50`, `0.3 ≤ v ≤ 1.5`) and `STALL` (`v < 0.2`), style (a).
Existence: the explicit zone runs (`flowR_run`) and the explicit `STALL` decay. Z3-free.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.BenchIR.rover_patrol_zones
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.ReplayOne
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolZones

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle


def vs : List String := ["v", "s"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := rover_patrol_zones_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp09 : Run.parseRat "0.9" = some ((9:ℚ)/10) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp15 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp16 : Run.parseRat "1.6" = some ((8:ℚ)/5) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp500 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
def capQ : ℕ → ℚ
  | 0 => 3/5 | 1 => 9/10 | 2 => 11/10 | _ => 3/2
noncomputable def capL (l : ℕ) : ℝ := (capQ l : ℝ)
theorem cap_bounds (l : ℕ) (hl : l < 4) : 3/5 ≤ capL l ∧ capL l ≤ 3/2 := by
  interval_cases l <;> norm_num [capL, capQ]
/-- Right driving zones: `v' = c − v` with `c` the zone cap (= its command). -/
theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = capL q - x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp09,
      hp11, hp15, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, capL, capQ]

theorem fR1_eval (q : ℕ) (hq : q < 5) (x : State (Var 3)) :
    Term.eval (fR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp09,
      hp11, hp15, hpm20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 5) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp09,
      hp11, hp15, hpm20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8/5 ∧ 0 ≤ x (Rv 1)) := by
  simp only [domR, hostEvolve, mR, rover_patrol_zones_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp16, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared transitions, as indices (`SLOW` 0, `MEDIUM_ECO` 1, `MEDIUM_BRISK` 2,
`FAST` 3, `STALL` 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 0), (0, 4), (1, 3), (1, 1), (1, 4), (2, 3), (2, 2), (2, 4), (3, 3),
   (3, 4), (4, 4)]

/-! ## Existence: each driving zone's flow, explicitly

`v(t) = c + (v₀ − c) e^{−t}` (a convex combination of `v₀` and the command `c`, so inside
`[0, 1.6]`), `s(t) = s₀ + c t + (v₀ − c)(1 − e^{−t}) = s₀ + v₀ (1 − e^{−t}) + c (t − 1 + e^{−t})
≥ s₀` (the odometer never decreases; it has no upper wall). -/

noncomputable def ex (t : ℝ) : ℝ := Real.exp (-t)

noncomputable def solR (c : ℝ) (b : State (Var 3)) (t : ℝ) : State (Var 3) := fun x =>
  if x = Rv 0 then c + (b (Rv 0) - c) * ex t
  else if x = Rv 1 then b (Rv 1) + c * t + (b (Rv 0) - c) * (1 - ex t)
  else b x

theorem solR_0 (c : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c b t (Rv 0) = c + (b (Rv 0) - c) * ex t := by simp [solR]
theorem solR_1 (c : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c b t (Rv 1) = b (Rv 1) + c * t + (b (Rv 0) - c) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (c : ℝ) (b : State (Var 3)) (t : ℝ) {x : Var 3} (h0 : x ≠ Rv 0)
    (h1 : x ≠ Rv 1) : solR c b t x = b x := by
  simp [solR, h0, h1]

theorem ex_hasDeriv (t : ℝ) : HasDerivAt ex (-ex t) t := by
  have h := ((hasDerivAt_id t).neg).exp
  have h' : HasDerivAt ex (Real.exp (-id t) * (-1)) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring
theorem ex_zero : ex 0 = 1 := by simp [ex]
theorem ex_pos (t : ℝ) : 0 < ex t := Real.exp_pos _
theorem ex_le_one {t : ℝ} (ht : 0 ≤ t) : ex t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; linarith
theorem ex_ge (t : ℝ) : 1 - t ≤ ex t := by
  unfold ex; have := Real.add_one_le_exp (-t); linarith

theorem solR_stays (q : ℕ) (hq : q < 4) (b : State (Var 3)) (hb : Formula.sat domR b)
    {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR (capL q) b t) := by
  rw [sat_domR] at hb ⊢
  obtain ⟨h0, h1, h2⟩ := hb
  have hc := cap_bounds q hq
  have he0 := ex_pos t
  have he1 := ex_le_one ht
  have he2 := ex_ge t
  rw [solR_0, solR_1]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem rightBlock_bound_mem (q : ℕ) (i : Fin 3) :
    Rv i ∈ (rightBlock (fR q) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- **The explicit run of a driving zone** (any duration `s ≥ 0`, from any envelope state). -/
theorem flowR_run (q : ℕ) (hq : q < 4) (b : State (Var 3)) (hb : Formula.sat domR b)
    (s : ℝ) :
    solR (capL q) b 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const 1),
          HasDerivWithinAt (fun u => solR (capL q) b u p.1) (p.2.eval (solR (capL q) b t))
            (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const 1)).bound →
        solR (capL q) b t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (solR (capL q) b t)) := by
  set c := capL q with hcdef
  refine ⟨?_, ?_, ?_, fun t ht => solR_stays q hq b hb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero]; ring
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero]; ring
    exact solR_other c b 0 h0 h1
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hd := ex_hasDeriv t
    fin_cases i
    · have h := (((hd.const_mul (b (Rv 0) - c)).const_add c)).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c b u (Rv 0)) = fun u => c + (b (Rv 0) - c) * ex u := by
        funext u; exact solR_0 c b u
      show HasDerivWithinAt (fun u => solR c b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) (solR c b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR0_eval q hq, solR_0]
      exact h.congr_deriv (by rw [← hcdef]; ring)
    · have h := ((((hasDerivAt_id t).const_mul c).const_add (b (Rv 1))).add
        ((hd.const_sub 1).const_mul (b (Rv 0) - c))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c b u (Rv 1)) =
          fun u => (b (Rv 1) + c * id u) + (b (Rv 0) - c) * (1 - ex u) := by
        funext u; rw [solR_1]; rfl
      show HasDerivWithinAt (fun u => solR c b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 1)) (solR c b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR1_eval q (by omega), solR_0]
      exact h.congr_deriv (by ring)
    · have hcurve : (fun u => solR c b u (Rv 2)) = fun _ => b (Rv 2) := by
        funext u
        exact solR_other c b u (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])
      show HasDerivWithinAt (fun u => solR c b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) (solR c b t)) (Icc 0 s) t
      rw [hcurve]
      simp only [Term.eval, AOp.interp]
      rw [fR2_eval q (by omega), mul_zero]
      exact hasDerivWithinAt_const t _ _
  · intro t _ x hx
    refine solR_other c b t (fun h => hx ?_) (fun h => hx ?_)
    · rw [h]; exact rightBlock_bound_mem q 0
    · rw [h]; exact rightBlock_bound_mem q 1

end V2RoverPatrolZones

namespace V2RoverPatrolZonesGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolZones


/-! ## The guarded right graph -/

/-- The declared edge `s → t` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The file's right automaton (the modes and `next` lists of `Gr`, `edgeList_eq_IR`), every
edge guarded. -/
noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_modeAt (q : ℕ) (hq : q < 5) : GrG.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrG_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : GrG.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])

theorem edgeG_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeG s t ∈ GrG.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 20 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/5) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 1)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 9/10) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 2)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 11/10) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR3 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 3)) x ↔
    (50 ≤ x (Rv 1) ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/2) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]


theorem epsR_eq : epsR rover_patrol_zones_IRv2 = 1 := by
  simp [epsR, rover_patrol_zones_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem sat_guardR4 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 4)) x ↔
    x (Rv 0) < 1/5 := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp02, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fR0_stall (x : State (Var 3)) : Term.eval (fR 4 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The explicit `STALL` run: `v = v₀ e^{−2t}`, `s = s₀ + v₀ (1 − e^{−2t}) / 2`. -/
noncomputable def stallφ (ρ : State (Var 3)) : Fin 3 → ℝ → ℝ := fun i t =>
  if i = 0 then 0 + (ρ (Rv 0) - 0) * Real.exp (-(2 * t))
  else if i = 1 then ρ (Rv 1) + 0 * t + (ρ (Rv 0) - 0) * (1 - Real.exp (-(2 * t))) / 2
  else ρ (Rv i)

theorem stall_sol (ρ : State (Var 3)) (hdom : Formula.sat domR ρ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeW 4).sys (modeW 4).dom ρ τ (trajR ρ (stallφ ρ)) := by
  have hD := (sat_domR ρ).mp hdom
  refine explicit_sol ρ (stallφ ρ) τ hτ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [stallφ]
  · intro i t _ _
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [fR0_stall, trajR_R]
      have h := hasDerivAt_expApproach 2 0 (ρ (Rv 0)) t
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [fR1_eval 4 (by norm_num), trajR_R]
      have h := hasDerivAt_expIntegral 2 0 (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
      convert h using 1
      · funext u; simp [stallφ]
      · simp [stallφ]
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [fR2_eval 4 (by norm_num)]
      have hf : stallφ ρ 2 = fun _ => ρ (Rv 2) := by funext u; simp [stallφ]
      rw [hf]
      exact hasDerivAt_const t _
  · intro t ht _
    have he0 := Real.exp_pos (-(2 * t))
    have he1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    obtain ⟨h0, h1, h2⟩ := hD
    refine (sat_domR _).mpr ⟨?_, ?_, ?_⟩ <;> rw [trajR_R] <;> simp only [stallφ] <;> norm_num
      <;> nlinarith

/-- **Assumption 1 for `rover_patrol_zones`**, every mode, Z3-free. -/
theorem rover_patrol_zones_wellFormedR :
    WellFormedR GrG guardR (epsR rover_patrol_zones_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := GrG_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  by_cases h4 : q < 4
  · refine ⟨?_, ?_⟩
    · obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q h4 x hd 1
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
  · have : q = 4 := by omega
    subst this
    have hgx := (sat_guardR4 x).mp hg
    refine ⟨⟨_, stall_sol x hd 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hdn := H.linear_down (rightBlock_mem' (fR 4) (Term.const 1) 0) 2 0 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fR0_stall]) hdx.1
    exact ⟨edgeG 4 4, edgeG_mem 4 4 (by simp [edgeList]), (sat_guardR4 _).mpr (by linarith [hdn.2])⟩

end V2RoverPatrolZonesGuarded
end RelCertifier
