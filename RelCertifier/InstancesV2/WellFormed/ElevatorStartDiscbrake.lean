/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `elevator_start_discbrake`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
four trip phases and their declared `next` lists), the lowered right guards, and `ε_r = 0.1`
read from the file.

The right model is the validated trip with the drum brake: car position `z` (coordinate 0),
speed `v` (coordinate 1) and brake lift `b` (coordinate 2), inside `−0.5 ≤ z ≤ 20.5`,
`0 ≤ v ≤ 1.7`, `0 ≤ b ≤ 1`.
`LIFT` (`z ≤ 0.1`, `v ≤ 0`, `b < 0.95`): `z' = v' = 0`, `b' = 5 (1 − b)`;
`UP` (`z < 18`, `b ≥ 0.95`): `z' = v`, `v' = 0.8 (1.6 − v)`, `b' = 5 (1 − b)`;
`APP` (`18 ≤ z < 19.9`): `z' = v`, `v' = 0.8 (0.25 − v)`, `b' = 5 (1 − b)`;
`STOP` (`z ≥ 19.9`, `z + v/4 ≤ 20.5`): `z' = v`, `v' = −4 v`, `b' = −5 b`.
* Existence (i): `v` and `b` the explicit exponentials (inside their ranges), `z` held in `LIFT`,
  the integral of `v` in `UP` and `APP` (it does not fall and grows by at most `1.7 · 0.1`, so
  it stays below `18.17` resp. `20.07`), and in `STOP` the closed form
  `z₀ + v₀/4 − (v₀/4) e^{−4 t}`, below the rest position `z₀ + v₀/4 ≤ 20.5` (the guard).
* (ii): `LIFT`: `z, v` are constant and `b` rises toward 1, so the run ends in `LIFT` or (once
  `b ≥ 0.95`) in `UP`; `UP`: `b ≥ 0.95` is kept and `z` grows by at most `0.17`, so the run
  ends in `UP` or `APP`; `APP`: `z` does not fall and ends below `20.07` with `v ≤ 1.7`, so in
  `APP` or in `STOP` (`z + v/4 < 20.07 + 0.425 ≤ 20.5`); `STOP`: the rest position `z + v/4` is
  constant along the flow and `z` does not fall (style (a)).
Z3-free; modelled on `MoldingPackCheckring.lean` and `WellFormedTerrain.intSol`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.elevator_start_discbrake

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ElevatorStartDiscbrake

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["z", "v", "b"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := elevator_start_discbrake_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_m0_5 : Run.parseRat "-0.5" = some ((-1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_25 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_8 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_95 : Run.parseRat "0.95" = some ((19:ℚ)/20) := by
  have h : parseQ "0.95" = some (⟨95, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_6 : Run.parseRat "1.6" = some ((8:ℚ)/5) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_7 : Run.parseRat "1.7" = some ((17:ℚ)/10) := by
  have h : parseQ "1.7" = some (⟨17, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_18_0 : Run.parseRat "18.0" = some (18 : ℚ) := by
  have h : parseQ "18.0" = some (⟨180, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_19_9 : Run.parseRat "19.9" = some ((199:ℚ)/10) := by
  have h : parseQ "19.9" = some (⟨199, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_20_5 : Run.parseRat "20.5" = some ((41:ℚ)/2) := by
  have h : parseQ "20.5" = some (⟨205, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_4_0 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_5_0 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The speed loop's set point: `UP` 1.6, `APP` 0.25. -/
noncomputable def cV (q : ℕ) : ℝ := if q = 1 then 8/5 else 1/4

theorem fL0_eval (x : State (Var 3)) : Term.eval (fR 0 0) x = 0 := by
  simp [fR, hostDyn, mR, elevator_start_discbrake_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fL1_eval (x : State (Var 3)) : Term.eval (fR 0 1) x = 0 := by
  simp [fR, hostDyn, mR, elevator_start_discbrake_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

/-- `z' = v` in `UP`, `APP`, `STOP`. -/
theorem fz_eval (q : ℕ) (h1 : 1 ≤ q) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = x (Rv 1) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, elevator_start_discbrake_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

/-- The speed loop of `UP` and `APP`. -/
theorem fv_eval (q : ℕ) (h1 : 1 ≤ q) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 4/5 * (cV q - x (Rv 1)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, elevator_start_discbrake_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, cV]

theorem fS1_eval (x : State (Var 3)) : Term.eval (fR 3 1) x = 4 * (0 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, elevator_start_discbrake_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

/-- The brake lifts in `LIFT`, `UP`, `APP`. -/
theorem fb_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 5 * (1 - x (Rv 2)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, elevator_start_discbrake_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem fS2_eval (x : State (Var 3)) : Term.eval (fR 3 2) x = 5 * (0 - x (Rv 2)) := by
  simp [fR, hostDyn, mR, elevator_start_discbrake_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv] <;> ring

theorem sat_domR (ν : State (Var 3)) :
    Formula.sat domR ν ↔
      (-1/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 41/2 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 17/10 ∧ 0 ≤ ν (Rv 2) ∧
        ν (Rv 2) ≤ 1) := by
  simp only [domR, hostEvolve, mR, elevator_start_discbrake_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (LIFT 0, UP 1, APP 2, STOP 3). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 3), (3, 3)]

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

theorem sat_g0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 0) ≤ 1/10 ∧ ν (Rv 1) ≤ 0 ∧ ν (Rv 2) < 19/20 ∧ -1/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 41/2 ∧
        0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 17/10 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, elevator_start_discbrake_IRv2, Run.lowerF, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (ν (Rv 0) < 18 ∧ 19/20 ≤ ν (Rv 2) ∧ -1/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 41/2 ∧
        0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 17/10 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, elevator_start_discbrake_IRv2, Run.lowerF, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      (18 ≤ ν (Rv 0) ∧ ν (Rv 0) < 199/10 ∧ -1/2 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 41/2 ∧
        0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 17/10 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, elevator_start_discbrake_IRv2, Run.lowerF, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔
      (199/10 ≤ ν (Rv 0) ∧ ν (Rv 0) + 1/4 * ν (Rv 1) ≤ 41/2 ∧ -1/2 ≤ ν (Rv 0) ∧
        ν (Rv 0) ≤ 41/2 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 17/10 ∧ 0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 1) := by
  simp [hostGuard, mR, elevator_start_discbrake_IRv2, Run.lowerF, Run.lowerE, hp_m0_5, hp_0_0, hp_0_1, hp_0_25, hp_0_8, hp_0_95, hp_1_0, hp_1_6, hp_1_7, hp_18_0, hp_19_9, hp_20_5, hp_4_0, hp_5_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR elevator_start_discbrake_IRv2 = 1/10 := by
  simp [epsR, elevator_start_discbrake_IRv2, hp_0_1]

/-! ## Existence: the explicit runs -/

/-- The exponential approach `c + (y₀ − c) e^{−k t}`. -/
noncomputable def ea (k c y0 t : ℝ) : ℝ := c + (y0 - c) * Real.exp (-(k * t))

theorem ea_cont (k c y0 : ℝ) : Continuous (ea k c y0) := by unfold ea; fun_prop

theorem ea_zero (k c y0 : ℝ) : ea k c y0 0 = y0 := by simp [ea]

theorem ea_der (k c y0 t : ℝ) : HasDerivAt (ea k c y0) (k * (c - ea k c y0 t)) t :=
  hasDerivAt_expApproach k c y0 t

theorem ea_between (k c y0 t : ℝ) (hk : 0 ≤ k) (ht : 0 ≤ t) {lo hi : ℝ} (h1 : lo ≤ y0)
    (h2 : y0 ≤ hi) (h3 : lo ≤ c) (h4 : c ≤ hi) : lo ≤ ea k c y0 t ∧ ea k c y0 t ≤ hi := by
  obtain ⟨l, u⟩ := exp_approach_between k c y0 t hk ht
  exact ⟨le_trans (le_min h1 h3) l, le_trans u (max_le h2 h4)⟩

/-- The integral of a rate in `[0, B]` does not fall and grows by at most `B t`. -/
theorem intSol_bounds (z0 : ℝ) {G : ℝ → ℝ} (hG : Continuous G) (B T : ℝ)
    (hb : ∀ u ∈ Icc (0:ℝ) T, 0 ≤ G u ∧ G u ≤ B) :
    ∀ t ∈ Icc (0:ℝ) T, z0 ≤ intSol z0 G t ∧ intSol z0 G t ≤ z0 + B * t := by
  intro t ht
  have h1 := mono_of_deriv_nonneg (fun u => intSol_hasDerivAt z0 hG u)
    (fun u hu => (hb u hu).1) t ht
  have hd2 : ∀ u, HasDerivAt (fun w => z0 + B * w - intSol z0 G w) (B - G u) u := by
    intro u
    have := (((hasDerivAt_id u).const_mul B).const_add z0).sub (intSol_hasDerivAt z0 hG u)
    simp only [mul_one] at this
    exact this
  have h2 := mono_of_deriv_nonneg hd2 (fun u hu => by linarith [(hb u hu).2]) t ht
  rw [intSol_zero] at h1 h2
  constructor
  · exact h1
  · simp only [mul_zero, add_zero, sub_self] at h2; linarith

/-- The run of `LIFT` from `x`: the car held, the brake lifting. -/
noncomputable def phiL (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) else if i.val = 1 then x (Rv 1) else ea 5 1 (x (Rv 2)) t

/-- The run of `UP` (`q = 1`) or `APP` (`q = 2`) from `x`: the speed loop, its integral, the
brake lifting. -/
noncomputable def phiM (q : ℕ) (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then intSol (x (Rv 0)) (ea (4/5) (cV q) (x (Rv 1))) t
  else if i.val = 1 then ea (4/5) (cV q) (x (Rv 1)) t
  else ea 5 1 (x (Rv 2)) t

/-- The run of `STOP` from `x`: the stop at rest position `z₀ + v₀/4`, the brake dropping. -/
noncomputable def phiS (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then ea 4 (x (Rv 0) + x (Rv 1) / 4) (x (Rv 0)) t
  else if i.val = 1 then ea 4 0 (x (Rv 1)) t
  else ea 5 0 (x (Rv 2)) t

theorem phiL_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiL x i) (Term.eval (fR 0 i) (trajRs x (phiL x) t)) t := by
  match i with
  | 0 =>
      rw [fL0_eval]
      have hf : phiL x 0 = fun _ => x (Rv 0) := by funext u; simp [phiL]
      rw [hf]; exact hasDerivAt_const _ _
  | 1 =>
      rw [fL1_eval]
      have hf : phiL x 1 = fun _ => x (Rv 1) := by funext u; simp [phiL]
      rw [hf]; exact hasDerivAt_const _ _
  | 2 =>
      rw [fb_eval 0 (by norm_num), trajRs_R]
      have hf : phiL x 2 = ea 5 1 (x (Rv 2)) := by funext u; simp [phiL]
      rw [hf]; exact ea_der _ _ _ t

theorem phiM_der (q : ℕ) (h1 : 1 ≤ q) (hq : q < 3) (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiM q x i) (Term.eval (fR q i) (trajRs x (phiM q x) t)) t := by
  match i with
  | 0 =>
      rw [fz_eval q h1 (by omega), trajRs_R]
      have hf : phiM q x 0 = intSol (x (Rv 0)) (ea (4/5) (cV q) (x (Rv 1))) := by
        funext u; simp [phiM]
      have hf1 : phiM q x 1 = ea (4/5) (cV q) (x (Rv 1)) := by funext u; simp [phiM]
      rw [hf, hf1]; exact intSol_hasDerivAt _ (ea_cont _ _ _) t
  | 1 =>
      rw [fv_eval q h1 hq, trajRs_R]
      have hf : phiM q x 1 = ea (4/5) (cV q) (x (Rv 1)) := by funext u; simp [phiM]
      rw [hf]; exact ea_der _ _ _ t
  | 2 =>
      rw [fb_eval q hq, trajRs_R]
      have hf : phiM q x 2 = ea 5 1 (x (Rv 2)) := by funext u; simp [phiM]
      rw [hf]; exact ea_der _ _ _ t

theorem phiS_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiS x i) (Term.eval (fR 3 i) (trajRs x (phiS x) t)) t := by
  match i with
  | 0 =>
      rw [fz_eval 3 (by norm_num) (by norm_num), trajRs_R]
      have hf : phiS x 0 = ea 4 (x (Rv 0) + x (Rv 1) / 4) (x (Rv 0)) := by
        funext u; simp [phiS]
      have hf1 : phiS x 1 t = ea 4 0 (x (Rv 1)) t := by simp [phiS]
      rw [hf, hf1]
      refine (ea_der 4 (x (Rv 0) + x (Rv 1) / 4) (x (Rv 0)) t).congr_deriv ?_
      simp only [ea]; ring
  | 1 =>
      rw [fS1_eval, trajRs_R]
      have hf : phiS x 1 = ea 4 0 (x (Rv 1)) := by funext u; simp [phiS]
      rw [hf]; exact ea_der _ _ _ t
  | 2 =>
      rw [fS2_eval, trajRs_R]
      have hf : phiS x 2 = ea 5 0 (x (Rv 2)) := by funext u; simp [phiS]
      rw [hf]; exact ea_der _ _ _ t

theorem exists_runL (x : State (Var 3)) (hd : Formula.sat domR x) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x (1/10) Φ := by
  obtain ⟨z0, z1, v0, v1, b0, b1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiL x) (1/10) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phiL_der x i t) (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiL]
    | 1 => simp [phiL]
    | 2 => simp [phiL, ea_zero]
  · obtain ⟨c0, c1⟩ := ea_between 5 1 (x (Rv 2)) t (by norm_num) ht b0 b1 (by norm_num)
      (le_refl (1:ℝ))
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiL, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    exact ⟨z0, z1, v0, v1, c0, c1⟩

/-- `UP` and `APP` from a state below `19.9`: the car stays below `19.9 + 0.17`. -/
theorem exists_runM (q : ℕ) (h1 : 1 ≤ q) (hq : q < 3) (x : State (Var 3))
    (hd : Formula.sat domR x) (hz : x (Rv 0) < 199/10) :
    ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x (1/10) Φ := by
  obtain ⟨z0, z1, v0, v1, b0, b1⟩ := (sat_domR x).mp hd
  have hc : 0 ≤ cV q ∧ cV q ≤ 17/10 := by unfold cV; split_ifs <;> norm_num
  have hv : ∀ u, 0 ≤ u → 0 ≤ ea (4/5) (cV q) (x (Rv 1)) u ∧ ea (4/5) (cV q) (x (Rv 1)) u ≤ 17/10 :=
    fun u hu => ea_between (4/5) (cV q) (x (Rv 1)) u (by norm_num) hu v0 v1 hc.1 hc.2
  refine ⟨_, trajRs_sol x (phiM q x) (1/10) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phiM_der q h1 hq x i t) (fun t ht hte => ?_)⟩
  · match i with
    | 0 => simp [phiM, intSol_zero]
    | 1 => simp [phiM, ea_zero]
    | 2 => simp [phiM, ea_zero]
  · have hz' := intSol_bounds (x (Rv 0)) (ea_cont (4/5) (cV q) (x (Rv 1))) (17/10) (1/10)
      (fun u hu => hv u hu.1) t ⟨ht, hte⟩
    obtain ⟨w0, w1⟩ := hv t ht
    obtain ⟨c0, c1⟩ := ea_between 5 1 (x (Rv 2)) t (by norm_num) ht b0 b1 (by norm_num)
      (le_refl (1:ℝ))
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiM, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    exact ⟨by linarith [hz'.1], by nlinarith [hz'.2], w0, w1, c0, c1⟩

/-- `STOP` from a guard state: below the rest position `z₀ + v₀/4 ≤ 20.5`. -/
theorem exists_runS (x : State (Var 3)) (hd : Formula.sat domR x)
    (hr : x (Rv 0) + 1/4 * x (Rv 1) ≤ 41/2) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 3) (Term.const 1)) domR x ε Φ := by
  obtain ⟨z0, z1, v0, v1, b0, b1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiS x) ε hε (fun i => ?_)
    (fun i t _ _ => phiS_der x i t) (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiS, ea_zero]
    | 1 => simp [phiS, ea_zero]
    | 2 => simp [phiS, ea_zero]
  · obtain ⟨p0, p1⟩ := ea_between 4 (x (Rv 0) + x (Rv 1) / 4) (x (Rv 0)) t (by norm_num) ht
      (lo := x (Rv 0)) (hi := 41/2) (le_refl _) z1 (by linarith) (by linarith)
    obtain ⟨w0, w1⟩ := ea_between 4 0 (x (Rv 1)) t (by norm_num) ht v0 v1 (le_refl 0)
      (by norm_num)
    obtain ⟨c0, c1⟩ := ea_between 5 0 (x (Rv 2)) t (by norm_num) ht b0 b1 (le_refl 0)
      (by norm_num)
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiS, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    exact ⟨by linarith, by linarith, w0, w1, c0, c1⟩

theorem memz (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0
theorem memv (q : ℕ) : (Rv 1, Term.binop .mul (Term.const 1) (fR q 1)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 1
theorem memb (q : ℕ) : (Rv 2, Term.binop .mul (Term.const 1) (fR q 2)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 2

/-- **Assumption 1 for `elevator_start_discbrake`**, every mode, Z3-free. -/
theorem elevator_start_discbrake_wellFormedR :
    WellFormedR Gr guardR (epsR elevator_start_discbrake_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- LIFT: the car is held, the brake rises toward 1: LIFT, or UP once b ≥ 0.95
    have hg' := (sat_g0 x).mp hg
    refine ⟨exists_runL x hd, ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    have hz := H.const (memz 0) (fun s _ => by rw [eval_unit_mul, fL0_eval])
    have hv := H.const (memv 0) (fun s _ => by rw [eval_unit_mul, fL1_eval])
    by_cases h95 : Φ t (Rv 2) < 19/20
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr
        ⟨by rw [hz]; exact hg'.1, by rw [hv]; exact hg'.2.1, h95, e0, e1, e2, e3, e4, e5⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_g1 _).mpr
        ⟨by rw [hz]; linarith [hg'.1], by linarith, e0, e1, e2, e3, e4, e5⟩⟩
  · -- UP: the brake stays lifted, the car rises by at most 0.17: UP, or APP from 18
    have hg' := (sat_g1 x).mp hg
    refine ⟨exists_runM 1 (by norm_num) (by norm_num) x hd (by linarith [hg'.1]), ?_⟩
    intro t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    have hb := H.linear_up (memb 1) 5 1 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fb_eval 1 (by norm_num)]) (by linarith [hg'.2.2.2.2.2.2.2])
    have hzr := H.rate_le (memz 1) (17/10) (fun s hs => by
      obtain ⟨-, -, -, h, -, -⟩ := (sat_domR s).mp hs
      rw [eval_unit_mul, fz_eval 1 (by norm_num) (by norm_num)]; exact h)
    have hr := H.hr
    by_cases h18 : Φ t (Rv 0) < 18
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr
        ⟨h18, by linarith [hg'.2.1, hb.1], e0, e1, e2, e3, e4, e5⟩⟩
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide), (sat_g2 _).mpr
        ⟨by linarith, by nlinarith [hg'.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- APP: the car does not fall and ends below 20.07 with v ≤ 1.7: APP, or STOP from 19.9
    have hg' := (sat_g2 x).mp hg
    refine ⟨exists_runM 2 (by norm_num) (by norm_num) x hd hg'.2.1, ?_⟩
    intro t Φ ht H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    have hzr := H.rate_le (memz 2) (17/10) (fun s hs => by
      obtain ⟨-, -, -, h, -, -⟩ := (sat_domR s).mp hs
      rw [eval_unit_mul, fz_eval 2 (by norm_num) (by norm_num)]; exact h)
    have hzm := H.mono (memz 2) (fun s hs => by
      obtain ⟨-, -, h, -, -, -⟩ := (sat_domR s).mp hs
      rw [eval_unit_mul, fz_eval 2 (by norm_num) (by norm_num)]; exact h)
    have hr := H.hr
    by_cases h199 : Φ t (Rv 0) < 199/10
    · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr
        ⟨by linarith [hg'.1], h199, e0, e1, e2, e3, e4, e5⟩⟩
    · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_g3 _).mpr
        ⟨by linarith, by nlinarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩
  · -- STOP: the rest position z + v/4 is constant and z does not fall
    have hg' := (sat_g3 x).mp hg
    refine ⟨exists_runS x hd hg'.2.1 (1/10) (by norm_num), ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := (sat_domR _).mp H.end_dom
    have hzm := H.mono (memz 3) (fun s hs => by
      obtain ⟨-, -, h, -, -, -⟩ := (sat_domR s).mp hs
      rw [eval_unit_mul, fz_eval 3 (by norm_num) (by norm_num)]; exact h)
    have hc := H.affine_const (memz 3) (memv 3) 1 (1/4) (fun s _ => by
      rw [eval_unit_mul, eval_unit_mul, fz_eval 3 (by norm_num) (by norm_num), fS1_eval]; ring)
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_g3 _).mpr
      ⟨by linarith [hg'.1], by linarith [hg'.2.1], e0, e1, e2, e3, e4, e5⟩⟩

end V2ElevatorStartDiscbrake
end RelCertifier
