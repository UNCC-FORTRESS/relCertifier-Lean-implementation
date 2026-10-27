/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `gantry_speed_zones`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (the file's one mode `MOVE` and its declared
`next` list `[MOVE]`), the lowered right guard, and `ε_r = 0.1` read from the file. The right
model is the commissioned gantry program: two independent first-order axis servos toward the
place point, `x' = 2 (0.5 − x)`, `y' = 1 (0.3 − y)`, guard = evolve domain = the travel box
`0 ≤ x ≤ 0.8`, `0 ≤ y ≤ 0.5`.
* Existence (i): the explicit run, one exponential per axis,
  `x(t) = 0.5 + (x₀ − 0.5) e^{−2t}`, `y(t) = 0.3 + (y₀ − 0.3) e^{−t}` (`trajRs_sol`); each axis
  stays between its start and its target (`exp_approach_between`), and both targets lie in the
  box, so the run lies in the evolve domain.
* (ii), style (a) (invariant): every run ends in the evolve domain, which is `MOVE`'s guard, and
  `MOVE` is its own declared successor.
Z3-free; modelled on `TankDos3to1.lean` (conventions, explicit run) and `EngineStartHighidle`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.gantry_speed_zones

namespace RelCertifier
namespace V2GantrySpeedZones

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["x", "y"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := gantry_speed_zones_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp08 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right field, domain and guard, evaluated -/

/-- The `x` axis: `x' = 2 (0.5 − x)`. -/
theorem fR0_eval (x : State (Var 2)) :
    Term.eval (fR 0 0) x = 2 * (1/2 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, gantry_speed_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp20, hp10, hp05,
    hp03, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The `y` axis: `y' = 1 (0.3 − y)`. -/
theorem fR1_eval (x : State (Var 2)) :
    Term.eval (fR 0 1) x = 1 * (3/10 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, gantry_speed_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp20, hp10, hp05,
    hp03, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 4/5 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 1/2) := by
  simp only [domR, hostEvolve, mR, gantry_speed_zones_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp08, hp05, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's mode and declared `next` list) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (MOVE 0). -/
def edgeList : List (ℕ × ℕ) := [(0, 0)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 1) : Gr.modeAt q = some (modeW q) := by
  interval_cases q; rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 1 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 1 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The right guard of `MOVE`, evaluated: the travel box (the evolve domain). -/
theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 4/5 ∧ 0 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 1/2) := by
  simp [hostGuard, mR, gantry_speed_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp08, hp05,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-! ## Existence: the explicit run -/

/-- The `x` axis from `x₀`: `x(t) = 0.5 + (x₀ − 0.5) e^{−2t}`. -/
noncomputable def xSol (x0 t : ℝ) : ℝ := 1/2 + (x0 - 1/2) * Real.exp (-(2 * t))

/-- The `y` axis from `y₀`: `y(t) = 0.3 + (y₀ − 0.3) e^{−t}`. -/
noncomputable def ySol (y0 t : ℝ) : ℝ := 3/10 + (y0 - 3/10) * Real.exp (-(1 * t))

theorem xSol_hasDerivAt (x0 t : ℝ) : HasDerivAt (xSol x0) (2 * (1/2 - xSol x0 t)) t :=
  hasDerivAt_expApproach 2 (1/2) x0 t

theorem ySol_hasDerivAt (y0 t : ℝ) : HasDerivAt (ySol y0) (1 * (3/10 - ySol y0 t)) t :=
  hasDerivAt_expApproach 1 (3/10) y0 t

/-- Each axis stays between its start and its target, so inside the travel box. -/
theorem xSol_box (x0 t : ℝ) (h0 : 0 ≤ x0) (h8 : x0 ≤ 4/5) (ht : 0 ≤ t) :
    0 ≤ xSol x0 t ∧ xSol x0 t ≤ 4/5 := by
  obtain ⟨hl, hu⟩ := exp_approach_between 2 (1/2) x0 t (by norm_num) ht
  have hmin : (0:ℝ) ≤ min x0 (1/2) := le_min h0 (by norm_num)
  have hmax : max x0 (1/2) ≤ (4/5:ℝ) := max_le h8 (by norm_num)
  exact ⟨le_trans hmin hl, le_trans hu hmax⟩

theorem ySol_box (y0 t : ℝ) (h0 : 0 ≤ y0) (h5 : y0 ≤ 1/2) (ht : 0 ≤ t) :
    0 ≤ ySol y0 t ∧ ySol y0 t ≤ 1/2 := by
  obtain ⟨hl, hu⟩ := exp_approach_between 1 (3/10) y0 t (by norm_num) ht
  have hmin : (0:ℝ) ≤ min y0 (3/10) := le_min h0 (by norm_num)
  have hmax : max y0 (3/10) ≤ (1/2:ℝ) := max_le h5 (by norm_num)
  exact ⟨le_trans hmin hl, le_trans hu hmax⟩

/-- The explicit run of `MOVE` from `x`: `xSol` on coordinate 0, `ySol` on coordinate 1. -/
noncomputable def phi (x : State (Var 2)) (i : Fin 2) (t : ℝ) : ℝ :=
  if i.val = 0 then xSol (x (Rv 0)) t else ySol (x (Rv 1)) t

theorem phi_zero (x : State (Var 2)) (t : ℝ) : phi x 0 t = xSol (x (Rv 0)) t := by
  simp [phi]

theorem phi_one (x : State (Var 2)) (t : ℝ) : phi x 1 t = ySol (x (Rv 1)) t := by
  simp [phi]

theorem phi_init (x : State (Var 2)) (i : Fin 2) : phi x i 0 = x (Rv i) := by
  match i with
  | 0 => rw [phi_zero]; simp [xSol]
  | 1 => rw [phi_one]; simp [ySol]

theorem phi_der (x : State (Var 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (phi x i) (Term.eval (fR 0 i) (trajRs x (phi x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval, trajRs_R, phi_zero]
      have hf : phi x 0 = xSol (x (Rv 0)) := by
        funext u; exact phi_zero x u
      rw [hf]
      exact xSol_hasDerivAt _ t
  | 1 =>
      rw [fR1_eval, trajRs_R, phi_one]
      have hf : phi x 1 = ySol (x (Rv 1)) := by
        funext u; exact phi_one x u
      rw [hf]
      exact ySol_hasDerivAt _ t

/-- **Existence (clause (i))**: from a domain state, the explicit run of every duration
`ε ≥ 0` lies in the evolve domain (each axis moves toward its target inside the box). -/
theorem exists_run (x : State (Var 2)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x ε Φ := by
  obtain ⟨x0, x8, y0, y5⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phi x) ε hε (phi_init x) (fun i t _ _ => phi_der x i t)
    (fun t ht _ => ?_)⟩
  obtain ⟨a0, a8⟩ := xSol_box (x (Rv 0)) t x0 x8 ht
  obtain ⟨b0, b5⟩ := ySol_box (x (Rv 1)) t y0 y5 ht
  rw [sat_domR, trajRs_R, trajRs_R, phi_zero, phi_one]
  exact ⟨a0, a8, b0, b5⟩

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR gantry_speed_zones_IRv2 = 1/10 := by
  simp [epsR, gantry_speed_zones_IRv2, hp01]

/-- **Assumption 1 for `gantry_speed_zones`**, every mode, Z3-free. -/
theorem gantry_speed_zones_wellFormedR : WellFormedR Gr guardR (epsR gantry_speed_zones_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq1, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  refine ⟨exists_run x hd (1/10) (by norm_num), ?_⟩
  intro t Φ _ H
  -- style (a): the run ends in the evolve domain, which is `MOVE`'s guard
  obtain ⟨e0, e8, f0, f5⟩ := (sat_domR _).mp H.end_dom
  exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨e0, e8, f0, f5⟩⟩

end V2GantrySpeedZones
end RelCertifier

