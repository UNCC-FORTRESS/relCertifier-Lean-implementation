/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_lag`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (one mode, `CLIMB`, with its self-loop),
the lowered right guard, `ε_r = 1`. The right model is the reference quadrotor's climb with
the motors' thrust lag, an affine cascade: `h' = w`, `w' = a − 4.905 w`,
`a' = 10 (9.81 − a)`; guard = evolve = `h ≥ 0 ∧ 0 ≤ w ≤ 2 ∧ 0 ≤ a ≤ 9.81`.

* Existence (i): the explicit run of the cascade. `a` is the forced contraction toward
  `9.81` (`forcedSol 10 a₀ 98.1`, kept in `[a₀, 9.81] ⊆ [0, 9.81]` by `forcedSol_between`);
  `w` is the contraction `w' = a(t) − 4.905 w` forced by that `a` (`forcedSol 4.905 w₀ a`,
  kept in `[min w₀ 0, max w₀ (9.81/4.905)] = [0, 2]` because `0 ≤ a(t) ≤ 9.81`); `h` is the
  integral of `w` (`intSol`), not decreasing since `w ≥ 0` (`mono_of_deriv_nonneg`). The run
  is assembled by `trajRs_sol` and stays in the evolve box over the interval.
* (ii), style (a): the guard is the evolve domain, so every run (of any duration) ends in
  `CLIMB`'s guard (`ODESol.end_dom`), and the self-loop `CLIMB → CLIMB` is declared.

Z3-free; modelled on `RoverTerrain2to4.lean` (the cascade runs) and the old
`QuadLightLag.lean` (the one-mode graph and clause (ii)).
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.quad_light_lag

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightLag

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["h", "w", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := quad_light_lag_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hp981 : Run.parseRat "9.81" = some ((981 : ℚ) / 100) := by
  have h : parseQ "9.81" = some (⟨981, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hp4905 : Run.parseRat "4.905" = some ((981 : ℚ) / 200) := by
  have h : parseQ "4.905" = some (⟨4905, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num

/-! ## The right field and the evolve box, evaluated (`h` = `Rv 0`, `w` = `Rv 1`, `a` = `Rv 2`) -/

/-- Altitude: `h' = w`. -/
theorem fR0_eval (x : State (Var 3)) : Term.eval (fR 0 0) x = x (Rv 1) := by
  simp [fR, hostDyn, mR, quad_light_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp0, hp00, hp20,
    hp100, hp981, hp4905, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]

/-- Climb rate: `w' = a − 4.905 w`. -/
theorem fR1_eval (x : State (Var 3)) :
    Term.eval (fR 0 1) x = x (Rv 2) - 981 / 200 * x (Rv 1) := by
  simp [fR, hostDyn, mR, quad_light_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp0, hp00, hp20,
    hp100, hp981, hp4905, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
  try norm_num

/-- Thrust lag: `a' = 10 (9.81 − a)`. -/
theorem fR2_eval (x : State (Var 3)) :
    Term.eval (fR 0 2) x = 10 * (981 / 100 - x (Rv 2)) := by
  simp [fR, hostDyn, mR, quad_light_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp0, hp00, hp20,
    hp100, hp981, hp4905, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
  try norm_num

/-- The climb box (guard = evolve domain). -/
def boxR (x : State (Var 3)) : Prop :=
  0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 2 ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 981 / 100

theorem sat_domR (x : State (Var 3)) : Formula.sat domR x ↔ boxR x := by
  simp only [domR, hostEvolve, mR, quad_light_lag_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp0, hp00, hp20, hp100, hp981, hp4905, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
    Rv, boxR, and_assoc]
  try norm_num

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CLIMB 0). -/
def edgeList : List (ℕ × ℕ) := [(0, 0)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 1) : Gr.modeAt q = some (modeW q) := by
  obtain rfl : q = 0 := by omega
  rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 1 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 1 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (guardR 0) x ↔ boxR x := by
  simp [guardR, hostGuard, mR, quad_light_lag_IRv2, Run.lowerF, Run.lowerE, hp0, hp00, hp20,
    hp100, hp981, hp4905, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, boxR, and_assoc]
  try norm_num

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR quad_light_lag_IRv2 = 1 := by
  simp [epsR, quad_light_lag_IRv2, hp10]

/-! ## Existence: the explicit run of the cascade -/

/-- Thrust lag `a' = 98.1 − 10 a`: `a → 9.81` exponentially. -/
noncomputable def φa (ρ : State (Var 3)) : ℝ → ℝ :=
  forcedSol 10 (ρ (Rv 2)) (fun _ => 981 / 10)

/-- Climb rate `w' = a(t) − 4.905 w`, forced by the thrust run. -/
noncomputable def φw (ρ : State (Var 3)) : ℝ → ℝ :=
  forcedSol (981 / 200) (ρ (Rv 1)) (φa ρ)

/-- Altitude `h' = w(t)`. -/
noncomputable def φh (ρ : State (Var 3)) : ℝ → ℝ := intSol (ρ (Rv 0)) (φw ρ)

theorem φa_cont (ρ : State (Var 3)) : Continuous (φa ρ) :=
  forcedSol_continuous _ _ continuous_const

theorem φw_cont (ρ : State (Var 3)) : Continuous (φw ρ) :=
  forcedSol_continuous _ _ (φa_cont ρ)

/-- The run: `h`, `w`, `a` along their explicit laws. -/
noncomputable def φR (ρ : State (Var 3)) : Fin 3 → ℝ → ℝ
  | 0 => φh ρ
  | 1 => φw ρ
  | 2 => φa ρ

theorem φR_zero (ρ : State (Var 3)) (i : Fin 3) : φR ρ i 0 = ρ (Rv i) := by
  match i with
  | 0 => exact intSol_zero _ _
  | 1 => exact forcedSol_zero _ _ _
  | 2 => exact forcedSol_zero _ _ _

theorem φR_der (ρ : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (φR ρ i) (Term.eval (fR 0 i) (trajRs ρ (φR ρ) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval, trajRs_R]
      exact intSol_hasDerivAt _ (φw_cont ρ) t
  | 1 =>
      rw [fR1_eval, trajRs_R, trajRs_R]
      exact forcedSol_hasDerivAt (981 / 200) (ρ (Rv 1)) (φa_cont ρ) t
  | 2 =>
      rw [fR2_eval, trajRs_R]
      refine (forcedSol_hasDerivAt 10 (ρ (Rv 2)) continuous_const t).congr_deriv ?_
      show 981 / 10 - 10 * φa ρ t = 10 * (981 / 100 - φa ρ t)
      ring

/-- The thrust stays in `[0, 9.81]` over one control interval. -/
theorem φa_bnd (ρ : State (Var 3)) (hρ : boxR ρ) :
    ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φa ρ τ ∧ φa ρ τ ≤ 981 / 100 := by
  obtain ⟨-, -, -, ha0, ha1⟩ := hρ
  intro τ hτ
  have h := forcedSol_between 10 (ρ (Rv 2)) (F := fun _ => (981 / 10 : ℝ)) continuous_const
    (lo := 981 / 10) (hi := 981 / 10) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
  have he : (981 / 10 : ℝ) / 10 = 981 / 100 := by norm_num
  rw [he] at h
  exact ⟨le_trans (le_min ha0 (by norm_num)) h.1, le_trans h.2 (max_le ha1 le_rfl)⟩

/-- The climb rate stays in `[0, 2]` over one control interval (`2 = 9.81 / 4.905`). -/
theorem φw_bnd (ρ : State (Var 3)) (hρ : boxR ρ) :
    ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φw ρ τ ∧ φw ρ τ ≤ 2 := by
  have hb := φa_bnd ρ hρ
  obtain ⟨-, hw0, hw1, -, -⟩ := hρ
  intro τ hτ
  have h := forcedSol_between (981 / 200) (ρ (Rv 1)) (F := φa ρ) (φa_cont ρ)
    (lo := 0) (hi := 981 / 100) (by norm_num) hb τ hτ
  have he0 : (0 : ℝ) / (981 / 200) = 0 := by norm_num
  have he1 : (981 / 100 : ℝ) / (981 / 200) = 2 := by norm_num
  rw [he0, he1] at h
  exact ⟨le_trans (le_min hw0 le_rfl) h.1, le_trans h.2 (max_le hw1 le_rfl)⟩

/-- The run stays in the evolve box over one control interval. -/
theorem φR_dom (ρ : State (Var 3)) (hρ : Formula.sat domR ρ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    Formula.sat domR (trajRs ρ (φR ρ) t) := by
  have hb := (sat_domR ρ).mp hρ
  have hw := φw_bnd ρ hb
  have ha := φa_bnd ρ hb
  have hh : ρ (Rv 0) ≤ φh ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 0)) (φw_cont ρ) τ)
      (fun τ hτ => (hw τ hτ).1) t ht
    rw [intSol_zero] at h
    exact h
  rw [sat_domR]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [trajRs_R]; exact le_trans hb.1 hh
  · rw [trajRs_R]; exact (hw t ht).1
  · rw [trajRs_R]; exact (hw t ht).2
  · rw [trajRs_R]; exact (ha t ht).1
  · rw [trajRs_R]; exact (ha t ht).2

/-- **Assumption 1 for `quad_light_lag`**, every mode, Z3-free. -/
theorem quad_light_lag_wellFormedR : WellFormedR Gr guardR (epsR quad_light_lag_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq1, rfl⟩ := Gr_modeAt_inv hm
  obtain rfl : q = 0 := by omega
  refine ⟨?_, ?_⟩
  · exact ⟨_, trajRs_sol x (φR x) 1 (by norm_num) (φR_zero x)
      (fun i t _ _ => φR_der x i t) (fun t h0 h1 => φR_dom x hd t ⟨h0, h1⟩)⟩
  · intro t Φ _ H
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
      (sat_guardR0 _).mpr ((sat_domR _).mp H.end_dom)⟩

end V2QuadLightLag
end RelCertifier

