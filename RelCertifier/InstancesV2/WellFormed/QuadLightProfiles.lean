/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_profiles`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (the file's three pilot-selectable climb
profiles and their declared `next` lists, each profile listing all three; review round 6,
2026-10-30, raised the `SPORT` set point from 2.4 to 2.5 m/s), the lowered right guards,
`ε_r = 1`. The right model is the reference quadrotor's climb, an affine cascade on
altitude `h` (`Rv 0`) and climb rate `w` (`Rv 1`): `h' = w`, `w' = c_q − 4.905 w` with
`c_q = 9.81` (`NORMAL`), `7.848` (`ECO`), `12.2625` (`SPORT`; `11.772` before), terminal climb rates
`c_q / 4.905 = 2.0, 1.6, 2.5`; in every profile guard = evolve = `h ≥ 0 ∧ 0 ≤ w ≤ 3` (the
autopilot's climb-rate limiter, since the domain audit of 2026-10-29; `2.4` before).
The bridge dimension is `3` (the cover uses the committed mode choice, so no modal pack fixes
it and it falls back to `max (#left state vars) 3`): coordinate `Rv 2` is a padding coordinate
outside `vs`, its right field lowers to `0`, and the run holds it still.

* Existence (i), every profile: the explicit run. `w` is the contraction toward
  `c_q / 4.905` (`forcedSol 4.905 w₀ c_q`, kept in `[min w₀ (c_q/4.905), max w₀ (c_q/4.905)]
  ⊆ [0, 3]` by `forcedSol_between`, every terminal rate lying in `[0, 3]`); `h` is the
  integral of `w` (`intSol`), not decreasing since `w ≥ 0` (`mono_of_deriv_nonneg`). The run
  is assembled by `trajRs_sol` and stays in the evolve box over the interval.
* (ii), style (a), every profile: the guard is the evolve domain, so every run (of any
  duration) ends in the profile's own guard (`ODESol.end_dom`), and every profile lists
  itself as a successor.

Z3-free; modelled on `QuadLightLag.lean` (the cascade run, the box) and `TankDos3to1.lean`
(conventions, several modes).
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.quad_light_profiles

namespace RelCertifier
namespace V2QuadLightProfiles

open DL DLCalTiming DLRel Parse Set

set_option linter.unusedSimpArgs false

def vs : List String := ["h", "w"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := quad_light_profiles_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp30 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hp981 : Run.parseRat "9.81" = some ((981 : ℚ) / 100) := by
  have h : parseQ "9.81" = some (⟨981, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hp7848 : Run.parseRat "7.848" = some ((981 : ℚ) / 125) := by
  have h : parseQ "7.848" = some (⟨7848, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hp122625 : Run.parseRat "12.2625" = some ((981 : ℚ) / 80) := by
  have h : parseQ "12.2625" = some (⟨122625, 10000⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hp4905 : Run.parseRat "4.905" = some ((981 : ℚ) / 200) := by
  have h : parseQ "4.905" = some (⟨4905, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num

/-! ## The right fields, domain and guards, evaluated (`h` = `Rv 0`, `w` = `Rv 1`) -/

/-- The profile's thrust term `c_q` (`NORMAL` 9.81, `ECO` 7.848, `SPORT` 12.2625). -/
noncomputable def cR (q : ℕ) : ℝ := if q = 0 then 981 / 100 else if q = 1 then 981 / 125 else 981 / 80

/-- Every terminal climb rate `c_q / 4.905` (2.0, 1.6, 2.5) lies in `[0, 3]`. -/
theorem cR_rate (q : ℕ) (hq : q < 3) : 0 ≤ cR q / (981 / 200) ∧ cR q / (981 / 200) ≤ 3 := by
  interval_cases q <;> norm_num [cR]

/-- Altitude: `h' = w`, every profile. -/
theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) : Term.eval (fR q 0) x = x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hp981, hp7848,
    hp122625, hp4905, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- Climb rate: `w' = c_q − 4.905 w`. -/
theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 1) x = cR q - 981 / 200 * x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hp981, hp7848,
    hp122625, hp4905, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, cR]

/-- The padding coordinate (not in `vs`): its right field lowers to `0`. -/
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) : Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hp981, hp7848,
    hp122625, hp4905, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The climb box (every profile's guard and the evolve domain). -/
def boxR (x : State (Var 3)) : Prop := 0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 3

theorem sat_domR (x : State (Var 3)) : Formula.sat domR x ↔ boxR x := by
  simp only [domR, hostEvolve, mR, quad_light_profiles_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp30, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, boxR, and_assoc]
  try norm_num

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, ECO 1, SPORT 2), in the file's order. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 1), (1, 0), (1, 2), (2, 2), (2, 0), (2, 1)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- Every profile lists itself as a successor. -/
theorem self_mem (q : ℕ) (hq : q < 3) : (q, q) ∈ edgeList := by
  interval_cases q <;> decide

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem sat_guardR (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Formula.sat (guardR q) x ↔ boxR x := by
  interval_cases q <;>
  simp [guardR, hostGuard, mR, quad_light_profiles_IRv2, Run.lowerF, Run.lowerE, hp00, hp30,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, boxR, and_assoc]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR quad_light_profiles_IRv2 = 1 := by
  simp [epsR, quad_light_profiles_IRv2, hp10]

/-! ## Existence: the explicit run of the cascade -/

/-- Climb rate `w' = c_q − 4.905 w`: `w → c_q / 4.905` exponentially. -/
noncomputable def φw (q : ℕ) (ρ : State (Var 3)) : ℝ → ℝ :=
  forcedSol (981 / 200) (ρ (Rv 1)) (fun _ => cR q)

/-- Altitude `h' = w(t)`. -/
noncomputable def φh (q : ℕ) (ρ : State (Var 3)) : ℝ → ℝ := intSol (ρ (Rv 0)) (φw q ρ)

theorem φw_cont (q : ℕ) (ρ : State (Var 3)) : Continuous (φw q ρ) :=
  forcedSol_continuous _ _ continuous_const

/-- The run: `h`, `w` along their explicit laws, the padding coordinate held still. -/
noncomputable def φR (q : ℕ) (ρ : State (Var 3)) : Fin 3 → ℝ → ℝ
  | 0 => φh q ρ
  | 1 => φw q ρ
  | 2 => fun _ => ρ (Rv 2)

theorem φR_zero (q : ℕ) (ρ : State (Var 3)) (i : Fin 3) : φR q ρ i 0 = ρ (Rv i) := by
  match i with
  | 0 => exact intSol_zero _ _
  | 1 => exact forcedSol_zero _ _ _
  | 2 => rfl

theorem φR_der (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (φR q ρ i) (Term.eval (fR q i) (trajRs ρ (φR q ρ) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, trajRs_R]
      exact intSol_hasDerivAt _ (φw_cont q ρ) t
  | 1 =>
      rw [fR1_eval q hq, trajRs_R]
      exact forcedSol_hasDerivAt (981 / 200) (ρ (Rv 1)) continuous_const t
  | 2 =>
      rw [fR2_eval q hq]
      exact hasDerivAt_const t (ρ (Rv 2))

/-- The climb rate stays in `[0, 3]` over one control interval. -/
theorem φw_bnd (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hρ : boxR ρ) :
    ∀ τ ∈ Icc (0:ℝ) 1, 0 ≤ φw q ρ τ ∧ φw q ρ τ ≤ 3 := by
  obtain ⟨-, hw0, hw1⟩ := hρ
  obtain ⟨hc0, hc1⟩ := cR_rate q hq
  intro τ hτ
  have h := forcedSol_between (981 / 200) (ρ (Rv 1)) (F := fun _ => cR q) continuous_const
    (lo := cR q) (hi := cR q) (by norm_num) (fun _ _ => ⟨le_rfl, le_rfl⟩) τ hτ
  exact ⟨le_trans (le_min hw0 hc0) h.1, le_trans h.2 (max_le hw1 hc1)⟩

/-- The run stays in the evolve box over one control interval. -/
theorem φR_dom (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hρ : Formula.sat domR ρ) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) : Formula.sat domR (trajRs ρ (φR q ρ) t) := by
  have hb := (sat_domR ρ).mp hρ
  have hw := φw_bnd q hq ρ hb
  have hh : ρ (Rv 0) ≤ φh q ρ t := by
    have h := mono_of_deriv_nonneg (fun τ => intSol_hasDerivAt (ρ (Rv 0)) (φw_cont q ρ) τ)
      (fun τ hτ => (hw τ hτ).1) t ht
    rw [intSol_zero] at h
    exact h
  rw [sat_domR]
  refine ⟨?_, ?_, ?_⟩
  · rw [trajRs_R]; exact le_trans hb.1 hh
  · rw [trajRs_R]; exact (hw t ht).1
  · rw [trajRs_R]; exact (hw t ht).2

/-- **Assumption 1 for `quad_light_profiles`**, every mode, Z3-free. -/
theorem quad_light_profiles_wellFormedR :
    WellFormedR Gr guardR (epsR quad_light_profiles_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨?_, ?_⟩
  · exact ⟨_, trajRs_sol x (φR q x) 1 (by norm_num) (φR_zero q x)
      (fun i t _ _ => φR_der q hq3 x i t) (fun t h0 h1 => φR_dom q hq3 x hd t ⟨h0, h1⟩)⟩
  · intro t Φ _ H
    exact ⟨edgeW q q, edge_mem q q (self_mem q hq3),
      (sat_guardR q hq3 _).mpr ((sat_domR _).mp H.end_dom)⟩

end V2QuadLightProfiles
end RelCertifier

