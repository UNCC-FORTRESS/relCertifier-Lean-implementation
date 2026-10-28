/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `flaps_slow_approach`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two flap phases and their declared `next` lists), the lowered right guards, and `ε_r = 0.1`
read from the file.

The right model is the flap extension on approach: the flap angle `f` (coordinate 0) and the
airspeed `V` (coordinate 1), inside `10 ≤ f ≤ 15.1`, `150 ≤ V ≤ 185`. `EXT` extends the flaps,
`f' = 1`; `CONF2` holds them, `f' = 0`; in both the airspeed decays toward 150 with a
flap-dependent rate, `V' = −(0.02 + 0.001 f)(V − 150)`. Guards: `EXT` `f < 15`, `CONF2`
`f ≥ 15` (each with the domain). `next`: `EXT → [EXT, CONF2]`, `CONF2 → [CONF2]`.
* Existence (i): the explicit run `f(t) = f₀ + r t` (`r = 1` in `EXT`, `0` in `CONF2`) and
  `V(t) = 150 + (V₀ − 150) e^{−((0.02 + 0.001 f₀) t + 0.0005 r t²)}`; the exponent is
  nonnegative for `t ≥ 0` (as `f₀ ≥ 10`), so `V` stays in `[150, V₀]`, and `f ≤ f₀ + 0.1`
  stays below `15.1` since `f₀ < 15` in `EXT`.
* (ii): a run ends in the domain; `EXT` ends in `EXT` (below 15) or `CONF2` (from 15); in
  `CONF2` the flap angle is constant (`ODESol.const`), so the run stays in `CONF2`.
Z3-free; modelled on `FurnaceProgramTimebase.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.flaps_slow_approach

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2FlapsSlowApproach

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["f", "V"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := flaps_slow_approach_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_02 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_001 : Run.parseRat "0.001" = some ((1:ℚ)/1000) := by
  have h : parseQ "0.001" = some (⟨1, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_10 : Run.parseRat "10" = some (10 : ℚ) := by
  have h : parseQ "10" = some (⟨10, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_15 : Run.parseRat "15" = some (15 : ℚ) := by
  have h : parseQ "15" = some (⟨15, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_15_1 : Run.parseRat "15.1" = some ((151:ℚ)/10) := by
  have h : parseQ "15.1" = some (⟨151, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_150 : Run.parseRat "150" = some (150 : ℚ) := by
  have h : parseQ "150" = some (⟨150, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_185 : Run.parseRat "185" = some (185 : ℚ) := by
  have h : parseQ "185" = some (⟨185, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- Flap rates: `EXT` 1, `CONF2` 0. -/
noncomputable def rR (q : ℕ) : ℝ := if q = 0 then 1 else 0

theorem rR_nonneg (q : ℕ) : 0 ≤ rR q := by unfold rR; split_ifs <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 0) x = rR q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, flaps_slow_approach_IRv2, vs, Run.dynOf, Run.lowerE, hp_0, hp_1,
      hp_0_0, hp_0_02, hp_0_001, hp_0_1, hp_10, hp_15, hp_15_1, hp_150, hp_185,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv, rR]

theorem fR1_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 1) x = -(1/50 + 1/1000 * x (Rv 0)) * (x (Rv 1) - 150) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, flaps_slow_approach_IRv2, vs, Run.dynOf, Run.lowerE, hp_0, hp_1,
      hp_0_0, hp_0_02, hp_0_001, hp_0_1, hp_10, hp_15, hp_15_1, hp_150, hp_185,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 151/10 ∧ 150 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 185) := by
  simp only [domR, hostEvolve, mR, flaps_slow_approach_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_0, hp_1, hp_0_0, hp_0_02, hp_0_001, hp_0_1, hp_10, hp_15,
    hp_15_1, hp_150, hp_185, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (EXT 0, CONF2 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  have hlen : q < 2 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 2 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 15 ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 151/10 ∧ 150 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 185) := by
  simp [hostGuard, mR, flaps_slow_approach_IRv2, Run.lowerF, Run.lowerE, hp_0, hp_1, hp_0_0,
    hp_0_02, hp_0_001, hp_0_1, hp_10, hp_15, hp_15_1, hp_150, hp_185, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔
      (15 ≤ ν (Rv 0) ∧ 10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 151/10 ∧ 150 ≤ ν (Rv 1) ∧
        ν (Rv 1) ≤ 185) := by
  simp [hostGuard, mR, flaps_slow_approach_IRv2, Run.lowerF, Run.lowerE, hp_0, hp_1, hp_0_0,
    hp_0_02, hp_0_001, hp_0_1, hp_10, hp_15, hp_15_1, hp_150, hp_185, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR flaps_slow_approach_IRv2 = 1/10 := by
  simp [epsR, flaps_slow_approach_IRv2, hp_0_1]

/-! ## Existence: the explicit run -/

/-- The flap angle of phase `q` from `f₀`. -/
noncomputable def fSol (q : ℕ) (f0 t : ℝ) : ℝ := f0 + rR q * t

/-- The decay exponent of the airspeed: the integral of `0.02 + 0.001 f(u)` over `[0, t]`. -/
noncomputable def gSol (q : ℕ) (f0 t : ℝ) : ℝ := (1/50 + 1/1000 * f0) * t + 1/2000 * rR q * (t * t)

/-- The airspeed of phase `q` from `(f₀, V₀)`. -/
noncomputable def vSol (q : ℕ) (f0 V0 t : ℝ) : ℝ := 150 + (V0 - 150) * Real.exp (-(gSol q f0 t))

theorem fSol_der (q : ℕ) (f0 t : ℝ) : HasDerivAt (fSol q f0) (rR q) t := by
  have h := ((hasDerivAt_id t).const_mul (rR q)).const_add f0
  unfold fSol
  exact h.congr_deriv (by simp)

theorem gSol_der (q : ℕ) (f0 t : ℝ) :
    HasDerivAt (gSol q f0) (1/50 + 1/1000 * fSol q f0 t) t := by
  have h1 := (hasDerivAt_id t).const_mul (1/50 + 1/1000 * f0)
  have h2 := ((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (1/2000 * rR q)
  have h3 := h1.add h2
  unfold gSol fSol
  refine h3.congr_deriv ?_
  simp only [id]
  ring

theorem vSol_der (q : ℕ) (f0 V0 t : ℝ) :
    HasDerivAt (vSol q f0 V0) (-(1/50 + 1/1000 * fSol q f0 t) * (vSol q f0 V0 t - 150)) t := by
  have h := (((gSol_der q f0 t).neg.exp).const_mul (V0 - 150)).const_add 150
  unfold vSol
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

theorem gSol_nonneg (q : ℕ) (f0 t : ℝ) (hf : 0 ≤ f0) (ht : 0 ≤ t) : 0 ≤ gSol q f0 t := by
  unfold gSol
  have := rR_nonneg q
  have h1 : 0 ≤ (1/50 + 1/1000 * f0) * t := mul_nonneg (by linarith) ht
  have h2 : 0 ≤ 1/2000 * rR q * (t * t) := mul_nonneg (by linarith) (mul_nonneg ht ht)
  linarith

theorem vSol_box (q : ℕ) (f0 V0 t : ℝ) (hf : 0 ≤ f0) (ht : 0 ≤ t) (hV : 150 ≤ V0) :
    150 ≤ vSol q f0 V0 t ∧ vSol q f0 V0 t ≤ V0 := by
  have he0 : 0 < Real.exp (-(gSol q f0 t)) := Real.exp_pos _
  have he1 : Real.exp (-(gSol q f0 t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [gSol_nonneg q f0 t hf ht]
  unfold vSol
  constructor <;> nlinarith

/-- The run of phase `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 2)) (i : Fin 2) (t : ℝ) : ℝ :=
  if i.val = 0 then fSol q (x (Rv 0)) t else vSol q (x (Rv 0)) (x (Rv 1)) t

theorem phi_zero (q : ℕ) (x : State (Var 2)) : phi q x 0 = fSol q (x (Rv 0)) := by
  funext t; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 2)) : phi q x 1 = vSol q (x (Rv 0)) (x (Rv 1)) := by
  funext t; simp [phi]

theorem phi_der (q : ℕ) (hq : q < 2) (x : State (Var 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, phi_zero]
      exact fSol_der q (x (Rv 0)) t
  | 1 =>
      rw [fR1_eval q hq, trajRs_R, trajRs_R, phi_zero, phi_one]
      exact vSol_der q (x (Rv 0)) (x (Rv 1)) t

/-- From the domain, with room `f₀ + 0.1 r ≤ 15.1` for the flap, the run of phase `q` lasts
the whole control interval inside the domain. -/
theorem exists_run (q : ℕ) (hq : q < 2) (x : State (Var 2)) (hd : Formula.sat domR x)
    (hroom : x (Rv 0) + rR q * (1/10) ≤ 151/10) :
    ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x (1/10) Φ := by
  obtain ⟨a0, a1, b0, b1⟩ := (sat_domR x).mp hd
  have hr := rR_nonneg q
  refine ⟨_, trajRs_sol x (phi q x) (1/10) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phi_der q hq x i t) (fun t ht hte => ?_)⟩
  · match i with
    | 0 => rw [phi_zero]; simp [fSol]
    | 1 => rw [phi_one]; simp [vSol, gSol]
  · obtain ⟨c0, c1⟩ := vSol_box q (x (Rv 0)) (x (Rv 1)) t (by linarith) ht b0
    have hft : rR q * t ≤ rR q * (1/10) := mul_le_mul_of_nonneg_left hte hr
    have hft0 : 0 ≤ rR q * t := mul_nonneg hr ht
    rw [sat_domR, trajRs_R, trajRs_R, phi_zero, phi_one]
    unfold fSol
    exact ⟨by linarith, by linarith, c0, by linarith⟩

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `flaps_slow_approach`**, every mode, Z3-free. -/
theorem flaps_slow_approach_wellFormedR :
    WellFormedR Gr guardR (epsR flaps_slow_approach_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  obtain ⟨e0, e1, e2, e3⟩ := (sat_domR x).mp hd
  interval_cases q
  · -- EXT: the flap starts below 15, so `f₀ + 0.1 ≤ 15.1`; a run ends in the domain,
    -- inside `EXT` (below 15) or `CONF2` (from 15)
    have hg0 := (sat_guard0 x).mp hg
    refine ⟨exists_run 0 (by norm_num) x hd (by norm_num [rR]; linarith [hg0.1]), ?_⟩
    intro t Φ _ H
    obtain ⟨d0, d1, d2, d3⟩ := (sat_domR _).mp H.end_dom
    by_cases h15 : Φ t (Rv 0) < 15
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨h15, d0, d1, d2, d3⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, d0, d1, d2, d3⟩⟩
  · -- CONF2: the flap is held (`f' = 0`), so the run stays in `CONF2`
    have hg1 := (sat_guard1 x).mp hg
    refine ⟨exists_run 1 (by norm_num) x hd (by norm_num [rR]; linarith), ?_⟩
    intro t Φ _ H
    obtain ⟨d0, d1, d2, d3⟩ := (sat_domR _).mp H.end_dom
    have hc := H.const (memR 1) (fun s _ => by rw [eval_unit_mul, fR0_eval 1 (by norm_num)]; simp [rR])
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
      (sat_guard1 _).mpr ⟨by rw [hc]; exact hg1.1, d0, d1, d2, d3⟩⟩

end V2FlapsSlowApproach
end RelCertifier
