/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tunnel_jetfan_pairout`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two modes `NORMAL`, `FIRE` and their declared `next` lists), the lowered right guards, and
`ε_r = 1` read from the file.

The right model is the tunnel ventilation: the clock `t` (coordinate 0), the jet-fan airflow
`u` (coordinate 1) and the contaminant `c` (coordinate 2), with `t' = 1`,
`u' = w − b u²` (`b = 0.00171875`; `w` = `0.0225` in `NORMAL`, `0.09` in `FIRE`) and
`c' = a − 0.000625 u c` (`a` = `0.1583`, `1.2583`), inside the evolve box `t ≥ 0`,
`3.2 ≤ u ≤ 7.3`, `0 ≤ c ≤ 630`. Guards: `NORMAL` `t < 600 ∧ c ≤ 100`, `FIRE` `t ≥ 600` (each
with the box); `NORMAL → {NORMAL, FIRE}`, `FIRE → {FIRE}`. The first suite right model with a
polynomial field (`u²`, `u c`).
* Existence (i), explicit (no Picard–Lindelöf): `u' = b (U² − u²)` with `U = √(w/b)`
  (`√(144/11) ≈ 3.618`, `√(576/11) ≈ 7.236`) is a Riccati equation with the run
  `uSol U u₀ s = U ((U + u₀) e^{2bUs} − (U − u₀)) / ((U + u₀) e^{2bUs} + (U − u₀))`, which stays
  between `u₀` and `U` (`uSol_between`), so in `[3.2, 7.3]`; given that run, `c` is linear with
  the continuous rate `p(s) = 0.000625 u(s) ≥ 0.002` (`linSol`, variation of constants with
  `e^{−∫p}`), and stays in `[0, 630]` since `a ≤ 1.2583 ≤ 630 · 0.002` (`linSol_between`).
* (ii): `NORMAL` keeps `c ≤ 100` (at `c ≥ 100`, `c' ≤ 0.1583 − 0.2 < 0`, `coord_le_barrier`),
  so a run ends in `NORMAL` (`t < 600`) or `FIRE` (`t ≥ 600`); `FIRE` keeps `t ≥ 600`
  (`t' = 1`, `coord_ge_barrier`).
Z3-free; modelled on `FurnaceProgramTimebase.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.tunnel_jetfan_pairout

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2TunnelJetfanPairout

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["t", "u", "c"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := tunnel_jetfan_pairout_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_100 : Run.parseRat "100" = some (100 : ℚ) := by
  have h : parseQ "100" = some (⟨100, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_600 : Run.parseRat "600" = some (600 : ℚ) := by
  have h : parseQ "600" = some (⟨600, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_630 : Run.parseRat "630" = some (630 : ℚ) := by
  have h : parseQ "630" = some (⟨630, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_3_2 : Run.parseRat "3.2" = some ((16:ℚ)/5) := by
  have h : parseQ "3.2" = some (⟨32, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_7_3 : Run.parseRat "7.3" = some ((73:ℚ)/10) := by
  have h : parseQ "7.3" = some (⟨73, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0225 : Run.parseRat "0.0225" = some ((9:ℚ)/400) := by
  have h : parseQ "0.0225" = some (⟨225, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_09 : Run.parseRat "0.09" = some ((9:ℚ)/100) := by
  have h : parseQ "0.09" = some (⟨9, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_00171875 : Run.parseRat "0.00171875" = some ((11:ℚ)/6400) := by
  have h : parseQ "0.00171875" = some (⟨171875, 100000000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_000625 : Run.parseRat "0.000625" = some ((1:ℚ)/1600) := by
  have h : parseQ "0.000625" = some (⟨625, 1000000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_1583 : Run.parseRat "0.1583" = some ((1583:ℚ)/10000) := by
  have h : parseQ "0.1583" = some (⟨1583, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_2583 : Run.parseRat "1.2583" = some ((12583:ℚ)/10000) := by
  have h : parseQ "1.2583" = some (⟨12583, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The `u` constant terms: `NORMAL` `0.0225`, `FIRE` `0.09`. -/
noncomputable def wR (q : ℕ) : ℝ := if q = 0 then 9/400 else 9/100

/-- The `c` source terms: `NORMAL` `0.1583`, `FIRE` `1.2583`. -/
noncomputable def aR (q : ℕ) : ℝ := if q = 0 then 1583/10000 else 12583/10000

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 0) x = 1 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, tunnel_jetfan_pairout_IRv2, vs, Run.dynOf, Run.lowerE, hp_1_0, hp_1,
      hp_0, hp_100, hp_600, hp_630, hp_3_2, hp_7_3, hp_0_0225, hp_0_09, hp_0_00171875,
      hp_0_000625, hp_0_1583, hp_1_2583,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fR1_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 1) x = wR q - 11/6400 * (x (Rv 1) * x (Rv 1)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, tunnel_jetfan_pairout_IRv2, vs, Run.dynOf, Run.lowerE, hp_1_0, hp_1,
      hp_0, hp_100, hp_600, hp_630, hp_3_2, hp_7_3, hp_0_0225, hp_0_09, hp_0_00171875,
      hp_0_000625, hp_0_1583, hp_1_2583,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv,
      wR]

theorem fR2_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 2) x = aR q - 1/1600 * (x (Rv 1) * x (Rv 2)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, tunnel_jetfan_pairout_IRv2, vs, Run.dynOf, Run.lowerE, hp_1_0, hp_1,
      hp_0, hp_100, hp_600, hp_630, hp_3_2, hp_7_3, hp_0_0225, hp_0_09, hp_0_00171875,
      hp_0_000625, hp_0_1583, hp_1_2583,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv,
      aR]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ 16/5 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 73/10 ∧ 0 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 630) := by
  simp only [domR, hostEvolve, mR, tunnel_jetfan_pairout_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_1_0, hp_1, hp_0, hp_100, hp_600, hp_630, hp_3_2, hp_7_3,
    Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, FIRE 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  have hlen : q < 2 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 2 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 600 ∧ ν (Rv 2) ≤ 100 ∧ 0 ≤ ν (Rv 0) ∧ 16/5 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 73/10 ∧
        0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 630) := by
  simp [hostGuard, mR, tunnel_jetfan_pairout_IRv2, Run.lowerF, Run.lowerE, hp_1_0, hp_1, hp_0,
    hp_100, hp_600, hp_630, hp_3_2, hp_7_3, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (600 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 0) ∧ 16/5 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 73/10 ∧
        0 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 630) := by
  simp [hostGuard, mR, tunnel_jetfan_pairout_IRv2, Run.lowerF, Run.lowerE, hp_1_0, hp_1, hp_0,
    hp_100, hp_600, hp_630, hp_3_2, hp_7_3, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR tunnel_jetfan_pairout_IRv2 = 1 := by
  simp [epsR, tunnel_jetfan_pairout_IRv2, hp_1]

/-! ## The airflow: the explicit Riccati run -/

/-- The run of `u' = b (U² − u²)` (`b = 11/6400`) from `u₀`, for `U > 0`, `u₀ ≥ 0`, `s ≥ 0`:
`U ((U + u₀) e^{2bUs} − (U − u₀)) / ((U + u₀) e^{2bUs} + (U − u₀))`. -/
noncomputable def uSol (U u0 s : ℝ) : ℝ :=
  U * ((U + u0) * Real.exp (11/3200 * U * s) - (U - u0)) /
    ((U + u0) * Real.exp (11/3200 * U * s) + (U - u0))

theorem uSol_den_pos (U u0 s : ℝ) (hU : 0 < U) (hu0 : 0 ≤ u0) (hs : 0 ≤ s) :
    0 < (U + u0) * Real.exp (11/3200 * U * s) + (U - u0) := by
  have hE : 1 ≤ Real.exp (11/3200 * U * s) := Real.one_le_exp (by positivity)
  nlinarith

theorem uSol_zero (U u0 : ℝ) (hU : 0 < U) : uSol U u0 0 = u0 := by
  simp only [uSol, mul_zero, Real.exp_zero, mul_one]
  have h : U + u0 + (U - u0) = 2 * U := by ring
  rw [h]
  field_simp
  ring

theorem uSol_hasDerivAt (U u0 s : ℝ) (hU : 0 < U) (hu0 : 0 ≤ u0) (hs : 0 ≤ s) :
    HasDerivAt (uSol U u0) (11/6400 * (U * U - uSol U u0 s * uSol U u0 s)) s := by
  have hE : HasDerivAt (fun y => Real.exp (11/3200 * U * y))
      (Real.exp (11/3200 * U * s) * (11/3200 * U * 1)) s :=
    ((hasDerivAt_id' s).const_mul (11/3200 * U)).exp
  have hD := uSol_den_pos U u0 s hU hu0 hs
  have h := (((hE.const_mul (U + u0)).sub_const (U - u0)).const_mul U).div
    ((hE.const_mul (U + u0)).add_const (U - u0)) hD.ne'
  refine h.congr_deriv ?_
  have hDne := hD.ne'
  simp only [uSol]
  generalize Real.exp (11/3200 * U * s) = E at hDne ⊢
  field_simp
  ring

/-- The Riccati run stays between its start and its equilibrium `U`. -/
theorem uSol_between (U u0 s lo hi : ℝ) (hU : 0 < U) (hu0 : 0 ≤ u0) (hs : 0 ≤ s)
    (h1 : lo ≤ u0) (h2 : u0 ≤ hi) (h3 : lo ≤ U) (h4 : U ≤ hi) :
    lo ≤ uSol U u0 s ∧ uSol U u0 s ≤ hi := by
  have hD := uSol_den_pos U u0 s hU hu0 hs
  have hE : 1 ≤ Real.exp (11/3200 * U * s) := Real.one_le_exp (by positivity)
  have key : uSol U u0 s * ((U + u0) * Real.exp (11/3200 * U * s) + (U - u0)) =
      U * ((U + u0) * Real.exp (11/3200 * U * s) - (U - u0)) := by
    have hDne := hD.ne'
    simp only [uSol]
    generalize Real.exp (11/3200 * U * s) = E at hDne ⊢
    field_simp
  have k1 : (uSol U u0 s - u0) * ((U + u0) * Real.exp (11/3200 * U * s) + (U - u0)) =
      (U + u0) * (U - u0) * (Real.exp (11/3200 * U * s) - 1) := by
    linear_combination key
  have k2 : (U - uSol U u0 s) * ((U + u0) * Real.exp (11/3200 * U * s) + (U - u0)) =
      2 * U * (U - u0) := by
    linear_combination (-1:ℝ) * key
  have hA : 0 ≤ U + u0 := by linarith
  rcases le_total u0 U with hB | hB
  · have m1 := mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hB)) (sub_nonneg.mpr hE)
    have m2 : 0 ≤ 2 * U * (U - u0) := by nlinarith
    constructor <;> nlinarith
  · have m1 := mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hB)) (sub_nonneg.mpr hE)
    have m2 : 0 ≤ 2 * U * (u0 - U) := by nlinarith
    constructor <;> nlinarith

theorem uSol_contOn (U u0 : ℝ) (hU : 0 < U) (hu0 : 0 ≤ u0) : ContinuousOn (uSol U u0) (Ici 0) :=
  fun s hs => (uSol_hasDerivAt U u0 s hU hu0 hs).continuousAt.continuousWithinAt

/-! ## The contaminant: the linear run with a time-varying rate -/

/-- `∫₀ˢ p`. -/
noncomputable def primP (p : ℝ → ℝ) (s : ℝ) : ℝ := ∫ τ in (0:ℝ)..s, p τ

/-- The run of `c' = a − p(s) c` from `c₀` (variation of constants). -/
noncomputable def linSol (p : ℝ → ℝ) (a c0 s : ℝ) : ℝ :=
  Real.exp (-(primP p s)) * (c0 + ∫ τ in (0:ℝ)..s, Real.exp (primP p τ) * a)

theorem primP_hasDerivAt {p : ℝ → ℝ} (hp : Continuous p) (s : ℝ) :
    HasDerivAt (primP p) (p s) s :=
  (hp.integral_hasStrictDerivAt 0 s).hasDerivAt

theorem primP_cont {p : ℝ → ℝ} (hp : Continuous p) : Continuous (primP p) :=
  continuous_iff_continuousAt.mpr fun s => (primP_hasDerivAt hp s).continuousAt

theorem linSol_zero (p : ℝ → ℝ) (a c0 : ℝ) : linSol p a c0 0 = c0 := by
  simp [linSol, primP]

theorem linSol_I_hasDerivAt {p : ℝ → ℝ} (hp : Continuous p) (a c0 s : ℝ) :
    HasDerivAt (fun u => c0 + ∫ τ in (0:ℝ)..u, Real.exp (primP p τ) * a)
      (Real.exp (primP p s) * a) s :=
  (((Real.continuous_exp.comp (primP_cont hp)).mul continuous_const).integral_hasStrictDerivAt
    0 s).hasDerivAt.const_add c0

theorem linSol_hasDerivAt {p : ℝ → ℝ} (hp : Continuous p) (a c0 s : ℝ) :
    HasDerivAt (linSol p a c0) (a - p s * linSol p a c0 s) s := by
  have hE : HasDerivAt (fun u => Real.exp (-(primP p u))) (Real.exp (-(primP p s)) * (-(p s))) s :=
    (primP_hasDerivAt hp s).neg.exp
  have hEE : Real.exp (-(primP p s)) * Real.exp (primP p s) = 1 := by
    rw [← Real.exp_add]; simp
  refine (hE.mul (linSol_I_hasDerivAt hp a c0 s)).congr_deriv ?_
  simp only [linSol]
  linear_combination a * hEE

/-- With `c₀ ∈ [0, M]`, `a ≥ 0` and `a ≤ M p` on `[0, T]`, the run stays in `[0, M]` there. -/
theorem linSol_between {p : ℝ → ℝ} (hp : Continuous p) {a c0 M T : ℝ} (ha : 0 ≤ a)
    (hc0 : 0 ≤ c0) (hc0M : c0 ≤ M) (hpa : ∀ s ∈ Icc (0:ℝ) T, a ≤ M * p s) :
    ∀ s ∈ Icc (0:ℝ) T, 0 ≤ linSol p a c0 s ∧ linSol p a c0 s ≤ M := by
  intro s hs
  have hEpos := Real.exp_pos (-(primP p s))
  have hEE : Real.exp (-(primP p s)) * Real.exp (primP p s) = 1 := by
    rw [← Real.exp_add]; simp
  have hInt : 0 ≤ ∫ τ in (0:ℝ)..s, Real.exp (primP p τ) * a :=
    intervalIntegral.integral_nonneg hs.1 (fun τ _ => mul_nonneg (Real.exp_pos _).le ha)
  refine ⟨mul_nonneg hEpos.le (by linarith), ?_⟩
  -- `M e^{P} − (c₀ + ∫ e^{P} a)` does not decrease
  have hg : ∀ u, HasDerivAt (fun u => M * Real.exp (primP p u) -
      (c0 + ∫ τ in (0:ℝ)..u, Real.exp (primP p τ) * a))
      (M * (Real.exp (primP p u) * p u) - Real.exp (primP p u) * a) u := fun u =>
    ((primP_hasDerivAt hp u).exp.const_mul M).sub (linSol_I_hasDerivAt hp a c0 u)
  have hm := mono_of_deriv_nonneg hg (fun u hu => by
    have h1 := hpa u hu
    have h2 := Real.exp_pos (primP p u)
    nlinarith) s hs
  simp only [primP, intervalIntegral.integral_same, Real.exp_zero, mul_one, add_zero] at hm
  have hle : c0 + ∫ τ in (0:ℝ)..s, Real.exp (primP p τ) * a ≤ M * Real.exp (primP p s) := by
    simp only [primP] at hInt ⊢; linarith
  have := mul_le_mul_of_nonneg_left hle hEpos.le
  simp only [linSol]
  nlinarith

/-! ## Existence: the explicit run -/

/-- The airflow equilibrium `U = √(w / b)` of mode `q` (`NORMAL` `√(144/11)`, `FIRE`
`√(576/11)`). -/
noncomputable def UR (q : ℕ) : ℝ := Real.sqrt (wR q * (6400/11))

theorem UR_sq (q : ℕ) : UR q * UR q = wR q * (6400/11) :=
  Real.mul_self_sqrt (by unfold wR; split_ifs <;> norm_num)

theorem UR_box (q : ℕ) : 0 < UR q ∧ 16/5 ≤ UR q ∧ UR q ≤ 73/10 := by
  have h0 : 0 ≤ UR q := Real.sqrt_nonneg _
  have h1 := UR_sq q
  have hw : 144/11 ≤ wR q * (6400/11) ∧ wR q * (6400/11) ≤ 576/11 := by
    unfold wR; split_ifs <;> norm_num
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The rate of the contaminant along the airflow run (clamped at `s = 0`, so it is
continuous everywhere). -/
noncomputable def pC (q : ℕ) (u0 s : ℝ) : ℝ := 1/1600 * uSol (UR q) u0 (max s 0)

theorem pC_cont (q : ℕ) (u0 : ℝ) (hu0 : 0 ≤ u0) : Continuous (pC q u0) :=
  continuous_const.mul ((uSol_contOn (UR q) u0 (UR_box q).1 hu0).comp_continuous
    (continuous_id.max continuous_const) (fun s => le_max_right s 0))

/-- The run of mode `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (s : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + s
  else if i.val = 1 then uSol (UR q) (x (Rv 1)) s
  else linSol (pC q (x (Rv 1))) (aR q) (x (Rv 2)) s

theorem phi_zero (q : ℕ) (x : State (Var 3)) : phi q x 0 = fun s => x (Rv 0) + s := by
  funext s; simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 3)) : phi q x 1 = uSol (UR q) (x (Rv 1)) := by
  funext s; simp [phi]

theorem phi_two (q : ℕ) (x : State (Var 3)) :
    phi q x 2 = linSol (pC q (x (Rv 1))) (aR q) (x (Rv 2)) := by
  funext s; simp [phi]

theorem phi_der (q : ℕ) (hq : q < 2) (x : State (Var 3)) (hx : 0 ≤ x (Rv 1)) (i : Fin 3)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, phi_zero]
      exact (hasDerivAt_id' t).const_add _
  | 1 =>
      rw [fR1_eval q hq, trajRs_R, phi_one]
      refine (uSol_hasDerivAt (UR q) (x (Rv 1)) t (UR_box q).1 hx ht).congr_deriv ?_
      rw [UR_sq]; ring
  | 2 =>
      rw [fR2_eval q hq, trajRs_R, trajRs_R, phi_one, phi_two]
      refine (linSol_hasDerivAt (pC_cont q _ hx) (aR q) (x (Rv 2)) t).congr_deriv ?_
      simp only [pC, max_eq_left ht]; ring

theorem exists_run (q : ℕ) (hq : q < 2) (x : State (Var 3)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := (sat_domR x).mp hd
  have hU := UR_box q
  have hx : 0 ≤ x (Rv 1) := by linarith
  refine ⟨_, trajRs_sol x (phi q x) ε hε (fun i => ?_) (fun i t ht _ => phi_der q hq x hx i t ht)
    (fun t ht hte => ?_)⟩
  · match i with
    | 0 => rw [phi_zero]; simp
    | 1 => rw [phi_one, uSol_zero _ _ hU.1]
    | 2 => rw [phi_two, linSol_zero]
  · have hu := uSol_between (UR q) (x (Rv 1)) t (16/5) (73/10) hU.1 hx ht a1 a2 hU.2.1 hU.2.2
    have hc := linSol_between (pC_cont q _ hx) (a := aR q) (M := 630) (T := t)
      (by unfold aR; split_ifs <;> norm_num) a3 a4 (fun s _ => by
        have h := uSol_between (UR q) (x (Rv 1)) (max s 0) (16/5) (73/10) hU.1 hx
          (le_max_right s 0) a1 a2 hU.2.1 hU.2.2
        have ha : aR q ≤ 12583/10000 := by unfold aR; split_ifs <;> norm_num
        simp only [pC]; nlinarith [h.1]) t ⟨ht, le_rfl⟩
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R, phi_zero, phi_one, phi_two]
    exact ⟨by linarith, hu.1, hu.2, hc.1, hc.2⟩

/-! ## Assumption 1 -/

/-- **Assumption 1 for `tunnel_jetfan_pairout`**, every mode, Z3-free. -/
theorem tunnel_jetfan_pairout_wellFormedR :
    WellFormedR Gr guardR (epsR tunnel_jetfan_pairout_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq2 x hd 1 (by norm_num), ?_⟩
  intro t Φ _ H
  have H' : ODESol (rightBlock (fR q) (Term.const 1)) domR x t Φ := H
  obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
  interval_cases q
  · -- NORMAL: `c ≤ 100` is kept (at `c = 100`, `c' ≤ 0.1583 − 0.2`); NORMAL before 600, FIRE after
    have hg0 := (sat_guard0 x).mp hg
    have hc := H'.coord_le_barrier 2 100 (fun s hs hK => by
      obtain ⟨-, s1, -, -, -⟩ := (sat_domR s).mp hs
      rw [fR2_eval 0 (by norm_num)]
      have := mul_le_mul s1 hK (by norm_num) (by linarith)
      rw [show aR 0 = 1583/10000 by simp [aR]]
      linarith) hg0.2.1
    by_cases h600 : Φ t (Rv 0) < 600
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨h600, hc, e0, e1, e2, e3, e4⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, e0, e1, e2, e3, e4⟩⟩
  · -- FIRE: the clock does not fall, so `t ≥ 600` is kept
    have hg1 := (sat_guard1 x).mp hg
    have ht := H'.coord_ge_barrier 0 600 (fun s _ _ => by
      rw [fR0_eval 1 (by norm_num)]; norm_num) hg1.1
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guard1 _).mpr ⟨ht, e0, e1, e2, e3, e4⟩⟩

end V2TunnelJetfanPairout
end RelCertifier
