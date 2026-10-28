/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
four pump stages and their declared `next` lists), the lowered right guards, and `ε_r = 10`
read from the file.

The tank level `h` (coordinate 0) and the demand conductance `w` (coordinate 1): stage `Pc`
(`c = 2, 3, 4, 5` pumps, right modes `0 … 3`) runs `h' = 0.005 c − 0.001 w h`,
`w' = 0.02 (22 − w)`, all stages inside `0 ≤ h ≤ 2.5`, `6 ≤ w ≤ 22`; the guards are the demand
bands `[6, 10)`, `[10, 14)`, `[14, 18)`, `[18, 22]` (each with `0 ≤ h ≤ 2.5`).
* Existence (i), every stage: the explicit run. `w(t) = 22 + (w₀ − 22) e^{−t/50}` stays in
  `[w₀, 22]`; `h` is the variation-of-constants solution of the time-varying linear equation
  `h' = a − (w(t)/1000) h` (`hSol`, with `∫₀ᵗ w/1000` in closed form, `BSol`). It is first a run
  over the demand floor `w ≥ 2c` (`domW`, below every guard's band floor and kept since `w` only
  rises); over that floor two barriers keep `0 ≤ h ≤ 2.5` (at `h ≤ 0` the field is `≥ 0.005 c`,
  at `h ≥ 2.5` it is `≤ 0.005 c − 0.0025 · 2c = 0`), so the same run lies in the evolve domain.
* (ii), style (b) for `P2`, `P3`, `P4`: `w` does not fall (`w' ≥ 0` on the domain) and rises by
  at most `0.32 · 10 = 3.2 < 4` (one band width) in one interval, so the end state lies in the
  stage's own band or the next one, both declared successors (`P4`: the next band `[18, 22]`
  reaches the domain's top). Style (a) for `P5` (`next = [P5]`): `w ≥ 18` is kept and the
  domain gives `w ≤ 22`, `0 ≤ h ≤ 2.5`.
Z3-free; modelled on the old `TankDos3to1.lean` (guards, edges), `AirheaderDos3to1.lean`
(bilinear field), `QuadLightLag.lean` (run over an auxiliary domain, then barriers) and
`WellFormedTerrain.forcedSol` (variation of constants).
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.tank_dos_3to1

namespace RelCertifier
namespace V2TankDos3to1

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["h", "w"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := tank_dos_3to1_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp30 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0005 : Run.parseRat "0.005" = some ((1:ℚ)/200) := by
  have h : parseQ "0.005" = some (⟨5, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0001 : Run.parseRat "0.001" = some ((1:ℚ)/1000) := by
  have h : parseQ "0.001" = some (⟨1, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp002 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp220 : Run.parseRat "22.0" = some (22 : ℚ) := by
  have h : parseQ "22.0" = some (⟨220, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp60 : Run.parseRat "6.0" = some (6 : ℚ) := by
  have h : parseQ "6.0" = some (⟨60, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp140 : Run.parseRat "14.0" = some (14 : ℚ) := by
  have h : parseQ "14.0" = some (⟨140, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp180 : Run.parseRat "18.0" = some (18 : ℚ) := by
  have h : parseQ "18.0" = some (⟨180, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The right fields, domain and guards, evaluated -/

/-- The number of pumps running in right mode `q` (`P2` … `P5`). -/
noncomputable def cR (q : ℕ) : ℝ := (q : ℝ) + 2

theorem cR_pos (q : ℕ) : 0 < cR q := by unfold cR; positivity

/-- The level row: `h' = 0.005 c − 0.001 w h`. -/
theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = cR q * (1/200) - 1/1000 * (x (Rv 1) * x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, tank_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp20, hp30, hp40,
      hp50, hp0005, hp0001, hp002, hp220, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, cR] <;> norm_num

/-- The demand row: `w' = 0.02 (22 − w)`, every stage. -/
theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 1/50 * (22 - x (Rv 1)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, tank_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp20, hp30, hp40,
      hp50, hp0005, hp0001, hp002, hp220, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 5/2 ∧ 6 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 22) := by
  simp only [domR, hostEvolve, mR, tank_dos_3to1_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp25, hp60, hp220, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (P2 0, P3 1, P4 2, P5 3). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 3), (3, 3)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The right guards, evaluated: the demand bands, each with the tank range. -/
theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (6 ≤ ν (Rv 1) ∧ ν (Rv 1) < 10 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 5/2) := by
  simp [hostGuard, mR, tank_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp00, hp25, hp60, hp100,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔
      (10 ≤ ν (Rv 1) ∧ ν (Rv 1) < 14 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 5/2) := by
  simp [hostGuard, mR, tank_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp00, hp25, hp100, hp140,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 2)) ν ↔
      (14 ≤ ν (Rv 1) ∧ ν (Rv 1) < 18 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 5/2) := by
  simp [hostGuard, mR, tank_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp00, hp25, hp140, hp180,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guard3 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 3)) ν ↔
      (18 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 22 ∧ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 5/2) := by
  simp [hostGuard, mR, tank_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp00, hp25, hp180, hp220,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- Every guard lies above the stage's demand floor `2 c` (`6 ≥ 4`, `10 ≥ 6`, `14 ≥ 8`,
`18 ≥ 10`). -/
theorem guard_floor (q : ℕ) (hq : q < 4) (x : State (Var 2)) (hg : Formula.sat (guardR q) x) :
    2 * cR q ≤ x (Rv 1) := by
  interval_cases q
  · obtain ⟨h, -⟩ := (sat_guard0 x).mp hg; norm_num [cR]; linarith
  · obtain ⟨h, -⟩ := (sat_guard1 x).mp hg; norm_num [cR]; linarith
  · obtain ⟨h, -⟩ := (sat_guard2 x).mp hg; norm_num [cR]; linarith
  · obtain ⟨h, -⟩ := (sat_guard3 x).mp hg; norm_num [cR]; linarith

/-! ## Existence: the explicit run -/

/-- The demand surge from `w₀`: `w(t) = 22 + (w₀ − 22) e^{−t/50}`. -/
noncomputable def wSol (w0 t : ℝ) : ℝ := 22 + (w0 - 22) * Real.exp (-(1/50 * t))

/-- `∫₀ᵗ w/1000`, in closed form. -/
noncomputable def BSol (w0 t : ℝ) : ℝ :=
  (22 * t + 50 * (w0 - 22) * (1 - Real.exp (-(1/50 * t)))) / 1000

/-- The level: variation of constants for `h' = a − (w(t)/1000) h`, `h 0 = h₀`. -/
noncomputable def hSol (a h0 w0 t : ℝ) : ℝ :=
  Real.exp (-(BSol w0 t)) * (h0 + ∫ τ in (0:ℝ)..t, Real.exp (BSol w0 τ) * a)

theorem wSol_hasDerivAt (w0 t : ℝ) : HasDerivAt (wSol w0) (1/50 * (22 - wSol w0 t)) t :=
  hasDerivAt_expApproach (1/50) 22 w0 t

theorem BSol_hasDerivAt (w0 t : ℝ) : HasDerivAt (BSol w0) (wSol w0 t / 1000) t := by
  have he : HasDerivAt (fun u => Real.exp (-(1/50 * u)))
      (Real.exp (-(1/50 * t)) * (-(1/50 * 1))) t :=
    (((hasDerivAt_id' t).const_mul (1/50)).neg).exp
  have h := ((((hasDerivAt_id' t).const_mul 22).add
    ((he.const_sub 1).const_mul (50 * (w0 - 22)))).div_const 1000)
  refine h.congr_deriv ?_
  simp only [wSol]
  ring

theorem BSol_continuous (w0 : ℝ) : Continuous (BSol w0) :=
  continuous_iff_continuousAt.mpr fun t => (BSol_hasDerivAt w0 t).continuousAt

theorem hSol_hasDerivAt (a h0 w0 t : ℝ) :
    HasDerivAt (hSol a h0 w0) (a - wSol w0 t / 1000 * hSol a h0 w0 t) t := by
  have hc : Continuous (fun τ => Real.exp (BSol w0 τ) * a) :=
    (Real.continuous_exp.comp (BSol_continuous w0)).mul continuous_const
  have hI : HasDerivAt (fun u => h0 + ∫ τ in (0:ℝ)..u, Real.exp (BSol w0 τ) * a)
      (Real.exp (BSol w0 t) * a) t :=
    (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add h0
  have hE : HasDerivAt (fun u => Real.exp (-(BSol w0 u)))
      (Real.exp (-(BSol w0 t)) * (-(wSol w0 t / 1000))) t :=
    ((BSol_hasDerivAt w0 t).neg).exp
  have hEE : Real.exp (-(BSol w0 t)) * Real.exp (BSol w0 t) = 1 := by
    rw [← Real.exp_add]; simp
  refine (hE.mul hI).congr_deriv ?_
  simp only [hSol]
  linear_combination a * hEE

theorem hSol_zero (a h0 w0 : ℝ) : hSol a h0 w0 0 = h0 := by
  simp [hSol, BSol]

theorem wSol_zero (w0 : ℝ) : wSol w0 0 = w0 := by
  simp [wSol]

/-- The explicit run of right mode `q` from `x`: level `hSol`, demand `wSol`. -/
noncomputable def phi (q : ℕ) (x : State (Var 2)) (i : Fin 2) (t : ℝ) : ℝ :=
  if i.val = 0 then hSol (cR q * (1/200)) (x (Rv 0)) (x (Rv 1)) t else wSol (x (Rv 1)) t

theorem phi_zero (q : ℕ) (x : State (Var 2)) (t : ℝ) :
    phi q x 0 t = hSol (cR q * (1/200)) (x (Rv 0)) (x (Rv 1)) t := by
  simp [phi]

theorem phi_one (q : ℕ) (x : State (Var 2)) (t : ℝ) :
    phi q x 1 t = wSol (x (Rv 1)) t := by
  simp [phi]

theorem phi_init (q : ℕ) (x : State (Var 2)) (i : Fin 2) : phi q x i 0 = x (Rv i) := by
  match i with
  | 0 => rw [phi_zero, hSol_zero]
  | 1 => rw [phi_one, wSol_zero]

theorem phi_der (q : ℕ) (hq : q < 4) (x : State (Var 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, trajRs_R, trajRs_R, phi_zero, phi_one]
      have hf : phi q x 0 = hSol (cR q * (1/200)) (x (Rv 0)) (x (Rv 1)) := by
        funext u; exact phi_zero q x u
      rw [hf]
      exact (hSol_hasDerivAt _ _ _ t).congr_deriv (by ring)
  | 1 =>
      rw [fR1_eval q hq, trajRs_R, phi_one]
      have hf : phi q x 1 = wSol (x (Rv 1)) := by
        funext u; exact phi_one q x u
      rw [hf]
      exact wSol_hasDerivAt _ t

/-- The demand floor `w ≥ 2 c` of right mode `q` (the auxiliary domain of the run). -/
noncomputable def domW (q : ℕ) : Formula (Var 2) :=
  Formula.cmp CompOp.le (Term.const (2 * cR q)) (Term.var (Rv 1))

theorem sat_domW (q : ℕ) (s : State (Var 2)) :
    Formula.sat (domW q) s ↔ 2 * cR q ≤ s (Rv 1) := by
  simp [domW, Formula.sat, CompOp.interp, Term.eval]

/-- The demand of the explicit run stays in `[w₀, 22]`. -/
theorem wSol_between (w0 t : ℝ) (hw : w0 ≤ 22) (ht : 0 ≤ t) :
    w0 ≤ wSol w0 t ∧ wSol w0 t ≤ 22 := by
  have h := exp_approach_between (1/50) 22 w0 t (by norm_num) ht
  rw [min_eq_left hw, max_eq_right hw] at h
  exact h

/-- The explicit run is a run over the demand floor. -/
theorem run_domW (q : ℕ) (hq : q < 4) (x : State (Var 2)) (hw : 2 * cR q ≤ x (Rv 1))
    (hw22 : x (Rv 1) ≤ 22) (ε : ℝ) (hε : 0 ≤ ε) :
    ODESol (rightBlock (fR q) (Term.const 1)) (domW q) x ε (trajRs x (phi q x)) :=
  trajRs_sol x (phi q x) ε hε (phi_init q x) (fun i t _ _ => phi_der q hq x i t)
    (fun t ht _ => by
      rw [sat_domW, trajRs_R, phi_one]
      linarith [(wSol_between (x (Rv 1)) t hw22 ht).1])

/-- **Existence (clause (i))**: from a domain state above the demand floor, the explicit run
of every duration `ε ≥ 0` lies in the evolve domain (two barriers over the floor keep
`0 ≤ h ≤ 2.5`). -/
theorem exists_run (q : ℕ) (hq : q < 4) (x : State (Var 2)) (hd : Formula.sat domR x)
    (hw : 2 * cR q ≤ x (Rv 1)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨h0, h25, w6, w22⟩ := (sat_domR x).mp hd
  have H := run_domW q hq x hw w22 ε hε
  have hc := cR_pos q
  refine ⟨_, ⟨H.hr, H.hΦ0, H.hder, H.hmask, fun t ht => ?_⟩⟩
  have Ht := H.restrict ht.1 ht.2
  -- `h ≥ 0`: at `h ≤ 0` (and `w ≥ 0`) the field is at least `0.005 c > 0`
  have hlo := Ht.coord_ge_barrier 0 0 (fun s hs hs0 => by
    rw [sat_domW] at hs
    rw [fR0_eval q hq]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s (Rv 1)) (by linarith : (0:ℝ) ≤ -s (Rv 0))])
    h0
  -- `h ≤ 2.5`: at `h ≥ 2.5` and `w ≥ 2c` the outflow `w h / 1000 ≥ 5c/1000` beats the pumps
  have hhi := Ht.coord_le_barrier 0 (5/2) (fun s hs hs5 => by
    rw [sat_domW] at hs
    rw [fR0_eval q hq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs5),
      mul_nonneg hc.le (sub_nonneg.mpr hs5)])
    h25
  obtain ⟨wl, wh⟩ := wSol_between (x (Rv 1)) t w22 ht.1
  have hw1 : trajRs x (phi q x) t (Rv 1) = wSol (x (Rv 1)) t := by rw [trajRs_R, phi_one]
  rw [sat_domR, hw1]
  exact ⟨hlo, hhi, by linarith, wh⟩

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR tank_dos_3to1_IRv2 = 10 := by
  simp [epsR, tank_dos_3to1_IRv2, hp100]

theorem memR1 (q : ℕ) : (Rv 1, Term.binop .mul (Term.const 1) (fR q 1)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 1

/-- **Assumption 1 for `tank_dos_3to1`**, every mode, Z3-free. -/
theorem tank_dos_3to1_wellFormedR : WellFormedR Gr guardR (epsR tank_dos_3to1_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq4 x hd (guard_floor q hq4 x hg) 10 (by norm_num), ?_⟩
  intro t Φ ht H
  -- the run ends in the domain
  obtain ⟨e0, e25, e6, e22⟩ := (sat_domR _).mp H.end_dom
  -- the demand does not fall (`w' ≥ 0` for `w ≤ 22`) ...
  have hup : x (Rv 1) ≤ Φ t (Rv 1) := H.mono (memR1 q) (fun s hs => by
    obtain ⟨-, -, -, hs22⟩ := (sat_domR s).mp hs
    rw [eval_unit_mul, fR1_eval q hq4]; linarith)
  -- ... and rises at rate at most `0.02 · 16 = 0.32` (`w ≥ 6`), so by at most `3.2`
  have hrate : Φ t (Rv 1) ≤ x (Rv 1) + 8/25 * t := H.rate_le (memR1 q) (8/25) (fun s hs => by
    obtain ⟨-, -, hs6, -⟩ := (sat_domR s).mp hs
    rw [eval_unit_mul, fR1_eval q hq4]; linarith)
  have hstep : Φ t (Rv 1) ≤ x (Rv 1) + 16/5 := by linarith
  have pick : ∀ t', (q, t') ∈ edgeList → Formula.sat (hostGuard vs 2 Side.R (mR t')) (Φ t) →
      ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
    fun t' he hs => ⟨edgeW q t', edge_mem q t' he, hs⟩
  interval_cases q
  · -- P2: `w₀ ∈ [6, 10)`, the end demand in `[6, 13.2)`: P2 or P3
    obtain ⟨g6, g10, -, -⟩ := (sat_guard0 x).mp hg
    by_cases h10 : Φ t (Rv 1) < 10
    · exact pick 0 (by decide) ((sat_guard0 _).mpr ⟨by linarith, h10, e0, e25⟩)
    · exact pick 1 (by decide) ((sat_guard1 _).mpr ⟨by linarith, by linarith, e0, e25⟩)
  · -- P3: `w₀ ∈ [10, 14)`, the end demand in `[10, 17.2)`: P3 or P4
    obtain ⟨g10, g14, -, -⟩ := (sat_guard1 x).mp hg
    by_cases h14 : Φ t (Rv 1) < 14
    · exact pick 1 (by decide) ((sat_guard1 _).mpr ⟨by linarith, h14, e0, e25⟩)
    · exact pick 2 (by decide) ((sat_guard2 _).mpr ⟨by linarith, by linarith, e0, e25⟩)
  · -- P4: `w₀ ∈ [14, 18)`, the end demand in `[14, 22]`: P4 or P5
    obtain ⟨g14, g18, -, -⟩ := (sat_guard2 x).mp hg
    by_cases h18 : Φ t (Rv 1) < 18
    · exact pick 2 (by decide) ((sat_guard2 _).mpr ⟨by linarith, h18, e0, e25⟩)
    · exact pick 3 (by decide) ((sat_guard3 _).mpr ⟨by linarith, e22, e0, e25⟩)
  · -- P5: `w ≥ 18` is kept, the domain caps it at 22
    obtain ⟨g18, -, -, -⟩ := (sat_guard3 x).mp hg
    exact pick 3 (by decide) ((sat_guard3 _).mpr ⟨by linarith, e22, e0, e25⟩)

end V2TankDos3to1
end RelCertifier

