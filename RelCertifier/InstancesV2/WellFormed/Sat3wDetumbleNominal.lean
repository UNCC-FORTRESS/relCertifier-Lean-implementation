/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_nominal`: Assumption 1 of the right model (style (a); the momentum band in the right evolve domain)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**The right evolve domain carries the momentum band `|h_i + J_i w_i| ≤ 2`** (the body's
momentum within the wheels' capacity, a constant of every design-model flow; since
2026-10-15). Without it `WellFormedR` would be false: the three
wheel momenta are bounded by the evolve domain (`|hᵢ| ≤ 2`) but driven by `DETUMBLE`
(`h₁' = w₁`, `h₂' = 2 w₂`, `h₃' = 2.5 w₃`, `w' = −w/2`), which conserves `h₁ + 2w₁`,
`h₂ + 4w₂`, `h₃ + 5w₃`. From `w₃ = 0.4`, `h₃ = 2`, the rest 0 (energy `0.8`, inside the
guard and the domain) no run of duration 1 exists: it would end at `h₃ = 4 − 2 e^{−1/2} > 2`
(clause (i) fails).

**With the band, Assumption 1 holds at every mode** (`sat3w_detumble_nominal_wellFormedR`, Z3-free), and
the band is kept by every mode's flow (`sat3w_detumble_nominal_band_invariant`): the active guard (`E ≤ 1`)
is forward invariant (each rate decays; style (a)); existence is the instance's explicit
solution `flowR_exists`, which stays in the domain because the conserved sums are constant.
`SAFE` (`E > 1`, frozen) holds still.
-/
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_nominal
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Sat3wDetumbleNominal

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["w1", "w2", "w3", "h1", "h2", "h3"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := sat3w_detumble_nominal_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.R (mR q)
noncomputable def domR : Formula (Var 6) := hostEvolve vs 6 Side.R (mR 0)
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp2 : Run.parseRat "2" = some (2 : ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp4 : Run.parseRat "4" = some (4 : ℚ) := by
  have h : parseQ "4" = some (⟨4, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp5 : Run.parseRat "5" = some (5 : ℚ) := by
  have h : parseQ "5" = some (⟨5, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm10 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fR0_eval (x : State (Var 6)) : Term.eval (fR 0 0) x = -(1/2) * x (Rv 0) := by
  simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
  ring
theorem fR1_eval (x : State (Var 6)) : Term.eval (fR 0 1) x = -(1/2) * x (Rv 1) := by
  simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
  ring
theorem fR2_eval (x : State (Var 6)) : Term.eval (fR 0 2) x = -(1/2) * x (Rv 2) := by
  simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
  ring
theorem fR3_eval (x : State (Var 6)) : Term.eval (fR 0 3) x = x (Rv 0) := by
  simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
theorem fR4_eval (x : State (Var 6)) : Term.eval (fR 0 4) x = 2 * x (Rv 1) := by
  simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]
theorem fR5_eval (x : State (Var 6)) : Term.eval (fR 0 5) x = 5/2 * x (Rv 2) := by
  simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 6)) :
    Formula.sat domR x ↔ (-1 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1 ∧ -1 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 1 ∧
      -1 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 1 ∧ -2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 2 ∧
      -2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 2 ∧ -2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 2 ∧
      -2 ≤ x (Rv 3) + 2 * x (Rv 0) ∧ x (Rv 3) + 2 * x (Rv 0) ≤ 2 ∧
      -2 ≤ x (Rv 4) + 4 * x (Rv 1) ∧ x (Rv 4) + 4 * x (Rv 1) ≤ 2 ∧
      -2 ≤ x (Rv 5) + 5 * x (Rv 2) ∧ x (Rv 5) + 5 * x (Rv 2) ≤ 2) := by
  simp only [domR, hostEvolve, mR, sat3w_detumble_nominal_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm10, hp10, hpm20, hp20, hp40, hp50, Run.resolveVar, AOp.interp,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]

/-! ## The nonblocking quantities `c_i = h_i + J_i w_i` (conserved by the right flow) -/

/-- `c1 = h1 + 2 w1` on the right. -/
noncomputable def c1T : Term (Var 6) :=
  Term.binop .add (Term.var (Rv 3)) (Term.binop .mul (Term.const 2) (Term.var (Rv 0)))
/-- `c2 = h2 + 4 w2` on the right. -/
noncomputable def c2T : Term (Var 6) :=
  Term.binop .add (Term.var (Rv 4)) (Term.binop .mul (Term.const 4) (Term.var (Rv 1)))
/-- `c3 = h3 + 5 w3` on the right. -/
noncomputable def c3T : Term (Var 6) :=
  Term.binop .add (Term.var (Rv 5)) (Term.binop .mul (Term.const 5) (Term.var (Rv 2)))

theorem eval_c1 (x : State (Var 6)) : Term.eval c1T x = x (Rv 3) + 2 * x (Rv 0) := by
  simp [c1T, Term.eval, AOp.interp]
theorem eval_c2 (x : State (Var 6)) : Term.eval c2T x = x (Rv 4) + 4 * x (Rv 1) := by
  simp [c2T, Term.eval, AOp.interp]
theorem eval_c3 (x : State (Var 6)) : Term.eval c3T x = x (Rv 5) + 5 * x (Rv 2) := by
  simp [c3T, Term.eval, AOp.interp]
/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := hostGuard vs 6 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (`DETUMBLE` 0, `SAFE` 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 6)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## Regions -/

/-- `−2 ≤ c ≤ 2` as a formula. -/
noncomputable def bandF (c : Term (Var 6)) : Formula (Var 6) :=
  Formula.and (Formula.cmp CompOp.le c (Term.const 2))
    (Formula.cmp CompOp.le (Term.const (-2)) c)

/-- The nonblocking conjunct `⋀_i −2 ≤ c_i ≤ 2` (NOT a tool cut; see the theorem). -/
noncomputable def nbF : Formula (Var 6) :=
  Formula.and (Formula.and (bandF c1T) (bandF c2T)) (bandF c3T)

theorem sat_nbF (ν : State (Var 6)) :
    Formula.sat nbF ν ↔
      ((ν (Rv 3) + 2 * ν (Rv 0) ≤ 2 ∧ -2 ≤ ν (Rv 3) + 2 * ν (Rv 0)) ∧
        (ν (Rv 4) + 4 * ν (Rv 1) ≤ 2 ∧ -2 ≤ ν (Rv 4) + 4 * ν (Rv 1))) ∧
      (ν (Rv 5) + 5 * ν (Rv 2) ≤ 2 ∧ -2 ≤ ν (Rv 5) + 5 * ν (Rv 2)) := by
  simp only [nbF, bandF, Formula.sat, CompOp.interp, eval_c1, eval_c2, eval_c3, Term.eval]

/-! ## Existence: the right `DETUMBLE` flow, explicitly, from a nonblocking start

`w_i(t) = w_i0 e^{−t/2}`, `h_i(t) = h_i0 + J_i w_i0 (1 − e^{−t/2})` (`J = (2, 4, 5)`): the
rates contract toward 0 (inside `[−1, 1]`), and
`h_i(t) = e^{−t/2} h_i0 + (1 − e^{−t/2}) (h_i0 + J_i w_i0)` is a convex combination of
`h_i0` and the conserved `c_i = h_i0 + J_i w_i0` — inside `[−2, 2]` exactly when the
nonblocking conjunct holds. -/

noncomputable def ex (t : ℝ) : ℝ := Real.exp (-(1/2) * t)

noncomputable def solR (b : State (Var 6)) (t : ℝ) : State (Var 6) := fun x =>
  if x = Rv 0 then b (Rv 0) * ex t
  else if x = Rv 1 then b (Rv 1) * ex t
  else if x = Rv 2 then b (Rv 2) * ex t
  else if x = Rv 3 then b (Rv 3) + 2 * b (Rv 0) * (1 - ex t)
  else if x = Rv 4 then b (Rv 4) + 4 * b (Rv 1) * (1 - ex t)
  else if x = Rv 5 then b (Rv 5) + 5 * b (Rv 2) * (1 - ex t)
  else b x

theorem solR_0 (b : State (Var 6)) (t : ℝ) : solR b t (Rv 0) = b (Rv 0) * ex t := by
  simp [solR]
theorem solR_1 (b : State (Var 6)) (t : ℝ) : solR b t (Rv 1) = b (Rv 1) * ex t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_2 (b : State (Var 6)) (t : ℝ) : solR b t (Rv 2) = b (Rv 2) * ex t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_3 (b : State (Var 6)) (t : ℝ) :
    solR b t (Rv 3) = b (Rv 3) + 2 * b (Rv 0) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_4 (b : State (Var 6)) (t : ℝ) :
    solR b t (Rv 4) = b (Rv 4) + 4 * b (Rv 1) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_5 (b : State (Var 6)) (t : ℝ) :
    solR b t (Rv 5) = b (Rv 5) + 5 * b (Rv 2) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (b : State (Var 6)) (t : ℝ) {x : Var 6} (hx : ∀ i, x ≠ Rv i) :
    solR b t x = b x := by
  simp [solR, hx]

theorem ex_hasDeriv (t : ℝ) : HasDerivAt ex (-(1/2) * ex t) t := by
  have h := ((hasDerivAt_id t).const_mul (-(1/2 : ℝ))).exp
  have h' : HasDerivAt ex (Real.exp (-(1/2) * id t) * (-(1/2) * 1)) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring

theorem ex_zero : ex 0 = 1 := by simp [ex]
theorem ex_pos (t : ℝ) : 0 < ex t := Real.exp_pos _
theorem ex_le_one {t : ℝ} (ht : 0 ≤ t) : ex t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; linarith

/-- A rate contracted by `e ∈ (0, 1]` stays in `[−1, 1]`. -/
theorem rate_band {w e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hl : -1 ≤ w) (hu : w ≤ 1) :
    -1 ≤ w * e ∧ w * e ≤ 1 := by
  constructor <;> nlinarith [mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 1 + w),
    mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 1 - w)]

/-- A wheel momentum `h0 + a w0 (1 − e)` (convex combination of `h0` and `h0 + a w0`) stays
in `[−2, 2]` when both ends do. -/
theorem mom_band {h a w e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hl : -2 ≤ h) (hu : h ≤ 2)
    (hcu : h + a * w ≤ 2) (hcl : -2 ≤ h + a * w) :
    -2 ≤ h + a * w * (1 - e) ∧ h + a * w * (1 - e) ≤ 2 := by
  constructor <;> nlinarith [mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 2 + h),
    mul_nonneg he0.le (by linarith : (0:ℝ) ≤ 2 - h),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - e) (by linarith : (0:ℝ) ≤ 2 + (h + a * w)),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - e) (by linarith : (0:ℝ) ≤ 2 - (h + a * w))]

theorem solR_stays (b : State (Var 6)) (hb : Formula.sat domR b)
    {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR b t) := by
  rw [sat_domR] at hb ⊢
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u,
    hc1l, hc1u, hc2l, hc2u, hc3l, hc3u⟩ := hb
  have he0 := ex_pos t
  have he1 := ex_le_one ht
  rw [solR_0, solR_1, solR_2, solR_3, solR_4, solR_5]
  obtain ⟨a0, b0⟩ := rate_band he0 he1 h0l h0u
  obtain ⟨a1, b1⟩ := rate_band he0 he1 h1l h1u
  obtain ⟨a2, b2⟩ := rate_band he0 he1 h2l h2u
  obtain ⟨a3, b3⟩ := mom_band he0 he1 h3l h3u hc1u hc1l
  obtain ⟨a4, b4⟩ := mom_band he0 he1 h4l h4u hc2u hc2l
  obtain ⟨a5, b5⟩ := mom_band he0 he1 h5l h5u hc3u hc3l
  -- the momentum sums are constants of the solution
  have e1 : b (Rv 3) + 2 * b (Rv 0) * (1 - ex t) + 2 * (b (Rv 0) * ex t) = b (Rv 3) + 2 * b (Rv 0) := by
    ring
  have e2 : b (Rv 4) + 4 * b (Rv 1) * (1 - ex t) + 4 * (b (Rv 1) * ex t) = b (Rv 4) + 4 * b (Rv 1) := by
    ring
  have e3 : b (Rv 5) + 5 * b (Rv 2) * (1 - ex t) + 5 * (b (Rv 2) * ex t) = b (Rv 5) + 5 * b (Rv 2) := by
    ring
  rw [e1, e2, e3]
  exact ⟨a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, hc1l, hc1u, hc2l, hc2u, hc3l, hc3u⟩

theorem rightBlock_bound_mem (i : Fin 6) : Rv i ∈ (rightBlock (fR 0) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- A rate coordinate `w0 e^{−t/2}` has derivative `−w0 e^{−t/2} / 2`. -/
theorem rate_deriv (w0 : ℝ) (s t : ℝ) :
    HasDerivWithinAt (fun u => w0 * ex u) (-(1/2) * (w0 * ex t)) (Icc 0 s) t :=
  (((ex_hasDeriv t).const_mul w0).hasDerivWithinAt).congr_deriv (by ring)

/-- A momentum coordinate `h0 + a w0 (1 − e^{−t/2})` has derivative `(a/2) w0 e^{−t/2}`. -/
theorem mom_deriv (h0 a w0 : ℝ) (s t : ℝ) :
    HasDerivWithinAt (fun u => h0 + a * w0 * (1 - ex u)) (a / 2 * (w0 * ex t)) (Icc 0 s) t :=
  ((((ex_hasDeriv t).const_sub 1).const_mul (a * w0)).const_add h0).hasDerivWithinAt.congr_deriv
    (by ring)

/-- **The right `DETUMBLE` flow exists, domain-staying, from every nonblocking start.** -/
theorem flowR_exists (b : State (Var 6)) (hb : Formula.sat domR b)
    (s : ℝ) (_hs : 0 ≤ s) :
    ∃ ΦR : ℝ → State (Var 6), ΦR 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR 0) (Term.const 1),
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR 0) (Term.const 1)).bound →
        ΦR t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  refine ⟨solR b, ?_, ?_, ?_, fun t ht => solR_stays b hb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero, mul_one]
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero, mul_one]
    by_cases h2 : x = Rv 2
    · subst h2; rw [solR_2, ex_zero, mul_one]
    by_cases h3 : x = Rv 3
    · subst h3; rw [solR_3, ex_zero]; ring
    by_cases h4 : x = Rv 4
    · subst h4; rw [solR_4, ex_zero]; ring
    by_cases h5 : x = Rv 5
    · subst h5; rw [solR_5, ex_zero]; ring
    refine solR_other b 0 (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    fin_cases i
    · have hf : (fun u => solR b u (Rv 0)) = fun u => b (Rv 0) * ex u := by
        funext u; exact solR_0 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 0)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR0_eval, solR_0]
      exact (rate_deriv _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR b u (Rv 1)) = fun u => b (Rv 1) * ex u := by
        funext u; exact solR_1 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 1)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR1_eval, solR_1]
      exact (rate_deriv _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR b u (Rv 2)) = fun u => b (Rv 2) * ex u := by
        funext u; exact solR_2 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 2)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR2_eval, solR_2]
      exact (rate_deriv _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR b u (Rv 3)) = fun u => b (Rv 3) + 2 * b (Rv 0) * (1 - ex u) := by
        funext u; exact solR_3 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 3))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 3)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR3_eval, solR_0]
      exact (mom_deriv _ _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR b u (Rv 4)) = fun u => b (Rv 4) + 4 * b (Rv 1) * (1 - ex u) := by
        funext u; exact solR_4 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 4))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 4)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR4_eval, solR_1]
      exact (mom_deriv _ _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR b u (Rv 5)) = fun u => b (Rv 5) + 5 * b (Rv 2) * (1 - ex u) := by
        funext u; exact solR_5 b u
      show HasDerivWithinAt (fun u => solR b u (Rv 5))
        (Term.eval (Term.binop .mul (Term.const 1) (fR 0 5)) (solR b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR5_eval, solR_2]
      exact (mom_deriv _ _ _ s t).congr_deriv (by ring)
  · intro t _ x hx
    refine solR_other b t (fun i hi => hx ?_)
    rw [hi]; exact rightBlock_bound_mem i


theorem epsR_eq : epsR sat3w_detumble_nominal_IRv2 = 1 := by
  simp [epsR, sat3w_detumble_nominal_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs 6 Side.R (mR q)

/-- The energy `E = 2 w1² + 4 w2² + 5 w3²`. -/
noncomputable def En (x : State (Var 6)) : ℝ :=
  x (Rv 0) * x (Rv 0) * 2 + x (Rv 1) * x (Rv 1) * 4 + x (Rv 2) * x (Rv 2) * 5

theorem sat_guardR0 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 0)) x ↔ En x ≤ 1 := by
  simp [hostGuard, mR, sat3w_detumble_nominal_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem sat_guardR1 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 1)) x ↔ 1 < En x := by
  simp [hostGuard, mR, sat3w_detumble_nominal_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem hp0' : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fR_safe (i : Fin 6) (x : State (Var 6)) : Term.eval (fR 1 i) x = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hp0',
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem memR (q : ℕ) (i : Fin 6) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys := rightBlock_mem' _ _ i

theorem detumble_En {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 0).sys (modeW 0).dom x t Φ) : En (Φ t) ≤ En x := by
  have d0 := H.decay_sq_le (memR 0 0) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR0_eval])
  have d1 := H.decay_sq_le (memR 0 1) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR1_eval])
  have d2 := H.decay_sq_le (memR 0 2) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR2_eval])
  simp only [En]; nlinarith

/-- The three conserved momenta along a `DETUMBLE` run. -/
theorem detumble_hw {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 0).sys (modeW 0).dom x t Φ) :
    (1 * Φ t (Rv 3) + 2 * Φ t (Rv 0) = 1 * x (Rv 3) + 2 * x (Rv 0)) ∧
    (1 * Φ t (Rv 4) + 4 * Φ t (Rv 1) = 1 * x (Rv 4) + 4 * x (Rv 1)) ∧
    (1 * Φ t (Rv 5) + 5 * Φ t (Rv 2) = 1 * x (Rv 5) + 5 * x (Rv 2)) :=
  ⟨H.affine_const (memR 0 3) (memR 0 0) 1 2
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR3_eval, fR0_eval]; ring),
   H.affine_const (memR 0 4) (memR 0 1) 1 4
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR4_eval, fR1_eval]; ring),
   H.affine_const (memR 0 5) (memR 0 2) 1 5
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR5_eval, fR2_eval]; ring)⟩

theorem safe_const {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 1).sys (modeW 1).dom x t Φ) (i : Fin 6) : Φ t (Rv i) = x (Rv i) :=
  H.const (memR 1 i) (fun s _ => by rw [eval_unit_mul, fR_safe])

/-- **The momentum band is invariant** under both modes' flows. -/
theorem sat3w_detumble_nominal_band_invariant : RegionInvariant Gr nbF := by
  intro q m hm x t Φ hx H
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  rw [sat_nbF] at hx ⊢
  simp only [and_assoc] at hx ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx
  interval_cases q
  · obtain ⟨c1, c2, c3⟩ := detumble_hw H
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · simp only [safe_const H]
    exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **Assumption 1 for `sat3w_detumble_nominal`** (Z3-free): the evolve domain carries the
momentum band `|hᵢ + Jᵢ wᵢ| ≤ 2`, a constant of every design-model flow, so the explicit
solution stays in the domain for a full period. -/
theorem sat3w_detumble_nominal_wellFormedR :
    WellFormedR Gr guardR (epsR sat3w_detumble_nominal_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · refine ⟨?_, ?_⟩
    · obtain ⟨Φ, h0, hder, hmask, hdom⟩ := flowR_exists x hd 1 (by norm_num)
      exact ⟨Φ, ⟨by norm_num, h0, hder, hmask, hdom⟩⟩
    · intro t Φ _ H
      have := detumble_En H
      have hgx := (sat_guardR0 x).mp hg
      exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr (by linarith)⟩
  · refine ⟨⟨_, const_sol fR_safe hd (r := 1) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hgx := (sat_guardR1 x).mp hg
    have hE : En (Φ t) = En x := by
      simp only [En, safe_const H 0, safe_const H 1, safe_const H 2]
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR1 _).mpr (by rw [hE]; exact hgx)⟩

/-- The witness: `w3 = 0.4`, `h3 = 2`, every other variable 0. -/
noncomputable def xw : State (Var 6) := fun y =>
  if y = Rv 2 then 2/5 else if y = Rv 5 then 2 else 0

end V2Sat3wDetumbleNominal
end RelCertifier
