/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_weak`: Assumption 1 of the right model (style (a); the momentum band in the right evolve domain)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**The right evolve domain carries the momentum band `|h_i + J_i w_i| ≤ 2`** (the body's
momentum within the wheels' capacity, a constant of every design-model flow; since
2026-10-15). Without it `WellFormedR` would be false: the three
wheel momenta are bounded by the evolve domain (`|hᵢ| ≤ 2`) but driven by the three active
modes (`NOMINAL`, `ECONOMY`, `SURVIVAL`: `w' = −k w`, `h₁' = 2k w₁`, `h₂' = 4k w₂`,
`h₃' = 5k w₃`, `k = 0.5, 0.45, 0.42`), each of which conserves `h₁ + 2w₁`, `h₂ + 4w₂`,
`h₃ + 5w₃`. From `w₃ = 0.4`, `h₃ = 2`, the rest 0 (energy `0.8`, inside the
guard and the domain) no run of duration 1 exists: it would end at `h₃ = 4 − 2 e^{−1/2} > 2`
(clause (i) fails).

**With the band, Assumption 1 holds at every mode** (`sat3w_detumble_weak_wellFormedR`, Z3-free), and
the band is kept by every mode's flow (`sat3w_detumble_weak_band_invariant`): the active guard (`E ≤ 1`)
is forward invariant (each rate decays; style (a)); existence is the instance's explicit
solution `flowR_exists`, which stays in the domain because the conserved sums are constant.
`SAFE` (`E > 1`, frozen) holds still.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_weak
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Sat3wDetumbleWeak

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["w1", "w2", "w3", "h1", "h2", "h3"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := sat3w_detumble_weak_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.R (mR q)
noncomputable def domR : Formula (Var 6) := hostEvolve vs 6 Side.R (mR 0)
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm045 : Run.parseRat "-0.45" = some (-(9:ℚ)/20) := by
  have h : parseQ "-0.45" = some (⟨-45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp09 : Run.parseRat "0.9" = some ((9:ℚ)/10) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp18 : Run.parseRat "1.8" = some ((9:ℚ)/5) := by
  have h : parseQ "1.8" = some (⟨18, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp225 : Run.parseRat "2.25" = some ((9:ℚ)/4) := by
  have h : parseQ "2.25" = some (⟨225, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm042 : Run.parseRat "-0.42" = some (-(21:ℚ)/50) := by
  have h : parseQ "-0.42" = some (⟨-42, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp084 : Run.parseRat "0.84" = some ((21:ℚ)/25) := by
  have h : parseQ "0.84" = some (⟨84, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp168 : Run.parseRat "1.68" = some ((42:ℚ)/25) := by
  have h : parseQ "1.68" = some (⟨168, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp21 : Run.parseRat "2.1" = some ((21:ℚ)/10) := by
  have h : parseQ "2.1" = some (⟨21, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
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

/-- The right profiles' gains: `NOMINAL` 0.5, `ECONOMY` 0.45, `SURVIVAL` 0.42. -/
noncomputable def kR (q : ℕ) : ℝ := if q = 0 then 1/2 else if q = 1 then 9/20 else 21/50

theorem kR_nonneg (q : ℕ) : 0 ≤ kR q := by
  unfold kR; split_ifs <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 0) x = -(kR q) * x (Rv 0) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 1) x = -(kR q) * x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 2) x = -(kR q) * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR3_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 3) x = 2 * kR q * x (Rv 0) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR4_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 4) x = 4 * kR q * x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring
theorem fR5_eval (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Term.eval (fR q 5) x = 5 * kR q * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05,
    hp10, hp20, hp25, hpm045, hp09, hp18, hp225, hpm042, hp084, hp168, hp21, Run.resolveVar,
    List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR,
    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

theorem sat_domR (x : State (Var 6)) :
    Formula.sat domR x ↔ (-1 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1 ∧ -1 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 1 ∧
      -1 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 1 ∧ -2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 2 ∧
      -2 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 2 ∧ -2 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 2 ∧
      -2 ≤ x (Rv 3) + 2 * x (Rv 0) ∧ x (Rv 3) + 2 * x (Rv 0) ≤ 2 ∧
      -2 ≤ x (Rv 4) + 4 * x (Rv 1) ∧ x (Rv 4) + 4 * x (Rv 1) ≤ 2 ∧
      -2 ≤ x (Rv 5) + 5 * x (Rv 2) ∧ x (Rv 5) + 5 * x (Rv 2) ≤ 2) := by
  simp only [domR, hostEvolve, mR, sat3w_detumble_weak_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm10, hp10, hpm20, hp20, hp40, hp50, Run.resolveVar, AOp.interp,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]

/-! ## The nonblocking quantities `c_i = h_i + J_i w_i` (conserved by every right profile) -/

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

/-- The declared transitions, as indices (`NOMINAL` 0, `ECONOMY` 1, `SURVIVAL` 2, `SAFE` 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 0), (1, 3), (2, 2), (2, 0), (2, 3), (3, 3)]

noncomputable def Gr : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 6)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

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

/-! ## Existence: each right profile's flow, explicitly, from a nonblocking start

At gain `k`: `w_i(t) = w_i0 e^{−kt}`, `h_i(t) = h_i0 + J_i w_i0 (1 − e^{−kt})`
(`J = (2, 4, 5)`): the rates contract toward 0 (inside `[−1, 1]`), and
`h_i(t) = e^{−kt} h_i0 + (1 − e^{−kt}) (h_i0 + J_i w_i0)` is a convex combination of `h_i0`
and the conserved `c_i = h_i0 + J_i w_i0` — inside `[−2, 2]` exactly when the nonblocking
conjunct holds. -/

noncomputable def ex (k t : ℝ) : ℝ := Real.exp (-k * t)

noncomputable def solR (k : ℝ) (b : State (Var 6)) (t : ℝ) : State (Var 6) := fun x =>
  if x = Rv 0 then b (Rv 0) * ex k t
  else if x = Rv 1 then b (Rv 1) * ex k t
  else if x = Rv 2 then b (Rv 2) * ex k t
  else if x = Rv 3 then b (Rv 3) + 2 * b (Rv 0) * (1 - ex k t)
  else if x = Rv 4 then b (Rv 4) + 4 * b (Rv 1) * (1 - ex k t)
  else if x = Rv 5 then b (Rv 5) + 5 * b (Rv 2) * (1 - ex k t)
  else b x

theorem solR_0 (k : ℝ) (b : State (Var 6)) (t : ℝ) : solR k b t (Rv 0) = b (Rv 0) * ex k t := by
  simp [solR]
theorem solR_1 (k : ℝ) (b : State (Var 6)) (t : ℝ) : solR k b t (Rv 1) = b (Rv 1) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_2 (k : ℝ) (b : State (Var 6)) (t : ℝ) : solR k b t (Rv 2) = b (Rv 2) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_3 (k : ℝ) (b : State (Var 6)) (t : ℝ) :
    solR k b t (Rv 3) = b (Rv 3) + 2 * b (Rv 0) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_4 (k : ℝ) (b : State (Var 6)) (t : ℝ) :
    solR k b t (Rv 4) = b (Rv 4) + 4 * b (Rv 1) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_5 (k : ℝ) (b : State (Var 6)) (t : ℝ) :
    solR k b t (Rv 5) = b (Rv 5) + 5 * b (Rv 2) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (k : ℝ) (b : State (Var 6)) (t : ℝ) {x : Var 6} (hx : ∀ i, x ≠ Rv i) :
    solR k b t x = b x := by
  simp [solR, hx]

theorem ex_hasDeriv (k t : ℝ) : HasDerivAt (ex k) (-k * ex k t) t := by
  have h := ((hasDerivAt_id t).const_mul (-k)).exp
  have h' : HasDerivAt (ex k) (Real.exp (-k * id t) * (-k * 1)) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring

theorem ex_zero (k : ℝ) : ex k 0 = 1 := by simp [ex]
theorem ex_pos (k t : ℝ) : 0 < ex k t := Real.exp_pos _
theorem ex_le_one {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) : ex k t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; nlinarith

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

theorem solR_stays {k : ℝ} (hk : 0 ≤ k) (b : State (Var 6)) (hb : Formula.sat domR b)
    {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR k b t) := by
  rw [sat_domR] at hb ⊢
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u,
    hc1l, hc1u, hc2l, hc2u, hc3l, hc3u⟩ := hb
  have he0 := ex_pos k t
  have he1 := ex_le_one hk ht
  rw [solR_0, solR_1, solR_2, solR_3, solR_4, solR_5]
  obtain ⟨a0, b0⟩ := rate_band he0 he1 h0l h0u
  obtain ⟨a1, b1⟩ := rate_band he0 he1 h1l h1u
  obtain ⟨a2, b2⟩ := rate_band he0 he1 h2l h2u
  obtain ⟨a3, b3⟩ := mom_band he0 he1 h3l h3u hc1u hc1l
  obtain ⟨a4, b4⟩ := mom_band he0 he1 h4l h4u hc2u hc2l
  obtain ⟨a5, b5⟩ := mom_band he0 he1 h5l h5u hc3u hc3l
  have e1 : b (Rv 3) + 2 * b (Rv 0) * (1 - ex k t) + 2 * (b (Rv 0) * ex k t) = b (Rv 3) + 2 * b (Rv 0) := by
    ring
  have e2 : b (Rv 4) + 4 * b (Rv 1) * (1 - ex k t) + 4 * (b (Rv 1) * ex k t) = b (Rv 4) + 4 * b (Rv 1) := by
    ring
  have e3 : b (Rv 5) + 5 * b (Rv 2) * (1 - ex k t) + 5 * (b (Rv 2) * ex k t) = b (Rv 5) + 5 * b (Rv 2) := by
    ring
  rw [e1, e2, e3]
  exact ⟨a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, hc1l, hc1u, hc2l, hc2u, hc3l, hc3u⟩

theorem rightBlock_bound_mem (q : ℕ) (i : Fin 6) :
    Rv i ∈ (rightBlock (fR q) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- A rate coordinate `w0 e^{−kt}` has derivative `−k w0 e^{−kt}`. -/
theorem rate_deriv (k w0 : ℝ) (s t : ℝ) :
    HasDerivWithinAt (fun u => w0 * ex k u) (-k * (w0 * ex k t)) (Icc 0 s) t :=
  (((ex_hasDeriv k t).const_mul w0).hasDerivWithinAt).congr_deriv (by ring)

/-- A momentum coordinate `h0 + a w0 (1 − e^{−kt})` has derivative `a k w0 e^{−kt}`. -/
theorem mom_deriv (k h0 a w0 : ℝ) (s t : ℝ) :
    HasDerivWithinAt (fun u => h0 + a * w0 * (1 - ex k u)) (a * k * (w0 * ex k t)) (Icc 0 s) t :=
  ((((ex_hasDeriv k t).const_sub 1).const_mul (a * w0)).const_add h0).hasDerivWithinAt.congr_deriv
    (by ring)

/-- **Each right profile's flow exists, domain-staying, from every nonblocking start.** -/
theorem flowR_exists (q : ℕ) (hq : q < 3) (b : State (Var 6)) (hb : Formula.sat domR b)
    (s : ℝ) (_hs : 0 ≤ s) :
    ∃ ΦR : ℝ → State (Var 6), ΦR 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const 1),
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const 1)).bound →
        ΦR t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  refine ⟨solR (kR q) b, ?_, ?_, ?_, fun t ht => solR_stays (kR_nonneg q) b hb ht.1⟩
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
    refine solR_other _ b 0 (fun i => ?_)
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
    · have hf : (fun u => solR (kR q) b u (Rv 0)) = fun u => b (Rv 0) * ex (kR q) u := by
        funext u; exact solR_0 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR0_eval q hq, solR_0]
      exact (rate_deriv _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 1)) = fun u => b (Rv 1) * ex (kR q) u := by
        funext u; exact solR_1 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 1)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR1_eval q hq, solR_1]
      exact (rate_deriv _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 2)) = fun u => b (Rv 2) * ex (kR q) u := by
        funext u; exact solR_2 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR2_eval q hq, solR_2]
      exact (rate_deriv _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 3))
          = fun u => b (Rv 3) + 2 * b (Rv 0) * (1 - ex (kR q) u) := by
        funext u; exact solR_3 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 3))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 3)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR3_eval q hq, solR_0]
      exact (mom_deriv _ _ _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 4))
          = fun u => b (Rv 4) + 4 * b (Rv 1) * (1 - ex (kR q) u) := by
        funext u; exact solR_4 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 4))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 4)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR4_eval q hq, solR_1]
      exact (mom_deriv _ _ _ _ s t).congr_deriv (by ring)
    · have hf : (fun u => solR (kR q) b u (Rv 5))
          = fun u => b (Rv 5) + 5 * b (Rv 2) * (1 - ex (kR q) u) := by
        funext u; exact solR_5 _ b u
      show HasDerivWithinAt (fun u => solR (kR q) b u (Rv 5))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 5)) (solR (kR q) b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR5_eval q hq, solR_2]
      exact (mom_deriv _ _ _ _ s t).congr_deriv (by ring)
  · intro t _ x hx
    refine solR_other _ b t (fun i hi => hx ?_)
    rw [hi]; exact rightBlock_bound_mem q i


theorem epsR_eq : epsR sat3w_detumble_weak_IRv2 = 1 := by
  simp [epsR, sat3w_detumble_weak_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs 6 Side.R (mR q)

/-- The energy `E = 2 w1² + 4 w2² + 5 w3²`. -/
noncomputable def En (x : State (Var 6)) : ℝ :=
  x (Rv 0) * x (Rv 0) * 2 + x (Rv 1) * x (Rv 1) * 4 + x (Rv 2) * x (Rv 2) * 5

theorem sat_guardR0 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR q)) x ↔ En x ≤ 1 := by
  interval_cases q <;>
  simp [hostGuard, mR, sat3w_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem sat_guardR1 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 3)) x ↔ 1 < En x := by
  simp [hostGuard, mR, sat3w_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem hp0' : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fR_safe (i : Fin 6) (x : State (Var 6)) : Term.eval (fR 3 i) x = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hp0',
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem memR (q : ℕ) (i : Fin 6) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys := rightBlock_mem' _ _ i

theorem detumble_En (q : ℕ) (hq : q < 3) {x : State (Var 6)} {t : ℝ}
    {Φ : ℝ → State (Var 6)} (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    En (Φ t) ≤ En x := by
  have hk := kR_nonneg q
  have d0 := H.decay_sq_le (memR q 0) (kR q) hk (fun s _ => by rw [eval_unit_mul, fR0_eval q hq])
  have d1 := H.decay_sq_le (memR q 1) (kR q) hk (fun s _ => by rw [eval_unit_mul, fR1_eval q hq])
  have d2 := H.decay_sq_le (memR q 2) (kR q) hk (fun s _ => by rw [eval_unit_mul, fR2_eval q hq])
  simp only [En]; nlinarith

/-- The three conserved momenta along an active-mode run. -/
theorem detumble_hw (q : ℕ) (hq : q < 3) {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    (1 * Φ t (Rv 3) + 2 * Φ t (Rv 0) = 1 * x (Rv 3) + 2 * x (Rv 0)) ∧
    (1 * Φ t (Rv 4) + 4 * Φ t (Rv 1) = 1 * x (Rv 4) + 4 * x (Rv 1)) ∧
    (1 * Φ t (Rv 5) + 5 * Φ t (Rv 2) = 1 * x (Rv 5) + 5 * x (Rv 2)) :=
  ⟨H.affine_const (memR q 3) (memR q 0) 1 2
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR3_eval q hq, fR0_eval q hq]; ring),
   H.affine_const (memR q 4) (memR q 1) 1 4
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR4_eval q hq, fR1_eval q hq]; ring),
   H.affine_const (memR q 5) (memR q 2) 1 5
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR5_eval q hq, fR2_eval q hq]; ring)⟩

theorem safe_const {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 3).sys (modeW 3).dom x t Φ) (i : Fin 6) : Φ t (Rv i) = x (Rv i) :=
  H.const (memR 3 i) (fun s _ => by rw [eval_unit_mul, fR_safe])

/-- **The momentum band is invariant** under both modes' flows. -/
theorem sat3w_detumble_weak_band_invariant : RegionInvariant Gr nbF := by
  intro q m hm x t Φ hx H
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  rw [sat_nbF] at hx ⊢
  simp only [and_assoc] at hx ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx
  by_cases h3 : q < 3
  · obtain ⟨c1, c2, c3⟩ := detumble_hw q h3 H
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · obtain rfl : q = 3 := by omega
    simp only [safe_const H]
    exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **Assumption 1 for `sat3w_detumble_weak` on the momentum band** (Z3-free). -/
theorem sat3w_detumble_weak_wellFormedR :
    WellFormedR Gr guardR (epsR sat3w_detumble_weak_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  by_cases h3 : q < 3
  · refine ⟨?_, ?_⟩
    · obtain ⟨Φ, h0, hder, hmask, hdom⟩ := flowR_exists q h3 x hd 1 (by norm_num)
      exact ⟨Φ, ⟨by norm_num, h0, hder, hmask, hdom⟩⟩
    · intro t Φ _ H
      have := detumble_En q h3 H
      have hgx := (sat_guardR0 q h3 x).mp hg
      exact ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide),
        (sat_guardR0 q h3 _).mpr (by linarith)⟩
  · obtain rfl : q = 3 := by omega
    refine ⟨⟨_, const_sol fR_safe hd (r := 1) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hgx := (sat_guardR1 x).mp hg
    have hE : En (Φ t) = En x := by
      simp only [En, safe_const H 0, safe_const H 1, safe_const H 2]
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR1 _).mpr (by rw [hE]; exact hgx)⟩

end V2Sat3wDetumbleWeak
end RelCertifier
