/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_weak`: Assumption 1 of the right model (style (a); the momentum band in the right evolve domain)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**The right evolve domain carries the momentum band `|h_i + J_i w_i| ≤ 2`** (the body's
momentum within the wheels' capacity, a constant of every design-model flow; since
2026-10-15). Without it `WellFormedR` would be false: the wheel
momentum `h` is bounded by the evolve domain (`|h| ≤ 2`) but driven by `h' = 5 k w3` in the three
active modes (`NOMINAL`, `ECONOMY`, `SURVIVAL`, `w' = −k w`, `k = 0.5, 0.45, 0.42`), and
`h + 5 w3` is conserved by each of those flows. From `w1 = w2 = 0`, `w3 = 0.4`,
`h = 2` (energy `0.8`: inside `NOMINAL`'s guard `2w1² + 4w2² + 5w3² ≤ 1`, inside the domain)
no `NOMINAL` run of duration 1 exists: it would end at `h = 4 − 2 e^{−1/2} > 2`, outside the domain
(clause (i) fails; the controller blocks). This is the model fact the Theorem 3 instance
already records (its region carries the nonblocking conjunct `nbF`).

**With the band, Assumption 1 holds at every mode** (`sat_detumble_weak_wellFormedR`, Z3-free), and
the band is kept by every mode's flow (`sat_detumble_weak_band_invariant`): the active guard (`E ≤ 1`)
is forward invariant (each rate decays; style (a)); existence is the instance's explicit
solution `flowR_exists`, which stays in the domain because the conserved sums are constant.
`SAFE` (`E > 1`, frozen) holds still.
-/
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.InstancesV2.BenchIR.sat_detumble_weak
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2SatDetumbleWeak

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["w1", "w2", "w3", "h"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := sat_detumble_weak_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 4 → Term (Var 4) := hostDyn vs 4 Side.R (mR q)
noncomputable def domR : Formula (Var 4) := hostEvolve vs 4 Side.R (mR 0)
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm045 : Run.parseRat "-0.45" = some (-(9:ℚ)/20) := by
  have h : parseQ "-0.45" = some (⟨-45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp225 : Run.parseRat "2.25" = some ((9:ℚ)/4) := by
  have h : parseQ "2.25" = some (⟨225, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm042 : Run.parseRat "-0.42" = some (-(21:ℚ)/50) := by
  have h : parseQ "-0.42" = some (⟨-42, 100⟩ : QF) := by decide
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
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
/-- The right profiles' rates: `NOMINAL` 0.5, `ECONOMY` 0.45, `SURVIVAL` 0.42. -/
noncomputable def kR (q : ℕ) : ℝ := if q = 1 then 9/20 else if q = 2 then 21/50 else 1/2

theorem kR_pos (q : ℕ) : 0 < kR q := by
  unfold kR; split_ifs <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 0) x = -(kR q) * x (Rv 0) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> ring
theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 1) x = -(kR q) * x (Rv 1) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> ring
theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 2) x = -(kR q) * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> ring
theorem fR3_eval (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Term.eval (fR q 3) x = 5 * kR q * x (Rv 2) := by
  interval_cases q <;>
  simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp25,
    hpm045, hp225, hpm042, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv, kR] <;> first | ring1 | norm_num

theorem sat_domR (x : State (Var 4)) :
    Formula.sat domR x ↔ (-1 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1 ∧ -1 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 1 ∧
      -1 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 1 ∧ -2 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 2 ∧
      -2 ≤ x (Rv 3) + 5 * x (Rv 2) ∧ x (Rv 3) + 5 * x (Rv 2) ≤ 2) := by
  simp only [domR, hostEvolve, mR, sat_detumble_weak_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hpm10, hp10, hpm20, hp20, hp50, Run.resolveVar, AOp.interp,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    and_assoc]

/-! ## The nonblocking quantity `h_R + 5 w3_R` (conserved by every right profile) -/

noncomputable def hw : Term (Var 4) :=
  Term.binop .add (Term.var (Rv 3)) (Term.binop .mul (Term.const 5) (Term.var (Rv 2)))
theorem eval_hw (x : State (Var 4)) : Term.eval hw x = x (Rv 3) + 5 * x (Rv 2) := by
  simp [hw, Term.eval, AOp.interp]
/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 4) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 4) :=
  { src := s, tgt := t, guard := hostGuard vs 4 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (`NOMINAL` 0, `ECONOMY` 1, `SURVIVAL` 2, `SAFE` 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 0), (1, 3), (2, 2), (2, 0), (2, 3), (3, 3)]

noncomputable def Gr : SearchGraph (Var 4) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 4)} (hm : Gr.modeAt q = some m) :
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

/-- The nonblocking conjunct `−2 ≤ h_R + 5 w3_R ≤ 2` (NOT a tool cut; see the theorem). -/
noncomputable def nbF : Formula (Var 4) :=
  Formula.and (Formula.cmp CompOp.le hw (Term.const 2))
    (Formula.cmp CompOp.le (Term.const (-2)) hw)

theorem sat_nbF (ν : State (Var 4)) :
    Formula.sat nbF ν ↔ (ν (Rv 3) + 5 * ν (Rv 2) ≤ 2 ∧ -2 ≤ ν (Rv 3) + 5 * ν (Rv 2)) := by
  simp [nbF, Formula.sat, CompOp.interp, eval_hw, Term.eval]

/-! ## Existence: each right profile's flow, explicitly, from a nonblocking start

`w_i(t) = w_i0 e^{−k t}`, `h(t) = h0 + 5 w3_0 (1 − e^{−k t})`: the rates contract toward 0
and `h(t)` is a convex combination of `h0` and the conserved `h0 + 5 w3_0`. -/

noncomputable def ex (k t : ℝ) : ℝ := Real.exp (-k * t)

noncomputable def solR (k : ℝ) (b : State (Var 4)) (t : ℝ) : State (Var 4) := fun x =>
  if x = Rv 0 then b (Rv 0) * ex k t
  else if x = Rv 1 then b (Rv 1) * ex k t
  else if x = Rv 2 then b (Rv 2) * ex k t
  else if x = Rv 3 then b (Rv 3) + 5 * b (Rv 2) * (1 - ex k t)
  else b x

theorem solR_0 (k : ℝ) (b : State (Var 4)) (t : ℝ) : solR k b t (Rv 0) = b (Rv 0) * ex k t := by
  simp [solR]
theorem solR_1 (k : ℝ) (b : State (Var 4)) (t : ℝ) : solR k b t (Rv 1) = b (Rv 1) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_2 (k : ℝ) (b : State (Var 4)) (t : ℝ) : solR k b t (Rv 2) = b (Rv 2) * ex k t := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_3 (k : ℝ) (b : State (Var 4)) (t : ℝ) :
    solR k b t (Rv 3) = b (Rv 3) + 5 * b (Rv 2) * (1 - ex k t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (k : ℝ) (b : State (Var 4)) (t : ℝ) {x : Var 4} (hx : ∀ i, x ≠ Rv i) :
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

theorem solR_stays {k : ℝ} (hk : 0 ≤ k) (b : State (Var 4)) (hb : Formula.sat domR b)
    {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR k b t) := by
  rw [sat_domR] at hb ⊢
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u, h3l, h3u, hc1l, hc1u⟩ := hb
  have he0 := ex_pos k t
  have he1 := ex_le_one hk ht
  rw [solR_0, solR_1, solR_2, solR_3]
  have e1 : b (Rv 3) + 5 * b (Rv 2) * (1 - ex k t) + 5 * (b (Rv 2) * ex k t) = b (Rv 3) + 5 * b (Rv 2) := by
    ring
  rw [e1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem rightBlock_bound_mem (q : ℕ) (i : Fin 4) :
    Rv i ∈ (rightBlock (fR q) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- **Each right profile's flow exists, domain-staying, from every nonblocking start.** -/
theorem flowR_exists (q : ℕ) (hq : q < 3) (b : State (Var 4)) (hb : Formula.sat domR b)
    (s : ℝ) (_hs : 0 ≤ s) :
    ∃ ΦR : ℝ → State (Var 4), ΦR 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const 1),
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const 1)).bound →
        ΦR t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  set k := kR q with hk
  have hk0 : 0 ≤ k := (kR_pos q).le
  refine ⟨solR k b, ?_, ?_, ?_, fun t ht => solR_stays hk0 b hb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero, mul_one]
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero, mul_one]
    by_cases h2 : x = Rv 2
    · subst h2; rw [solR_2, ex_zero, mul_one]
    by_cases h3 : x = Rv 3
    · subst h3; rw [solR_3, ex_zero]; ring
    refine solR_other k b 0 (fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hd := ex_hasDeriv k t
    fin_cases i
    · have h := ((hd.const_mul (b (Rv 0))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR k b u (Rv 0)) = fun u => b (Rv 0) * ex k u := by
        funext u; exact solR_0 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR0_eval q hq, solR_0, ← hk]
      exact h.congr_deriv (by ring)
    · have h := ((hd.const_mul (b (Rv 1))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR k b u (Rv 1)) = fun u => b (Rv 1) * ex k u := by
        funext u; exact solR_1 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 1)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR1_eval q hq, solR_1, ← hk]
      exact h.congr_deriv (by ring)
    · have h := ((hd.const_mul (b (Rv 2))).hasDerivWithinAt (s := Icc 0 s))
      have hf : (fun u => solR k b u (Rv 2)) = fun u => b (Rv 2) * ex k u := by
        funext u; exact solR_2 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR2_eval q hq, solR_2, ← hk]
      exact h.congr_deriv (by ring)
    · have h := (((hd.const_sub 1).const_mul (5 * b (Rv 2))).const_add
        (b (Rv 3))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR k b u (Rv 3)) =
          fun u => b (Rv 3) + 5 * b (Rv 2) * (1 - ex k u) := by
        funext u; exact solR_3 k b u
      show HasDerivWithinAt (fun u => solR k b u (Rv 3))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 3)) (solR k b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp, fR3_eval q hq, solR_2, ← hk]
      exact h.congr_deriv (by ring)
  · intro t _ x hx
    refine solR_other k b t (fun i hi => hx ?_)
    rw [hi]; exact rightBlock_bound_mem q i


theorem epsR_eq : epsR sat_detumble_weak_IRv2 = 1 := by
  simp [epsR, sat_detumble_weak_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 4) := hostGuard vs 4 Side.R (mR q)

/-- The energy `E = 2 w1² + 4 w2² + 5 w3²`. -/
noncomputable def En (x : State (Var 4)) : ℝ :=
  x (Rv 0) * x (Rv 0) * 2 + x (Rv 1) * x (Rv 1) * 4 + x (Rv 2) * x (Rv 2) * 5

theorem sat_guardR0 (q : ℕ) (hq : q < 3) (x : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR q)) x ↔ En x ≤ 1 := by
  interval_cases q <;>
  simp [hostGuard, mR, sat_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem sat_guardR1 (x : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR 3)) x ↔ 1 < En x := by
  simp [hostGuard, mR, sat_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fR_safe (i : Fin 4) (x : State (Var 4)) : Term.eval (fR 3 i) x = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mR, sat_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem memR (q : ℕ) (i : Fin 4) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys := rightBlock_mem' _ _ i

/-- Along any active-mode run the energy does not grow. -/
theorem detumble_En (q : ℕ) (hq : q < 3) {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW q).sys (modeW q).dom x t Φ) : En (Φ t) ≤ En x := by
  have hk := (kR_pos q).le
  have d0 := H.decay_sq_le (memR q 0) (kR q) hk
    (fun s _ => by rw [eval_unit_mul, fR0_eval q hq])
  have d1 := H.decay_sq_le (memR q 1) (kR q) hk
    (fun s _ => by rw [eval_unit_mul, fR1_eval q hq])
  have d2 := H.decay_sq_le (memR q 2) (kR q) hk
    (fun s _ => by rw [eval_unit_mul, fR2_eval q hq])
  simp only [En]; nlinarith

/-- `h + 5 w3` is conserved along an active-mode run. -/
theorem detumble_hw (q : ℕ) (hq : q < 3) {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    1 * Φ t (Rv 3) + 5 * Φ t (Rv 2) = 1 * x (Rv 3) + 5 * x (Rv 2) :=
  H.affine_const (memR q 3) (memR q 2) 1 5
    (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR3_eval q hq, fR2_eval q hq]; ring)

theorem safe_const {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW 3).sys (modeW 3).dom x t Φ) (i : Fin 4) : Φ t (Rv i) = x (Rv i) :=
  H.const (memR 3 i) (fun s _ => by rw [eval_unit_mul, fR_safe])

/-- **The momentum band is invariant** under both modes' flows. -/
theorem sat_detumble_weak_band_invariant : RegionInvariant Gr nbF := by
  intro q m hm x t Φ hx H
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  rw [sat_nbF] at hx ⊢
  by_cases h3 : q < 3
  · have := detumble_hw q h3 H; constructor <;> linarith [hx.1, hx.2]
  · obtain rfl : q = 3 := by omega
    rw [safe_const H 3, safe_const H 2]; exact hx

/-- **Assumption 1 for `sat_detumble_weak` on the momentum band** (Z3-free). -/
theorem sat_detumble_weak_wellFormedR :
    WellFormedR Gr guardR (epsR sat_detumble_weak_IRv2) := by
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

end V2SatDetumbleWeak
end RelCertifier
