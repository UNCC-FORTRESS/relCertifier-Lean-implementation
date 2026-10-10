/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_profiles` — Theorem 3 over the GUARDED right automaton is FALSE (windows `dt ≥ 1`)

`V2Platoon3Profiles.platoon3_profiles_modal` proves Theorem 3 over the `⊤`-guarded right
graph `Gr` at the cut region. This file states the strengthened statement — the right
automaton GUARDED (every edge tests the lowered guard of the profile it enters, `GrG`), the
loop invariant carrying the mode-consistent region `gregion q = guard q ∧ region q` — and
proves it false for every window length `dt ≥ 1`: no legal witness exists.

**Why.** The three profiles share one closed loop per link, so the difference of links 1
and 2 on the reference, `x = g₁ − g₂`, `y = r₁ − r₂`, obeys `x' = y`, `y' = −x/8 − 3y/4` in
EVERY profile (the set point cancels). Its decoupling forms `P = y + x/2`, `W = y + x/4`
decay as `e^{−t/4}`, `e^{−t/2}` whichever profile runs, so `9 W − P²` and the sign of `P`
are invariants of every profile flow (`flow_J`), and the AEB sinks are excluded by their
empty region. Every profile guard bounds `x ≤ 8` (`|g_k − c| ≤ 4`), which on the invariant
curve `9 W = P²` from `P = 6` leaves only `P = 6` (`W = 4`) or `P ≤ 3` (`W ≤ 1`).

The witness: the reference in `NORMAL` at links `(34, 1)`, `(26, −1)`, `(30, 0)` (`P = 6`,
`W = 4`), the deployed at `(33, 1)`, `(25, −1)`, `(29, 0)` (every row at its center, the
left guard holds). The deployed's `FOLLOW` window of length 1 ends with
`W_L = 4 e^{−1/2} ∈ (2, 3)`. The rows on the `ρ = 1/4` forms of links 1 and 2 give
`|W_R − W_L| ≤ 1`, so `W_R ∈ (1, 4)`: no reachable reference state in a profile's guard
satisfies them.
-/
import RelCertifier.InstancesV2.Modal.Platoon3Profiles
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Instances.GuardedPins

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Platoon3ProfilesRefuted

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2Platoon3Profiles GPins

/-! ## The guarded right automaton and the mode-consistent region -/

noncomputable def edgeG (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := hostGuard vs 6 Side.R (mR t), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4, modeW 5]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_len : GrG.modes.length = 6 := rfl

/-- The mode-consistent region: the right mode's lowered guard and its kept cut atoms. -/
noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vs 6 Side.R (mR q)) region q

/-! ## One step of the guarded right automaton -/

theorem step_cases {σ μ : State (Var 6)} (h : Program.sem (rightAutomatonBody GrG mv) σ μ) :
    ∃ q : ℕ, q < 6 ∧ σ mv = (q : ℝ) ∧
      ∃ κ, Program.sem (Program.ode (modeW q).sys (modeW q).dom) σ κ ∧
      ∃ t : ℕ, (q, t) ∈ edgeList ∧ μ = Function.update κ mv (t : ℝ) := by
  obtain ⟨p, hp, hsem⟩ := bigChoiceP_sem_forward h
  simp only [List.mem_filterMap, List.mem_range] at hp
  obtain ⟨q, hq, hqm⟩ := hp
  have hq6 : q < 6 := by simpa [GrG] using hq
  have hmq : GrG.modeAt q = some (modeW q) := by interval_cases q <;> rfl
  rw [hmq] at hqm
  simp only [Option.map_some, Option.some.injEq] at hqm
  subst hqm
  obtain ⟨σ1, ⟨rfl, htest⟩, κ, hflow, hedge⟩ := hsem
  have hmv : σ mv = (q : ℝ) := by
    simpa [modeIs, Formula.sat, CompOp.interp, Term.eval] using htest
  refine ⟨q, hq6, hmv, κ, hflow, ?_⟩
  obtain ⟨p2, hp2, hsem2⟩ := bigChoiceP_sem_forward hedge
  simp only [List.mem_map] at hp2
  obtain ⟨e, he, rfl⟩ := hp2
  obtain ⟨κ1, ⟨hκ1, -⟩, hasg⟩ := hsem2
  subst hκ1
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  have hsrc : e.src = q := by simpa using (List.mem_filter.mp he).2
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨⟨s, t⟩, hst, rfl⟩ := hmem
  simp only [edgeG] at hsrc
  subst hsrc
  refine ⟨t, hst, ?_⟩
  rw [sem_assign] at hasg
  funext y
  by_cases hy : y = mv
  · subst hy; rw [Function.update_self, hasg.1]; simp [Term.eval, edgeG]
  · rw [Function.update_of_ne hy, hasg.2 y hy]

/-! ## The link-difference invariant of every profile flow -/

/-- `P = (r₁ − r₂) + (g₁ − g₂)/2` and `W = (r₁ − r₂) + (g₁ − g₂)/4` on the reference. -/
noncomputable def PR (x : State (Var 6)) : ℝ :=
  (x (Rv 1) - x (Rv 3)) + 1/2 * (x (Rv 0) - x (Rv 2))
noncomputable def WR (x : State (Var 6)) : ℝ :=
  (x (Rv 1) - x (Rv 3)) + 1/4 * (x (Rv 0) - x (Rv 2))

/-- The invariant curve: `9 W = P²`, `0 < P ≤ 6`. -/
def J (x : State (Var 6)) : Prop := 9 * WR x = PR x * PR x ∧ 0 < PR x ∧ PR x ≤ 6

theorem const_of_deriv0 {f : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt f 0 (Icc 0 r) t) : f r = f 0 := by
  have hcont : ContinuousOn f (Icc 0 r) := fun t ht => (hf t ht).continuousWithinAt
  have hmono : MonotoneOn f (Icc 0 r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun _ => 0) (convex_Icc 0 r) hcont
      (fun t ht => (hf t (interior_subset ht)).mono interior_subset) (fun _ _ => le_rfl)
  have hanti : AntitoneOn f (Icc 0 r) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun _ => 0) (convex_Icc 0 r) hcont
      (fun t ht => (hf t (interior_subset ht)).mono interior_subset) (fun _ _ => le_rfl)
  exact le_antisymm (hanti ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩ hr) (hmono ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩ hr)

/-- **Every profile flow keeps the invariant curve.** -/
theorem flow_J (q : ℕ) (hq : q < 3) {σ κ : State (Var 6)}
    (h : Program.sem (Program.ode (modeW q).sys (modeW q).dom) σ κ) (hJ : J σ) : J κ := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, -, -⟩ := h
  have hd : ∀ (i : Fin 6), ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt (fun u => Φ u (Rv i))
      (Term.eval (fR q i) (Φ t)) (Icc 0 r) t := by
    intro i t ht
    have := hder t ht (Rv i, Term.binop .mul (Term.const 1) (fR q i))
      (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    simpa [Term.eval, AOp.interp] using this
  have hF := fR_field q hq
  have hP : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt (fun u => PR (Φ u)) (-(1/4) * PR (Φ t))
      (Icc 0 r) t := by
    intro t ht
    obtain ⟨f0, f1, f2, f3, -, -⟩ := hF (Φ t)
    have h := ((hd 1 t ht).sub (hd 3 t ht)).add (((hd 0 t ht).sub (hd 2 t ht)).const_mul (1/2))
    rw [f0, f1, f2, f3] at h
    refine h.congr_deriv ?_
    simp only [PR]; ring
  have hW : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt (fun u => WR (Φ u)) (-(1/2) * WR (Φ t))
      (Icc 0 r) t := by
    intro t ht
    obtain ⟨f0, f1, f2, f3, -, -⟩ := hF (Φ t)
    have h := ((hd 1 t ht).sub (hd 3 t ht)).add (((hd 0 t ht).sub (hd 2 t ht)).const_mul (1/4))
    rw [f0, f1, f2, f3] at h
    refine h.congr_deriv ?_
    simp only [WR]; ring
  have hE : ∀ (k : ℝ) (t : ℝ), HasDerivWithinAt (fun u => Real.exp (k * u))
      (Real.exp (k * t) * k) (Icc 0 r) t := by
    intro k t
    have := ((hasDerivAt_id t).const_mul k).exp
    simpa using this.hasDerivWithinAt
  -- `P e^{t/4}` and `(9 W − P²) e^{t/2}` are constant
  have hc1 := const_of_deriv0 (f := fun u => PR (Φ u) * Real.exp (1/4 * u)) hr (by
    intro t ht
    exact ((hP t ht).mul (hE (1/4) t)).congr_deriv (by ring))
  have hc2 := const_of_deriv0
    (f := fun u => (9 * WR (Φ u) - PR (Φ u) * PR (Φ u)) * Real.exp (1/2 * u)) hr (by
    intro t ht
    have h := ((((hW t ht).const_mul 9).sub ((hP t ht).mul (hP t ht))).mul (hE (1/2) t))
    exact h.congr_deriv (by simp only [Pi.sub_apply, Pi.mul_apply]; ring))
  simp only [mul_zero, Real.exp_zero, mul_one, hΦ0, hΦr] at hc1 hc2
  obtain ⟨h9, hp0, hp6⟩ := hJ
  have he1 := Real.exp_pos (1/4 * r)
  have he2 := Real.exp_pos (1/2 * r)
  have he1ge : 1 ≤ Real.exp (1/4 * r) := Real.one_le_exp (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have : 9 * WR κ - PR κ * PR κ = 0 := by
      rcases mul_eq_zero.mp (show (9 * WR κ - PR κ * PR κ) * Real.exp (1/2 * r) = 0 by
        rw [hc2]; linarith) with h | h
      · exact h
      · exact absurd h he2.ne'
    linarith
  · by_contra hneg
    push Not at hneg
    nlinarith
  · nlinarith

/-- **Along any run of the guarded right automaton**, a state in a profile lies on the curve. -/
theorem star_J {σ μ : State (Var 6)}
    (h : Relation.ReflTransGen (Program.sem (rightAutomatonBody GrG mv)) σ μ)
    (hσ : (σ mv = 0 ∨ σ mv = 1 ∨ σ mv = 2) → J σ) :
    (μ mv = 0 ∨ μ mv = 1 ∨ μ mv = 2) → J μ := by
  induction h with
  | refl => exact hσ
  | @tail b c _ hstep ih =>
      intro hc
      obtain ⟨q, hq6, hbq, κ, hflow, t, hqt, rfl⟩ := step_cases hstep
      have hct : (t : ℝ) = 0 ∨ (t : ℝ) = 1 ∨ (t : ℝ) = 2 := by
        simpa [Function.update_self] using hc
      have hJR : ∀ x y : State (Var 6), (∀ i, x (Rv i) = y (Rv i)) → J x → J y := by
        intro x y hxy hx
        simp only [J, PR, WR, ← hxy]; exact hx
      -- an edge into a profile leaves a profile
      have ht3 : t < 3 := by
        rcases hct with h | h | h <;> (norm_cast at h; omega)
      have hq3 : q < 3 := by
        simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hqt
        omega
      have hJb : J b := ih (by
        interval_cases q
        · left; simpa using hbq
        · right; left; simpa using hbq
        · right; right; simpa using hbq)
      refine hJR κ _ (fun i => ?_) (flow_J q hq3 hflow hJb)
      rw [Function.update_of_ne (by simp [Rv, Prod.ext_iff])]

/-! ## The rows, evaluated -/

theorem comps_eval (x : State (Var 6)) : comps.map (fun c => Term.eval c x) =
    [x (Lv 1) - x (Rv 1) + 4⁻¹ * (x (Lv 0) - x (Rv 0) + 1) - 2⁻¹,
      -2⁻¹ - (x (Lv 1) - x (Rv 1) + 4⁻¹ * (x (Lv 0) - x (Rv 0) + 1)),
      x (Lv 1) - x (Rv 1) + 2⁻¹ * (x (Lv 0) - x (Rv 0) + 1) - 1,
      -1 - (x (Lv 1) - x (Rv 1) + 2⁻¹ * (x (Lv 0) - x (Rv 0) + 1)),
      x (Lv 3) - x (Rv 3) + 4⁻¹ * (x (Lv 2) - x (Rv 2) + 1) - 2⁻¹,
      -2⁻¹ - (x (Lv 3) - x (Rv 3) + 4⁻¹ * (x (Lv 2) - x (Rv 2) + 1)),
      x (Lv 3) - x (Rv 3) + 2⁻¹ * (x (Lv 2) - x (Rv 2) + 1) - 1,
      -1 - (x (Lv 3) - x (Rv 3) + 2⁻¹ * (x (Lv 2) - x (Rv 2) + 1)),
      x (Lv 5) - x (Rv 5) + 4⁻¹ * (x (Lv 4) - x (Rv 4) + 1) - 2⁻¹,
      -2⁻¹ - (x (Lv 5) - x (Rv 5) + 4⁻¹ * (x (Lv 4) - x (Rv 4) + 1)),
      x (Lv 5) - x (Rv 5) + 2⁻¹ * (x (Lv 4) - x (Rv 4) + 1) - 1,
      -1 - (x (Lv 5) - x (Rv 5) + 2⁻¹ * (x (Lv 4) - x (Rv 4) + 1)),
      x (Lv 0) - x (Rv 0) + 1 - 2, -2 - (x (Lv 0) - x (Rv 0) + 1),
      x (Lv 2) - x (Rv 2) + 1 - 2, -2 - (x (Lv 2) - x (Rv 2) + 1),
      x (Lv 4) - x (Rv 4) + 1 - 2, -2 - (x (Lv 4) - x (Rv 4) + 1)] := by
  have e1 : ("L_g1".drop 2).copy = "g1" := by decide
  have e2 : ("R_g1".drop 2).copy = "g1" := by decide
  have e3 : ("L_r1".drop 2).copy = "r1" := by decide
  have e4 : ("R_r1".drop 2).copy = "r1" := by decide
  have e5 : ("L_g2".drop 2).copy = "g2" := by decide
  have e6 : ("R_g2".drop 2).copy = "g2" := by decide
  have e7 : ("L_r2".drop 2).copy = "r2" := by decide
  have e8 : ("R_r2".drop 2).copy = "r2" := by decide
  have e9 : ("L_g3".drop 2).copy = "g3" := by decide
  have e10 : ("R_g3".drop 2).copy = "g3" := by decide
  have e11 : ("L_r3".drop 2).copy = "r3" := by decide
  have e12 : ("R_r3".drop 2).copy = "r3" := by decide
  simp [comps, hostComps, platoon3_profiles_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    List.findIdx?_cons, hp00, hp10, hq0_25, hq0_5, hp20, ITerm.toHost, Term.eval, AOp.interp,
    Lv, Rv]

theorem eval_getD (i : ℕ) (x : State (Var 6)) :
    Term.eval (comps.getD i c0) x = (comps.map (fun c => Term.eval c x)).getD i 0 := by
  have h := List.getD_map (fun c => Term.eval c x) (l := comps) (n := i) (d := c0)
  simp only [c0, Term.eval] at h
  exact h.symm

theorem sat_canonInvM_bi (g' : Term (Var 6)) (gs' : List (Term (Var 6))) (a b : State (Var 6)) :
    RFormula.sat (canonInvM g' gs') (a, b) ↔
      ∀ c ∈ g' :: gs', Term.eval c (fun x => if x.1 = Side.R then b x else a x) ≤ 0 := by
  induction gs' with
  | nil => simp [canonInvM, sat_canonInv_bi]
  | cons h t ih =>
      show RFormula.sat (RFormula.and (canonInv h) (canonInvM g' t)) (a, b) ↔ _
      rw [RFormula.sat, sat_canonInv_bi, ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

/-! ## The witness and the deployed's `FOLLOW` window -/

/-- Deployed links `(33, 1)`, `(25, −1)`, `(29, 0)`; reference links `(34, 1)`, `(26, −1)`,
`(30, 0)` in `NORMAL` (`mv = 0`); every other coordinate 0. -/
noncomputable def σ0 : State (Var 6) :=
  fun y => if y = Lv 0 then 33 else if y = Lv 1 then 1 else if y = Lv 2 then 25
    else if y = Lv 3 then -1 else if y = Lv 4 then 29
    else if y = Rv 0 then 34 else if y = Rv 1 then 1 else if y = Rv 2 then 26
    else if y = Rv 3 then -1 else if y = Rv 4 then 30 else 0

/-- The deployed's links along `FOLLOW` (set point 29), from `σ0`. -/
noncomputable def φL (t : ℝ) : Fin 6 → ℝ :=
  ![gS 29 33 1 t, rS 29 33 1 t, gS 29 25 (-1) t, rS 29 25 (-1) t, gS 29 29 0 t, rS 29 29 0 t]

noncomputable def trajL (t : ℝ) : State (Var 6) :=
  fun y => if y.1 = Side.L then φL t y.2 else if y = tg then t else σ0 y

theorem trajL_L (t : ℝ) (i : Fin 6) : trajL t (Lv i) = φL t i := by simp [trajL, Lv]
theorem trajL_tg (t : ℝ) : trajL t tg = t := by simp [trajL]
theorem trajL_R (t : ℝ) (i : Fin 6) : trajL t (Rv i) = σ0 (Rv i) := by
  simp [trajL, Rv, Prod.ext_iff]

theorem φL_0 (t : ℝ) : φL t 0 = gS 29 33 1 t := rfl
theorem φL_1 (t : ℝ) : φL t 1 = rS 29 33 1 t := rfl
theorem φL_2 (t : ℝ) : φL t 2 = gS 29 25 (-1) t := rfl
theorem φL_3 (t : ℝ) : φL t 3 = rS 29 25 (-1) t := rfl

theorem tg_ne_L (i : Fin 6) : tg ≠ Lv i := by simp [Lv, Prod.ext_iff]

theorem left_ode :
    Program.sem (Program.ode (DLCalTiming.clk tg (leftBlock (fL 0))) domL)
      (Function.update σ0 tg 0) (trajL 1) := by
  refine ⟨1, trajL, by norm_num, ?_, rfl, ?_, ?_, ?_⟩
  · funext y
    obtain ⟨s, i⟩ := y
    cases s with
    | L =>
        rw [Function.update_of_ne (by simp [Prod.ext_iff])]
        show trajL 0 (Lv i) = σ0 (Lv i)
        rw [trajL_L]
        fin_cases i <;> simp [φL, gS_zero, rS_zero, σ0, Lv, Rv]
    | R =>
        rw [Function.update_of_ne (by simp [Prod.ext_iff])]
        simp [trajL]
    | Aux =>
        by_cases h : ((Side.Aux, i) : Var 6) = tg
        · rw [h, trajL_tg, Function.update_self]
        · rw [Function.update_of_ne h]; simp [trajL, h]
  · intro t ht p hp
    simp only [DLCalTiming.clk, leftBlock, List.mem_append, List.mem_map, List.mem_finRange,
      true_and, List.mem_singleton] at hp
    rcases hp with ⟨i, rfl⟩ | rfl
    · have hfield := fL_field (trajL t)
      obtain ⟨f0, f1, f2, f3, f4, f5⟩ := hfield
      fin_cases i
      · show HasDerivWithinAt (fun u => trajL u (Lv 0)) (Term.eval (fL 0 0) (trajL t)) _ t
        rw [f0, trajL_L]
        simp only [trajL_L, φL]
        exact (gS_hasDeriv 29 33 1 t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 1)) (Term.eval (fL 0 1) (trajL t)) _ t
        rw [f1, trajL_L, trajL_L]
        simp only [trajL_L, φL]
        exact (rS_hasDeriv 29 33 1 t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 2)) (Term.eval (fL 0 2) (trajL t)) _ t
        rw [f2, trajL_L]
        simp only [trajL_L, φL]
        exact (gS_hasDeriv 29 25 (-1) t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 3)) (Term.eval (fL 0 3) (trajL t)) _ t
        rw [f3, trajL_L, trajL_L]
        simp only [trajL_L, φL]
        exact (rS_hasDeriv 29 25 (-1) t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 4)) (Term.eval (fL 0 4) (trajL t)) _ t
        rw [f4, trajL_L]
        simp only [trajL_L, φL]
        exact (gS_hasDeriv 29 29 0 t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 5)) (Term.eval (fL 0 5) (trajL t)) _ t
        rw [f5, trajL_L, trajL_L]
        simp only [trajL_L, φL]
        exact (rS_hasDeriv 29 29 0 t).hasDerivWithinAt
    · show HasDerivWithinAt (fun u => trajL u tg) (Term.eval (Term.const 1) (trajL t)) _ t
      simp only [Term.eval, trajL_tg]
      exact hasDerivWithinAt_id t _
  · intro t _ x hx
    have hxL : x.1 ≠ Side.L := by
      intro h
      obtain ⟨s, i⟩ := x
      simp only at h
      subst h
      exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock, Lv])
    have hxtg : x ≠ tg := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    rw [Function.update_of_ne hxtg]
    simp [trajL, hxL, hxtg]
  · intro t ht
    rw [sat_domL]
    have a1 := E1_pos t
    have a2 := E2_pos t
    have b1 := E1_le t ht.1
    have b2 := E2_le t ht.1
    have h5 : φL t 5 = rS 29 29 0 t := rfl
    simp only [Box, trajL_L, h5]
    simp only [φL, gS, rS, Q1, Q2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]
    norm_num
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> nlinarith

theorem sat_guardL0 : Formula.sat (hostGuard vs 6 Side.L (mL 0)) σ0 := by
  simp [hostGuard, mL, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, gp_25_0, gp_33_0,
    gp_m1_0, gp_1_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, σ0, Lv, Rv]
  norm_num

/-- The deployed's `FOLLOW` window, run for time 1 (any `dt ≥ 1`). -/
theorem left_window (dt : ℝ) (hdt : 1 ≤ dt) :
    Program.sem (gwindowSeg (hostGuard vs 6 Side.L (mL 0)) (leftBlock (fL 0)) domL tg dt 1)
      σ0 (trajL 1) := by
  refine ⟨σ0, ⟨rfl, sat_guardL0⟩, ?_⟩
  rw [sem_windowSeg_one]
  refine ⟨Function.update σ0 tg 0, ?_, trajL 1, left_ode, ?_⟩
  · exact ⟨by simp [Term.eval], fun y hy => Function.update_of_ne hy _ _⟩
  · exact ⟨rfl, by rw [sat_clkGuard, trajL_tg]; exact hdt⟩


/-! ## The guards, the start, and the refutation -/

/-- Every profile guard bounds the link-1/link-2 gap difference: `g₁ − g₂ ≤ 8`. -/
theorem guard_gap (q : ℕ) (hq : q < 3) (x : State (Var 6))
    (h : Formula.sat (hostGuard vs 6 Side.R (mR q)) x) : x (Rv 0) - x (Rv 2) ≤ 8 := by
  interval_cases q <;>
  · simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, gp_24_0, gp_26_0,
      gp_28_0, gp_32_0, gp_34_0, gp_36_0, gp_m1_0, gp_1_0, vs, Run.resolveVar,
      List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
      Rv, and_assoc] at h
    have a1 := h.2.1
    have a2 := h.2.2.2.2.1
    show x (Side.R, 0) - x (Side.R, 2) ≤ 8
    linarith

theorem sat_guardR0_σ0 : Formula.sat (hostGuard vs 6 Side.R (mR 0)) σ0 := by
  simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, gp_26_0, gp_34_0,
    gp_m1_0, gp_1_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, σ0, Lv, Rv]
  norm_num

theorem region0_σ0 : Formula.sat (region 0) σ0 := by
  rw [sat_region_lt 0 (by norm_num)]
  intro a ha
  refine (hiffR 0 (by norm_num) a ha σ0).mpr ?_
  have hmem : a.2 ∈ termsW Rv 30 38 22 36 24 := by
    rw [← cR_terms0]; exact List.mem_map_of_mem ha
  have hall : ∀ t ∈ termsW Rv 30 38 22 36 24, Term.eval t σ0 ≤ 0 := by
    simp only [termsW, linT, derT, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [linLe, linGe, linQ, thrLe, thrGe, Term.eval, AOp.interp, σ0, Lv, Rv]
    norm_num
  exact hall _ hmem

theorem rows_σ0 : RFormula.sat (canonInvM g gs) (σ0, σ0) := by
  rw [sat_canonInvM_bi]
  simp only [ite_self]
  have hall : ∀ i < 18, Term.eval (comps.getD i c0) σ0 ≤ 0 := by
    intro i hi
    rw [eval_getD, comps_eval]
    interval_cases i <;> simp [σ0, Lv, Rv] <;> norm_num
  intro c hc
  simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> exact hall _ (by norm_num)

theorem J_σ0 : J σ0 := by
  simp only [J, PR, WR]
  simp [σ0, Lv, Rv]
  norm_num

theorem exp_half_bounds : 1/2 < Real.exp (-(1/2)) ∧ Real.exp (-(1/2)) < 3/4 := by
  have hinv : Real.exp (-(1/2)) * Real.exp (1/2) = 1 := by rw [← Real.exp_add]; simp
  have h1 : 3/2 ≤ Real.exp (1/2) := by have := Real.add_one_le_exp (1/2 : ℝ); linarith
  have hsq : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (1/2 : ℝ)
  have h2 : Real.exp (1/2) < 2 := by nlinarith
  constructor <;> nlinarith [Real.exp_pos (-(1/2) : ℝ)]

/-- The arithmetic core: on the curve `9 W = P²` (`0 < P ≤ 6`) with `P − W ≤ 2`, `W` is `4`
or at most `1`; neither is within 1 of `4 e` for `e ∈ (1/2, 3/4)`. -/
theorem curve_arith (P W e : ℝ) (h9 : 9 * W = P * P) (hP0 : 0 < P) (hP6 : P ≤ 6)
    (hx : P - W ≤ 2) (hlo : 4 * e - 1 ≤ W) (hhi : W ≤ 4 * e + 1) (e1 : 1/2 < e) (e2 : e < 3/4) :
    False := by
  by_cases hP3 : P ≤ 3
  · have hPP : P * P ≤ 9 := by nlinarith
    linarith
  · push Not at hP3
    have hq : (P - 3) * (P - 6) ≥ 0 := by nlinarith
    have hP6' : 6 ≤ P := by
      by_contra hc
      push Not at hc
      nlinarith
    have hW4 : W = 4 := by nlinarith
    linarith

/-- **The guarded Theorem 3 of `platoon3_profiles` is false**: the statement of
`platoon3_profiles_modal`, with the right automaton guarded and the loop invariant carrying the
mode-consistent region `gregion = guard ∧ region`, fails for every window length `dt ≥ 1`. -/
theorem platoon3_profiles_guarded_false (dt : ℝ) (hdt : 1 ≤ dt) :
    ¬ RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody GrG mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv gregion GrG.modes.length))) := by
  intro hvalid
  have h := (RFormula_sat_imp _ _ (σ0, σ0)).mp (hvalid (σ0, σ0))
  have hpre : RFormula.sat (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
      (mvRegionR mv gregion GrG.modes.length)) (σ0, σ0) := by
    refine ⟨⟨rows_σ0, ?_, ?_⟩, ?_⟩
    · show Formula.sat domL σ0
      rw [sat_domL]; simp [Box, σ0, Lv, Rv]; norm_num
    · show Formula.sat domR σ0
      rw [sat_domR]; simp [Box, σ0, Lv, Rv]; norm_num
    · show Formula.sat (mvRegion mv gregion GrG.modes.length) σ0
      rw [sat_mvRegion]
      exact ⟨0, by simp [GrG], by simp [σ0, Lv, Rv],
        sat_regionG.mpr ⟨sat_guardR0_σ0, region0_σ0⟩⟩
  have hfa := h hpre
  have hleft : RProgram.sem (RProgram.biprog (Program.star (bigChoice (leftProgs dt)))
      (Program.test Formula.tt)) (σ0, σ0) (trajL 1, σ0) := by
    refine ⟨Relation.ReflTransGen.single (Or.inl (left_window dt hdt)), rfl, trivial⟩
  have hdia := hfa (trajL 1, σ0) hleft
  apply hdia
  rintro ⟨ωL, ωR⟩ ⟨hL, hR⟩ hΦ
  obtain ⟨rfl, -⟩ := hL
  have hreg : Formula.sat (mvRegion mv gregion GrG.modes.length) ωR := hΦ.2
  rw [sat_mvRegion] at hreg
  obtain ⟨q, hq6, hmvq, hgq⟩ := hreg
  rw [GrG_len] at hq6
  have hgq' := sat_regionG.mp hgq
  by_cases hq3 : q < 3
  swap
  · exact not_sat_region_sink q hq3 ωR hgq'.2
  -- the end is on the invariant curve and in a profile's guard
  have hJ : J ωR := star_J hR (fun _ => J_σ0) (by
    interval_cases q
    · left; simpa using hmvq
    · right; left; simpa using hmvq
    · right; right; simpa using hmvq)
  have hgap := guard_gap q hq3 ωR hgq'.1
  -- the rows on the `ρ = 1/4` forms of links 1 and 2
  have hrows := (sat_canonInvM_bi g gs (trajL 1) ωR).mp hΦ.1.1
  have hr : ∀ i ∈ [0, 1, 4, 5], Term.eval (comps.getD i c0)
      (fun x => if x.1 = Side.R then ωR x else trajL 1 x) ≤ 0 := by
    intro i hi
    apply hrows
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false]
    rcases hi with rfl | rfl | rfl | rfl <;> simp
  have r0 := hr 0 (by simp)
  have r1 := hr 1 (by simp)
  have r4 := hr 4 (by simp)
  have r5 := hr 5 (by simp)
  rw [eval_getD, comps_eval] at r0 r1 r4 r5
  simp only [List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r4 r5
  have hLs : ∀ i : Fin 6, (Lv i : Var 6).1 = Side.L := fun _ => rfl
  have hRs : ∀ i : Fin 6, (Rv i : Var 6).1 = Side.R := fun _ => rfl
  simp only [hLs, hRs, if_true, reduceCtorEq, if_false, trajL_L] at r0 r1 r4 r5
  simp only [φL_0, φL_1, φL_2, φL_3] at r0 r1 r4 r5
  simp only [gS, rS, Q1, Q2] at r0 r1 r4 r5
  norm_num at r0 r1 r4 r5
  obtain ⟨h9, hP0, hP6⟩ := hJ
  simp only [PR, WR] at h9 hP0 hP6
  have hE1 : E1 1 = Real.exp (-(1/2)) := by simp [E1]
  rw [hE1] at r0 r1 r4 r5
  obtain ⟨eb1, eb2⟩ := exp_half_bounds
  set e := Real.exp (-(1/2)) with he
  set P := (ωR (Rv 1) - ωR (Rv 3)) + 1/2 * (ωR (Rv 0) - ωR (Rv 2)) with hP
  set W := (ωR (Rv 1) - ωR (Rv 3)) + 1/4 * (ωR (Rv 0) - ωR (Rv 2)) with hW
  -- `|W − 4 e| ≤ 1`
  have hWlo : 4 * e - 1 ≤ W := by rw [hW]; linarith
  have hWhi : W ≤ 4 * e + 1 := by rw [hW]; linarith
  -- the guard: `4 (P − W) = g₁ − g₂ ≤ 8`
  have hx : P - W ≤ 2 := by rw [hP, hW]; linarith
  exact curve_arith P W e h9 hP0 hP6 hx hWlo hWhi eb1 eb2

end V2Platoon3ProfilesRefuted
end RelCertifier
