/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_lag`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`. The
right model has one mode `CRUISE`: the stock loop with powertrain lag, `v' = a`,
`a' = 3.125 (0.5 (30 − v) − a)`, guard the engaged envelope `a + 2.5 v ∈ [60.5, 77]`,
`a + 0.625 v ∈ [13.625, 20.75]`, evolve box `v ∈ [0, 40]`, `a ∈ [−10, 10]`, next `[CRUISE]`.
The loop decouples into the modal coordinates `P = a + 2.5 v − 75` (`P' = −0.625 P`) and
`Q = a + 0.625 v − 18.75` (`Q' = −2.5 Q`); the guard is the box `P ∈ [−14.5, 2]`,
`Q ∈ [−5.125, 2]`, which contains `0`, so each coordinate stays in its band along every run
(style (a), the self-loop; `affine_linear_exact`). Existence: the explicit solution
`v = 30 + (8/15)(P₀ e^{−5t/8} − Q₀ e^{−5t/2})`, `a = (−P₀ e^{−5t/8} + 4 Q₀ e^{−5t/2})/3`
(`trajRs_sol`), inside the evolve box because the envelope spans `v ∈ [21.2, 33.8]`,
`a ∈ [−7.5, 7.5]`. Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.acc_tune_lag
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccTuneLag

open DL DLCalTiming DLRel Parse Set

/-! ## Two-coordinate linear systems (local) -/

/-- **Closed form of a decaying affine combination of two coordinates**: if
`α f₁ + β f₂ = k (c − (α y₁ + β y₂))` on the domain, the combination `w = α y₁ + β y₂`
satisfies `w(r) = c + (w₀ − c) e^{−k r}` (a modal coordinate of a linear system). -/
theorem affine_linear_exact {n : ℕ} {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y₁ y₂ : Var n} {f₁ f₂ : Term (Var n)} (h₁ : (y₁, f₁) ∈ sys) (h₂ : (y₂, f₂) ∈ sys)
    (α β k c : ℝ)
    (hf : ∀ s, Formula.sat dom s →
      α * Term.eval f₁ s + β * Term.eval f₂ s = k * (c - (α * s y₁ + β * s y₂))) :
    α * Φ r y₁ + β * Φ r y₂ = c + (α * x y₁ + β * x y₂ - c) * Real.exp (-(k * r)) := by
  set G : ℝ → ℝ := fun t => (c - (α * Φ t y₁ + β * Φ t y₂)) * Real.exp (k * t) with hG
  have hGder : ∀ t ∈ Set.Icc (0:ℝ) r, HasDerivWithinAt G 0 (Set.Icc 0 r) t := by
    intro t ht
    have d1 := (H.hder t ht (y₁, f₁) h₁).const_mul α
    have d2 := (H.hder t ht (y₂, f₂) h₂).const_mul β
    have h2 : HasDerivWithinAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1))
        (Set.Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul k).exp).hasDerivWithinAt
    have hft := hf _ (H.hdom t ht)
    exact (((d1.add d2).const_sub c).mul h2).congr_deriv
      (by simp only [Pi.add_apply]; linear_combination (-(Real.exp (k * t))) * hft)
  have hcont : ContinuousOn G (Set.Icc 0 r) := fun t ht => (hGder t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht =>
    (hGder t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    r ⟨H.hr, le_refl r⟩
  simp only [hG, H.hΦ0, mul_zero, Real.exp_zero, mul_one] at hconst
  have hexp : Real.exp (k * r) * Real.exp (-(k * r)) = 1 := by
    rw [← Real.exp_add]; simp
  have : c - (α * Φ r y₁ + β * Φ r y₂) = (c - (α * x y₁ + β * x y₂)) * Real.exp (-(k * r)) := by
    calc c - (α * Φ r y₁ + β * Φ r y₂)
        = (c - (α * Φ r y₁ + β * Φ r y₂)) * (Real.exp (k * r) * Real.exp (-(k * r))) := by
          rw [hexp, mul_one]
      _ = ((c - (α * Φ r y₁ + β * Φ r y₂)) * Real.exp (k * r)) * Real.exp (-(k * r)) := by ring
      _ = (c - (α * x y₁ + β * x y₂)) * Real.exp (-(k * r)) := by rw [hconst]
  linarith

/-- A value scaled by a factor in `(0, 1]` stays in a band containing `0` and the value. -/
theorem scale_band {lo hi p e : ℝ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hp1 : lo ≤ p) (hp2 : p ≤ hi)
    (he0 : 0 < e) (he1 : e ≤ 1) : lo ≤ p * e ∧ p * e ≤ hi := by
  rcases le_total p 0 with h | h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- **A modal coordinate keeps its band**: a decaying affine combination (`k ≥ 0`) whose set
point `c` and start lie in `[lo, hi]` ends in `[lo, hi]`. -/
theorem affine_band {n : ℕ} {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y₁ y₂ : Var n} {f₁ f₂ : Term (Var n)} (h₁ : (y₁, f₁) ∈ sys) (h₂ : (y₂, f₂) ∈ sys)
    (α β k c lo hi : ℝ) (hk : 0 ≤ k)
    (hf : ∀ s, Formula.sat dom s →
      α * Term.eval f₁ s + β * Term.eval f₂ s = k * (c - (α * s y₁ + β * s y₂)))
    (hc1 : lo ≤ c) (hc2 : c ≤ hi) (hx1 : lo ≤ α * x y₁ + β * x y₂)
    (hx2 : α * x y₁ + β * x y₂ ≤ hi) :
    lo ≤ α * Φ r y₁ + β * Φ r y₂ ∧ α * Φ r y₁ + β * Φ r y₂ ≤ hi := by
  rw [affine_linear_exact H h₁ h₂ α β k c hf]
  have he0 : 0 < Real.exp (-(k * r)) := Real.exp_pos _
  have he1 : Real.exp (-(k * r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [H.hr]
  have := scale_band (lo := lo - c) (hi := hi - c) (p := α * x y₁ + β * x y₂ - c)
    (by linarith) (by linarith) (by linarith) (by linarith) he0 he1
  constructor <;> linarith [this.1, this.2]

/-- `e^{c u}` has derivative `c e^{c t}`. -/
theorem hasDerivAt_exp_mul (c t : ℝ) :
    HasDerivAt (fun u => Real.exp (c * u)) (c * Real.exp (c * t)) t :=
  (((hasDerivAt_id t).const_mul c).exp).congr_deriv (by simp [mul_comm])

/-! ## The lowered right mode -/

def vs : List String := ["v", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := acc_tune_lag_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp3125 : Run.parseRat "3.125" = some ((25:ℚ)/8) := by
  have h : parseQ "3.125" = some (⟨3125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0625 : Run.parseRat "0.625" = some ((5:ℚ)/8) := by
  have h : parseQ "0.625" = some (⟨625, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp605 : Run.parseRat "60.5" = some ((121:ℚ)/2) := by
  have h : parseQ "60.5" = some (⟨605, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp770 : Run.parseRat "77.0" = some (77 : ℚ) := by
  have h : parseQ "77.0" = some (⟨770, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp13625 : Run.parseRat "13.625" = some ((109:ℚ)/8) := by
  have h : parseQ "13.625" = some (⟨13625, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp2075 : Run.parseRat "20.75" = some ((83:ℚ)/4) := by
  have h : parseQ "20.75" = some (⟨2075, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm100 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- `v' = a`. -/
theorem fR0_eval (x : State (Var 2)) : Term.eval (fR 0 0) x = x (Rv 1) := by
  simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hp3125,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- `a' = 3.125 (0.5 (30 − v) − a)`. -/
theorem fR1_eval (x : State (Var 2)) :
    Term.eval (fR 0 1) x = 25/8 * (1/2 * (30 - x (Rv 0)) - x (Rv 1)) := by
  simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hp3125,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

/-- The field, coordinatewise. -/
theorem fR_eval (i : Fin 2) (x : State (Var 2)) :
    Term.eval (fR 0 i) x =
      if i.val = 0 then x (Rv 1) else 25/8 * (1/2 * (30 - x (Rv 0)) - x (Rv 1)) := by
  fin_cases i
  · exact fR0_eval x
  · exact fR1_eval x

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 40) ∧ (-10 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 10) := by
  simp only [domR, hostEvolve, mR, acc_tune_lag_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp400, hpm100, hp100, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  tauto

/-! ## The right automaton (the file's mode and declared `next` list) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CRUISE 0). -/
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

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- `CRUISE`'s guard, evaluated (the engaged envelope). -/
theorem sat_guardR0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔
      (121/2 ≤ ν (Rv 1) + 5/2 * ν (Rv 0) ∧ ν (Rv 1) + 5/2 * ν (Rv 0) ≤ 77) ∧
      (109/8 ≤ ν (Rv 1) + 5/8 * ν (Rv 0) ∧ ν (Rv 1) + 5/8 * ν (Rv 0) ≤ 83/4) := by
  simp [hostGuard, mR, acc_tune_lag_IRv2, Run.lowerF, Run.lowerE, hp25, hp0625, hp605, hp770,
    hp13625, hp2075, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  tauto

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem epsR_eq : epsR acc_tune_lag_IRv2 = 1 := by
  simp [epsR, acc_tune_lag_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem memR (q : ℕ) (i : Fin 2) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ i

/-- The slow modal coordinate `P = a + 2.5 v − 75`: `P' = −0.625 P`. -/
theorem modeP (s : State (Var 2)) :
    5/2 * Term.eval (Term.binop .mul (Term.const 1) (fR 0 0)) s +
      1 * Term.eval (Term.binop .mul (Term.const 1) (fR 0 1)) s =
    5/8 * (75 - (5/2 * s (Rv 0) + 1 * s (Rv 1))) := by
  rw [eval_unit_mul, eval_unit_mul, fR0_eval, fR1_eval]; ring

/-- The fast modal coordinate `Q = a + 0.625 v − 18.75`: `Q' = −2.5 Q`. -/
theorem modeQ (s : State (Var 2)) :
    5/8 * Term.eval (Term.binop .mul (Term.const 1) (fR 0 0)) s +
      1 * Term.eval (Term.binop .mul (Term.const 1) (fR 0 1)) s =
    5/2 * (75/4 - (5/8 * s (Rv 0) + 1 * s (Rv 1))) := by
  rw [eval_unit_mul, eval_unit_mul, fR0_eval, fR1_eval]; ring

/-! ## The explicit solution -/

/-- The decaying exponentials of the slow (`P`) and fast (`Q`) modes. -/
noncomputable def eP (t : ℝ) : ℝ := Real.exp (-(5/8) * t)
noncomputable def eQ (t : ℝ) : ℝ := Real.exp (-(5/2) * t)

/-- The run from modal start `(P₀, Q₀)`: `v = 30 + (8/15)(P − Q)`, `a = (−P + 4 Q)/3`. -/
noncomputable def solV (P0 Q0 t : ℝ) : ℝ := 30 + 8/15 * (P0 * eP t - Q0 * eQ t)
noncomputable def solA (P0 Q0 t : ℝ) : ℝ := (-(P0 * eP t) + 4 * (Q0 * eQ t)) / 3

theorem eP_mem (t : ℝ) (ht : 0 ≤ t) : 0 < eP t ∧ eP t ≤ 1 :=
  ⟨Real.exp_pos _, by unfold eP; rw [Real.exp_le_one_iff]; linarith⟩
theorem eQ_mem (t : ℝ) (ht : 0 ≤ t) : 0 < eQ t ∧ eQ t ≤ 1 :=
  ⟨Real.exp_pos _, by unfold eQ; rw [Real.exp_le_one_iff]; linarith⟩

theorem hasDerivAt_solV (P0 Q0 t : ℝ) : HasDerivAt (solV P0 Q0) (solA P0 Q0 t) t := by
  have h1 := (hasDerivAt_exp_mul (-(5/8)) t).const_mul P0
  have h2 := (hasDerivAt_exp_mul (-(5/2)) t).const_mul Q0
  exact HasDerivAt.congr_deriv (((h1.sub h2).const_mul (8/15)).const_add 30)
    (by simp only [solA, eP, eQ]; ring)

theorem hasDerivAt_solA (P0 Q0 t : ℝ) :
    HasDerivAt (solA P0 Q0) (25/8 * (1/2 * (30 - solV P0 Q0 t) - solA P0 Q0 t)) t := by
  have h1 := (hasDerivAt_exp_mul (-(5/8)) t).const_mul P0
  have h2 := (hasDerivAt_exp_mul (-(5/2)) t).const_mul Q0
  exact HasDerivAt.congr_deriv ((h1.neg.add (h2.const_mul 4)).div_const 3)
    (by simp only [solA, solV, eP, eQ]; ring)

/-- **Assumption 1 for `acc_tune_lag`**, Z3-free. -/
theorem acc_tune_lag_wellFormedR : WellFormedR Gr guardR (epsR acc_tune_lag_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg _ _
  obtain ⟨hq1, rfl⟩ := Gr_modeAt_inv hm
  have hq0 : q = 0 := by omega
  subst hq0
  have hgx := (sat_guardR0 x).mp hg
  refine ⟨?_, ?_⟩
  · -- existence: the explicit two-exponential solution
    set P0 := x (Rv 1) + 5/2 * x (Rv 0) - 75 with hP0
    set Q0 := x (Rv 1) + 5/8 * x (Rv 0) - 75/4 with hQ0
    refine ⟨_, trajRs_sol x (fun i t => if i.val = 0 then solV P0 Q0 t else solA P0 Q0 t)
        1 (by norm_num) ?_ ?_ ?_⟩
    · intro i
      fin_cases i <;> simp [solV, solA, eP, eQ, hP0, hQ0] <;> ring
    · intro i t _ _
      rw [fR_eval]
      fin_cases i
      · simp only [trajRs_R]
        simpa using hasDerivAt_solV P0 Q0 t
      · simp only [trajRs_R]
        simpa using hasDerivAt_solA P0 Q0 t
    · intro t ht0 _
      change Formula.sat domR _
      rw [sat_domR]
      simp only [trajRs_R]
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false,
        solV, solA]
      obtain ⟨hP1, hP2⟩ := eP_mem t ht0
      obtain ⟨hQ1, hQ2⟩ := eQ_mem t ht0
      have hp := scale_band (lo := -29/2) (hi := 2) (p := P0) (e := eP t)
        (by norm_num) (by norm_num) (by linarith [hgx.1.1]) (by linarith [hgx.1.2]) hP1 hP2
      have hq := scale_band (lo := -41/8) (hi := 2) (p := Q0) (e := eQ t)
        (by norm_num) (by norm_num) (by linarith [hgx.2.1]) (by linarith [hgx.2.2]) hQ1 hQ2
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hp.1, hp.2, hq.1, hq.2]
  · -- every run keeps both modal bands: the self-loop
    intro t Φ _ H
    have hP := affine_band H (memR 0 0) (memR 0 1) (5/2) 1 (5/8) 75 (121/2) 77 (by norm_num)
      (fun s _ => modeP s) (by norm_num) (by norm_num) (by linarith [hgx.1.1])
      (by linarith [hgx.1.2])
    have hQ := affine_band H (memR 0 0) (memR 0 1) (5/8) 1 (5/2) (75/4) (109/8) (83/4)
      (by norm_num) (fun s _ => modeQ s) (by norm_num) (by norm_num) (by linarith [hgx.2.1])
      (by linarith [hgx.2.2])
    refine ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hP.1, hP.2, hQ.1, hQ.2]

end V2AccTuneLag
end RelCertifier
