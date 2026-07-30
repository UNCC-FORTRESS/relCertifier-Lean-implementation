/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The window displacement bound (the pump-and-hold prerequisite)

The `⟨…⟩` side of `faModal` runs AFTER the left window completes, so a response
may consist purely of right-only flows: the right "catches up" by pumping its
velocity and then holding, and the invariant is re-established by ARITHMETIC at
the endpoint — no joint flow certificate is involved at all. The one fact that
argument needs about the left is a bound on how far a `windowSeg` run can move
any given quantity:

* `clockedSeg_run`: a clocked segment's run is an integral curve of the
  clock-extended system whose duration is pinned by the clock — exactly the
  segment's clock reading, which the trailing test bounds by `dt`.
* `clockedSeg_growth` / `windowSeg_growth`: if `Lie g ≤ M` on the evolve
  domain then `g` grows by at most `M·dt` per segment, `M·(k·dt)` per window
  (`growth_along_dom` telescoped through the `k` segments).
* `windowSeg_mask`: coordinates outside the left block (and distinct from the
  clock) are untouched — the right state survives the window verbatim.
* `windowSeg_end_domL`: a nonempty window ends inside the evolve domain.

New leaf over `SplitCoupling` (for `growth_along_dom`/`integralCurve_of_tuple`)
and the reposition-bridge definitions; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.SplitCoupling
import RelCertifier.Proofs.Encoding.UniformMultiflow

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- The clock-extended left system is well-formed when the base is and the
clock is fresh for its bound set. -/
theorem clk_wellFormed (tg : Var n) (sys : ODESystem (Var n))
    (hwf : sys.WellFormed) (htg : tg ∉ sys.bound) :
    (DLCalTiming.clk tg sys).WellFormed := by
  simp only [DLCalTiming.clk, ODESystem.WellFormed, List.map_append, List.map_cons,
    List.map_nil]
  rw [List.nodup_append]
  refine ⟨hwf, List.nodup_singleton _, ?_⟩
  intro a ha b hb
  have hbtg : b = tg := List.mem_singleton.mp hb
  intro hab
  rw [hab, hbtg] at ha
  exact htg (show tg ∈ sys.bound from by
    simpa [ODESystem.bound] using ha)

/-- Decompose one clocked segment's run: an integral-curve tuple of the
clock-extended system from the clock-reset start, with the duration equal to
the final clock reading (≤ `dt` by the trailing test). -/
theorem clockedSeg_run (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (hwf : leftSys.WellFormed) (htg : tg ∉ leftSys.bound)
    {σ ν : State (Var n)}
    (hsem : Program.sem (clockedSeg leftSys domL tg dt) σ ν) :
    ∃ (r : ℝ) (Φ : ℝ → State (Var n)), 0 ≤ r ∧ r ≤ dt ∧
      Φ 0 = Function.update σ tg 0 ∧ Φ r = ν ∧
      IsIntegralCurveOn Φ (fun _ => odeField (DLCalTiming.clk tg leftSys))
        (Set.Icc 0 r) ∧
      (∀ t ∈ Set.Icc (0:ℝ) r, Formula.sat domL (Φ t)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ (DLCalTiming.clk tg leftSys).bound →
        Φ t x = Function.update σ tg 0 x) := by
  obtain ⟨σ₁, hassign, ν₀, hode, htest⟩ := hsem
  rw [sem_assign] at hassign
  rw [sem_test] at htest
  obtain ⟨rfl, hguard⟩ := htest
  simp only [Term.eval, Formula.sat, CompOp.interp, clkGuard] at hguard
  have hσ₁ : σ₁ = Function.update σ tg 0 := by
    funext y
    by_cases hy : y = tg
    · subst hy
      rw [Function.update_self]
      simpa [Term.eval] using hassign.1
    · rw [Function.update_of_ne hy]
      exact hassign.2 y hy
  subst hσ₁
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hode
  have hwfclk := clk_wellFormed tg leftSys hwf htg
  have hcurve := integralCurve_of_tuple hwfclk hder hmask
  -- the clock coordinate reads exactly the elapsed time
  have htgrow : ∀ t ∈ Set.Icc (0:ℝ) r, Φ t tg = t := by
    have hpair : (tg, (Term.const 1 : Term (Var n))) ∈ DLCalTiming.clk tg leftSys := by
      simp [DLCalTiming.clk]
    have hdertg : ∀ t ∈ Set.Icc (0:ℝ) r,
        HasDerivWithinAt (fun u => Φ u tg) 1 (Set.Icc 0 r) t := by
      intro t ht
      have := hder t ht (tg, Term.const 1) hpair
      simpa [Term.eval] using this
    have hconst : ∀ t ∈ Set.Icc (0:ℝ) r, Φ t tg - t = Φ 0 tg - 0 := by
      have hd0 : ∀ t ∈ Set.Icc (0:ℝ) r,
          HasDerivWithinAt (fun u => Φ u tg - u) 0 (Set.Icc 0 r) t := by
        intro t ht
        have hsub : HasDerivWithinAt (fun u => Φ u tg - u) (1 - 1)
            (Set.Icc 0 r) t :=
          (hdertg t ht).sub (hasDerivWithinAt_id t (Set.Icc (0:ℝ) r))
        have h11 : (1:ℝ) - 1 = 0 := by norm_num
        rw [h11] at hsub
        exact hsub
      have hmono : MonotoneOn (fun u => Φ u tg - u) (Set.Icc 0 r) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
          (fun t ht => (hd0 t ht).continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
        · rw [interior_Icc] at hx
          exact ((hd0 x (Set.Ioo_subset_Icc_self hx)).hasDerivAt
            (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
        · rw [interior_Icc] at hx
          rw [((hd0 x (Set.Ioo_subset_Icc_self hx)).hasDerivAt
            (Icc_mem_nhds hx.1 hx.2)).deriv]
      have hanti : AntitoneOn (fun u => Φ u tg - u) (Set.Icc 0 r) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r)
          (fun t ht => (hd0 t ht).continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
        · rw [interior_Icc] at hx
          exact ((hd0 x (Set.Ioo_subset_Icc_self hx)).hasDerivAt
            (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
        · rw [interior_Icc] at hx
          rw [((hd0 x (Set.Ioo_subset_Icc_self hx)).hasDerivAt
            (Icc_mem_nhds hx.1 hx.2)).deriv]
      intro t ht
      have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) r := Set.left_mem_Icc.mpr hr
      exact le_antisymm (hanti h0mem ht ht.1) (hmono h0mem ht ht.1)
    intro t ht
    have h0 : Φ 0 tg = 0 := by rw [hΦ0]; simp
    have := hconst t ht
    rw [h0] at this
    linarith
  have hrdt : r ≤ dt := by
    have := htgrow r (Set.right_mem_Icc.mpr hr)
    rw [hΦr] at this
    linarith [hguard, this.symm.le, this.le]
  exact ⟨r, Φ, hr, hrdt, hΦ0, hΦr, hcurve, hdom, hmask⟩

/-- Growth of a clock-free quantity over one clocked segment: at most `M·dt`. -/
theorem clockedSeg_growth (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (hwf : leftSys.WellFormed) (htg : tg ∉ leftSys.bound)
    (g : Term (Var n)) (M : ℝ) (hM : 0 ≤ M) (htgg : tg ∉ g.fv)
    (hbnd : ∀ x : State (Var n), Formula.sat domL x →
      Lie (DLCalTiming.clk tg leftSys) (fun ω => Term.eval g ω) x ≤ M)
    {σ ν : State (Var n)}
    (hsem : Program.sem (clockedSeg leftSys domL tg dt) σ ν) :
    Term.eval g ν ≤ Term.eval g σ + M * dt := by
  obtain ⟨r, Φ, hr, hrdt, hΦ0, hΦr, hcurve, hdom, -⟩ :=
    clockedSeg_run leftSys domL tg dt hwf htg hsem
  have hgrow := growth_along_dom (clk_wellFormed tg leftSys hwf htg) g M domL
    hbnd hr hcurve hdom
  rw [hΦr, hΦ0] at hgrow
  have hcoin : Term.eval g (Function.update σ tg 0) = Term.eval g σ :=
    Term.coincidence g (fun y hy =>
      Function.update_of_ne (fun hc => htgg (by rw [← hc]; exact hy)) _ _)
  rw [hcoin] at hgrow
  nlinarith [mul_le_mul_of_nonneg_left hrdt hM]

/-- Coordinates outside the left block and distinct from the clock survive one
clocked segment unchanged. -/
theorem clockedSeg_mask (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (hwf : leftSys.WellFormed) (htg : tg ∉ leftSys.bound)
    {σ ν : State (Var n)}
    (hsem : Program.sem (clockedSeg leftSys domL tg dt) σ ν) :
    ∀ x, x ∉ (DLCalTiming.clk tg leftSys).bound → ν x = σ x := by
  obtain ⟨r, Φ, hr, -, hΦ0, hΦr, -, -, hmask⟩ :=
    clockedSeg_run leftSys domL tg dt hwf htg hsem
  intro x hx
  have hxtg : x ≠ tg := by
    intro h; subst h
    exact hx (by simp [DLCalTiming.clk, ODESystem.bound])
  have := hmask r (Set.right_mem_Icc.mpr hr) x hx
  rw [hΦr] at this
  rw [this, Function.update_of_ne hxtg]

/-- **Window displacement bound**: over `k` clocked segments, a clock-free
quantity with `Lie ≤ M` on the domain grows by at most `M·(k·dt)`. -/
theorem windowSeg_growth (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ) (hwf : leftSys.WellFormed)
    (htg : tg ∉ leftSys.bound)
    (g : Term (Var n)) (M : ℝ) (hM : 0 ≤ M) (htgg : tg ∉ g.fv)
    (hbnd : ∀ x : State (Var n), Formula.sat domL x →
      Lie (DLCalTiming.clk tg leftSys) (fun ω => Term.eval g ω) x ≤ M)
    (_hdt : 0 ≤ dt)
    {σ ν : State (Var n)}
    (hsem : Program.sem (windowSeg leftSys domL tg dt k) σ ν) :
    Term.eval g ν ≤ Term.eval g σ + M * (k * dt) := by
  induction k generalizing σ with
  | zero =>
      simp only [windowSeg, List.replicate, bigSeq, sem_test] at hsem
      obtain ⟨rfl, -⟩ := hsem
      simp
  | succ k ih =>
      simp only [windowSeg, List.replicate_succ, bigSeq] at hsem
      obtain ⟨mid, hseg, hrest⟩ := hsem
      have h1 := clockedSeg_growth leftSys domL tg dt hwf htg g M hM htgg hbnd hseg
      have h2 := ih (by simpa [windowSeg] using hrest)
      push_cast
      nlinarith

/-- **Window mask**: coordinates outside the left block and distinct from the
clock survive the whole window unchanged. -/
theorem windowSeg_mask (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ) (hwf : leftSys.WellFormed)
    (htg : tg ∉ leftSys.bound)
    {σ ν : State (Var n)}
    (hsem : Program.sem (windowSeg leftSys domL tg dt k) σ ν) :
    ∀ x, x ∉ (DLCalTiming.clk tg leftSys).bound → ν x = σ x := by
  induction k generalizing σ with
  | zero =>
      simp only [windowSeg, List.replicate, bigSeq, sem_test] at hsem
      obtain ⟨rfl, -⟩ := hsem
      intro x _; rfl
  | succ k ih =>
      simp only [windowSeg, List.replicate_succ, bigSeq] at hsem
      obtain ⟨mid, hseg, hrest⟩ := hsem
      intro x hx
      rw [ih (by simpa [windowSeg] using hrest) x hx,
        clockedSeg_mask leftSys domL tg dt hwf htg hseg x hx]

/-- A nonempty window ends inside the left evolve domain. -/
theorem windowSeg_end_domL (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ) (hk : 0 < k)
    {σ ν : State (Var n)}
    (hsem : Program.sem (windowSeg leftSys domL tg dt k) σ ν) :
    Formula.sat domL ν := by
  induction k generalizing σ with
  | zero => exact absurd hk (by norm_num)
  | succ k ih =>
      simp only [windowSeg, List.replicate_succ, bigSeq] at hsem
      obtain ⟨mid, hseg, hrest⟩ := hsem
      cases k with
      | zero =>
          simp only [List.replicate, bigSeq, sem_test] at hrest
          obtain ⟨rfl, -⟩ := hrest
          obtain ⟨σ₁, -, ν₀, hode, htest⟩ := hseg
          rw [sem_test] at htest
          obtain ⟨rfl, -⟩ := htest
          exact sem_ode_ends_in_domain hode
      | succ k2 =>
          exact ih (by norm_num) (by simpa [windowSeg] using hrest)

end RelCertifier
