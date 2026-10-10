/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Guarded responses built step by step, and left-window bounds

Building blocks for the guarded right automaton (`GuardedSwitch.lean`) when the response is
chosen after the left window from the left run's end state (a catch-up or a climb through
the declared bands):

* `RResp G q post ν`: from the right state `ν` in mode `q`, a chain of declared segments (each
  flow followed by a LEGAL switch, the `gseg` test) ending where `post` of the final mode holds.
  `GResp` is exactly `RResp` at every end state of the left program (`gresp_of_rresp`).
* `rresp_stop` (no step: the postcondition already holds for the current mode) and
  `rresp_step` (one flow of the current mode, then a legal switch along a declared edge, then a
  response from the entered mode): a climb is a chain of `rresp_step`s closed by `rresp_stop`.
* `windowSeg_coord_le_max`/`ge_min`: a left coordinate with the linear field `k (c − x)`
  (`k ≥ 0`) ends a window of clocked pieces between its start value and its set point
  `c` (each piece is the explicit exponential approach, `ode_linear_coord`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.GuardedSwitch

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## Right-only guarded responses -/

/-- **A right-only guarded response** from the state `ν` in mode `q`: declared, chained
segments starting at `q`, every switch legal, ending where `post` of the final mode holds. -/
def RResp (G : SearchGraph (Var n)) (q : ℕ) (post : ℕ → Formula (Var n))
    (ν : State (Var n)) : Prop :=
  ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
    (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
    List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
    (∀ s, segs.head? = some s → s.1 = q) ∧
    ∃ μ, Program.sem (bigSeq (segs.map gseg)) ν μ ∧ Formula.sat (post (qfOf segs q)) μ

/-- `GResp` is `RResp` at every end state of the left program. -/
theorem gresp_of_rresp {G : SearchGraph (Var n)} {q : ℕ} {P : Program (Var n)}
    {post : ℕ → Formula (Var n)} {σ : State (Var n)}
    (h : ∀ ν, Program.sem P σ ν → RResp G q post ν) : GResp G q P post σ := h

theorem rresp_mono {G : SearchGraph (Var n)} {q : ℕ} {post post' : ℕ → Formula (Var n)}
    {ν : State (Var n)} (himp : ∀ q' μ, Formula.sat (post q') μ → Formula.sat (post' q') μ)
    (h : RResp G q post ν) : RResp G q post' ν := by
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := h
  exact ⟨segs, ha, hc, hh, μ, hrun, himp _ μ hp⟩

/-- **No step**: the postcondition already holds for the current mode. -/
theorem rresp_stop {G : SearchGraph (Var n)} {q : ℕ} {post : ℕ → Formula (Var n)}
    {ν : State (Var n)} (h : Formula.sat (post q) ν) : RResp G q post ν := by
  refine ⟨[], by simp, by simp, by simp, ν, ?_, by simpa [qfOf] using h⟩
  show Program.sem (Program.test Formula.tt) ν ν
  exact ⟨rfl, trivial⟩

/-- **One guarded step**: flow in the current mode `q` from `ν` to `κ`, switch along the
declared edge `e` (legal at `κ`), then respond from the entered mode. -/
theorem rresp_step {G : SearchGraph (Var n)} {q : ℕ} {m : RMode (Var n)} {e : REdge (Var n)}
    {post : ℕ → Formula (Var n)} {ν κ : State (Var n)}
    (hm : G.modeAt q = some m) (he : e ∈ G.edgesFrom q)
    (hflow : Program.sem (Program.ode m.sys m.dom) ν κ) (hleg : SwitchLegal e κ)
    (hrest : RResp G e.tgt post κ) : RResp G q post ν := by
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := hrest
  refine ⟨(q, m, e) :: segs, ?_, ?_, by simp, μ, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨hm, he⟩
    · exact ha s hs
  · rcases segs with - | ⟨r, rs⟩
    · simp
    · exact hc.cons (by
        intro y hy
        rw [List.head?_cons, Option.mem_some_iff] at hy
        subst hy
        exact (hh r rfl).symm)
  · simp only [List.map_cons, bigSeq]
    exact ⟨κ, sem_gseg.mpr ⟨hflow, hleg⟩, hrun⟩
  · rw [qfOf_cons]
    exact hp

/-! ## Left-window bounds on a linear coordinate -/

theorem clockedSeg_runs {leftSys : ODESystem (Var n)} {domL : Formula (Var n)} {tg : Var n}
    {dt : ℝ} {σ ν : State (Var n)} (h : Program.sem (clockedSeg leftSys domL tg dt) σ ν) :
    Program.sem (Program.ode (clk tg leftSys) domL) (Function.update σ tg 0) ν := by
  obtain ⟨κ, hκ, κ', hode, hκ'⟩ := h
  rw [sem_assign] at hκ
  rw [sem_test] at hκ'
  obtain ⟨rfl, -⟩ := hκ'
  have hκeq : κ = Function.update σ tg 0 := by
    funext y
    by_cases hy : y = tg
    · subst hy; rw [Function.update_self, hκ.1]; rfl
    · rw [Function.update_of_ne hy, hκ.2 y hy]
  rw [← hκeq]
  exact hode

/-- **A linear left coordinate across a window.** If the left field of coordinate `Lv j` is
`k (c − x)` on the domain (`k ≥ 0`), every window of clocked pieces ends with that coordinate
at most `max(start, c)`. -/
theorem windowSeg_coord_le_max (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n)
    (dt : ℝ) (j : Fin n) (k c : ℝ) (hk : 0 ≤ k) (htg : tg ≠ Lv j)
    (hf : ∀ s, Formula.sat domL s → Term.eval (fL j) s = k * (c - s (Lv j))) :
    ∀ (K : ℕ) {σ ν : State (Var n)},
      Program.sem (windowSeg (leftBlock fL) domL tg dt K) σ ν →
      ν (Lv j) ≤ max (σ (Lv j)) c := by
  intro K σ ν h
  refine windowSeg_preserve (leftBlock fL) domL tg dt (fun x => x (Lv j) ≤ max (σ (Lv j)) c)
    ?_ K σ ν (le_max_left _ _) h
  intro σ' ν' hP hrun
  have hode := clockedSeg_runs hrun
  have hmem : ((Lv j : Var n), fL j) ∈ clk tg (leftBlock fL) := by
    simp only [clk, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  obtain ⟨r, hr, heq⟩ := ode_linear_coord hode hmem k c hf
  rw [Function.update_of_ne htg.symm] at heq
  have he0 : 0 < Real.exp (-(k * r)) := Real.exp_pos _
  have he1 : Real.exp (-(k * r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  show ν' (Lv j) ≤ max (σ (Lv j)) c
  rw [heq]
  have hc : c ≤ max (σ (Lv j)) c := le_max_right _ _
  rcases le_total (σ' (Lv j)) c with hle | hle
  · nlinarith
  · nlinarith

/-- The lower companion of `windowSeg_coord_le_max`. -/
theorem windowSeg_coord_ge_min (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n)
    (dt : ℝ) (j : Fin n) (k c : ℝ) (hk : 0 ≤ k) (htg : tg ≠ Lv j)
    (hf : ∀ s, Formula.sat domL s → Term.eval (fL j) s = k * (c - s (Lv j))) :
    ∀ (K : ℕ) {σ ν : State (Var n)},
      Program.sem (windowSeg (leftBlock fL) domL tg dt K) σ ν →
      min (σ (Lv j)) c ≤ ν (Lv j) := by
  intro K σ ν h
  refine windowSeg_preserve (leftBlock fL) domL tg dt (fun x => min (σ (Lv j)) c ≤ x (Lv j))
    ?_ K σ ν (min_le_left _ _) h
  intro σ' ν' hP hrun
  have hode := clockedSeg_runs hrun
  have hmem : ((Lv j : Var n), fL j) ∈ clk tg (leftBlock fL) := by
    simp only [clk, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  obtain ⟨r, hr, heq⟩ := ode_linear_coord hode hmem k c hf
  rw [Function.update_of_ne htg.symm] at heq
  have he0 : 0 < Real.exp (-(k * r)) := Real.exp_pos _
  have he1 : Real.exp (-(k * r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  show min (σ (Lv j)) c ≤ ν' (Lv j)
  rw [heq]
  have hc : min (σ (Lv j)) c ≤ c := min_le_right _ _
  rcases le_total (σ' (Lv j)) c with hle | hle
  · nlinarith
  · nlinarith

/-- A guarded window's run is a run of its window after the (passed) guard test. -/
theorem gwindowSeg_runs {guardL : Formula (Var n)} {leftSys : ODESystem (Var n)}
    {domL : Formula (Var n)} {tg : Var n} {dt : ℝ} {K : ℕ} {σ ν : State (Var n)}
    (h : Program.sem (gwindowSeg guardL leftSys domL tg dt K) σ ν) :
    Formula.sat guardL σ ∧ Program.sem (windowSeg leftSys domL tg dt K) σ ν := by
  obtain ⟨κ, hκ, hrun⟩ := h
  rw [sem_test] at hκ
  obtain ⟨rfl, hg⟩ := hκ
  exact ⟨hg, hrun⟩

/-! ## Explicit right trajectories

A right trajectory given coordinatewise by explicit functions `φ i` (the right coordinates;
every other variable frozen at the start state) is a run of the right block as soon as each
`φ i` has the field's derivative along it. The helpers below supply the derivatives of the
shapes the benchmarks use: the exponential approach `c + (x₀ − c) e^{−k t}` of a linear
coordinate, its integral (an odometer `s' = v`), and constants. -/

/-- The right trajectory with coordinates `φ`, every non-right variable frozen at `ρ`. -/
noncomputable def trajR (ρ : State (Var n)) (φ : Fin n → ℝ → ℝ) (t : ℝ) : State (Var n) :=
  fun x => if x.1 = Side.R then φ x.2 t else ρ x

theorem trajR_R (ρ : State (Var n)) (φ : Fin n → ℝ → ℝ) (t : ℝ) (i : Fin n) :
    trajR ρ φ t (Rv i) = φ i t := by
  simp [trajR]

theorem trajR_L (ρ : State (Var n)) (φ : Fin n → ℝ → ℝ) (t : ℝ) (i : Fin n) :
    trajR ρ φ t (Lv i) = ρ (Lv i) := by
  simp [trajR, Lv]

theorem trajR_aux (ρ : State (Var n)) (φ : Fin n → ℝ → ℝ) (t : ℝ) (i : Fin n) :
    trajR ρ φ t ((Side.Aux, i) : Var n) = ρ ((Side.Aux, i) : Var n) := by
  simp [trajR]

/-- **An explicit right solution.** If every coordinate function starts at `ρ`'s right
coordinate and has the right field's derivative along the trajectory, and the domain holds
along it, the trajectory solves the right block (unit stretch) on `[0, τ]`. -/
theorem explicit_sol {fR : Fin n → Term (Var n)} {dom : Formula (Var n)} (ρ : State (Var n))
    (φ : Fin n → ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (h0 : ∀ i, φ i 0 = ρ (Rv i))
    (hder : ∀ i, ∀ t, 0 ≤ t → t ≤ τ →
      HasDerivAt (φ i) (Term.eval (fR i) (trajR ρ φ t)) t)
    (hdom : ∀ t, 0 ≤ t → t ≤ τ → Formula.sat dom (trajR ρ φ t)) :
    ODESol (rightBlock fR (Term.const 1)) dom ρ τ (trajR ρ φ) := by
  refine ⟨hτ, ?_, ?_, ?_, fun t ht => hdom t ht.1 ht.2⟩
  · funext x
    obtain ⟨sd, i⟩ := x
    cases sd with
    | R => exact h0 i
    | L => rfl
    | Aux => rfl
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hf : (fun u => trajR ρ φ u (Rv i)) = φ i := by
      funext u; exact trajR_R ρ φ u i
    show HasDerivWithinAt (fun u => trajR ρ φ u (Rv i))
      (Term.eval (Term.binop .mul (Term.const 1) (fR i)) (trajR ρ φ t)) (Icc 0 τ) t
    rw [hf]
    simp only [Term.eval, AOp.interp, one_mul]
    exact (hder i t ht.1 ht.2).hasDerivWithinAt
  · intro t _ x hx
    obtain ⟨sd, i⟩ := x
    cases sd with
    | R =>
        exact absurd (List.mem_map.mpr ⟨(Rv i, Term.binop .mul (Term.const 1) (fR i)),
          List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, rfl⟩) hx
    | L => rfl
    | Aux => rfl

/-- **An explicit right run.** The run of `explicit_sol`. -/
theorem explicit_run {fR : Fin n → Term (Var n)} {dom : Formula (Var n)} (ρ : State (Var n))
    (φ : Fin n → ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (h0 : ∀ i, φ i 0 = ρ (Rv i))
    (hder : ∀ i, ∀ t, 0 ≤ t → t ≤ τ →
      HasDerivAt (φ i) (Term.eval (fR i) (trajR ρ φ t)) t)
    (hdom : ∀ t, 0 ≤ t → t ≤ τ → Formula.sat dom (trajR ρ φ t)) :
    Program.sem (Program.ode (rightBlock fR (Term.const 1)) dom) ρ (trajR ρ φ τ) := by
  have H := explicit_sol ρ φ τ hτ h0 hder hdom
  exact ⟨τ, trajR ρ φ, H.hr, H.hΦ0, rfl, H.hder, H.hmask, H.hdom⟩

/-- The exponential approach `c + (x₀ − c) e^{−k t}` solves `x' = k (c − x)`. -/
theorem hasDerivAt_expApproach (k c x0 t : ℝ) :
    HasDerivAt (fun u => c + (x0 - c) * Real.exp (-(k * u)))
      (k * (c - (c + (x0 - c) * Real.exp (-(k * t))))) t := by
  have h1 : HasDerivAt (fun u => -(k * u)) (-(k * 1)) t :=
    ((hasDerivAt_id t).const_mul k).neg
  have h2 := (h1.exp.const_mul (x0 - c)).const_add c
  refine h2.congr_deriv ?_
  ring

/-- Its integral `s₀ + c t + (x₀ − c)(1 − e^{−k t})/k` (`k ≠ 0`) solves `s' = x`. -/
theorem hasDerivAt_expIntegral (k c x0 s0 t : ℝ) (hk : k ≠ 0) :
    HasDerivAt (fun u => s0 + c * u + (x0 - c) * (1 - Real.exp (-(k * u))) / k)
      (c + (x0 - c) * Real.exp (-(k * t))) t := by
  have h1 : HasDerivAt (fun u => -(k * u)) (-(k * 1)) t :=
    ((hasDerivAt_id t).const_mul k).neg
  have h2 : HasDerivAt (fun u => 1 - Real.exp (-(k * u))) (0 - Real.exp (-(k * t)) * -(k * 1)) t :=
    (hasDerivAt_const t 1).sub h1.exp
  have h3 := ((((hasDerivAt_id t).const_mul c).const_add s0).add
    ((h2.const_mul (x0 - c)).div_const k))
  refine h3.congr_deriv ?_
  field_simp
  ring

theorem exp_approach_between (k c x0 t : ℝ) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    min x0 c ≤ c + (x0 - c) * Real.exp (-(k * t)) ∧
      c + (x0 - c) * Real.exp (-(k * t)) ≤ max x0 c := by
  have he0 : 0 < Real.exp (-(k * t)) := Real.exp_pos _
  have he1 : Real.exp (-(k * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  rcases le_total x0 c with h | h
  · rw [min_eq_left h, max_eq_right h]; constructor <;> nlinarith
  · rw [min_eq_right h, max_eq_left h]; constructor <;> nlinarith

/-- **Linear coordinates across a window: either no higher than the start, or strictly below
the set point.** The disjunction is what a catch-up needs: a target strictly below the set
point is reached by the reference in finite time. -/
theorem windowSeg_coord_le_or_lt (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (j : Fin n) (k c : ℝ) (hk : 0 ≤ k) (htg : tg ≠ Lv j)
    (hf : ∀ s, Formula.sat domL s → Term.eval (fL j) s = k * (c - s (Lv j))) :
    ∀ (K : ℕ) {σ ν : State (Var n)},
      Program.sem (windowSeg (leftBlock fL) domL tg dt K) σ ν →
      ν (Lv j) ≤ σ (Lv j) ∨ ν (Lv j) < c := by
  intro K σ ν h
  refine windowSeg_preserve (leftBlock fL) domL tg dt
    (fun x => x (Lv j) ≤ σ (Lv j) ∨ x (Lv j) < c) ?_ K σ ν (Or.inl le_rfl) h
  intro σ' ν' hP hrun
  have hode := clockedSeg_runs hrun
  have hmem : ((Lv j : Var n), fL j) ∈ clk tg (leftBlock fL) := by
    simp only [clk, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  obtain ⟨r, hr, heq⟩ := ode_linear_coord hode hmem k c hf
  rw [Function.update_of_ne htg.symm] at heq
  have he0 : 0 < Real.exp (-(k * r)) := Real.exp_pos _
  have he1 : Real.exp (-(k * r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  show ν' (Lv j) ≤ σ (Lv j) ∨ ν' (Lv j) < c
  rw [heq]
  rcases lt_or_ge (σ' (Lv j)) c with hlt | hge
  · right; nlinarith
  · rcases hP with hP | hP
    · left; nlinarith
    · exact absurd hP (not_lt.mpr hge)

/-- **Right responses leave the left coordinates alone.** A run of declared right flows (each
binding only right coordinates) ends with the start state's left coordinates. -/
theorem bigSeq_odes_left (G : SearchGraph (Var n))
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    ∀ (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
      (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) →
      ∀ {ν μ : State (Var n)},
        Program.sem (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) ν μ →
        ∀ i, μ (Lv i) = ν (Lv i) := by
  intro segs
  induction segs with
  | nil =>
      intro _ ν μ h i
      rw [List.map_nil, bigSeq, sem_test] at h
      rw [h.1]
  | cons a rest ih =>
      intro halign ν μ h i
      simp only [List.map_cons, bigSeq] at h
      obtain ⟨κ, h1, h2⟩ := h
      have hκ : κ (Lv i) = ν (Lv i) := by
        refine sem_ode_mask h1 (fun hb => ?_)
        have := hRv a.1 a.2.1 (halign a List.mem_cons_self).1 (Or.inl (Or.inl hb))
        obtain ⟨j, hj⟩ := this
        exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
      rw [ih (fun s hs => halign s (List.mem_cons_of_mem _ hs)) h2 i, hκ]

end RelCertifier
