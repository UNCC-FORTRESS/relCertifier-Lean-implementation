/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# B>1 — the multi-segment ∀∃ witness composition (clock-free)

The non-trivial ∀∃ case: the right switches modes mid-residence to respond to the left. Per
Gate 0, this is **clock-free** — no `tg` coordinate, no `ExtVar`. The composition `multiseg`
assembles `B` per-segment couplings (`pair_faModal`, proven) into a `B`-fold lockstep `faModal`,
via the proven `faModal_seq` (both-sides sequential) + `faModal_MR` (rule of consequence),
by induction on `B`. Each step peels one right segment coupled with one left `piter` factor.

Remaining after this file (the one analytic piece): `ode` **self-concatenation**
`sem (ode sys ϕ ; ode sys ϕ) = sem (ode sys ϕ)` — so `piter leftOde B ≡ leftOde` and the
`B`-fold left collapses to the single left residence. It mirrors `plantT_glue`'s junction
differentiability, minus the clock. Then `faModal_loopN` lifts the right to `star`, and
`faModal_MULTI` (proven) closes the loop.
-/
import RelCertifier.ToolLevel

namespace RelCertifier

open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## `ode` split into `piter` — the left doesn't multiply (only the right does)

For `multiseg → hstep` we only need `sem leftOde ⊆ sem (piter leftOde B)` (the **split**
direction: one ODE run realized as a `B`-fold `piter` run), which collapses the box
`[piter leftOde B]` to `[leftOde]`. This avoids the junction-differentiability concat entirely
(that would be `plantT_glue` minus the clock) — the single residence is padded with
zero-duration runs, not concatenated. -/

/-- A zero-duration ODE run: from an in-domain state to itself. The `HasDerivWithinAt` on the
degenerate interval `[0,0] = {0}` is trivial (`s \ {x} = ∅`, filter `⊥`). -/
theorem sem_ode_zero (sys : ODESystem (Var n)) (ϕ : Formula (Var n)) {ν : State (Var n)}
    (hν : Formula.sat ϕ ν) : Program.sem (Program.ode sys ϕ) ν ν := by
  refine ⟨0, fun _ => ν, le_refl 0, rfl, rfl, ?_, ?_, ?_⟩
  · intro t ht p _
    simp only [Set.Icc_self, Set.mem_singleton_iff] at ht
    subst ht
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hemp : (Set.Icc (0:ℝ) 0) \ {0} = ∅ := by rw [Set.Icc_self]; simp
    rw [hemp, nhdsWithin_empty]
    exact Filter.tendsto_bot
  · intro t _ x _; rfl
  · intro t _; exact hν

/-- **The split.** A single ODE run is a `(B+1)`-fold `piter` run — the full run in the last
factor, zero-duration runs padding the rest. -/
theorem sem_ode_sub_piter (sys : ODESystem (Var n)) (ϕ : Formula (Var n)) :
    ∀ (B : ℕ) {ω ν : State (Var n)}, Program.sem (Program.ode sys ϕ) ω ν →
      Program.sem (piter (Program.ode sys ϕ) (B + 1)) ω ν := by
  intro B
  induction B with
  | zero =>
      intro ω ν hrun
      exact ⟨ν, hrun, rfl, trivial⟩
  | succ B ih =>
      intro ω ν hrun
      obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hrun
      have hϕω : Formula.sat ϕ ω := by
        have := hdom 0 ⟨le_refl 0, hr⟩
        rwa [hΦ0] at this
      exact ⟨ω, sem_ode_zero sys ϕ hϕω, ih ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩⟩

/-- **Left collapse.** Because `sem leftOde ⊆ sem (piter leftOde (B+1))`, a `faModal` over the
`piter`-repeated left collapses to one over the single left residence. (The box shrinks its
universally-quantified left runs to the genuine ones — sound; the right is untouched.) -/
theorem faModal_left_collapse (sys : ODESystem (Var n)) (ϕ : Formula (Var n))
    (Q : Program (Var n)) (φ : Formula (Var n)) (B : ℕ) (ω : State (Var n))
    (h : Formula.sat (faModal (Equiv.refl (Var n)) (piter (Program.ode sys ϕ) (B + 1)) Q φ) ω) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode sys ϕ) Q φ) ω := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  exact h ν (sem_ode_sub_piter sys ϕ B hν)

/-- `piter` does not introduce variables beyond its body. -/
theorem vars_piter_subset (Q : Program (Var n)) :
    ∀ B, Program.vars (piter Q B) ⊆ Program.vars Q := by
  intro B
  induction B with
  | zero =>
      intro x hx
      simp [piter, Program.vars, Program.fv, Program.bv, Formula.fv] at hx
  | succ B ih =>
      have hfv : (piter Q B).fv ⊆ Program.vars Q := Set.subset_union_left.trans ih
      have hbv : (piter Q B).bv ⊆ Program.vars Q := Set.subset_union_right.trans ih
      simp only [piter, Program.vars, Program.fv, Program.bv]
      refine Set.union_subset (Set.union_subset ?_ ?_) (Set.union_subset ?_ ?_)
      · exact Set.subset_union_left
      · exact Set.diff_subset.trans hfv
      · exact Set.subset_union_right
      · exact hbv

/-- **The multi-segment lockstep composition (clock-free).** Given a per-segment coupling
`hcouple` (one left factor ↔ one right segment, preserving the invariant `φinv` — discharged by
`pair_faModal`) and left/right variable disjointness, the `B`-fold lockstep `faModal` over
`piter leftOde B` (left) and `piter rightStep B` (right) preserves `φinv`. By induction on `B`
via `faModal_seq` (both-sides sequential) + `faModal_MR` (consequence). `ρ = id`. -/
theorem multiseg (leftOde rightStep : Program (Var n)) (φinv : Formula (Var n))
    (hdis : Disjoint (Program.vars (rightStep.rename (Equiv.refl (Var n))))
                     (Program.vars leftOde))
    (hcouple : ∀ σ, Formula.sat φinv σ →
        Formula.sat (faModal (Equiv.refl (Var n)) leftOde rightStep φinv) σ) :
    ∀ (B : ℕ) (ω : State (Var n)), Formula.sat φinv ω →
      Formula.sat (faModal (Equiv.refl (Var n)) (piter leftOde B) (piter rightStep B) φinv) ω := by
  intro B
  induction B with
  | zero =>
      intro ω hω
      simp only [piter]
      rw [faModal_sat]
      intro ν hν
      rw [sem_test] at hν
      obtain ⟨rfl, _⟩ := hν
      exact ⟨ω, by rw [rename_test, sem_test]; exact ⟨rfl, trivial⟩, hω⟩
  | succ B ih =>
      intro ω hω
      simp only [piter]
      refine faModal_seq (Equiv.refl (Var n)) leftOde (piter leftOde B) rightStep
        (piter rightStep B) φinv ω ?_ ?_
      · exact Set.disjoint_of_subset_right (vars_piter_subset leftOde B) hdis
      · refine faModal_MR (Equiv.refl (Var n)) leftOde rightStep φinv _ ω (hcouple ω hω) ?_
        intro μ hμ
        exact ih μ hμ

/-- **The B>1 core (one left mode ↔ right star).** From the per-segment coupling `hcouple`
(discharged by `pair_faModal` + `unionR`), the left mode coupled with the **right star**
(the right's multi-mode response) preserves `φinv`. Chains: `multiseg` (B-fold lockstep) →
`faModal_left_collapse` (the left `piter` collapses to the single residence — `sem_ode_zero`,
no junction concat) → `faModal_loopN` (the right `piter` lifts to `star`). Clock-free; reuses
only proven pieces. This is `faModal_MULTI`'s per-left-cycle hypothesis for B>1. -/
theorem hstep_multiseg (leftSys : ODESystem (Var n)) (leftDom : Formula (Var n))
    (rightStep : Program (Var n)) (φinv : Formula (Var n)) (B' : ℕ) (ω : State (Var n))
    (hdis : Disjoint (Program.vars (rightStep.rename (Equiv.refl (Var n))))
                     (Program.vars (Program.ode leftSys leftDom)))
    (hcouple : ∀ σ, Formula.sat φinv σ →
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode leftSys leftDom) rightStep φinv) σ)
    (hσ : Formula.sat φinv ω) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode leftSys leftDom)
      (Program.star rightStep) φinv) ω := by
  have hm := multiseg (Program.ode leftSys leftDom) rightStep φinv hdis hcouple (B' + 1) ω hσ
  have hc := faModal_left_collapse leftSys leftDom (piter rightStep (B' + 1)) φinv B' ω hm
  exact faModal_loopN (Equiv.refl (Var n)) (Program.ode leftSys leftDom) rightStep φinv ω
    ⟨B' + 1, hc⟩

/-! ## Heterogeneous multi-segment — genuine mode-switching (the real B>1 content)

`multiseg` is homogeneous (same right step per segment). The B>1 benchmarks switch right modes
mid-residence (`visited ≥ 2`), so the right response is a sequence of **different** modes.
`multiseg_het` composes such a sequence via the same `faModal_seq` + `faModal_MR`, but each
segment carries its **own** right mode with its **own** coupling (its own evolution-domain
`pair_faModal`). This is where the fixed-branch `bigChoiceR` was insufficient. -/

/-- Sequential composition over a list of programs (the right's mode-switch sequence). -/
def bigSeq : List (Program V) → Program V
  | []      => Program.test Formula.tt
  | Q :: qs => Program.seq Q (bigSeq qs)

/-- **Heterogeneous multi-segment lockstep composition.** Each segment couples the left factor
with its **own** right mode `Q ∈ rights` (its own `pair_faModal`), so the right genuinely
switches modes across the sequence. The left is `piter leftOde (length rights)` (same residence,
split into `|rights|` pieces). Induction on `rights` via `faModal_seq` + `faModal_MR`. -/
theorem multiseg_het (leftOde : Program (Var n)) (φinv : Formula (Var n)) :
    ∀ (rights : List (Program (Var n))),
      (∀ Q ∈ rights, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
          (Program.vars leftOde)) →
      (∀ Q ∈ rights, ∀ σ, Formula.sat φinv σ →
          Formula.sat (faModal (Equiv.refl (Var n)) leftOde Q φinv) σ) →
      ∀ ω, Formula.sat φinv ω →
        Formula.sat (faModal (Equiv.refl (Var n)) (piter leftOde rights.length)
          (bigSeq rights) φinv) ω := by
  intro rights
  induction rights with
  | nil =>
      intro _ _ ω hω
      simp only [List.length_nil, piter, bigSeq]
      rw [faModal_sat]
      intro ν hν
      rw [sem_test] at hν
      obtain ⟨rfl, _⟩ := hν
      exact ⟨ω, by rw [rename_test, sem_test]; exact ⟨rfl, trivial⟩, hω⟩
  | cons Q qs ih =>
      intro hdis hcouple ω hω
      simp only [List.length_cons, piter, bigSeq]
      refine faModal_seq (Equiv.refl (Var n)) leftOde (piter leftOde qs.length) Q
        (bigSeq qs) φinv ω ?_ ?_
      · exact Set.disjoint_of_subset_right (vars_piter_subset leftOde qs.length)
          (hdis Q (List.mem_cons_self ..))
      · refine faModal_MR (Equiv.refl (Var n)) leftOde Q φinv _ ω
          (hcouple Q (List.mem_cons_self ..) ω hω) ?_
        intro μ hμ
        exact ih (fun R hR => hdis R (List.mem_cons_of_mem Q hR))
          (fun R hR => hcouple R (List.mem_cons_of_mem Q hR)) μ hμ

/-- A `bigSeq` run (the mode-switch sequence) is a `star` run of the right automaton, provided
each segment `Q ∈ rights` is a step of `rightBody` (`sem Q ⊆ sem rightBody`). -/
theorem sem_bigSeq_sub_star (rightBody : Program (Var n)) :
    ∀ (rights : List (Program (Var n))),
      (∀ Q ∈ rights, ∀ ν μ, Program.sem Q ν μ → Program.sem rightBody ν μ) →
      ∀ ν μ, Program.sem (bigSeq rights) ν μ → Program.sem (Program.star rightBody) ν μ := by
  intro rights
  induction rights with
  | nil =>
      intro _ ν μ h
      simp only [bigSeq] at h; rw [sem_test] at h
      obtain ⟨rfl, _⟩ := h
      exact Relation.ReflTransGen.refl
  | cons Q qs ih =>
      intro hsub ν μ h
      simp only [bigSeq] at h
      obtain ⟨κ, hQ, hrest⟩ := h
      exact Relation.ReflTransGen.head (hsub Q (List.mem_cons_self ..) ν κ hQ)
        (ih (fun R hR => hsub R (List.mem_cons_of_mem Q hR)) κ μ hrest)

/-- **The B>1 core, with genuine mode-switching.** Given the actual right mode-switch sequence
`rights` (each `Q` a step of `rightBody`, its own evolution-domain coupling), the left mode
coupled with the **right star** preserves `φinv`. `multiseg_het` (heterogeneous compose) →
`faModal_left_collapse` (left `piter` → one residence) → `bigSeq → star` (the mode sequence is a
right-automaton run). Clock-free, concat-free; the right genuinely switches modes. -/
theorem hstep_multiseg_het (leftSys : ODESystem (Var n)) (leftDom : Formula (Var n))
    (rightBody : Program (Var n)) (rights : List (Program (Var n))) (φinv : Formula (Var n))
    (ω : State (Var n)) (hne : rights ≠ [])
    (hstepR : ∀ Q ∈ rights, ∀ ν μ, Program.sem Q ν μ → Program.sem rightBody ν μ)
    (hdis : ∀ Q ∈ rights, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (Program.ode leftSys leftDom)))
    (hcouple : ∀ Q ∈ rights, ∀ σ, Formula.sat φinv σ →
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode leftSys leftDom) Q φinv) σ)
    (hσ : Formula.sat φinv ω) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode leftSys leftDom)
      (Program.star rightBody) φinv) ω := by
  -- rights = R :: rs, so its length is B'+1 ≥ 1 (for faModal_left_collapse)
  obtain ⟨R, rs, rfl⟩ : ∃ R rs, rights = R :: rs := by
    cases rights with
    | nil => exact absurd rfl hne
    | cons R rs => exact ⟨R, rs, rfl⟩
  have hm := multiseg_het (Program.ode leftSys leftDom) φinv (R :: rs) hdis hcouple ω hσ
  rw [List.length_cons] at hm
  have hc := faModal_left_collapse leftSys leftDom (bigSeq (R :: rs)) φinv rs.length ω hm
  -- convert the right `bigSeq` to `star rightBody`
  rw [faModal_sat] at hc ⊢
  intro ν hν
  obtain ⟨μ, hμ, hφ⟩ := hc ν hν
  refine ⟨μ, ?_, hφ⟩
  rw [Program.rename_refl] at hμ ⊢
  exact sem_bigSeq_sub_star rightBody (R :: rs) hstepR ν μ hμ

end RelCertifier
