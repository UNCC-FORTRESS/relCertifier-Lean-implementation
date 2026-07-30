/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# B>1 — the multi-segment ∀∃ witness composition (clock-free)

The non-trivial ∀∃ case: the right switches modes mid-residence to respond to the left. Per
Gate 0, this is **clock-free** — no `tg` coordinate, no `ExtVar`. The composition `multiseg`
assembles `B` per-segment couplings (`pair_faModal`, proven) into a `B`-fold lockstep `faModal`,
via the proven `faModal_seq` (both-sides sequential) + `faModal_MR` (rule of consequence),
by induction on `B`. Each step peels one right segment coupled with one left `piter` factor.

Historical note: this clock-free route needed `ode` self-concatenation
(`sem (ode sys ϕ ; ode sys ϕ) = sem (ode sys ϕ)`) to collapse the `B`-fold left residence.
That analytic piece was never needed in the end — the live chain went the clocked way
instead (`multiseg_clocked`, `BridgeReposition`), where the clock makes each segment's
duration explicit and the collapse question does not arise. Kept because the clock-free
composition lemmas here are still the readable statement of how segments compose.
-/
import RelCertifier.Proofs.Encoding.ToolLevel

namespace RelCertifier

open DL DLCalTiming DLRel Set RelCertifier.Parse RelCertifier.Run

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

/-! ## Tool-level B>1 threading — `reified_relational_multi`

Mirror of B=1's `reified_relational`, over the heterogeneous mode-switching core. Per left mode:
its right mode-switch sequence + per-mode couplings feed `hstep_multiseg_het`; `faModal_bigChoiceL`
composes over left modes; `relational_loop_multi` (`faModal_MULTI`) closes the loop to
`[|(L*,R*)⟩⟩ψ`. The one non-B=1 datum is the per-left-mode **sequence** `rights` (which modes,
in order) — supplied by the cover; each mode's coupling is its own evolution-domain `pair_faModal`. -/

/-- A right mode is a branch of the right automaton `bigChoice rightProgs`. -/
theorem sem_mem_bigChoice (Q : Program (Var n)) {ν μ : State (Var n)}
    (h : Program.sem Q ν μ) :
    ∀ (Qs : List (Program (Var n))), Q ∈ Qs → Program.sem (bigChoice Qs) ν μ
  | [], hm => absurd hm (by simp)
  | q :: qs, hm => by
      rw [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact Or.inl h
      · exact Or.inr (sem_mem_bigChoice Q h qs hm)

/-- Per-left-mode B>1 data: the left mode, its right **mode-switch sequence**, and the
per-mode structural + coupling facts (each coupling an evolution-domain `pair_faModal`). -/
structure MultiLeft (n : ℕ) (rightProgs : List (Program (Var n))) (φinv : Formula (Var n)) where
  leftSys : ODESystem (Var n)
  leftDom : Formula (Var n)
  rights : List (Program (Var n))
  hne : rights ≠ []
  hmem : ∀ Q ∈ rights, Q ∈ rightProgs
  hdis : ∀ Q ∈ rights, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
      (Program.vars (Program.ode leftSys leftDom))
  hcouple : ∀ Q ∈ rights, ∀ σ, Formula.sat φinv σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode leftSys leftDom) Q φinv) σ

/-- The left program of a `MultiLeft` bundle. -/
def MultiLeft.leftProg {n : ℕ} {rightProgs : List (Program (Var n))} {φinv : Formula (Var n)}
    (d : MultiLeft n rightProgs φinv) : Program (Var n) :=
  Program.ode d.leftSys d.leftDom

/-- **Tool-level B>1 (all-17 form).** Given per-left-mode mode-switch data and the structural
`Bridges`/disjointness, the paper's ∀∃ relational modality over the looped choice-automata holds
— with genuine multi-segment mode-switching witnesses. Mirror of `reified_relational` via
`faModal_bigChoiceL` + `hstep_multiseg_het` + `relational_loop_multi`. `φinv = encode id ψ`. -/
theorem reified_relational_multi {n : ℕ}
    (rightProgs : List (Program (Var n))) (ψ : RFormula (Var n))
    (leftData : List (MultiLeft n rightProgs (encode (Equiv.refl (Var n)) ψ)))
    (ν : State (Var n)) (bs : BiState (Var n))
    (hd : Disjoint (Program.vars (bigChoice (leftData.map MultiLeft.leftProg)))
        (Program.vars ((bigChoice rightProgs).rename (Equiv.refl (Var n)))))
    (hinv : Formula.sat (encode (Equiv.refl (Var n)) ψ) ν)
    (hdd : Disjoint (faShape (Program.star (bigChoice (leftData.map MultiLeft.leftProg)))
          (Program.star (bigChoice rightProgs)) ψ).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map MultiLeft.leftProg)))
          (Program.star (bigChoice rightProgs)) ψ).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star (bigChoice (leftData.map MultiLeft.leftProg)))
          (Program.star (bigChoice rightProgs)) ψ).varsL
        (faShape (Program.star (bigChoice (leftData.map MultiLeft.leftProg)))
          (Program.star (bigChoice rightProgs)) ψ).varsR bs ν) :
    RFormula.sat (faShape (Program.star (bigChoice (leftData.map MultiLeft.leftProg)))
      (Program.star (bigChoice rightProgs)) ψ) bs := by
  refine relational_loop_multi (bigChoice (leftData.map MultiLeft.leftProg))
    (bigChoice rightProgs) ψ ν bs hd hinv ?_ hdd hb
  intro σ hσ
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (bigChoice rightProgs))
    (encode (Equiv.refl (Var n)) ψ) σ (leftData.map MultiLeft.leftProg) ?_
  intro P hP
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hP
  exact hstep_multiseg_het d.leftSys d.leftDom (bigChoice rightProgs) d.rights
    (encode (Equiv.refl (Var n)) ψ) σ d.hne
    (fun Q hQ a b hsem => sem_mem_bigChoice Q hsem rightProgs (d.hmem Q hQ))
    d.hdis d.hcouple hσ

/-! ## Parser emit — `PProblem → MultiLeft` (B>1), same boundary as B=1

Mirror of B=1's `lowerSeg`/`SegData.toCertSeg`. `lowerMultiLeft` lowers a left mode + its right
**mode-switch sequence** (from the cover) to **pure data** (`leftSys`/`leftDom` via `dynOf`/
`lowerF` on the **evolve** fields — guard-bug barred; each right segment `ode (rightBlock …) domR`).
The `MultiLeft` proofs (`hcouple` per segment via `pair_faModal`/`z3_unsat_sound`, `hmem`, `hdis`,
`hne`) enter at the smart constructor — the same Z3 trust boundary. A complete pure emit is
impossible for the same reason as B=1 (`hcouple`/`hz3` mention the opaque `z3solve`). -/

/-- Pure lowered **data** of a B>1 left cell: the left mode + its right mode-switch sequence. -/
structure MLData (n : ℕ) where
  leftSys : ODESystem (Var n)
  leftDom : Formula (Var n)
  rights : List (Program (Var n))

/-- **The B>1 parser emit (data).** Lower a left mode `mL` and its right mode-switch sequence
`rightSeq` (each `(rightMode, λ)`, from the cover) to `MLData` — `leftSys = leftBlock (fL of mL)`,
`leftDom` from `mL.evolve`, each right segment `ode (rightBlock (fR) λ) (evolveR)` (the **evolution**
domains, guards removed). `none` if unlowerable (→ the tool's `ERROR`). Pure, computable. -/
def lowerMultiLeft (vars : List String) (n : ℕ) (mL : PMode)
    (rightSeq : List (PMode × ℚ)) : Option (MLData n) := do
  let fLi ← dynOf vars n Side.L mL
  let domLi ← lowerF vars n Side.L mL.evolve
  let rights ← rightSeq.mapM (fun p => do
    let fRi ← dynOf vars n Side.R p.1
    let domRi ← lowerF vars n Side.R p.1.evolve
    some (Program.ode (rightBlock (fun i => (fRi i).toHost) (Term.const (p.2 : ℝ)))
      domRi.toHost))
  some { leftSys := leftBlock (fun i => (fLi i).toHost),
         leftDom := domLi.toHost, rights := rights }

/-- Smart constructor completing `MLData` to a `MultiLeft` by supplying the boundary proofs —
`hne`/`hmem`/`hdis` (structural/parser-level) and `hcouple` (per-segment `pair_faModal`, the
evolution-domain Z3 verdict via `z3_unsat_sound`). Makes the trust boundary explicit: data pure,
proofs here. -/
def MLData.toMultiLeft {n : ℕ} (d : MLData n) (rightProgs : List (Program (Var n)))
    (φinv : Formula (Var n))
    (hne : d.rights ≠ [])
    (hmem : ∀ Q ∈ d.rights, Q ∈ rightProgs)
    (hdis : ∀ Q ∈ d.rights, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (Program.ode d.leftSys d.leftDom)))
    (hcouple : ∀ Q ∈ d.rights, ∀ σ, Formula.sat φinv σ →
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode d.leftSys d.leftDom) Q φinv) σ) :
    MultiLeft n rightProgs φinv :=
  { leftSys := d.leftSys, leftDom := d.leftDom, rights := d.rights,
    hne := hne, hmem := hmem, hdis := hdis, hcouple := hcouple }

end RelCertifier
