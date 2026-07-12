/-
GAP 1 — the `Hmulti` discharge: derive the genuine-multi-flow emit from `cert.segPres`, making the
reposition-inclusive multi Theorem 3 **checker-entailed** (`decideCovered`/`cert ⟹ Theorem 3`)
rather than emit-conditional. Mirror of `hpair_from_cover` (single-flow), multi-flow version.

The new plumbing vs single-flow: the bounded per-segment coupling (`faModal_ODE_G'_bounded`) runs the
left under a fresh clock (`clk tg leftBlock`), but `cert.segPres` is an **unclocked** joint `BoxLe`.
This file lifts the certificate across the clock — `sem_ode_perm` (semantics is permutation-invariant),
`box_ode_perm`, and `boxLe_clock_lift` (reuse `clockReduce`) — so the segment certs come from `cert`,
not re-assumed.
-/
import RelCertifier.BridgeReposition
import RelCertifier.ClockReduce

namespace RelCertifier
open DL DLCalTiming Function Set

variable {n : ℕ}

/-! ## Clock plumbing — lift an unclocked certificate box across a fresh clock -/

/-- **ODE semantics is permutation-invariant.** All the run conditions (per-equation derivatives,
non-bound masking, throughout-domain) are membership- and ∀-based, so reordering the equation list
leaves the reachability relation unchanged. -/
theorem sem_ode_perm {sys1 sys2 : ODESystem (Var n)} (hperm : List.Perm sys1 sys2)
    (dom : Formula (Var n)) {ω ν : State (Var n)}
    (h : Program.sem (Program.ode sys1 dom) ω ν) :
    Program.sem (Program.ode sys2 dom) ω ν := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  refine ⟨r, Φ, hr, hΦ0, hΦr, ?_, ?_, hdom⟩
  · intro t ht p hp; exact hder t ht p (hperm.mem_iff.mpr hp)
  · intro t ht x hx
    exact hmask t ht x (fun hc => hx ((hperm.map Prod.fst).mem_iff.mp hc))

/-- Box transfers across a permutation of the ODE equation list. -/
theorem box_ode_perm {sys1 sys2 : ODESystem (Var n)} (hperm : List.Perm sys1 sys2)
    (dom : Formula (Var n)) (φ : Formula (Var n)) {ω : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode sys1 dom) φ) ω) :
    Formula.sat (Formula.box (Program.ode sys2 dom) φ) ω := by
  rw [sat_box] at h ⊢
  intro ν hν
  exact h ν (sem_ode_perm hperm.symm dom hν)

/-- **Certificate clock-lift.** An unclocked `invLe g` box lifts to the clock-augmented system
(`clk tg sys = sys ++ [(tg,1)]`), for `tg` fresh. A clocked run drops (`clockReduce`) to an unclocked
run reaching the same state up to `tg`; `invLe g` is `tg`-invisible (`tg ∉ g.fv`), so it transfers. -/
theorem boxLe_clock_lift (sys : ODESystem (Var n)) (dom : Formula (Var n)) (g : Term (Var n))
    (tg : Var n) (htgb : tg ∉ sys.bound) (htgr : tg ∉ sys.readVars) (htgd : tg ∉ dom.fv)
    (htgg : tg ∉ g.fv) {ω : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode sys dom) (invLe g)) ω) :
    Formula.sat (Formula.box (Program.ode (clk tg sys) dom) (invLe g)) ω := by
  rw [sat_box] at h ⊢
  intro ν hν
  have hdrop := clockReduce sys dom tg htgb htgr htgd hν
  have hinv := h _ hdrop
  rw [sat_invLe] at hinv ⊢
  rwa [Term.coincidence g (fun y hy =>
    Function.update_of_ne (fun hc => htgg (by rw [← hc]; exact hy)) _ _)] at hinv

/-- The permutation moving the fresh clock from mid-position (`clk tg A ++ B`) to the tail
(`clk tg (A ++ B)`), so `boxLe_clock_lift` (clock-at-tail) applies to the joint system
`faModal_ODE_G'_bounded` forms. -/
theorem clk_mid_perm (A B : ODESystem (Var n)) (tg : Var n) :
    List.Perm ((clk tg A) ++ B) (clk tg (A ++ B)) := by
  simp only [clk]
  rw [List.append_assoc, List.append_assoc]
  exact (List.perm_append_comm.append_left A)

/-! ## Assembly — the genuine-multi-flow `faModal` from per-segment bounded couplings -/

/-- **The Hmulti `faModal`, assembled.** Given the per-segment bounded couplings (`faModalB`, each
one right mode over the clocked left, sourced from `cert.segPres` via `boxLe_clock_lift` +
`faModal_ODE_G'_bounded`) and the carried budget bound `r ≤ k·dt`, produce the genuine-multi-flow
`faModal (ode leftSys domL) (bigSeq rights) (invLe g)` — a **single physical left** residence against
the mode-switch sequence. `multiseg_clocked` composes the couplings; `clockLift_collapse` collapses
the `k`-fold clocked left to the physical one (`k` the carried budget count). -/
theorem multi_faModal_from_couplings (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (g : Term (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ)
    (htgb : tg ∉ leftSys.bound) (htgr : tg ∉ leftSys.readVars) (htgd : tg ∉ domL.fv)
    (htgg : tg ∉ g.fv) (hdt : 0 ≤ dt)
    (rights : List (Program (Var n))) (hklen : rights.length = k)
    (htgR : tg ∉ ((bigSeq rights).rename (Equiv.refl (Var n))).fv)
    (hdis : ∀ Q ∈ rights, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg leftSys domL tg dt)))
    (hcouple : ∀ Q ∈ rights, ∀ σ', Formula.sat (invLe g) σ' →
        faModalB (Equiv.refl (Var n)) (Program.ode (clk tg leftSys) domL) Q (invLe g) tg dt
          (Function.update σ' tg 0))
    {σ : State (Var n)} (hσ : Formula.sat (invLe g) σ)
    (hbudget : ∀ {r : ℝ} {Φ : ℝ → State (Var n)}, ODESol leftSys domL σ r Φ → r ≤ (k : ℝ) * dt) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode leftSys domL) (bigSeq rights)
      (invLe g)) σ := by
  have hmc := multiseg_clocked (invLe g) leftSys domL tg dt rights hdis hcouple σ hσ
  rw [List.map_const', hklen] at hmc
  have htgφ : tg ∉ (invLe g).fv := by
    simp only [invLe, Formula.fv, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false]
    exact htgg
  exact clockLift_collapse leftSys domL (bigSeq rights) (invLe g) tg dt k htgb htgr htgd hdt htgR
    htgφ hbudget hmc

/-! ## Cert-sourcing — the per-segment bounded coupling from `cert.segPres` -/

/-- **The joint certificate box, clock-lifted to the coupling's shape.** An unclocked joint `invLe g`
box at `σ` (as `cert.segPres` supplies via `sat_box`/`sat_invLe`) becomes the box at the reset state
`σ[tg↦0]` over the clocked joint `(clk tg A) ++ B` that `faModal_ODE_G'_bounded` consumes. Start-change
`σ → σ[tg↦0]` is `Program.coincidence` (the joint ignores the fresh `tg` entirely); then
`boxLe_clock_lift` (+ `clk_mid_perm`). -/
theorem box_joint_to_clocked (g : Term (Var n)) (A B : ODESystem (Var n)) (dom : Formula (Var n))
    (tg : Var n)
    (htgAb : tg ∉ A.bound) (htgBb : tg ∉ B.bound)
    (htgAr : tg ∉ A.readVars) (htgBr : tg ∉ B.readVars)
    (htgd : tg ∉ dom.fv) (htgg : tg ∉ g.fv) {σ : State (Var n)}
    (h : Formula.sat (Formula.box (Program.ode (A ++ B) dom) (invLe g)) σ) :
    Formula.sat (Formula.box (Program.ode ((clk tg A) ++ B) dom) (invLe g))
      (Function.update σ tg 0) := by
  have htgABb : tg ∉ (A ++ B).bound := by
    simp only [ODESystem.bound, List.map_append, List.mem_append]
    exact fun hc => hc.elim htgAb htgBb
  have htgABr : tg ∉ (A ++ B).readVars := by
    simp only [ODESystem.readVars, Set.mem_setOf_eq]
    rintro ⟨p, hp, hpx⟩
    exact (List.mem_append.mp hp).elim (fun ha => htgAr ⟨p, ha, hpx⟩) (fun hb => htgBr ⟨p, hb, hpx⟩)
  have hgfv : g.fv ⊆ {x | x ≠ tg} := fun y hy hc => htgg (hc ▸ hy)
  -- step 1: start-change σ → σ[tg↦0] over the unclocked joint
  have hstart : Formula.sat (Formula.box (Program.ode (A ++ B) dom) (invLe g))
      (Function.update σ tg 0) := by
    rw [sat_box] at h ⊢
    intro ν hν
    have hWsub : (Program.ode (A ++ B) dom).fv ⊆ {x | x ≠ tg} := by
      refine Set.union_subset (Set.union_subset ?_ ?_) ?_
      · intro x hx hc; exact htgABb (hc ▸ hx)
      · intro x hx hc; exact htgABr (hc ▸ hx)
      · intro x hx hc; exact htgd (hc ▸ hx)
    have hag : Set.EqOn (Function.update σ tg 0) σ {x | x ≠ tg} :=
      fun x hx => Function.update_of_ne hx 0 σ
    obtain ⟨ω2, hrun2, heq⟩ := Program.coincidence (Program.ode (A ++ B) dom) hWsub hag hν
    have hinv := h ω2 hrun2
    rw [sat_invLe] at hinv ⊢
    rw [Term.coincidence g (heq.mono (hgfv.trans Set.subset_union_left))]; exact hinv
  -- step 2: clock-lift; step 3: perm the tail clock to mid-position
  exact box_ode_perm (List.Perm.symm (clk_mid_perm A B tg)) dom (invLe g)
    (boxLe_clock_lift (A ++ B) dom g tg htgABb htgABr htgd htgg hstart)

end RelCertifier
