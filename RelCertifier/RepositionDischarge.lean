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
import RelCertifier.BridgeDischarge
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

/-! ## hExist clock-adaptation — project the deterministic clock coordinate -/

/-- **The bounded hExist over the clocked left, from the cover's unclocked `HExistSeg`.**
`faModal_ODE_G'_bounded` evolves the left under `clk tg leftBlock`; `HExistSeg` is over `leftBlock`.
The adaptation is a pure clock-coordinate projection: drop `tg` from the left curve
(`ΦL' = update (ΦL·) tg 0`) — the **physical trajectory is unchanged** (`tg ∉ leftBlock.read`),
`HExistSeg` responds, then restore `tg` on the right witness (`ΦR' = update (ΦR·) tg (ΦL s tg)`).
The right never reads `tg` (`tg ∉ rightBlock`), so its response is identical — the tg-invisibility
mechanism applied to the run construction. `update x tg (x tg) = x` makes `ΦR' 0 = ΦL s` exact. -/
theorem hExist_clocked_of_HExistSeg (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (htgLb : tg ∉ (leftBlock fL).bound) (htgLr : tg ∉ (leftBlock fL).readVars)
    (htgRb : tg ∉ (rightBlock fR lam).bound) (htgRr : tg ∉ (rightBlock fR lam).readVars)
    (htgdL : tg ∉ domL.fv) (htgdR : tg ∉ domR.fv) {σ : State (Var n)}
    (hES : HExistSeg fL fR lam domL domR (Function.update σ tg 0)) :
    ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → s ≤ dt → ΦL 0 = Function.update σ tg 0 →
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ clk tg (leftBlock fL),
          HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (clk tg (leftBlock fL)).bound →
          ΦL t x = Function.update σ tg 0 x) →
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
      ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
            HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) := by
  intro s ΦL hs0 _ hΦL0 hclkder hclkmask hdomL
  set ν := Function.update σ tg 0 with hν
  have hνtg : ν tg = 0 := Function.update_self tg 0 σ
  have htgclkb : tg ∈ (clk tg (leftBlock fL)).bound := by
    simp only [clk, ODESystem.bound, List.map_append, List.map_cons, List.map_nil]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  -- projected (declocked) left curve
  set ΦL' : ℝ → State (Var n) := fun t => Function.update (ΦL t) tg (ν tg) with hΦL'
  have hL'phys : ∀ t x, x ≠ tg → ΦL' t x = ΦL t x := fun t x hx => Function.update_of_ne hx _ _
  have hΦL'0 : ΦL' 0 = ν := by
    funext x; by_cases hx : x = tg
    · subst hx; simp only [hΦL', Function.update_self, hνtg]
    · rw [hL'phys 0 x hx, hΦL0]
  have hder' : ∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
      HasDerivWithinAt (fun u => ΦL' u p.1) (p.2.eval (ΦL' t)) (Icc 0 s) t := by
    intro t ht p hp
    have hp1 : p.1 ≠ tg := fun hc => htgLb (by rw [← hc]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hfun : (fun u => ΦL' u p.1) = fun u => ΦL u p.1 := by funext u; exact hL'phys u p.1 hp1
    rw [hfun]
    have hev : p.2.eval (ΦL' t) = p.2.eval (ΦL t) :=
      Term.coincidence p.2 (fun y hy => hL'phys t y
        (fun hc => htgLr (by rw [← hc]; exact ⟨p, hp, hy⟩)))
    rw [hev]
    exact hclkder t ht p (List.mem_append_left _ hp)
  have hmask' : ∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL' t x = ν x := by
    intro t ht x hx
    by_cases hxtg : x = tg
    · subst hxtg; simp only [hΦL', Function.update_self]
    · rw [hL'phys t x hxtg]
      refine hclkmask t ht x (fun hc => ?_)
      simp only [clk, ODESystem.bound, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton] at hc
      exact hc.elim (fun h => hx h) (fun h => hxtg h)
  have hdomL' : ∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL' t) := by
    intro t ht
    exact (Formula.coincidence domL (fun y hy => (hL'phys t y
      (fun hc => htgdL (by rw [← hc]; exact hy))).symm)).mp (hdomL t ht)
  obtain ⟨ΦR, hΦR0, hRder, hRmask, hRdom⟩ := hES s ΦL' hs0 hΦL'0 hder' hmask' hdomL'
  -- restore the clock coordinate on the right witness
  set ΦR' : ℝ → State (Var n) := fun t => Function.update (ΦR t) tg (ΦL s tg) with hΦR'
  have hR'phys : ∀ t x, x ≠ tg → ΦR' t x = ΦR t x := fun t x hx => Function.update_of_ne hx _ _
  have hΦLs' : ΦL' s = Function.update (ΦL s) tg (ν tg) := rfl
  refine ⟨ΦR', ?_, ?_, ?_, ?_⟩
  · -- ΦR' 0 = ΦL s
    show Function.update (ΦR 0) tg (ΦL s tg) = ΦL s
    rw [hΦR0, hΦLs']
    funext x; by_cases hx : x = tg
    · subst hx; simp only [Function.update_self]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
  · intro t ht p hp
    have hp1 : p.1 ≠ tg := fun hc => htgRb (by rw [← hc]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hfun : (fun u => ΦR' u p.1) = fun u => ΦR u p.1 := by funext u; exact hR'phys u p.1 hp1
    rw [hfun]
    have hev : p.2.eval (ΦR' t) = p.2.eval (ΦR t) :=
      Term.coincidence p.2 (fun y hy => hR'phys t y
        (fun hc => htgRr (by rw [← hc]; exact ⟨p, hp, hy⟩)))
    rw [hev]; exact hRder t ht p hp
  · intro t ht x hx
    by_cases hxtg : x = tg
    · subst hxtg; simp only [hΦR', Function.update_self]
    · rw [hR'phys t x hxtg, hRmask t ht x hx, hL'phys s x hxtg]
  · intro t ht
    exact (Formula.coincidence domR (fun y hy => (hR'phys t y
      (fun hc => htgdR (by rw [← hc]; exact hy))).symm)).mp (hRdom t ht)

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

/-! ## Cert-sourcing — the per-segment bounded coupling from `cert.segPres` -/

/-- The clock adds `tg` to the bound set, nothing to read vars (`(tg,1)` reads nothing). -/
theorem clk_boundSet (sys : ODESystem (Var n)) (tg : Var n) :
    (clk tg sys).boundSet = sys.boundSet ∪ {tg} := by
  ext x
  simp only [clk, ODESystem.boundSet, ODESystem.bound, List.map_append, List.map_cons,
    List.map_nil, Set.mem_setOf_eq, List.mem_append, List.mem_singleton, Set.mem_union]
  tauto

theorem clk_readVars (sys : ODESystem (Var n)) (tg : Var n) :
    (clk tg sys).readVars = sys.readVars := by
  ext x
  simp only [clk, ODESystem.readVars, Set.mem_setOf_eq, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨p, hp | hp, hpx⟩
    · exact ⟨p, hp, hpx⟩
    · subst hp; simp only [Term.fv, Set.mem_empty_iff_false] at hpx
  · rintro ⟨p, hp, hpx⟩; exact ⟨p, Or.inl hp, hpx⟩

/-- **The per-segment bounded coupling, cert-sourced.** `faModal_ODE_G'_bounded` fed by
`box_joint_to_clocked` (the flow certificate from `cert.segPres`, clock-lifted) and
`hExist_clocked_of_HExistSeg` (the cover's `HExistSeg`, clock-adapted). NO assumed segment `faModal`:
the box `hbox` is `cert.segPres`'s. -/
theorem segment_faModalB_from_cert (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (domL domR : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (hdisj0 : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                       ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (htgLb : tg ∉ (leftBlock fL).bound) (htgLr : tg ∉ (leftBlock fL).readVars)
    (htgRb : tg ∉ (rightBlock fR lam).bound) (htgRr : tg ∉ (rightBlock fR lam).readVars)
    (htgRbs : tg ∉ (rightBlock fR lam).boundSet)
    (htgdL : tg ∉ domL.fv) (htgdR : tg ∉ domR.fv) (htgg : tg ∉ g.fv)
    {σ : State (Var n)}
    (hbox : Formula.sat (Formula.box (Program.ode (leftBlock fL ++ rightBlock fR lam)
        (Formula.and domL domR)) (invLe g)) σ)
    (hES : HExistSeg fL fR lam domL domR (Function.update σ tg 0)) :
    faModalB (Equiv.refl (Var n)) (Program.ode (clk tg (leftBlock fL)) domL)
      (Program.ode (rightBlock fR lam) domR) (invLe g) tg dt (Function.update σ tg 0) := by
  have hrv := clk_readVars (leftBlock fL) tg
  have hbs := clk_boundSet (leftBlock fL) tg
  refine faModal_ODE_G'_bounded (Equiv.refl (Var n)) (clk tg (leftBlock fL)) (rightBlock fR lam)
    domL domR (invLe g) tg dt (Function.update σ tg 0) ?_ ?_ ?_ ?_ ?_ ?_
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · -- hdisj: (clocked-left vars) ⊥ (right vars)
    rw [ODESystem.rename_refl, hbs, hrv]
    have hset : (leftBlock fL).boundSet ∪ {tg} ∪ (leftBlock fL).readVars
        = ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars) ∪ {tg} := by
      ext y; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto
    rw [hset]
    refine Set.disjoint_union_left.mpr ⟨hdisj0, ?_⟩
    rw [Set.disjoint_singleton_left, Set.mem_union]
    exact fun hc => hc.elim htgRbs htgRr
  · -- hφx
    rw [hbs, hrv]
    exact hφL.trans (Set.union_subset_union_left _ Set.subset_union_left)
  · rw [Formula.rename_refl, ODESystem.rename_refl]; exact hφR
  · -- hP2 from cert box, clock-lifted
    rw [ODESystem.rename_refl, Formula.rename_refl]
    have htgdom : tg ∉ (Formula.and domL domR).fv := by
      simp only [Formula.fv, Set.mem_union, not_or]; exact ⟨htgdL, htgdR⟩
    exact box_joint_to_clocked g (leftBlock fL) (rightBlock fR lam) (Formula.and domL domR) tg
      htgLb htgRb htgLr htgRr htgdom htgg hbox
  · -- hExist, clock-adapted from HExistSeg
    simp only [ODESystem.rename_refl, Formula.rename_refl]
    exact hExist_clocked_of_HExistSeg fL fR lam domL domR tg dt htgLb htgLr htgRb htgRr htgdL htgdR
      hES

/-! ## The structural emit — the `Hmulti` discharge -/

/-- **The multi-flow emit (structural, cert-linked).** Per current right mode `q` and invariant
state `σ`, the cover emits the right's mode-switch **sequence** `segs` for one left residence, with:
the sequence aligned to `Gr` (`halign`) and a **declared-edge chain** (`hchain`: `a.2.2.tgt = b.1`
with each `s.2.2 ∈ edgesFrom s.1` — a real `star (rightAutomatonBody)` path, not an arbitrary
sequence), starting at `q` (`hhead`); the carried budget bound `r ≤ |segs|·dt` (`hbudget`); and the
`tg`-freshness/disjointness the coupling assembly needs. No Z3 obligation — the flow certificates come
from `cert` through `RightProjAlign` per seg. -/
def EmitSegs (Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (tg : Var n) (dt : ℝ) : Prop :=
  ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) → Formula.sat (invLe g) σ →
    ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      (∀ {r : ℝ} {Φ : ℝ → State (Var n)},
        ODESol (leftBlock fL0) domL0 σ r Φ → r ≤ (segs.length : ℝ) * dt) ∧
      tg ∉ ((bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))).rename
        (Equiv.refl (Var n))).fv ∧
      (∀ Q ∈ segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom),
        Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
          (Program.vars (clockedSeg (leftBlock fL0) domL0 tg dt)))

/-- **The `Hmulti` discharge (flow segments).** Produces the emit `Hmulti` that
`theorem3_faithful_multi_of_emit` consumes, with each segment's `faModal` drawn from **`cert.segPres`**
(via `segment_faModalB_from_cert`) — not assumed. The per-seg alignment (`fR`/`domR`/`mj`/`HExistSeg`)
is the reused single-flow `RightProjAlign`; the sequence structure is `EmitSegs`. `cert` is
load-bearing: delete it and the box (hence each `faModalB`, hence the `faModal`) is gone. -/
theorem Hmulti_from_cover (Gj Gr : SearchGraph (Var n)) (g : Term (Var n)) (mv : Var n)
    (fL0 : Fin n → Term (Var n)) (domL0 : Formula (Var n)) (lam : Term (Var n)) (tg : Var n) (dt : ℝ)
    (cert : CoverCert Gj g) (hdt : 0 ≤ dt)
    (hmvL0 : mv ∉ (leftBlock fL0).bound) (hg : mv ∉ g.fv)
    (hφL0 : domL0.fv ⊆ (leftBlock fL0).boundSet ∪ (leftBlock fL0).readVars)
    (htgLb : tg ∉ (leftBlock fL0).bound) (htgLr : tg ∉ (leftBlock fL0).readVars)
    (htgdL0 : tg ∉ domL0.fv) (htgg : tg ∉ g.fv)
    (htgRight : ∀ q m, Gr.modeAt q = some m →
      tg ∉ m.sys.bound ∧ tg ∉ m.sys.readVars ∧ tg ∉ m.sys.boundSet ∧ tg ∉ m.dom.fv)
    (hRPA : RightProjAlign Gj Gr g mv fL0 domL0 lam)
    (hemit : EmitSegs Gr g mv fL0 domL0 tg dt) :
    ∀ P ∈ [Program.ode (leftBlock fL0) domL0], ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (invLe g) σ →
      ∃ (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
        (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
        P = Program.ode (leftBlock fL) domL ∧ mv ∉ (leftBlock fL).bound ∧
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ := by
  intro P hP q hqlt σ hmvq hσ
  simp only [List.mem_singleton] at hP; subst hP
  obtain ⟨segs, halign, hchain, hhead, hbudget, htgRbig, hdis⟩ := hemit q hqlt σ hmvq hσ
  refine ⟨fL0, domL0, segs, rfl, hmvL0, halign, hchain, hhead, ?_⟩
  -- assemble the genuine-multi-flow faModal from per-segment cert-sourced couplings
  refine multi_faModal_from_couplings (leftBlock fL0) domL0 g tg dt segs.length htgLb htgLr htgdL0
    htgg hdt _ (List.length_map ..) htgRbig hdis ?_ hσ hbudget
  -- hcouple: each right segment's bounded coupling from cert.segPres
  intro Q hQ σ' hσ'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hQ
  obtain ⟨hmodeAt, _⟩ := halign s hs
  obtain ⟨fR, domR, e, mj, hsys, hdom, _, _, _, hdisj0, hφR, hmj, hjOK, hmjsys, hmjdom, hES⟩ :=
    hRPA s.1 s.2.1 hmodeAt
  obtain ⟨htgRb, htgRr, htgRbs, htgdR⟩ := htgRight s.1 s.2.1 hmodeAt
  rw [hsys] at htgRb htgRr htgRbs
  rw [hdom] at htgdR
  rw [hsys, hdom]
  -- the joint box at σ' from cert.segPres
  have hbox : Formula.sat (Formula.box (Program.ode (leftBlock fL0 ++ rightBlock fR lam)
      (Formula.and domL0 domR)) (invLe g)) σ' := by
    rw [sat_box]; intro ω hω; rw [sat_invLe]
    have hBL := cert.segPres s.1 mj hmj hjOK σ' ((sat_invLe g σ').mp hσ')
    rw [hmjsys, hmjdom] at hBL
    exact hBL ω (by rw [← jointSys_split] at hω; exact hω)
  exact segment_faModalB_from_cert g fL0 fR lam domL0 domR tg dt hdisj0 hφL0 hφR
    htgLb htgLr htgRb htgRr htgRbs htgdL0 htgdR htgg hbox (hES (Function.update σ' tg 0))

end RelCertifier
