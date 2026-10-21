/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The clocked right automaton: response layer and clock erasure

The right automaton of the general chain is unclocked (`modeStep`/`rightAutomatonBody`,
`JointBridge.lean`): one cycle may flow arbitrarily long in a mode, so the mechanized
Theorem 3 ranges over more right runs than the paper's Eq. (1) allows. Its clocked twin
(`modeStepC`/`rightAutomatonBodyC`, `ClockedTop.lean`) replaces the flow by
`clockedSeg sys dom tg dt = tg := 0 ; {sys, tg' = 1 & dom} ; ?(tg ≤ dt)`. This file is the
response layer of that twin (`docs/CLOCKED-RIGHT-SCOPE.md`, W1) plus the clock-erasure
lemma of W4. Everything is additive; the unclocked layer is untouched.

* `sem_clockedSeg_of_flow_le` / `sem_clockedSeg_of_odeSol`: dressing a flow of duration
  `r ≤ dt` with the clock (the `[0, r]` generalization of `sem_clockedSeg_of_flow`), stated
  so the producers of the chain, which hold `ODESol … r Φ` and a bound on the duration,
  call it directly.
* `gsegC`, `sem_gsegC`, `RRespPC`, `rrespPC_stop`/`_mono`/`_step`: the clocked guarded
  segment and response relation, mirrors of `gseg`/`RRespP` (`GuardedSwitch.lean`,
  `GuardedClimb.lean`).
* `modeStepC_sem`, `guarded_seg_stepC`, `guarded_rights_bridgeC`: a chain of clocked
  segments with legal switches is a run of `star (rightAutomatonBodyC G mv tg dt)`.
* Footprints: `bv_rightAutomatonBodyC`, `vars_modeStepCG_sub`, `vars_bodyCG_sub`,
  `fv_bodyCG_sub`, `notMem_bv_rightAutomatonBodyC` (the clocked body touches `mv`, `tg` and
  the right coordinates).
* Clock erasure: `sem_ode_of_clockedSeg` (a clocked run, with the clock overwritten by any
  constant, is a run of the unclocked ode: `tg` is evolved by nothing but its own equation and
  read by nothing) and `star_bodyC_to_body` (a run of the clocked star is, off `tg`, a run
  of the unclocked star), the converse of the dressing direction.

Switch tests are evaluated at the END state of the clocked segment, which carries
`tg = r` (the segment's duration); since every guard is `tg`-free in the intended use
(`GuardsFresh G tg`), this is the same as evaluating at the unclocked end state.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.GuardedClimb

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## Clock hygiene, split and lifted -/

/-- `x ∉ FV(ode sys dom)` is the conjunction of the three hygiene facts the clocked-segment
lemmas take: `x` is evolved by no equation, read by no right-hand side, absent from the
domain. The producers hold the left-hand side (`hfresh`-style); the segment lemmas take the
right-hand side (`sem_clockedSeg_of_flow`-style). -/
theorem notMem_ode_fv_iff (sys : ODESystem (Var n)) (dom : Formula (Var n)) (x : Var n) :
    x ∉ (Program.ode sys dom).fv ↔
      x ∉ sys.bound ∧ (∀ p ∈ sys, x ∉ (p.2 : Term (Var n)).fv) ∧ x ∉ dom.fv := by
  constructor
  · intro h
    simp only [Program.fv, ODESystem.boundSet, ODESystem.readVars, Set.mem_union,
      Set.mem_setOf_eq, not_or, not_exists, not_and] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩ h
    simp only [Program.fv, ODESystem.boundSet, ODESystem.readVars, Set.mem_union,
      Set.mem_setOf_eq] at h
    rcases h with (h | h) | h
    · exact h1 h
    · obtain ⟨p, hp, hx⟩ := h
      exact h2 p hp hx
    · exact h3 h

/-- Freshness of `x ≠ tg` for `ode sys dom` lifts to the clocked system: `clk` only adds the
equation `tg' = 1`, which binds `tg` and reads nothing. -/
theorem notMem_ode_clk_fv {sys : ODESystem (Var n)} {dom : Formula (Var n)} {tg x : Var n}
    (hx : x ≠ tg) (hfv : x ∉ (Program.ode sys dom).fv) :
    x ∉ (Program.ode (DLCalTiming.clk tg sys) dom).fv := by
  intro h
  simp only [Program.fv, Set.mem_union] at h
  rcases h with (h | h) | h
  · rcases clk_boundSet_sub tg sys h with h | h
    · exact hfv (Or.inl (Or.inl h))
    · exact hx (Set.mem_singleton_iff.mp h)
  · exact hfv (Or.inl (Or.inr (clk_readVars_sub tg sys h)))
  · exact hfv (Or.inr h)

/-! ## Dressing a flow of duration `r ≤ dt` with the clock -/

/-- **Dressing, `[0, r]` with `r ≤ dt`.** If `Φ` solves `sys` on `[0, r]` from a state agreeing
with `μ` off `tg` (with `tg` outside `sys`'s bound, terms, and domain), the dressed flow
`Φ t [tg ↦ t]` is a `clockedSeg sys dom tg dt` run from `μ` to `Φ r [tg ↦ r]`; the final clock
`r ≤ dt` passes the cap test. This is `sem_clockedSeg_of_flow` with the duration decoupled
from the cap. -/
theorem sem_clockedSeg_of_flow_le (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (tg : Var n) (dt : ℝ) (μ : State (Var n)) (Φ : ℝ → State (Var n)) {r : ℝ}
    (hr0 : 0 ≤ r) (hrdt : r ≤ dt)
    (htgb : tg ∉ sys.bound) (htgt : ∀ p ∈ sys, tg ∉ (p.2 : Term (Var n)).fv)
    (htgdom : tg ∉ dom.fv)
    (hΦ0 : ∀ x, x ≠ tg → Φ 0 x = μ x)
    (hder : ∀ t ∈ Icc (0 : ℝ) r, ∀ p ∈ sys,
        HasDerivWithinAt (fun u => Φ u p.1) (Term.eval p.2 (Φ t)) (Icc 0 r) t)
    (hmask : ∀ t ∈ Icc (0 : ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = Φ 0 x)
    (hstay : ∀ t ∈ Icc (0 : ℝ) r, Formula.sat dom (Φ t)) :
    Program.sem (clockedSeg sys dom tg dt) μ (Function.update (Φ r) tg r) := by
  set Φc : ℝ → State (Var n) := fun t => Function.update (Φ t) tg t with hΦc
  have hagree : ∀ t x, x ≠ tg → Φc t x = Φ t x := by
    intro t x hx
    simp only [hΦc, Function.update_of_ne hx]
  have hΦc0 : Φc 0 = Function.update μ tg 0 := by
    funext x
    by_cases hx : x = tg
    · subst hx; simp [hΦc]
    · rw [hagree 0 x hx, hΦ0 x hx, Function.update_of_ne hx]
  refine ⟨Function.update μ tg 0,
    ⟨by simp only [Term.eval, Function.update_self],
     fun y hy => Function.update_of_ne hy _ _⟩, ?_⟩
  refine ⟨Φc r, ?_, ⟨rfl, ?_⟩⟩
  · -- the clocked ode run
    refine ⟨r, Φc, hr0, hΦc0, rfl, ?_, ?_, ?_⟩
    · -- derivatives: original pairs by agreement, the clock at rate 1
      intro t ht p hp
      simp only [DLCalTiming.clk, List.mem_append] at hp
      rcases hp with hp | hp
      · have hne : p.1 ≠ tg := fun h => htgb (h ▸ List.mem_map_of_mem hp)
        have hfun : (fun u => Φc u p.1) = (fun u => Φ u p.1) := by
          funext u; exact hagree u p.1 hne
        rw [hfun]
        have heval : Term.eval p.2 (Φc t) = Term.eval p.2 (Φ t) := by
          refine Term.coincidence p.2 ?_
          intro x hx
          exact hagree t x (fun h => htgt p hp (h ▸ hx))
        rw [heval]
        exact hder t ht p hp
      · simp only [List.mem_singleton] at hp
        subst hp
        have hfun : (fun u => Φc u tg) = fun u => u := by
          funext u; simp [hΦc]
        rw [hfun]
        simp only [Term.eval]
        exact (hasDerivAt_id t).hasDerivWithinAt
    · -- mask
      intro t ht x hx
      simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      push Not at hx
      obtain ⟨hxs, hxtg⟩ := hx
      rw [hagree t x hxtg, hmask t ht x (by simpa [ODESystem.bound] using hxs), hΦ0 x hxtg,
        Function.update_of_ne hxtg]
    · -- staying (tg-free domain)
      intro t ht
      refine (Formula.coincidence dom ?_).mp (hstay t ht)
      intro x hx
      exact (hagree t x (fun h => htgdom (h ▸ hx))).symm
  · -- the clock cap test
    simp only [sat_clkGuard, hΦc, Function.update_self]
    exact hrdt

/-- **Dressing from an `ODESol`.** The form the chain's producers call: they hold
`ODESol sys dom ν r Φ` and a time `s ∈ [0, r]` with `s ≤ dt` (the span bound `hspan`, or
`epsR` itself). The restricted solution, dressed with the clock, is a clocked run from `ν`
to `Φ s [tg ↦ s]`. Replaces `DLCalTiming.sem_ode_restrict H hs hsr` at those sites. -/
theorem sem_clockedSeg_of_odeSol (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (tg : Var n) (dt : ℝ) {ν : State (Var n)} {r s : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol sys dom ν r Φ) (hs : 0 ≤ s) (hsr : s ≤ r) (hsdt : s ≤ dt)
    (htgb : tg ∉ sys.bound) (htgt : ∀ p ∈ sys, tg ∉ (p.2 : Term (Var n)).fv)
    (htgdom : tg ∉ dom.fv) :
    Program.sem (clockedSeg sys dom tg dt) ν (Function.update (Φ s) tg s) := by
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 r := fun u hu => ⟨hu.1, hu.2.trans hsr⟩
  refine sem_clockedSeg_of_flow_le sys dom tg dt ν Φ hs hsdt htgb htgt htgdom ?_ ?_ ?_ ?_
  · intro x _; rw [H.hΦ0]
  · intro t ht p hp; exact (H.hder t (hsub ht) p hp).mono hsub
  · intro t ht x hx; rw [H.hmask t (hsub ht) x hx, H.hΦ0]
  · intro t ht; exact H.hdom t (hsub ht)

/-- `sem_clockedSeg_of_odeSol` with the hygiene packaged as `tg ∉ FV(ode sys dom)`. -/
theorem sem_clockedSeg_of_odeSol_fv (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (tg : Var n) (dt : ℝ) {ν : State (Var n)} {r s : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol sys dom ν r Φ) (hs : 0 ≤ s) (hsr : s ≤ r) (hsdt : s ≤ dt)
    (htg : tg ∉ (Program.ode sys dom).fv) :
    Program.sem (clockedSeg sys dom tg dt) ν (Function.update (Φ s) tg s) := by
  obtain ⟨htgb, htgt, htgdom⟩ := (notMem_ode_fv_iff sys dom tg).mp htg
  exact sem_clockedSeg_of_odeSol sys dom tg dt H hs hsr hsdt htgb htgt htgdom

/-! ## Framing the mode variable through a clocked segment -/

/-- Clocked-segment frame-lift: updating the fresh `mv ≠ tg` on both endpoints preserves a
`clockedSeg` run (`sem_ode_frame_upd` for the clocked flow; the reset and the cap test
touch only `tg`). The freshness premise is the UNCLOCKED one the chain already holds. -/
theorem sem_clockedSeg_frame_upd {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {tg : Var n} {dt : ℝ} (mv : Var n) (c : ℝ) (hmvtg : mv ≠ tg)
    (hfv : mv ∉ (Program.ode sys dom).fv) {ν κ : State (Var n)}
    (h : Program.sem (clockedSeg sys dom tg dt) ν κ) :
    Program.sem (clockedSeg sys dom tg dt) (update ν mv c) (update κ mv c) := by
  obtain ⟨ν₁, ⟨hν₁tg, hν₁⟩, ν₂, hode, hκ, hg⟩ := h
  subst hκ
  refine ⟨update ν₁ mv c, ⟨?_, ?_⟩, update ν₂ mv c, ?_, rfl, ?_⟩
  · rw [Function.update_of_ne hmvtg.symm, hν₁tg]
    simp only [Term.eval]
  · intro y hy
    by_cases hymv : y = mv
    · subst hymv; simp only [Function.update_self]
    · rw [Function.update_of_ne hymv, Function.update_of_ne hymv, hν₁ y hy]
  · exact sem_ode_frame_upd mv c (notMem_ode_clk_fv hmvtg hfv) hode
  · rw [sat_clkGuard] at hg ⊢
    rwa [Function.update_of_ne hmvtg.symm]

/-! ## The clocked guarded segment and response relation -/

/-- One clocked guarded segment: the clocked flow of the segment's mode (reset, flow under
`tg' = 1`, cap `?(tg ≤ dt)`), then the switch test of its edge. The clocked twin of `gseg`. -/
def gsegC (tg : Var n) (dt : ℝ) (s : ℕ × RMode (Var n) × REdge (Var n)) : Program (Var n) :=
  Program.seq (clockedSeg s.2.1.sys s.2.1.dom tg dt) (Program.test s.2.2.guard)

/-- A `gsegC` run is a clocked flow followed by a legal switch at ITS end state (which carries
`tg` = the flow's duration). -/
theorem sem_gsegC {tg : Var n} {dt : ℝ} {s : ℕ × RMode (Var n) × REdge (Var n)}
    {ν μ : State (Var n)} :
    Program.sem (gsegC tg dt s) ν μ ↔
      Program.sem (clockedSeg s.2.1.sys s.2.1.dom tg dt) ν μ ∧ SwitchLegal s.2.2 μ := by
  constructor
  · rintro ⟨κ, hflow, hκ, hg⟩
    subst hκ
    exact ⟨hflow, hg⟩
  · rintro ⟨hflow, hg⟩
    exact ⟨μ, hflow, rfl, hg⟩

/-- `RRespP` over clocked segments: from the right state `ν` in mode `q`, a chain of declared
segments, each a clocked flow of its mode followed by a legal switch along a declared edge,
ending in a state where `P` of the final mode holds. -/
def RRespPC (G : SearchGraph (Var n)) (tg : Var n) (dt : ℝ) (q : ℕ)
    (P : ℕ → State (Var n) → Prop) (ν : State (Var n)) : Prop :=
  ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
    (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
    List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
    (∀ s, segs.head? = some s → s.1 = q) ∧
    ∃ μ, Program.sem (bigSeq (segs.map (gsegC tg dt))) ν μ ∧ P (qfOf segs q) μ

theorem rrespPC_mono {G : SearchGraph (Var n)} {tg : Var n} {dt : ℝ} {q : ℕ}
    {P Q : ℕ → State (Var n) → Prop} {ν : State (Var n)}
    (himp : ∀ q' μ, P q' μ → Q q' μ) (h : RRespPC G tg dt q P ν) : RRespPC G tg dt q Q ν := by
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := h
  exact ⟨segs, ha, hc, hh, μ, hrun, himp _ μ hp⟩

/-- **No step**: the predicate already holds for the current mode. -/
theorem rrespPC_stop {G : SearchGraph (Var n)} {tg : Var n} {dt : ℝ} {q : ℕ}
    {P : ℕ → State (Var n) → Prop} {ν : State (Var n)} (h : P q ν) : RRespPC G tg dt q P ν := by
  refine ⟨[], by simp, by simp, by simp, ν, ?_, by simpa [qfOf] using h⟩
  show Program.sem (Program.test Formula.tt) ν ν
  exact ⟨rfl, trivial⟩

/-- **One clocked guarded step**: a clocked flow of the current mode `q` from `ν` to `κ`
(so `κ tg` is the flow's duration, `≤ dt`), a switch along the declared edge `e` legal at
`κ`, then a response from the entered mode. The producers obtain `hflow` from
`sem_clockedSeg_of_odeSol`. -/
theorem rrespPC_step {G : SearchGraph (Var n)} {tg : Var n} {dt : ℝ} {q : ℕ}
    {m : RMode (Var n)} {e : REdge (Var n)} {P : ℕ → State (Var n) → Prop}
    {ν κ : State (Var n)}
    (hm : G.modeAt q = some m) (he : e ∈ G.edgesFrom q)
    (hflow : Program.sem (clockedSeg m.sys m.dom tg dt) ν κ) (hleg : SwitchLegal e κ)
    (hrest : RRespPC G tg dt e.tgt P κ) : RRespPC G tg dt q P ν := by
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
    exact ⟨κ, sem_gsegC.mpr ⟨hflow, hleg⟩, hrun⟩
  · rw [qfOf_cons]
    exact hp

/-! ## The clocked bridge: legal switches make a run of the clocked automaton -/

/-- A single clocked automaton step: clocked flow `ν → μ` at mode `q`, then declared edge
`e` (guard satisfied at the mode-updated end state) to mode `e.tgt`, the mode variable
tracking `q ↦ e.tgt`. Mirror of `modeStep_sem`; the freshness premise is the unclocked
`mv ∉ FV(ode)` plus `mv ≠ tg`. -/
theorem modeStepC_sem (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ) (q : ℕ)
    (m : RMode (Var n)) (hmvtg : mv ≠ tg) (hfv : mv ∉ (Program.ode m.sys m.dom).fv)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) {ν μ : State (Var n)}
    (hflow : Program.sem (clockedSeg m.sys m.dom tg dt) ν μ)
    (hg : Formula.sat e.guard (update μ mv (q : ℝ))) :
    Program.sem (modeStepC G mv tg dt q m) (update ν mv (q : ℝ)) (update μ mv (e.tgt : ℝ)) := by
  refine ⟨update ν mv (q : ℝ), ⟨rfl, ?_⟩, ⟨update μ mv (q : ℝ), ?_, ?_⟩⟩
  · -- test (mode = q)
    simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, Function.update_self]
  · -- clocked flow, mode framed
    exact sem_clockedSeg_frame_upd mv (q : ℝ) hmvtg hfv hflow
  · -- declared-edge branch: (test guard ; mv := tgt)
    refine bigChoiceP_sem_of_mem (List.mem_map_of_mem hef) ?_
    refine ⟨update μ mv (q : ℝ), ⟨rfl, hg⟩, ?_, ?_⟩
    · simp only [Term.eval, Function.update_self]
    · intro y hy; simp only [Function.update_of_ne hy]

/-- One clocked flow at a declared mode followed by a LEGAL switch along a declared edge is
one step of the clocked guarded automaton. Mirror of `guarded_seg_step`. -/
theorem guarded_seg_stepC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ) (q : ℕ)
    (m : RMode (Var n)) (hmvtg : mv ≠ tg) (hfv : mv ∉ (Program.ode m.sys m.dom).fv)
    {e : REdge (Var n)} (hm : G.modeAt q = some m) (he : e ∈ G.edgesFrom q)
    (hgf : mv ∉ e.guard.fv)
    {ν κ : State (Var n)} (hflow : Program.sem (clockedSeg m.sys m.dom tg dt) ν κ)
    (hleg : SwitchLegal e κ) :
    Program.sem (Program.star (rightAutomatonBodyC G mv tg dt))
      (Function.update ν mv (q : ℝ)) (Function.update κ mv (e.tgt : ℝ)) := by
  have hg : Formula.sat e.guard (Function.update κ mv (q : ℝ)) :=
    (Formula.coincidence e.guard (fun y hy =>
      (Function.update_of_ne (fun hc => hgf (by rw [← hc]; exact hy)) _ _).symm)).mp hleg
  have hstep := modeStepC_sem G mv tg dt q m hmvtg hfv he hflow hg
  have hbody : Program.sem (rightAutomatonBodyC G mv tg dt)
      (Function.update ν mv (q : ℝ)) (Function.update κ mv (e.tgt : ℝ)) := by
    refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
    · exact List.mem_range.mpr (by
        have := hm; simp only [SearchGraph.modeAt] at this
        exact List.getElem?_eq_some_iff.mp this |>.1)
    · rw [hm]; rfl
  exact Relation.ReflTransGen.head hbody Relation.ReflTransGen.refl

/-- **The clocked guarded bridge, final mode pinned.** A run of `bigSeq (segs.map (gsegC tg dt))`
(declared modes, declared chained edges, every switch legal) is a run of the clocked
automaton's star, the mode variable going from `q0` to `qfOf segs q0`. Mirror of
`guarded_rights_bridge`; the only new premise is `mv ≠ tg`. -/
theorem guarded_rights_bridgeC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (hmvtg : mv ≠ tg)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv) :
    ∀ (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
      (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) →
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs →
      ∀ (q0 : ℕ), ∀ {ν μ : State (Var n)},
        (∀ s, segs.head? = some s → s.1 = q0) →
        Program.sem (bigSeq (segs.map (gsegC tg dt))) ν μ →
        Program.sem (Program.star (rightAutomatonBodyC G mv tg dt))
          (Function.update ν mv (q0 : ℝ)) (Function.update μ mv ((qfOf segs q0) : ℝ)) := by
  intro segs
  induction segs with
  | nil =>
      intro _ _ q0 _ _ _ hrun
      rw [List.map_nil, bigSeq, sem_test] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Relation.ReflTransGen.refl
  | cons s rest ih =>
      intro halign hchain q0 ν μ hstart hrun
      have hq0 : s.1 = q0 := hstart s rfl
      subst hq0
      simp only [List.map_cons, bigSeq] at hrun
      obtain ⟨κ, hseg, hrest⟩ := hrun
      obtain ⟨hflow, hleg⟩ := sem_gsegC.mp hseg
      obtain ⟨hm, he⟩ := halign s (List.mem_cons_self ..)
      have hfirst := guarded_seg_stepC G mv tg dt s.1 s.2.1 hmvtg (hfresh s.1 s.2.1 hm) hm he
        (hgf s.1 s.2.2 he) hflow hleg
      have htailstart : ∀ t, rest.head? = some t → t.1 = s.2.2.tgt := by
        intro t ht
        rcases rest with - | ⟨r, rs⟩
        · exact absurd ht (by simp)
        · simp only [List.head?_cons, Option.some.injEq] at ht
          subst ht; exact hchain.rel.symm
      have htail := ih (fun t ht => halign t (List.mem_cons_of_mem s ht))
        hchain.of_cons s.2.2.tgt htailstart hrest
      rw [qfOf_cons]
      exact Relation.ReflTransGen.trans hfirst htail

/-- `RRespPC` with its predicate discharged into a run of the clocked automaton's star: the
mode variable goes from `q` to the chain's final mode, at which `P` holds. -/
theorem rrespPC_run (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ) (hmvtg : mv ≠ tg)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv) {q : ℕ} {P : ℕ → State (Var n) → Prop} {ν : State (Var n)}
    (h : RRespPC G tg dt q P ν) :
    ∃ (qf : ℕ) (μ : State (Var n)), Program.sem (Program.star (rightAutomatonBodyC G mv tg dt))
      (Function.update ν mv (q : ℝ)) (Function.update μ mv (qf : ℝ)) ∧ P qf μ := by
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := h
  exact ⟨qfOf segs q, μ, guarded_rights_bridgeC G mv tg dt hmvtg hfresh hgf segs ha hc q hh hrun,
    hp⟩

/-! ## Footprints of the clocked automaton -/

/-- A bound variable of a `bigChoiceP` is bound by one of its members. -/
theorem bv_mem_bigChoiceP {ps : List (Program (Var n))} {x : Var n}
    (h : x ∈ (bigChoiceP ps).bv) : ∃ q ∈ ps, x ∈ q.bv := by
  induction ps with
  | nil => simp [bigChoiceP, Program.bv] at h
  | cons a as ih =>
      rcases h with h | h
      · exact ⟨a, List.mem_cons_self, h⟩
      · obtain ⟨q, hq, hx⟩ := ih h; exact ⟨q, List.mem_cons_of_mem _ hq, hx⟩

/-- A clocked segment binds its clock and the system's evolving variables. -/
theorem bv_clockedSeg_sub (sys : ODESystem (Var n)) (dom : Formula (Var n)) (tg : Var n)
    (dt : ℝ) : (clockedSeg sys dom tg dt).bv ⊆ {tg} ∪ sys.boundSet := by
  intro x hx
  simp only [clockedSeg, Program.bv, Set.union_empty, Set.mem_union] at hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · rcases clk_boundSet_sub tg sys hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx

/-- **The clocked body binds only `mv`, `tg` and right coordinates.** Mirror of
`bv_rightAutomatonBody` with the clock added. -/
theorem bv_rightAutomatonBodyC {G : SearchGraph (Var n)} {mv tg x : Var n} {dt : ℝ}
    (hsys : ∀ q m, G.modeAt q = some m → m.sys.boundSet ⊆ range Rv)
    (h : x ∈ (rightAutomatonBodyC G mv tg dt).bv) : x = mv ∨ x = tg ∨ x ∈ range Rv := by
  obtain ⟨st, hst, hx⟩ := bv_mem_bigChoiceP h
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hst
  obtain ⟨q, -, m, hm, rfl⟩ := hst
  simp only [modeStepC, Program.bv, Set.empty_union, Set.mem_union] at hx
  rcases hx with hx | hx
  · rcases bv_clockedSeg_sub _ _ _ _ hx with hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (hsys q m hm hx))
  · obtain ⟨e, he, hxe⟩ := bv_mem_bigChoiceP hx
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp he
    simp only [Program.bv, Set.empty_union, Set.mem_singleton_iff] at hxe
    exact Or.inl hxe

/-- A clocked mode step touches `mv`, `tg`, the mode's own footprint and the outgoing
guards'. Mirror of `vars_modeStepG_sub` (the settling-model precedent is
`vars_modeStepC_sub`). -/
theorem vars_modeStepCG_sub (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ) (q : ℕ)
    (m : RMode (Var n)) (S : Set (Var n))
    (hg : ∀ e ∈ G.edgesFrom q, e.guard.fv ⊆ S) :
    Program.vars (modeStepC G mv tg dt q m)
      ⊆ {mv, tg} ∪ (m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv) ∪ S := by
  intro x hx
  rcases vars_seq_sub _ _ hx with hx | hx
  · rw [vars_test_eq] at hx
    simp only [modeIs, Formula.fv, Term.fv] at hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact absurd hx (by simp)
  · rcases vars_seq_sub _ _ hx with hx | hx
    · rcases vars_clockedSeg_sub _ _ _ _ hx with ((hx | hx) | hx) | hx
      · exact Or.inl (Or.inl (Or.inr hx))
      · exact Or.inl (Or.inr (Or.inl (Or.inl hx)))
      · exact Or.inl (Or.inr (Or.inl (Or.inr hx)))
      · exact Or.inl (Or.inr (Or.inr hx))
    · refine vars_bigChoiceP_sub _ _ ?_ hx
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨e, hef, rfl⟩ := hp
      intro y hy
      rcases vars_seq_sub _ _ hy with hy | hy
      · rw [vars_test_eq] at hy
        exact Or.inr (hg e hef hy)
      · rcases vars_assign_sub mv _ hy with hy | hy
        · exact Or.inl (Or.inl (Or.inl hy))
        · exact absurd hy (by simp [Term.fv])

/-- **The clocked right automaton touches only `mv`, `tg` and right coordinates**, given
that the modes' footprints and the declared guards are right-side. Mirror of
`vars_bodyG_sub`. -/
theorem vars_bodyCG_sub (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    Program.vars (rightAutomatonBodyC G mv tg dt) ⊆ {mv, tg} ∪ range Rv := by
  refine vars_bigChoiceP_sub _ _ ?_
  intro p hp
  simp only [List.mem_filterMap, List.mem_range] at hp
  obtain ⟨q, -, hq⟩ := hp
  rcases hm : G.modeAt q with _ | m
  · rw [hm] at hq; simp at hq
  · rw [hm] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    intro x hx
    rcases vars_modeStepCG_sub G mv tg dt q m (range Rv) (hgR q) hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (hRv q m hm hx)
    · exact Or.inr hx

/-- The free variables of the clocked body: `mv`, `tg` and right coordinates. -/
theorem fv_bodyCG_sub (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    Program.fv (rightAutomatonBodyC G mv tg dt) ⊆ {mv, tg} ∪ range Rv :=
  fun _ hx => vars_bodyCG_sub G mv tg dt hgR hRv (Or.inl hx)

/-- The clocked counterpart of `notMem_bv_rightAutomatonBody_G`: a variable other than
`mv`, `tg` and the right coordinates is not bound by the clocked body. -/
theorem notMem_bv_rightAutomatonBodyC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (x : Var n) (hx : x ≠ mv) (hxtg : x ≠ tg) (hxR : x ∉ range Rv) (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    x ∉ (rightAutomatonBodyC G mv tg dt).bv := by
  intro h
  have hv : x ∈ Program.vars (rightAutomatonBodyC G mv tg dt) := Or.inr h
  rcases vars_bodyCG_sub G mv tg dt hgR hRv hv with hx' | hx'
  · rcases hx' with hx' | hx'
    · exact hx hx'
    · exact hxtg (Set.mem_singleton_iff.mp hx')
  · exact hxR hx'

/-! ## Clock erasure (W4): a clocked run is an unclocked run off `tg` -/

/-- **Erasing the clock from one segment.** A `clockedSeg sys dom tg dt` run `ν → κ`, with the
clock overwritten by any constant `c` at both ends, is a run of the unclocked `ode sys dom`:
the projected trajectory `Φ t [tg ↦ c]` solves `sys` because `tg` is evolved by no equation of
`sys` and read by no right-hand side or domain (the converse of `sem_clockedSeg_of_flow`;
the cap test is simply dropped). -/
theorem sem_ode_of_clockedSeg {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {tg : Var n} {dt : ℝ} {ν κ : State (Var n)} (c : ℝ)
    (htgb : tg ∉ sys.bound) (htgt : ∀ p ∈ sys, tg ∉ (p.2 : Term (Var n)).fv)
    (htgdom : tg ∉ dom.fv)
    (h : Program.sem (clockedSeg sys dom tg dt) ν κ) :
    Program.sem (Program.ode sys dom) (update ν tg c) (update κ tg c) := by
  obtain ⟨ν₁, ⟨-, hν₁⟩, ν₂, ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩, hκ, -⟩ := h
  subst hκ
  set Ψ : ℝ → State (Var n) := fun t => update (Φ t) tg c with hΨ
  have hagree : ∀ t x, x ≠ tg → Ψ t x = Φ t x := by
    intro t x hx
    simp only [hΨ, Function.update_of_ne hx]
  refine ⟨r, Ψ, hr, ?_, ?_, ?_, ?_, ?_⟩
  · -- start: `Φ 0 = ν₁ = ν[tg ↦ 0]`, so `Ψ 0 = ν[tg ↦ c]`
    funext x
    by_cases hx : x = tg
    · subst hx; simp [hΨ]
    · rw [hagree 0 x hx, hΦ0, hν₁ x hx, Function.update_of_ne hx]
  · -- end
    funext x
    by_cases hx : x = tg
    · subst hx; simp [hΨ]
    · rw [hagree r x hx, hΦr, Function.update_of_ne hx]
  · -- derivatives of the original pairs, by agreement off `tg`
    intro t ht p hp
    have hne : p.1 ≠ tg := fun h => htgb (h ▸ List.mem_map_of_mem hp)
    have hfun : (fun u => Ψ u p.1) = (fun u => Φ u p.1) := by
      funext u; exact hagree u p.1 hne
    rw [hfun]
    have heval : Term.eval p.2 (Ψ t) = Term.eval p.2 (Φ t) := by
      refine Term.coincidence p.2 ?_
      intro x hx
      exact hagree t x (fun h => htgt p hp (h ▸ hx))
    rw [heval]
    have hp' : p ∈ DLCalTiming.clk tg sys := by
      unfold DLCalTiming.clk; exact List.mem_append_left _ hp
    exact hder t ht p hp'
  · -- mask: `tg` is pinned to `c`; the others were masked by the clocked system
    intro t ht x hx
    by_cases hxtg : x = tg
    · subst hxtg; simp [hΨ]
    · have hx' : x ∉ (DLCalTiming.clk tg sys).bound := by
        intro hmem
        simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with hmem | hmem
        · exact hx (by simpa [ODESystem.bound] using hmem)
        · exact hxtg hmem
      rw [hagree t x hxtg, Function.update_of_ne hxtg, hmask t ht x hx', hν₁ x hxtg]
  · -- domain (tg-free)
    intro t ht
    refine (Formula.coincidence dom ?_).mp (hdom t ht)
    intro x hx
    exact (hagree t x (fun h => htgdom (h ▸ hx))).symm

/-- **Erasing the clock from one body step.** A `rightAutomatonBodyC` step `ν → κ`, started
instead from any `ν'` agreeing with `ν` off `tg`, is matched by a `rightAutomatonBody` step
`ν' → κ'` with `κ'` agreeing with `κ` off `tg`. Hygiene: `mv ≠ tg`, `tg` is fresh for every
mode's flow and for every declared guard. -/
theorem bodyC_to_body_step (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (hmvtg : mv ≠ tg)
    (hfreshT : ∀ q m, G.modeAt q = some m → tg ∉ (Program.ode m.sys m.dom).fv)
    (hgfT : GuardsFresh G tg) {ν κ : State (Var n)}
    (h : Program.sem (rightAutomatonBodyC G mv tg dt) ν κ) (ν' : State (Var n))
    (hν' : ∀ x, x ≠ tg → ν' x = ν x) :
    ∃ κ', Program.sem (rightAutomatonBody G mv) ν' κ' ∧ ∀ x, x ≠ tg → κ' x = κ x := by
  obtain ⟨p, hp, hrun⟩ := bigChoiceP_sem_forward h
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, m, hm, rfl⟩ := hp
  obtain ⟨ν₀, ⟨hν₀, hmode⟩, κ₁, hflow, hsw⟩ := hrun
  subst hν₀
  obtain ⟨p', hp', hsw'⟩ := bigChoiceP_sem_forward hsw
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp'
  obtain ⟨κ₂, ⟨hκ₂, hg⟩, hκmv, hκfr⟩ := hsw'
  subst hκ₂
  obtain ⟨htgb, htgt, htgdom⟩ := (notMem_ode_fv_iff _ _ _).mp (hfreshT q m hm)
  have hode := sem_ode_of_clockedSeg (ν' tg) htgb htgt htgdom hflow
  have hν'eq : update ν tg (ν' tg) = ν' := by
    funext x
    by_cases hx : x = tg
    · subst hx; simp
    · rw [Function.update_of_ne hx, hν' x hx]
  rw [hν'eq] at hode
  have hstep : Program.sem (modeStep G mv q m) ν'
      (update (update κ₁ tg (ν' tg)) mv (e.tgt : ℝ)) := by
    refine ⟨ν', ⟨rfl, ?_⟩, update κ₁ tg (ν' tg), hode, ?_⟩
    · -- mode test at `ν'` (`mv ≠ tg`)
      simp only [modeIs, Formula.sat, CompOp.interp, Term.eval] at hmode ⊢
      rw [hν' mv hmvtg]; exact hmode
    · refine bigChoiceP_sem_of_mem (List.mem_map_of_mem he) ?_
      refine ⟨update κ₁ tg (ν' tg), ⟨rfl, ?_⟩, ?_, ?_⟩
      · -- the guard is `tg`-free
        refine (Formula.coincidence e.guard ?_).mp hg
        intro x hx
        have hx' : x ≠ tg := fun h => hgfT q e he (h ▸ hx)
        rw [Function.update_of_ne hx']
      · simp only [Term.eval, Function.update_self]
      · intro y hy; simp only [Function.update_of_ne hy]
  refine ⟨update (update κ₁ tg (ν' tg)) mv (e.tgt : ℝ), ?_, ?_⟩
  · exact bigChoiceP_sem_of_mem
      (List.mem_filterMap.mpr ⟨q, List.mem_range.mpr hq, by rw [hm]; rfl⟩) hstep
  · intro x hx
    by_cases hxmv : x = mv
    · rw [hxmv, Function.update_self, hκmv]
      simp only [Term.eval]
    · rw [Function.update_of_ne hxmv, Function.update_of_ne hx, hκfr x hxmv]

/-- **Clock erasure for the star.** A run of the clocked automaton's star is, off `tg`, a run
of the unclocked automaton's star from the same state: fewer right runs are admitted with the
clock, so a claim over the clocked body implies the claim over the unclocked one, and the
refutations of the unclocked claim transfer by contraposition. The converse direction of the
dressing lemmas. -/
theorem star_bodyC_to_body (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (hmvtg : mv ≠ tg)
    (hfreshT : ∀ q m, G.modeAt q = some m → tg ∉ (Program.ode m.sys m.dom).fv)
    (hgfT : GuardsFresh G tg) {ν μ : State (Var n)}
    (h : Program.sem (Program.star (rightAutomatonBodyC G mv tg dt)) ν μ) :
    ∃ μ', Program.sem (Program.star (rightAutomatonBody G mv)) ν μ' ∧
      ∀ x, x ≠ tg → μ' x = μ x := by
  have h' : Relation.ReflTransGen (Program.sem (rightAutomatonBodyC G mv tg dt)) ν μ := h
  clear h
  induction h' with
  | refl => exact ⟨ν, Relation.ReflTransGen.refl, fun _ _ => rfl⟩
  | tail _ hstep ih =>
      obtain ⟨b', hb', hagree⟩ := ih
      obtain ⟨κ', hκ', hagree'⟩ :=
        bodyC_to_body_step G mv tg dt hmvtg hfreshT hgfT hstep b' hagree
      exact ⟨κ', Relation.ReflTransGen.tail hb' hκ', hagree'⟩

/-! ## W2: composition of clocked responses, the zero-duration segment -/

/-- **Clocked responses compose** (mirror of `rrespP_bind`). -/
theorem rrespPC_bind {G : SearchGraph (Var n)} {tg : Var n} {dt : ℝ}
    {P Q : ℕ → State (Var n) → Prop} :
    ∀ (segs : List (ℕ × RMode (Var n) × REdge (Var n))) {q : ℕ} {ν μ : State (Var n)},
      (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) →
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs →
      (∀ s, segs.head? = some s → s.1 = q) →
      Program.sem (bigSeq (segs.map (gsegC tg dt))) ν μ → P (qfOf segs q) μ →
      (∀ q' μ', P q' μ' → RRespPC G tg dt q' Q μ') → RRespPC G tg dt q Q ν := by
  intro segs
  induction segs with
  | nil =>
      intro q ν μ _ _ _ hrun hp hk
      rw [List.map_nil, bigSeq, sem_test] at hrun
      obtain ⟨rfl, -⟩ := hrun
      simpa [qfOf] using hk _ _ hp
  | cons a rest ih =>
      intro q ν μ ha hc hh hrun hp hk
      have hq : a.1 = q := hh a rfl
      simp only [List.map_cons, bigSeq] at hrun
      obtain ⟨κ, hseg, hrest⟩ := hrun
      obtain ⟨hflow, hleg⟩ := sem_gsegC.mp hseg
      obtain ⟨hm, he⟩ := ha a List.mem_cons_self
      rw [← hq]
      refine rrespPC_step hm he hflow hleg (ih (q := a.2.2.tgt)
        (fun s hs => ha s (List.mem_cons_of_mem _ hs)) hc.of_cons ?_ hrest
        (by rw [← qfOf_cons]; exact hp) hk)
      intro t ht
      rcases rest with - | ⟨r, rs⟩
      · simp at ht
      · simp only [List.head?_cons, Option.some.injEq] at ht
        subst ht; exact hc.rel.symm

theorem rrespPC_bind' {G : SearchGraph (Var n)} {tg : Var n} {dt : ℝ} {q : ℕ}
    {P Q : ℕ → State (Var n) → Prop} {ν : State (Var n)} (h : RRespPC G tg dt q P ν)
    (hk : ∀ q' μ', P q' μ' → RRespPC G tg dt q' Q μ') : RRespPC G tg dt q Q ν := by
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := h
  exact rrespPC_bind segs ha hc hh hrun hp hk

/-- **The zero-duration clocked segment**: from an in-domain state, reset the clock, flow for
no time, pass the cap (`0 ≤ dt`). The end state is the start with the clock at `0`. Replaces
`sem_ode_zero` at the hop sites of the chain. -/
theorem sem_clockedSeg_zero (sys : ODESystem (Var n)) (dom : Formula (Var n)) (tg : Var n)
    (dt : ℝ) {ν : State (Var n)} (hdt : 0 ≤ dt) (htgdom : tg ∉ dom.fv)
    (hν : Formula.sat dom ν) :
    Program.sem (clockedSeg sys dom tg dt) ν (Function.update ν tg 0) := by
  refine ⟨Function.update ν tg 0,
    ⟨by simp only [Term.eval, Function.update_self], fun y hy => Function.update_of_ne hy _ _⟩,
    Function.update ν tg 0, sem_ode_zero _ _ ?_, rfl, ?_⟩
  · refine (Formula.coincidence dom (fun x hx => ?_)).mp hν
    exact (Function.update_of_ne (fun h : x = tg => htgdom (by rw [← h]; exact hx)) _ _).symm
  · rw [sat_clkGuard, Function.update_self]
    exact hdt

/-! ## W2: the clocked guarded obligation and the loop step over the clocked automaton -/

/-- `GResp` over clocked segments: for every run of the left program `P` from `σ`, the right
responds from mode `q` with a chain of clocked segments ending where `post` of the final mode
holds. Stated through `RRespPC`, so `coverX_gresp`'s response is this by definition. -/
def GRespC (G : SearchGraph (Var n)) (tg : Var n) (dt : ℝ) (q : ℕ) (P : Program (Var n))
    (post : ℕ → Formula (Var n)) (σ : State (Var n)) : Prop :=
  ∀ ν, Program.sem P σ ν → RRespPC G tg dt q (fun q' μ => Formula.sat (post q') μ) ν

/-- The left window's own guard test (mirror of `gresp_gate`). -/
theorem grespC_gate {G : SearchGraph (Var n)} {tg : Var n} {dt : ℝ} {q : ℕ}
    {φ : Formula (Var n)} {P' : Program (Var n)} {post : ℕ → Formula (Var n)}
    {σ : State (Var n)} (h : Formula.sat φ σ → GRespC G tg dt q P' post σ) :
    GRespC G tg dt q (Program.seq (Program.test φ) P') post σ := by
  intro ν hν
  obtain ⟨κ, ⟨rfl, hφ⟩, hrun⟩ := hν
  exact h hφ ν hrun

/-- The end of a chain of clocked segments: unchanged if empty, else legal for the last
switch (mirror of `bigSeq_gseg_end`). -/
theorem bigSeq_gsegC_end {tg : Var n} {dt : ℝ} :
    ∀ (segs : List (ℕ × RMode (Var n) × REdge (Var n))) {ν μ : State (Var n)},
      Program.sem (bigSeq (segs.map (gsegC tg dt))) ν μ →
      (segs = [] → μ = ν) ∧ ∀ s, segs.getLast? = some s → SwitchLegal s.2.2 μ := by
  intro segs
  induction segs with
  | nil =>
      intro ν μ h
      rw [List.map_nil, bigSeq, sem_test] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨fun _ => rfl, fun s hs => by simp at hs⟩
  | cons a rest ih =>
      intro ν μ h
      simp only [List.map_cons, bigSeq] at h
      obtain ⟨κ, hseg, hrest⟩ := h
      refine ⟨fun h => by simp at h, fun s hs => ?_⟩
      rcases rest with - | ⟨r, rs⟩
      · simp only [List.map_nil, bigSeq, sem_test] at hrest
        obtain ⟨rfl, -⟩ := hrest
        simp only [List.getLast?_singleton, Option.some.injEq] at hs
        subst hs
        exact (sem_gsegC.mp hseg).2
      · exact (ih hrest).2 s (by rw [List.getLast?_cons_cons] at hs; exact hs)

/-- **The clocked guarded jump re-establishes the entered mode's guard** (mirror of
`gresp_guard`). -/
theorem grespC_guard {G : SearchGraph (Var n)} {tg : Var n} {dt : ℝ}
    (guard : ℕ → Formula (Var n))
    (hGg : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
    {q : ℕ} {P : Program (Var n)} {post post' : ℕ → Formula (Var n)} {σ : State (Var n)}
    (hidle : ∀ ν, Program.sem P σ ν → Formula.sat (guard q) ν)
    (himp : ∀ q' μ, Formula.sat (post q') μ → Formula.sat (guard q') μ →
      Formula.sat (post' q') μ)
    (h : GRespC G tg dt q P post σ) : GRespC G tg dt q P post' σ := by
  intro ν hν
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := h ν hν
  refine ⟨segs, ha, hc, hh, μ, hrun, himp _ μ hp ?_⟩
  obtain ⟨hnil, hlast⟩ := bigSeq_gsegC_end segs hrun
  rcases hsl : segs.getLast? with _ | s
  · have hsegs : segs = [] := List.getLast?_eq_none_iff.mp hsl
    have hq : qfOf segs q = q := by simp [qfOf, hsl]
    rw [hq, hnil hsegs]
    exact hidle ν hν
  · have hq : qfOf segs q = s.2.2.tgt := by simp [qfOf, hsl]
    have hmem : s ∈ segs := List.mem_of_getLast? hsl
    have hleg := hlast s hsl
    unfold SwitchLegal at hleg
    rw [hGg s.1 s.2.2 (ha s hmem).2] at hleg
    rw [hq]
    exact hleg

/-- The clocked step provider over the mode-consistent region (mirror of `Hmulti_regionG`). -/
theorem Hmulti_regionGC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (guard cuts : ℕ → Formula (Var n))
    (hGg : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
    (F env : Formula (Var n)) (leftProgs : List (Program (Var n)))
    (hframeG : ∀ P ∈ leftProgs, ∀ q, q < G.modes.length → ∀ σ ν, Program.sem P σ ν →
      Formula.sat (guard q) σ → Formula.sat (guard q) ν)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ → Formula.sat (guard q) σ → Formula.sat (cuts q) σ →
      GRespC G tg dt q P (fun qf => Formula.and (Formula.and F env) (cuts qf)) σ) :
    ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ → Formula.sat (regionG guard cuts q) σ →
      GRespC G tg dt q P (fun qf => Formula.and (Formula.and F env) (regionG guard cuts qf)) σ := by
  intro P hP q hq σ hmv hσ hreg
  refine grespC_guard guard hGg (fun ν hν => hframeG P hP q hq σ ν hν hreg.1) ?_
    (Hmulti P hP q hq σ hmv hσ hreg.1 hreg.2)
  intro q' μ hp hg
  exact ⟨hp.1, hg, hp.2⟩

/-- **The clocked guarded step, region-carrying chain** (mirror of `hstep_single_GR`): the
clocked obligation lifts to one loop step against `star (rightAutomatonBodyC G mv tg dt)`. -/
theorem hstep_single_GRC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ) (q : ℕ)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv) (hregf : ∀ q', mv ∉ (regions q').fv)
    (hframe : FramesMv P mv) (hqlt : q < G.modes.length) (hmvtg : mv ≠ tg)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hresp : GRespC G tg dt q P (fun qf => Formula.and (Formula.and F env) (regions qf)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P
      (Program.star (rightAutomatonBodyC G mv tg dt))
      (phiInvR F env mv regions G.modes.length)) σ := by
  rw [faModal_sat]
  intro ν hleft
  obtain ⟨segs, halign, hchain, hhead, μ, hrun, hpostμ⟩ := hresp ν hleft
  have hνmv : ν mv = (q : ℝ) := (hframe σ ν hleft).trans hmvq
  have hstar := guarded_rights_bridgeC G mv tg dt hmvtg hfresh hgf segs halign hchain q hhead hrun
  have hupdν : Function.update ν mv (q : ℝ) = ν := by
    funext x
    by_cases hx : x = mv
    · subst hx; rw [Function.update_self, hνmv]
    · rw [Function.update_of_ne hx]
  rw [hupdν] at hstar
  refine ⟨Function.update μ mv ((qfOf segs q) : ℝ),
    by rw [Program.rename_refl]; exact hstar, ?_⟩
  obtain ⟨⟨hFμ, henvμ⟩, hregμ⟩ := hpostμ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rwa [(Formula.coincidence F (fun y hy =>
      Function.update_of_ne (fun hc => hF (by rw [← hc]; exact hy)) _ _) :
        Formula.sat F _ ↔ Formula.sat F μ)]
  · rwa [(Formula.coincidence env (fun y hy =>
      Function.update_of_ne (fun hc => henv (by rw [← hc]; exact hy)) _ _) :
        Formula.sat env _ ↔ Formula.sat env μ)]
  · rw [sat_mvRegion]
    refine ⟨qfOf segs q, qfOf_lt G hlt segs halign q hqlt,
      Function.update_self mv _ μ, ?_⟩
    rwa [(Formula.coincidence (regions (qfOf segs q)) (fun y hy =>
      Function.update_of_ne (fun hc => hregf _ (by rw [← hc]; exact hy)) _ _) :
        Formula.sat (regions (qfOf segs q)) _ ↔ _)]

/-- **The assembled clocked step, region-carrying chain** (mirror of `hstep_assembled_GR`). -/
theorem hstep_assembled_GRC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n))
    (leftProgs : List (Program (Var n))) (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hregf : ∀ q', mv ∉ (regions q').fv) (hmvtg : mv ≠ tg)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ → Formula.sat (regions q) σ →
      GRespC G tg dt q P (fun qf => Formula.and (Formula.and F env) (regions qf)) σ) :
    ∀ σ, Formula.sat (phiInvR F env mv regions G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBodyC G mv tg dt))
        (phiInvR F env mv regions G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq, hregq⟩ := sat_mvRegion.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBodyC G mv tg dt))
    (phiInvR F env mv regions G.modes.length) σ leftProgs ?_
  intro P hP
  exact hstep_single_GRC G mv tg dt q F env regions P hF henv hregf (hframes P hP) hqlt hmvtg
    hfresh hgf hlt hmvq (Hmulti P hP q hqlt σ hmvq hφ'.1 hregq)

/-! ## W2: the Theorem 3 assembly with any right body, and its `hddF` discharger -/

/-- `theorem3_faithful_multiR_LR` with the right body abstracted: the proof never looks
inside it (the loop rule `relational_loop_multi` is generic). The clocked chain instantiates
`Rb := rightAutomatonBodyC G mv tg dt`. -/
theorem theorem3_faithful_multiR_LR_gen (G : SearchGraph (Var n)) (mv : Var n)
    (Rb : Program (Var n))
    (F : Formula (Var n)) (domL domR : Formula (Var n))
    (regions : ℕ → Formula (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = F)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars (Rb.rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInvR F (Formula.and domL domR) mv regions
        G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star Rb)
        (phiInvR F (Formula.and domL domR) mv regions G.modes.length)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star Rb)
          (RFormula.and (RFormula.and ϕinv (envLR domL domR))
            (mvRegionR mv regions G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star Rb)
          (RFormula.and (RFormula.and ϕinv (envLR domL domR))
            (mvRegionR mv regions G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) Rb
      (RFormula.and (RFormula.and ϕinv (envLR domL domR))
        (mvRegionR mv regions G.modes.length))) := by
  set k := G.modes.length
  set ψpost := RFormula.and (RFormula.and ϕinv (envLR domL domR))
    (mvRegionR mv regions k) with hψpost
  set Lp := Program.star (bigChoice leftProgs)
  set Rp := Program.star Rb
  have hencψ : encode (Equiv.refl (Var n)) ψpost
      = phiInvR F (Formula.and domL domR) mv regions k := encode_phiInvR_LR hψ
  intro bs
  rw [theorem3Form]
  refine (RFormula_sat_imp _ _ bs).mpr ?_
  intro hpre
  obtain ⟨ν, hbdg⟩ := exists_bridge (Equiv.refl (Var n))
    (faShape Lp Rp ψpost).varsL (faShape Lp Rp ψpost).varsR hddF bs
  have hbψ : Bridges (Equiv.refl (Var n)) ψpost.varsL ψpost.varsR bs ν :=
    hbdg.mono (varsL_subset_faShape Lp Rp ψpost) (varsR_subset_faShape Lp Rp ψpost)
  have hdψ : Disjoint ψpost.varsL (Equiv.refl (Var n) '' ψpost.varsR) :=
    hddF.mono (varsL_subset_faShape Lp Rp ψpost)
      (Set.image_mono (varsR_subset_faShape Lp Rp ψpost))
  have hInvν : Formula.sat (phiInvR F (Formula.and domL domR) mv regions k) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_multi (bigChoice leftProgs) Rb ψpost ν bs hd
    (by rw [hencψ]; exact hInvν)
    (fun σ hσ => by rw [hencψ] at hσ ⊢; exact hstep σ hσ) hddF hbdg

/-- The `hddF` discharger of the clocked chain (mirror of `hddF_multiR_G`): the left clock
`(Aux, b)` is distinct from the mode variable `(Aux, a)` and the right clock `(Aux, d)`. -/
theorem hddF_multiR_GC (Gr : SearchGraph (Var n)) (a b d : Fin n) (dt epsR : ℝ)
    (leftData : List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (regions : ℕ → Formula (Var n))
    (ϕinv : RFormula (Var n)) (domL domR : Formula (Var n)) (hab : a ≠ b) (hbd : b ≠ d)
    (hgR : GuardsRight Gr)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
      d.2.2.1.fv ⊆ range Lv)
    (hreg : ∀ q < Gr.modes.length, (regions q).fv ⊆ range Rv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv) :
    Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
          gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2))))
        (Program.star (rightAutomatonBodyC Gr ((Side.Aux, a) : Var n) ((Side.Aux, d) : Var n)
          epsR))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
          gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2))))
        (Program.star (rightAutomatonBodyC Gr ((Side.Aux, a) : Var n) ((Side.Aux, d) : Var n)
          epsR))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint a b d hab.symm hbd ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 b dt d.2.2.2 (hL d hd).1
        (hL d hd).2.1 (hL d hd).2.2
    · intro v hv
      rcases ψmultiR_varsL_sub _ regions Gr.modes.length ϕinv domL domR hv with hv | hv
      · exact Or.inr (hinvL hv)
      · exact Or.inr (hdomLv hv)
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyCG_sub Gr _ _ _ hgR hRv hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr hv
    · intro v hv
      rcases ψmultiR_varsR_sub _ regions Gr.modes.length ϕinv domL domR hreg hv
        with (hv | hv) | (hv | hv)
      · exact Or.inr (hinvR hv)
      · exact Or.inr (hdomRv hv)
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv

end RelCertifier
