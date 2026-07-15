/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The clocked top theorem (task C, left): ε in the statement, `hbudget` retired

`theorem3_faithful_settling` states its ∀-side over the RAW left ode star — unclocked, so
single flows of arbitrary duration exist and the physical-collapse bridge needs the
external budget hypothesis `hbudgetAll` (unsatisfiable for autonomous benchmarks unless
the caller smuggles a clock into `domL` — a vacuity trap).

This file re-cuts the theorem at the joint the ∀∃ CALCULUS intends (CSF'25): the
per-segment obligation `inv → [|(one clocked left segment, R)⟩⟩ inv` extends to
`inv → [|(L*, R*)⟩⟩ inv` by the LOOP RULE — `faModal_LOCK` (dL-caltiming), no counting,
no budget. The ∀-side is the star of `clockedSeg (leftBlock fL) domL tg dt` — reset,
clocked flow, `?(tg ≤ dt)` — so segment boundedness is SEMANTIC and `dt = ε_R/λ` finally
appears in the statement as the cadence it denotes. ε_L-cadenced missions are compositions
of `dt`-segments, hence contained in the star; nothing is lost by the finer granularity.

Polarity note (why only the LEFT carries a clock here): the left is the ∀-side — the
adversary must be CAPPED, and a cap needs a clock and a reset. The right is the ∃-side —
the witness CHOOSES its duration (`GuardSettlingB` constructs it on exactly `[0, dt]`), so
a clock there adds nothing to this theorem; giving the right its ε_R syntactically is the
separate claim-fidelity upgrade (task C, right).

Hypotheses relative to `theorem3_faithful_settling`: `hbudgetAll`, `htgb`, `htgr`, `htgϕ`,
`htgR`, `htgφ`, `hdMULTI`, and `k` all GONE; what remains is the settling hypothesis
itself, the invariant encoding, and the two variable-hygiene facts (task B's targets). -/
import RelCertifier.GuardThreaded

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

/-- **Theorem 3, settling, clocked ∀-side.** `rvalid` of the ∀∃ modality whose left star
ranges over clocked `dt`-segments; from `GuardSettlingH` by the per-segment coupling and
the loop rule alone. -/
theorem theorem3_faithful_settling_clocked (G : SearchGraph (Var n))
    (Gd : ℕ → Formula (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL evolShared : Formula (Var n)) (tg : Var n)
    (dt : ℝ) (lam : Term (Var n)) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hH : GuardSettlingH G Gd mv g lam tg dt fL evolShared)
    (hdis : Disjoint (Program.vars (clockedSeg (leftBlock fL) domL tg dt))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (clockedSeg (leftBlock fL) domL tg dt))
          (Program.star (rightAutomatonBody G mv)) (ψpostG G Gd mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL tg dt))
          (Program.star (rightAutomatonBody G mv)) (ψpostG G Gd mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (clockedSeg (leftBlock fL) domL tg dt)
      (rightAutomatonBody G mv) (ψpostG G Gd mv ϕinv)) := by
  set ψpost := ψpostG G Gd mv ϕinv with hψpost
  set Lp := Program.star (clockedSeg (leftBlock fL) domL tg dt)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost = starInvGF G Gd mv g :=
    encode_ψpostG G Gd mv g ϕinv hψ
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
  have hInvν : Formula.sat (starInvGF G Gd mv g) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  refine faModal_to_faShape (Equiv.refl (Var n)) Lp Rp ψpost ν bs hddF hbdg ?_
  rw [hencψ]
  -- the loop rule over the per-segment coupling: no budget, no counting
  exact faModal_LOCK (Equiv.refl (Var n)) (clockedSeg (leftBlock fL) domL tg dt)
    (rightAutomatonBody G mv) (starInvGF G Gd mv g) (starInvGF G Gd mv g) ν hdis hInvν
    (fun σ hσ =>
      (faModalB_clockedSeg_iff (leftBlock fL) domL (rightAutomatonBody G mv)
        (starInvGF G Gd mv g) tg dt σ).mpr
        (hHcoupleG_of_GuardSettlingH G Gd mv g lam tg dt fL domL evolShared hH σ hσ))
    (fun _ h => h)

/-! ## Task C, right: the ε-cadenced right automaton

The unclocked `rightAutomatonBody` admits response segments of ANY duration — a strict
superset of the physical R's cadenced behaviors. On the ∃-side, permissiveness WEAKENS
the claim: "∃ response in the superset" does not certify that the response is one the
coarse model can execute. The witnesses the settling machinery constructs run exactly
`dt` — legal — but the statement never said so. `rightAutomatonBodyC` says so: each mode
step's flow is a clocked segment (reset, `clk`-ode, `?(tg ≤ dt)`) — the SAME clock as the
left (the sides strictly alternate, so one clock serves both; no new coordinate, no new
freshness). The witness is dressed with the clock ONCE here (`Φc t = Φ t [tg ↦ t]`); the
per-shape discharge lemmas are untouched. -/

/-- `modeStep` with the flow as a clocked `≤ dt` segment. -/
def modeStepC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ) (q : ℕ)
    (m : RMode (Var n)) : Program (Var n) :=
  Program.seq (Program.test (modeIs mv q))
    (Program.seq (clockedSeg m.sys m.dom tg dt)
      (bigChoiceP ((G.edgesFrom q).map (fun e =>
        Program.seq (Program.test e.guard) (Program.assign mv (Term.const (e.tgt : ℝ)))))))

/-- The ε-cadenced right automaton body. -/
def rightAutomatonBodyC (G : SearchGraph (Var n)) (mv tg : Var n) (dt : ℝ) :
    Program (Var n) :=
  bigChoiceP ((List.range G.modes.length).filterMap (fun q =>
    (G.modeAt q).map (fun m => modeStepC G mv tg dt q m)))

/-- Dress an unclocked witness flow with the clock: `Φc t = Φ t [tg ↦ t]`. If `Φ` solves
`sys` on `[0, dt]` from `μ[tg ↦ 0]` (with `tg` outside `sys`'s bound, terms, and domain),
then the dressed flow yields a `clockedSeg sys dom tg dt` run from `μ`. -/
theorem sem_clockedSeg_of_flow (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (tg : Var n) (dt : ℝ) (μ : State (Var n)) (Φ : ℝ → State (Var n)) (hdt : 0 ≤ dt)
    (htgb : tg ∉ sys.bound) (htgt : ∀ p ∈ sys, tg ∉ (p.2 : Term (Var n)).fv)
    (htgdom : tg ∉ dom.fv)
    (hΦ0 : Φ 0 = Function.update μ tg 0)
    (hder : ∀ t ∈ Icc (0 : ℝ) dt, ∀ p ∈ sys,
        HasDerivWithinAt (fun u => Φ u p.1) (Term.eval p.2 (Φ t)) (Icc 0 dt) t)
    (hmask : ∀ t ∈ Icc (0 : ℝ) dt, ∀ x, x ∉ sys.bound → Φ t x = Φ 0 x)
    (hstay : ∀ t ∈ Icc (0 : ℝ) dt, Formula.sat dom (Φ t)) :
    Program.sem (clockedSeg sys dom tg dt) μ
      (Function.update (Φ dt) tg dt) := by
  set Φc : ℝ → State (Var n) := fun t => Function.update (Φ t) tg t with hΦc
  have hagree : ∀ t x, x ≠ tg → Φc t x = Φ t x := by
    intro t x hx
    simp only [hΦc, Function.update_of_ne hx]
  have hΦc0 : Φc 0 = Function.update μ tg 0 := by
    funext x
    by_cases hx : x = tg
    · subst hx; simp [hΦc]
    · rw [hagree 0 x hx, hΦ0]
  refine ⟨Function.update μ tg 0,
    ⟨by simp only [Term.eval, Function.update_self],
     fun y hy => Function.update_of_ne hy _ _⟩, ?_⟩
  refine ⟨Φc dt, ?_, ⟨rfl, ?_⟩⟩
  · -- the clocked ode run
    refine ⟨dt, Φc, hdt, hΦc0, rfl, ?_, ?_, ?_⟩
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
      push_neg at hx
      obtain ⟨hxs, hxtg⟩ := hx
      rw [hagree t x hxtg, hmask t ht x (by simpa [ODESystem.bound] using hxs), hΦ0]
    · -- staying (tg-free domain)
      intro t ht
      refine (Formula.coincidence dom ?_).mp (hstay t ht)
      intro x hx
      exact (hagree t x (fun h => htgdom (h ▸ hx))).symm
  · -- the clock cap test
    simp only [sat_clkGuard, hΦc, Function.update_self]
    exact le_refl dt

/-- `starStep_wrapG` for the cadenced body: one `modeStepC` step from `μ` preserving
`StarInvG`, given a clocked middle run. -/
theorem starStep_wrapGC (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv tg : Var n)
    (q : ℕ) (m : RMode (Var n)) (g : Term (Var n)) (fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (domR : Formula (Var n)) (dt : ℝ) (μ : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam)
    (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length) (hmvq : μ mv = (q : ℝ))
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvgd' : mv ∉ (Gd e.tgt).fv)
    (hstep : ∃ μ', Program.sem (clockedSeg (rightBlock fR lam) domR tg dt) μ μ' ∧
        Formula.sat (invLe g) μ' ∧ Formula.sat (Gd e.tgt) μ') :
    ∃ ω, Program.sem (rightAutomatonBodyC G mv tg dt) μ ω ∧ StarInvG G Gd mv g ω := by
  obtain ⟨μ', hode, hinv, hgd'⟩ := hstep
  refine ⟨update μ' mv (e.tgt : ℝ), ?_, ?_, ?_, ?_⟩
  · have hjump : Program.sem
        (bigChoiceP ((G.edgesFrom q).map (fun e =>
          Program.seq (Program.test e.guard) (Program.assign mv (Term.const (e.tgt : ℝ))))))
        μ' (update μ' mv (e.tgt : ℝ)) := by
      refine bigChoiceP_sem_of_mem (List.mem_map_of_mem hef) ?_
      exact ⟨μ', ⟨rfl, by rw [hetg]; trivial⟩,
        ⟨by simp only [Term.eval, Function.update_self], fun y hy => update_of_ne hy _ _⟩⟩
    have hstep' : Program.sem (modeStepC G mv tg dt q m) μ (update μ' mv (e.tgt : ℝ)) := by
      refine ⟨μ, ⟨rfl, ?_⟩, μ', ?_, ?_⟩
      · simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, hmvq]
      · rw [hsys, hdom]; exact hode
      · exact hjump
    refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep'
    · exact List.mem_range.mpr (by
        have := hm; simp only [SearchGraph.modeAt] at this
        exact (List.getElem?_eq_some_iff.mp this).1)
    · rw [hm]; rfl
  · have : Set.EqOn μ' (update μ' mv (e.tgt : ℝ)) (invLe g).fv := by
      intro x hx
      have hxg : x ≠ mv := by
        intro hxmv; subst hxmv
        exact hg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
      exact (update_of_ne hxg _ _).symm
    exact (Formula.coincidence (invLe g) this).mp hinv
  · rw [sat_mvValid]; exact ⟨e.tgt, hetv, by simp only [Function.update_self]⟩
  · refine ⟨e.tgt, m', by simp only [Function.update_self], het', ?_⟩
    have : Set.EqOn μ' (update μ' mv (e.tgt : ℝ)) (Gd e.tgt).fv := by
      intro x hx
      exact (update_of_ne (by rintro rfl; exact hmvgd' hx) _ _).symm
    exact (Formula.coincidence (Gd e.tgt) this).mp hgd'

/-- The settling star-step, cadenced: the flow is a clocked `≤ dt` segment. -/
theorem starStep_settlingC (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (mv tg : Var n) (q : ℕ) (m : RMode (Var n)) (g : Term (Var n))
    (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n)) (dt : ℝ)
    (μ : State (Var n))
    (hg : mv ∉ g.fv) (htgg : tg ∉ g.fv)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hmvq : μ mv = (q : ℝ)) (hdt : 0 ≤ dt)
    (htgbR : tg ∉ (rightBlock fR lam).bound)
    (htgfR : ∀ p ∈ rightBlock fR lam, tg ∉ (p.2 : Term (Var n)).fv)
    (htgdom : tg ∉ domR.fv)
    (hset : GuardSettlingB G Gd fR lam domR dt q) (hν : Formula.sat (Gd q) μ)
    (hgboxGd : ∀ ν, Formula.sat (Gd q) ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hmvgdAll : ∀ q', mv ∉ (Gd q').fv) (htggdAll : ∀ q', tg ∉ (Gd q').fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    (hqlen : q < G.modes.length)
    (hmodeAll : ∀ q', q' ∈ q :: G.retainedSucc q → q' < G.modes.length →
        ∃ m', G.modeAt q' = some m') :
    ∃ ω, Program.sem (rightAutomatonBodyC G mv tg dt) μ ω ∧ StarInvG G Gd mv g ω := by
  -- reset state, still in the guard (tg-free)
  set μ0 := Function.update μ tg 0 with hμ0
  have hν0 : Formula.sat (Gd q) μ0 := by
    refine (Formula.coincidence (Gd q) ?_).mp hν
    intro x hx
    exact (update_of_ne (by rintro rfl; exact htggdAll q hx) _ _).symm
  obtain ⟨ΦR, hΦ0, hder, hmask, hstay, q', hq'mem, hgd'⟩ := hset μ0 hν0
  -- the clocked middle run
  have hclk : Program.sem (clockedSeg (rightBlock fR lam) domR tg dt) μ
      (Function.update (ΦR dt) tg dt) := by
    refine sem_clockedSeg_of_flow (rightBlock fR lam) domR tg dt μ ΦR hdt htgbR htgfR
      htgdom hΦ0 hder ?_ hstay
    intro t ht x hx
    rw [hmask t ht x hx, hΦ0]
  -- invLe and landing transfer through the tg-update
  have hmask0 : ∀ t ∈ Icc (0 : ℝ) dt, ∀ x, x ∉ (rightBlock fR lam).bound →
      ΦR t x = μ0 x := hmask
  have hsemU : Program.sem (Program.ode (rightBlock fR lam) domR) μ0 (ΦR dt) :=
    ⟨dt, ΦR, hdt, hΦ0, rfl, hder, hmask0, hstay⟩
  have hinv : Formula.sat (invLe g) (Function.update (ΦR dt) tg dt) := by
    have h1 : Formula.sat (invLe g) (ΦR dt) := by
      rw [sat_invLe]; exact hgboxGd μ0 hν0 (ΦR dt) hsemU
    refine (Formula.coincidence (invLe g) ?_).mp h1
    intro x hx
    have hxtg : x ≠ tg := by
      rintro rfl
      exact htgg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
    exact (update_of_ne hxtg _ _).symm
  have hgd'U : Formula.sat (Gd q') (Function.update (ΦR dt) tg dt) := by
    refine (Formula.coincidence (Gd q') ?_).mp hgd'
    intro x hx
    exact (update_of_ne (by rintro rfl; exact htggdAll q' hx) _ _).symm
  rcases List.mem_cons.mp hq'mem with hq'self | hq'succ
  · subst hq'self
    obtain ⟨e, hef, hetgt, hetg⟩ := hedgeSelf
    obtain ⟨m', het'⟩ := hmodeAll q' (List.mem_cons_self ..) hqlen
    refine starStep_wrapGC G Gd mv tg q' m g fR lam domR dt μ hg hm hsys hdom hef hetg
      (by rw [hetgt]; exact hqlen) hmvq (by rw [hetgt]; exact het') (hmvgdAll e.tgt) ?_
    exact ⟨_, hclk, hinv, by rw [hetgt]; exact hgd'U⟩
  · obtain ⟨e, hef, hetgt, hetg, hetv⟩ := hedgeSucc q' hq'succ
    obtain ⟨m', het'⟩ := hmodeAll q' hq'mem (by rw [← hetgt]; exact hetv)
    refine starStep_wrapGC G Gd mv tg q m g fR lam domR dt μ hg hm hsys hdom hef hetg hetv
      hmvq (by rw [hetgt]; exact het') (hmvgdAll e.tgt) ?_
    exact ⟨_, hclk, hinv, by rw [hetgt]; exact hgd'U⟩

/-- The clocked per-mode coupling, cadenced right (mirror of
`landing_step_settling_clocked`). -/
theorem landing_step_settling_clockedC (G : SearchGraph (Var n))
    (Gd : ℕ → Formula (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n)) (g : Term (Var n))
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
    (tg : Var n) (dt : ℝ) (ω : State (Var n))
    (hg : mv ∉ g.fv) (htgg : tg ∉ g.fv)
    (hmvLclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hqlen : q < G.modes.length) (hdt : 0 ≤ dt)
    (htgbR : tg ∉ (rightBlock fR lam).bound)
    (htgfR : ∀ p ∈ rightBlock fR lam, tg ∉ (p.2 : Term (Var n)).fv)
    (htgdom : tg ∉ domR.fv)
    (hset : GuardSettlingB G Gd fR lam domR dt q)
    (hgboxGd : ∀ ν, Formula.sat (Gd q) ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrzClkGd : ∀ x ∈ (Gd q).fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvgdAll : ∀ q', mv ∉ (Gd q').fv) (htggdAll : ∀ q', tg ∉ (Gd q').fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    (hmodeAll : ∀ q', q' ∈ q :: G.retainedSucc q → q' < G.modes.length →
        ∃ m', G.modeAt q' = some m')
    (hωmv : ω mv = (q : ℝ)) (hωgd : Formula.sat (Gd q) ω) :
    faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
      (rightAutomatonBodyC G mv tg dt) (starInvGF G Gd mv g) tg dt ω := by
  intro ν hplant
  obtain ⟨hsemL, _⟩ := hplant
  obtain ⟨s, Φ, hs, hΦ0, hΦs, _, hmask, _⟩ := hsemL
  have hmvν : ν mv = (q : ℝ) := by
    rw [← hΦs, hmask s (right_mem_Icc.mpr hs) mv hmvLclk]; exact hωmv
  have hνgd : Formula.sat (Gd q) ν := by
    have heqon : Set.EqOn ω ν (Gd q).fv := by
      intro x hx
      rw [← hΦs]; exact (hmask s (right_mem_Icc.mpr hs) x (hfrzClkGd x hx)).symm
    exact (Formula.coincidence (Gd q) heqon).mp hωgd
  obtain ⟨o, hsemω, hstarω⟩ :=
    starStep_settlingC G Gd mv tg q m g fR lam domR dt ν hg htgg hm hsys hdom hmvν hdt
      htgbR htgfR htgdom hset hνgd (hgboxGd) hmvgdAll htggdAll hedgeSelf hedgeSucc
      hqlen hmodeAll
  exact ⟨o, by simpa only [Program.rename_refl] using hsemω, sat_starInvGF.mpr hstarω⟩

/-- The clocked coupling from `GuardSettlingH`, cadenced right. -/
theorem hHcoupleGC_of_GuardSettlingH (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (mv : Var n) (g : Term (Var n)) (lam : Term (Var n)) (tg : Var n) (dt : ℝ)
    (fL : Fin n → Term (Var n)) (domL evolShared : Formula (Var n))
    (htgg : tg ∉ g.fv)
    (htgS : ∀ q m, G.modeAt q = some m → ∀ fR, m.sys = rightBlock fR lam →
        tg ∉ (rightBlock fR lam).bound ∧
        (∀ p ∈ rightBlock fR lam, tg ∉ (p.2 : Term (Var n)).fv))
    (htgdom : tg ∉ evolShared.fv)
    (h : GuardSettlingH G Gd mv g lam tg dt fL evolShared) :
    ∀ σ', Formula.sat (starInvGF G Gd mv g) σ' →
      faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
        (rightAutomatonBodyC G mv tg dt) (starInvGF G Gd mv g) tg dt
        (Function.update σ' tg 0) := by
  obtain ⟨hdt, hg, hmvLclk, hmvtg, hmvGd, htgGd, hfrzGd, hmodes⟩ := h
  intro σ' hσ'
  obtain ⟨q, m, hqmv, hmode, hqgd⟩ := (sat_starInvGF.mp hσ').2.2
  obtain ⟨fR, hsys, hdom, hqlen, hset, hgboxGd, hself, hsucc, hmodeAll⟩ := hmodes q m hmode
  obtain ⟨htgbR, htgfR⟩ := htgS q m hmode fR hsys
  have hωmv : (Function.update σ' tg 0) mv = (q : ℝ) := by
    rw [Function.update_of_ne hmvtg]; exact hqmv
  have hωgd : Formula.sat (Gd q) (Function.update σ' tg 0) := by
    have heq : Set.EqOn σ' (Function.update σ' tg 0) (Gd q).fv :=
      fun x hx => (Function.update_of_ne (by rintro rfl; exact htgGd q hx) _ _).symm
    exact (Formula.coincidence (Gd q) heq).mp hqgd
  exact landing_step_settling_clockedC G Gd mv q m g fL fR lam domL evolShared tg dt
    (Function.update σ' tg 0) hg htgg hmvLclk hmode hsys hdom hqlen hdt htgbR htgfR
    htgdom hset hgboxGd (hfrzGd q) hmvGd htgGd hself hsucc hmodeAll hωmv hωgd

/-- **Theorem 3, settling, ε-CADENCED BOTH SIDES.** The ∀-side left star ranges over
clocked `dt`-segments; the ∃-side right star over clocked `dt`-responses — the statement
finally certifies that the responses are cadence-legal. -/
theorem theorem3_faithful_settling_cadenced (G : SearchGraph (Var n))
    (Gd : ℕ → Formula (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL evolShared : Formula (Var n)) (tg : Var n)
    (dt : ℝ) (lam : Term (Var n)) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hH : GuardSettlingH G Gd mv g lam tg dt fL evolShared)
    (htgg : tg ∉ g.fv)
    (htgS : ∀ q m, G.modeAt q = some m → ∀ fR, m.sys = rightBlock fR lam →
        tg ∉ (rightBlock fR lam).bound ∧
        (∀ p ∈ rightBlock fR lam, tg ∉ (p.2 : Term (Var n)).fv))
    (htgdom : tg ∉ evolShared.fv)
    (hdis : Disjoint (Program.vars (clockedSeg (leftBlock fL) domL tg dt))
        (Program.vars ((rightAutomatonBodyC G mv tg dt).rename (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (clockedSeg (leftBlock fL) domL tg dt))
          (Program.star (rightAutomatonBodyC G mv tg dt)) (ψpostG G Gd mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL tg dt))
          (Program.star (rightAutomatonBodyC G mv tg dt)) (ψpostG G Gd mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (clockedSeg (leftBlock fL) domL tg dt)
      (rightAutomatonBodyC G mv tg dt) (ψpostG G Gd mv ϕinv)) := by
  set ψpost := ψpostG G Gd mv ϕinv with hψpost
  set Lp := Program.star (clockedSeg (leftBlock fL) domL tg dt)
  set Rp := Program.star (rightAutomatonBodyC G mv tg dt)
  have hencψ : encode (Equiv.refl (Var n)) ψpost = starInvGF G Gd mv g :=
    encode_ψpostG G Gd mv g ϕinv hψ
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
  have hInvν : Formula.sat (starInvGF G Gd mv g) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  refine faModal_to_faShape (Equiv.refl (Var n)) Lp Rp ψpost ν bs hddF hbdg ?_
  rw [hencψ]
  exact faModal_LOCK (Equiv.refl (Var n)) (clockedSeg (leftBlock fL) domL tg dt)
    (rightAutomatonBodyC G mv tg dt) (starInvGF G Gd mv g) (starInvGF G Gd mv g) ν hdis
    hInvν
    (fun σ hσ =>
      (faModalB_clockedSeg_iff (leftBlock fL) domL (rightAutomatonBodyC G mv tg dt)
        (starInvGF G Gd mv g) tg dt σ).mpr
        (hHcoupleGC_of_GuardSettlingH G Gd mv g lam tg dt fL domL evolShared
          htgg htgS htgdom hH σ hσ))
    (fun _ h => h)

/-! ## The calculus-faithful coupling slot: one left segment vs the right STAR

`faModal_LOCK` instantiated at `Q := body` demands LOCKSTEP — one right body step per
left segment. That is a witness discipline, not the calculus: the ∀∃ loop rule is
`inv → [|(L, R*)⟩⟩ inv ⟹ inv → [|(L*, R*)⟩⟩ inv`, allowing arbitrarily many right
steps per left segment (the certifier's own route search uses solo-hops). Instantiating
`LOCK` at `Q := star body` and collapsing `star (star body) = star body` gives exactly
that rule. The settling witnesses are single-hop and embed by ∃-weakening; discharges
needing multi-hop responses now have a slot to feed. -/

/-- `⟦(α*)*⟧ = ⟦α*⟧` (reflexive-transitive closure is idempotent). -/
theorem sem_star_star (α : Program (Var n)) (ν μ : State (Var n)) :
    Program.sem (Program.star (Program.star α)) ν μ ↔ Program.sem (Program.star α) ν μ := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.trans ih hstep
  · intro h
    exact Relation.ReflTransGen.single h

/-- **The loop rule in its calculus form**: from `inv → [|(P, R*)⟩⟩ inv` (one left segment,
right STAR — any number of right steps), conclude `inv → [|(P*, R*)⟩⟩ inv`. -/
theorem faModal_LOCK_starR (ρ : Var n ≃ Var n) (P R : Program (Var n))
    (φinv : Formula (Var n)) (ω : State (Var n))
    (hd : Disjoint (Program.vars P) (Program.vars ((Program.star R).rename ρ)))
    (hinv : Formula.sat φinv ω)
    (hstep : ∀ σ, Formula.sat φinv σ →
        Formula.sat (faModal ρ P (Program.star R) φinv) σ) :
    Formula.sat (faModal ρ (Program.star P) (Program.star R) φinv) ω := by
  have h := faModal_LOCK ρ P (Program.star R) φinv φinv ω hd hinv hstep (fun _ h => h)
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hsem, hφ⟩ := h ν hν
  refine ⟨μ, ?_, hφ⟩
  rw [rename_star] at hsem ⊢
  exact (sem_star_star _ _ _).mp (by rwa [rename_star] at hsem)

/-- **Theorem 3, settling, ε-cadenced, calculus-faithful coupling.** Identical to
`theorem3_faithful_settling_cadenced`, but the per-segment obligation passes through the
`R*` slot — the settling witness (one body step) enters by ∃-weakening, and multi-hop
responses fit the same slot. -/
theorem theorem3_faithful_settling_cadenced' (G : SearchGraph (Var n))
    (Gd : ℕ → Formula (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL evolShared : Formula (Var n)) (tg : Var n)
    (dt : ℝ) (lam : Term (Var n)) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hH : GuardSettlingH G Gd mv g lam tg dt fL evolShared)
    (htgg : tg ∉ g.fv)
    (htgS : ∀ q m, G.modeAt q = some m → ∀ fR, m.sys = rightBlock fR lam →
        tg ∉ (rightBlock fR lam).bound ∧
        (∀ p ∈ rightBlock fR lam, tg ∉ (p.2 : Term (Var n)).fv))
    (htgdom : tg ∉ evolShared.fv)
    (hdis : Disjoint (Program.vars (clockedSeg (leftBlock fL) domL tg dt))
        (Program.vars ((Program.star (rightAutomatonBodyC G mv tg dt)).rename
          (Equiv.refl (Var n)))))
    (hddF : Disjoint (faShape (Program.star (clockedSeg (leftBlock fL) domL tg dt))
          (Program.star (rightAutomatonBodyC G mv tg dt)) (ψpostG G Gd mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (clockedSeg (leftBlock fL) domL tg dt))
          (Program.star (rightAutomatonBodyC G mv tg dt)) (ψpostG G Gd mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (clockedSeg (leftBlock fL) domL tg dt)
      (rightAutomatonBodyC G mv tg dt) (ψpostG G Gd mv ϕinv)) := by
  set ψpost := ψpostG G Gd mv ϕinv with hψpost
  set Lp := Program.star (clockedSeg (leftBlock fL) domL tg dt)
  set Rp := Program.star (rightAutomatonBodyC G mv tg dt)
  have hencψ : encode (Equiv.refl (Var n)) ψpost = starInvGF G Gd mv g :=
    encode_ψpostG G Gd mv g ϕinv hψ
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
  have hInvν : Formula.sat (starInvGF G Gd mv g) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  refine faModal_to_faShape (Equiv.refl (Var n)) Lp Rp ψpost ν bs hddF hbdg ?_
  rw [hencψ]
  refine faModal_LOCK_starR (Equiv.refl (Var n)) (clockedSeg (leftBlock fL) domL tg dt)
    (rightAutomatonBodyC G mv tg dt) (starInvGF G Gd mv g) ν hdis hInvν ?_
  -- per-segment obligation in the CALCULUS form: one left segment vs the right STAR;
  -- the settling witness is a single body step, entering by ∃-weakening
  intro σ hσ
  have h1 := (faModalB_clockedSeg_iff (leftBlock fL) domL (rightAutomatonBodyC G mv tg dt)
    (starInvGF G Gd mv g) tg dt σ).mpr
    (hHcoupleGC_of_GuardSettlingH G Gd mv g lam tg dt fL domL evolShared
      htgg htgS htgdom hH σ hσ)
  rw [faModal_sat] at h1 ⊢
  intro ν' hν'
  obtain ⟨μ, hsem, hφ⟩ := h1 ν' hν'
  refine ⟨μ, ?_, hφ⟩
  rw [rename_star]
  exact Relation.ReflTransGen.single (by rwa [Program.rename_refl] at hsem ⊢)

end RelCertifier
