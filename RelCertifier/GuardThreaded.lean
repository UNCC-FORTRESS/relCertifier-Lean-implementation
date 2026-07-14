/-
# Tier B — the guard-threaded discharge (margin class)

Upgrades the guard-capped growing benchmarks from CARRIED staying to DISCHARGED staying.

The obstruction (UniformEvol.lean): `WellFormedFlowB` quantifies `∀ base ∈ evolShared`, and a
growing mode exits from bases in the MARGIN BAND (above its guard cap, below the envelope
boundary) — states the settling design makes unreachable, but which the `starInvF` invariant
("state ∈ shared domain") cannot exclude. Fix: thread the GUARD through the star invariant —

* `StarInModeGuard` / `inModeGuardF` / `starInvGF` — the invariant's third conjunct becomes
  "the state satisfies the guard `Gd q` of the mode `q` it is in" (`Gd : ℕ → Formula` is the
  guard map; the Lean-side `RMode` carries no guard field, so it is threaded as a parameter).
* `GuardSettlingB` — the guard-based staying-and-landing obligation, PER MODE: from every base
  in the mode's guard region, the `dt`-flow exists, stays in the shared envelope, and its
  endpoint lands in the guard of the mode itself or of a declared successor. This is exactly
  the settling-guard geometry (margin > rate·dt; guards tile the one-step reachable band).
* `starStep_wrapG` / `starStep_settling` / `landing_step_settling_clocked` — the per-segment
  landing chain re-derived carrying the guard fact (mirrors of the `starInvF` versions).
* `clocked_residence_physical_gen` — the clocked→physical residence chain, stated GENERIC in
  the threaded invariant (the underlying `multiseg_clocked`/`clockLift_collapse`/`faModal_MULTI`
  never depended on `starInvF`), instantiated at `starInvGF`.
* `theorem3_faithful_settling` — the shipped `rvalid (theorem3Form …)` on the guard-threaded
  foundation, via `ψpostG` (`encode`s exactly to `starInvGF`).
* `GuardSettlingB_of_margin_const` — **the margin-class discharge**: a single-coordinate
  constant-rate mode with a guard band `[a, cap]`, envelope `[lo, hi]`, margin `cap + c·dt ≤ hi`,
  and a successor guard band covering `[a + c·dt, cap + c·dt]` satisfies `GuardSettlingB` BY
  CONSTRUCTION (explicit affine witness + `linarith`) — the exact geometry the certifier-verified
  settling discipline enforces.
* `GuardSettlingB_of_contract` — the contractive analog (equilibrium inside the OWN guard band:
  the flow self-lands; exponential witness reused from `UniformEvol.lean`).

Honest scope: the precondition strengthens from "initial state in some mode's domain" to
"initial state in some mode's GUARD" (`inModeGuardR`) — true of every well-formed benchmark
config (runs start in a mode's operating region). Benchmarks whose guards do not cap every
envelope-bounded coordinate (e.g. rover `px`) remain on the carried-H path (`UniformEvol.lean`);
non-settling systems remain on the per-mode-domain path. Non-breaking throughout.
-/
import RelCertifier.UniformEvol

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-! ## The guard-threaded star invariant -/

/-- The state is in the GUARD region of the mode `mv` names (guard map `Gd`). -/
def StarInModeGuard (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (μ : State (Var n)) : Prop :=
  ∃ (q' : ℕ) (m' : RMode (Var n)),
    μ mv = (q' : ℝ) ∧ G.modeAt q' = some m' ∧ Formula.sat (Gd q') μ

/-- `StarInModeGuard` as a Formula (finite disjunction over declared modes). -/
def inModeGuardF (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n) :
    Formula (Var n) :=
  bigOr ((List.range G.modes.length).filterMap (fun q =>
    (G.modeAt q).map (fun _ => Formula.and (modeIs mv q) (Gd q))))

theorem sat_inModeGuardF {G : SearchGraph (Var n)} {Gd : ℕ → Formula (Var n)} {mv : Var n}
    {μ : State (Var n)} :
    Formula.sat (inModeGuardF G Gd mv) μ ↔ StarInModeGuard G Gd mv μ := by
  rw [inModeGuardF, sat_bigOr]
  constructor
  · rintro ⟨f, hf, hsat⟩
    rw [List.mem_filterMap] at hf
    obtain ⟨q, _, hmap⟩ := hf
    rcases hopt : G.modeAt q with _ | m
    · rw [hopt] at hmap; simp at hmap
    · rw [hopt] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      subst hmap
      obtain ⟨hmode, hgd⟩ := hsat
      refine ⟨q, m, ?_, hopt, hgd⟩
      simpa only [modeIs, Formula.sat, CompOp.interp, Term.eval] using hmode
  · rintro ⟨q, m, hmv, hmode, hgd⟩
    refine ⟨Formula.and (modeIs mv q) (Gd q), ?_, ?_, hgd⟩
    · rw [List.mem_filterMap]
      exact ⟨q, List.mem_range.mpr (by
        have := hmode; simp only [SearchGraph.modeAt] at this
        exact (List.getElem?_eq_some_iff.mp this).1), by rw [hmode]; rfl⟩
    · simpa only [modeIs, Formula.sat, CompOp.interp, Term.eval] using hmv

/-- The guard-threaded star invariant (Prop form). -/
def StarInvG (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n) (g : Term (Var n))
    (μ : State (Var n)) : Prop :=
  Formula.sat (invLe g) μ ∧ Formula.sat (mvValid mv G.modes.length) μ ∧ StarInModeGuard G Gd mv μ

/-- The guard-threaded star invariant (Formula form). -/
def starInvGF (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (g : Term (Var n)) : Formula (Var n) :=
  Formula.and (invLe g) (Formula.and (mvValid mv G.modes.length) (inModeGuardF G Gd mv))

theorem sat_starInvGF {G : SearchGraph (Var n)} {Gd : ℕ → Formula (Var n)} {mv : Var n}
    {g : Term (Var n)} {μ : State (Var n)} :
    Formula.sat (starInvGF G Gd mv g) μ ↔ StarInvG G Gd mv g μ := by
  rw [starInvGF, StarInvG]
  simp only [Formula.sat, sat_inModeGuardF]

/-! ## The guard-based per-mode obligation (the discharged H) -/

/-- **`GuardSettlingB` — guard-based staying-and-landing, per mode `q`.** From EVERY base in
mode `q`'s guard region: the `dt`-flow of `q`'s field exists, stays in the shared envelope
`domR` throughout, and its endpoint satisfies the guard of `q` itself or of a declared retained
successor. This is the settling-guard geometry as a proof obligation — dischargeable by
construction for the margin/contractive shapes (below), never quantifying over the margin band. -/
def GuardSettlingB (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (dt : ℝ) (q : ℕ) : Prop :=
  ∀ (base : State (Var n)), Formula.sat (Gd q) base →
    ∃ ΦR : ℝ → State (Var n), ΦR 0 = base ∧
      (∀ t ∈ Icc (0 : ℝ) dt, ∀ p ∈ rightBlock fR lam,
          HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 dt) t) ∧
      (∀ t ∈ Icc (0 : ℝ) dt, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = base x) ∧
      (∀ t ∈ Icc (0 : ℝ) dt, Formula.sat domR (ΦR t)) ∧
      ∃ q' ∈ q :: G.retainedSucc q, Formula.sat (Gd q') (ΦR dt)

/-! ## The per-segment chain, guard-threaded (mirrors of the `starInvF` versions) -/

/-- `starStep_wrap` carrying the TARGET GUARD instead of the target domain: one
`rightAutomatonBody` step from `μ` reaches `ω = μ'[mv ↦ e.tgt]` with `StarInvG`. -/
theorem starStep_wrapG (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (q : ℕ) (m : RMode (Var n)) (g : Term (Var n)) (fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (domR : Formula (Var n)) (μ : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam)
    (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length) (hmvq : μ mv = (q : ℝ))
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvgd' : mv ∉ (Gd e.tgt).fv)
    (hstep : ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) μ μ' ∧
        Formula.sat (invLe g) μ' ∧ Formula.sat (Gd e.tgt) μ') :
    ∃ ω, Program.sem (rightAutomatonBody G mv) μ ω ∧ StarInvG G Gd mv g ω := by
  obtain ⟨μ', hode, hinv, hgd'⟩ := hstep
  refine ⟨update μ' mv (e.tgt : ℝ), ?_, ?_, ?_, ?_⟩
  · -- the mode-q body-step: test(mv=q) ; ode ; (test e.guard ; mv := e.tgt)
    have hjump : Program.sem
        (bigChoiceP ((G.edgesFrom q).map (fun e =>
          Program.seq (Program.test e.guard) (Program.assign mv (Term.const (e.tgt : ℝ))))))
        μ' (update μ' mv (e.tgt : ℝ)) := by
      refine bigChoiceP_sem_of_mem (List.mem_map_of_mem hef) ?_
      exact ⟨μ', ⟨rfl, by rw [hetg]; trivial⟩,
        ⟨by simp only [Term.eval, Function.update_self], fun y hy => update_of_ne hy _ _⟩⟩
    have hstep' : Program.sem (modeStep G mv q m) μ (update μ' mv (e.tgt : ℝ)) := by
      refine ⟨μ, ⟨rfl, ?_⟩, μ', ?_, ?_⟩
      · simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, hmvq]
      · rw [hsys, hdom]; exact hode
      · exact hjump
    refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep'
    · exact List.mem_range.mpr (by
        have := hm; simp only [SearchGraph.modeAt] at this
        exact (List.getElem?_eq_some_iff.mp this).1)
    · rw [hm]; rfl
  · -- invLe g survives the mv-assign (mv ∉ g.fv)
    have : Set.EqOn μ' (update μ' mv (e.tgt : ℝ)) (invLe g).fv := by
      intro x hx
      have hxg : x ≠ mv := by
        intro hxmv; subst hxmv
        exact hg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
      exact (update_of_ne hxg _ _).symm
    exact (Formula.coincidence (invLe g) this).mp hinv
  · -- mvValid : e.tgt is a valid mode index
    rw [sat_mvValid]; exact ⟨e.tgt, hetv, by simp only [Function.update_self]⟩
  · -- StarInModeGuard : endpoint mv = e.tgt, mode m' there, μ' ∈ Gd e.tgt (mv-frozen)
    refine ⟨e.tgt, m', by simp only [Function.update_self], het', ?_⟩
    have : Set.EqOn μ' (update μ' mv (e.tgt : ℝ)) (Gd e.tgt).fv := by
      intro x hx
      exact (update_of_ne (by rintro rfl; exact hmvgd' hx) _ _).symm
    exact (Formula.coincidence (Gd e.tgt) this).mp hgd'

/-- **The settling star-step.** From a state in mode `q`'s GUARD: run the `dt`-flow
(`GuardSettlingB` — stays in the envelope, endpoint lands in a self-or-successor guard), read
off `g`-preservation from the certificate box, dispatch the landed guard's edge. One
`rightAutomatonBody` step preserving `StarInvG`. No margin-band base ever enters. -/
theorem starStep_settling (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (q : ℕ) (m : RMode (Var n)) (g : Term (Var n)) (fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (domR : Formula (Var n)) (dt : ℝ) (μ : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam)
    (hdom : m.dom = domR) (hmvq : μ mv = (q : ℝ)) (hdt : 0 ≤ dt)
    (hset : GuardSettlingB G Gd fR lam domR dt q) (hν : Formula.sat (Gd q) μ)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) μ)
    (hmvgdAll : ∀ q', mv ∉ (Gd q').fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    (hqlen : q < G.modes.length)
    (hmodeAll : ∀ q', q' ∈ q :: G.retainedSucc q → q' < G.modes.length →
        ∃ m', G.modeAt q' = some m') :
    ∃ ω, Program.sem (rightAutomatonBody G mv) μ ω ∧ StarInvG G Gd mv g ω := by
  obtain ⟨ΦR, hΦ0, hder, hmask, hstay, q', hq'mem, hgd'⟩ := hset μ hν
  have hsem : Program.sem (Program.ode (rightBlock fR lam) domR) μ (ΦR dt) :=
    ⟨dt, ΦR, hdt, hΦ0, rfl, hder, hmask, hstay⟩
  have hinv : Formula.sat (invLe g) (ΦR dt) := by
    rw [sat_invLe]; exact hgbox (ΦR dt) hsem
  rcases List.mem_cons.mp hq'mem with hq'self | hq'succ
  · -- landed in the CURRENT mode's guard: dispatch the self-edge
    subst hq'self
    obtain ⟨e, hef, hetgt, hetg⟩ := hedgeSelf
    obtain ⟨m', het'⟩ := hmodeAll q' (List.mem_cons_self ..) hqlen
    refine starStep_wrapG G Gd mv q' m g fR lam domR μ hg hm hsys hdom hef hetg
      (by rw [hetgt]; exact hqlen) hmvq (by rw [hetgt]; exact het') (hmvgdAll e.tgt) ?_
    exact ⟨ΦR dt, hsem, hinv, by rw [hetgt]; exact hgd'⟩
  · -- landed in a SUCCESSOR's guard: dispatch the declared edge
    obtain ⟨e, hef, hetgt, hetg, hetv⟩ := hedgeSucc q' hq'succ
    obtain ⟨m', het'⟩ := hmodeAll q' hq'mem (by rw [← hetgt]; exact hetv)
    refine starStep_wrapG G Gd mv q m g fR lam domR μ hg hm hsys hdom hef hetg hetv hmvq
      (by rw [hetgt]; exact het') (hmvgdAll e.tgt) ?_
    exact ⟨ΦR dt, hsem, hinv, by rw [hetgt]; exact hgd'⟩

/-- The clocked per-mode coupling on the guard invariant (mirror of
`landing_step_landingH_clocked`): the left runs a `≤dt` clocked segment (freezing the right
coordinates), the right settles per `starStep_settling`. -/
theorem landing_step_settling_clocked (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (mv : Var n) (q : ℕ) (m : RMode (Var n)) (g : Term (Var n))
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (tg : Var n) (dt : ℝ) (ω : State (Var n))
    (hg : mv ∉ g.fv) (hmvLclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hqlen : q < G.modes.length) (hdt : 0 ≤ dt)
    (hset : GuardSettlingB G Gd fR lam domR dt q)
    (hgboxGd : ∀ ν, Formula.sat (Gd q) ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrzClkGd : ∀ x ∈ (Gd q).fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvgdAll : ∀ q', mv ∉ (Gd q').fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    (hmodeAll : ∀ q', q' ∈ q :: G.retainedSucc q → q' < G.modes.length →
        ∃ m', G.modeAt q' = some m')
    (hωmv : ω mv = (q : ℝ)) (hωgd : Formula.sat (Gd q) ω) :
    faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
      (rightAutomatonBody G mv) (starInvGF G Gd mv g) tg dt ω := by
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
    starStep_settling G Gd mv q m g fR lam domR dt ν hg hm hsys hdom hmvν hdt hset hνgd
      (hgboxGd ν hνgd) hmvgdAll hedgeSelf hedgeSucc hqlen hmodeAll
  exact ⟨o, by simpa only [Program.rename_refl] using hsemω, sat_starInvGF.mpr hstarω⟩

/-! ## The clocked→physical residence, generic in the threaded invariant

`clocked_H_residence`/`_physical`/`multiseg_landing_clocked_physical` used only φinv-generic
machinery — restated here with the invariant abstract, then instantiated at `starInvGF`. -/

/-- The clocked residence chain (generic φinv). -/
theorem clocked_residence_gen (G : SearchGraph (Var n)) (mv : Var n) (φinv : Formula (Var n))
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ)
    (hHcouple : ∀ σ', Formula.sat φinv σ' →
      faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
        (rightAutomatonBody G mv) φinv tg dt (Function.update σ' tg 0))
    (hdis : Disjoint (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg dt)))
    {σ : State (Var n)} (hσ : Formula.sat φinv σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (bigSeq (List.replicate k (clockedSeg (leftBlock fL) domL tg dt)))
      (Program.star (rightAutomatonBody G mv)) φinv) σ := by
  have hmc := multiseg_clocked φinv (leftBlock fL) domL tg dt
    (List.replicate k (rightAutomatonBody G mv))
    (fun Q hQ => by rw [List.eq_of_mem_replicate hQ]; exact hdis)
    (fun Q hQ σ' hσ' => by rw [List.eq_of_mem_replicate hQ]; exact hHcouple σ' hσ')
    σ hσ
  rw [List.map_replicate] at hmc
  exact faModal_bigSeq_replicate_to_star (Equiv.refl (Var n)) _ (rightAutomatonBody G mv)
    φinv σ k hmc

/-- The physical collapse (generic φinv). -/
theorem clocked_residence_physical_gen (G : SearchGraph (Var n)) (mv : Var n)
    (φinv : Formula (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ)
    (htgb : tg ∉ (leftBlock fL).bound) (htgr : tg ∉ (leftBlock fL).readVars)
    (htgϕ : tg ∉ domL.fv) (hdt : 0 ≤ dt)
    (htgR : tg ∉ ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))).fv)
    (htgφ : tg ∉ φinv.fv)
    (hHcouple : ∀ σ', Formula.sat φinv σ' →
      faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
        (rightAutomatonBody G mv) φinv tg dt (Function.update σ' tg 0))
    (hdis : Disjoint (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg dt)))
    {σ : State (Var n)} (hσ : Formula.sat φinv σ)
    (hbudget : ∀ {r : ℝ} {Φ : ℝ → State (Var n)},
        ODESol (leftBlock fL) domL σ r Φ → r ≤ (k : ℝ) * dt) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
      (Program.star (rightAutomatonBody G mv)) φinv) σ := by
  have hres := clocked_residence_gen G mv φinv fL domL tg dt k hHcouple hdis hσ
  have htgRstar : tg ∉ ((Program.star (rightAutomatonBody G mv)).rename (Equiv.refl (Var n))).fv := by
    rw [rename_star]; simpa [Program.fv] using htgR
  exact clockLift_collapse (leftBlock fL) domL (Program.star (rightAutomatonBody G mv))
    φinv tg dt k htgb htgr htgϕ hdt htgRstar htgφ hbudget hres

/-- The collapsed physical modality (generic φinv). -/
theorem multiseg_clocked_physical_gen (G : SearchGraph (Var n)) (mv : Var n)
    (φinv : Formula (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ)
    (htgb : tg ∉ (leftBlock fL).bound) (htgr : tg ∉ (leftBlock fL).readVars)
    (htgϕ : tg ∉ domL.fv) (hdt : 0 ≤ dt)
    (htgR : tg ∉ ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))).fv)
    (htgφ : tg ∉ φinv.fv)
    (hHcouple : ∀ σ', Formula.sat φinv σ' →
      faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
        (rightAutomatonBody G mv) φinv tg dt (Function.update σ' tg 0))
    (hdis : Disjoint (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg dt)))
    (hdMULTI : Disjoint (Program.vars (Program.ode (leftBlock fL) domL))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hbudgetAll : ∀ (σ' : State (Var n)), ∀ {r : ℝ} {Φ : ℝ → State (Var n)},
        ODESol (leftBlock fL) domL σ' r Φ → r ≤ (k : ℝ) * dt)
    {σ : State (Var n)} (hσ : Formula.sat φinv σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.star (Program.ode (leftBlock fL) domL))
      (Program.star (rightAutomatonBody G mv)) φinv) σ :=
  faModal_MULTI (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL) (rightAutomatonBody G mv)
    φinv φinv σ hdMULTI hσ
    (fun σ' hσ' => clocked_residence_physical_gen G mv φinv fL domL tg dt k htgb htgr htgϕ hdt
      htgR htgφ hHcouple hdis hσ' (hbudgetAll σ')) (fun _ h => h)

/-! ## Reification: `ψpostG` encodes to `starInvGF` -/

/-- `inModeGuardF` as a right-projection rel formula. -/
def inModeGuardR (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n) :
    RFormula (Var n) :=
  RFormula.proj DLRel.Side.R (inModeGuardF G Gd mv)

theorem encode_inModeGuardR (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n) :
    encode (Equiv.refl (Var n)) (inModeGuardR G Gd mv) = inModeGuardF G Gd mv := by
  unfold encode inModeGuardR
  simp only [RFormula.renameR, RFormula.enc, Formula.rename_refl]

/-- The guard-threaded precondition (RFormula). -/
def ψpostG (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (ϕinv : RFormula (Var n)) : RFormula (Var n) :=
  RFormula.and ϕinv (RFormula.and (mvValidR mv G.modes.length) (inModeGuardR G Gd mv))

theorem encode_ψpostG (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (g : Term (Var n)) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g) :
    encode (Equiv.refl (Var n)) (ψpostG G Gd mv ϕinv) = starInvGF G Gd mv g := by
  have hand : ∀ a b : RFormula (Var n), encode (Equiv.refl (Var n)) (RFormula.and a b)
      = Formula.and (encode (Equiv.refl (Var n)) a) (encode (Equiv.refl (Var n)) b) := by
    intro a b; unfold encode; simp only [RFormula.renameR, RFormula.enc]
  unfold ψpostG starInvGF
  rw [hand, hand, hψ, encode_mvValidR, encode_inModeGuardR]

/-! ## The Tier B H bundle and the shipped `rvalid` theorem -/

/-- **The guard-threaded settling well-formedness (Tier B H).** Per mode: the guard-based
staying-and-landing (`GuardSettlingB` — dischargeable by construction from the settling-guard
geometry, below) + the `g`-certificate over the shared envelope + the structural plumbing. The
staying obligation quantifies ONLY over guard-region bases — the margin band never enters. -/
def GuardSettlingH (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) (mv : Var n)
    (g : Term (Var n)) (lam : Term (Var n)) (tg : Var n) (dt : ℝ)
    (fL : Fin n → Term (Var n)) (evolShared : Formula (Var n)) : Prop :=
  0 ≤ dt ∧ mv ∉ g.fv ∧ mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound ∧ mv ≠ tg ∧
  (∀ q', mv ∉ (Gd q').fv) ∧ (∀ q', tg ∉ (Gd q').fv) ∧
  (∀ q', ∀ x ∈ (Gd q').fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) ∧
  (∀ q m, G.modeAt q = some m → ∃ fR : Fin n → Term (Var n),
    m.sys = rightBlock fR lam ∧ m.dom = evolShared ∧ q < G.modes.length ∧
    GuardSettlingB G Gd fR lam evolShared dt q ∧
    (∀ ν, Formula.sat (Gd q) ν →
      BoxLe (Program.ode (rightBlock fR lam) evolShared) (fun ω => Term.eval g ω) ν) ∧
    (∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt) ∧
    (∀ q', q' ∈ G.retainedSucc q →
      ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length) ∧
    (∀ q', q' ∈ q :: G.retainedSucc q → q' < G.modes.length →
      ∃ m', G.modeAt q' = some m'))

/-- The clocked coupling from the Tier B H (mirror of `hHcouple_of_LandingWellFormed`). -/
theorem hHcoupleG_of_GuardSettlingH (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (mv : Var n) (g : Term (Var n)) (lam : Term (Var n)) (tg : Var n) (dt : ℝ)
    (fL : Fin n → Term (Var n)) (domL evolShared : Formula (Var n))
    (h : GuardSettlingH G Gd mv g lam tg dt fL evolShared) :
    ∀ σ', Formula.sat (starInvGF G Gd mv g) σ' →
      faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
        (rightAutomatonBody G mv) (starInvGF G Gd mv g) tg dt (Function.update σ' tg 0) := by
  obtain ⟨hdt, hg, hmvLclk, hmvtg, hmvGd, htgGd, hfrzGd, hmodes⟩ := h
  intro σ' hσ'
  obtain ⟨q, m, hqmv, hmode, hqgd⟩ := (sat_starInvGF.mp hσ').2.2
  obtain ⟨fR, hsys, hdom, hqlen, hset, hgboxGd, hself, hsucc, hmodeAll⟩ := hmodes q m hmode
  have hωmv : (Function.update σ' tg 0) mv = (q : ℝ) := by
    rw [Function.update_of_ne hmvtg]; exact hqmv
  have hωgd : Formula.sat (Gd q) (Function.update σ' tg 0) := by
    have heq : Set.EqOn σ' (Function.update σ' tg 0) (Gd q).fv :=
      fun x hx => (Function.update_of_ne (by rintro rfl; exact htgGd q hx) _ _).symm
    exact (Formula.coincidence (Gd q) heq).mp hqgd
  exact landing_step_settling_clocked G Gd mv q m g fL fR lam domL evolShared tg dt
    (Function.update σ' tg 0) hg hmvLclk hmode hsys hdom hqlen hdt hset
    hgboxGd (hfrzGd q) hmvGd hself hsucc hmodeAll hωmv hωgd

/-- **Tier B — the shipped `rvalid` theorem on the guard-threaded settling foundation.**
`rvalid (theorem3Form (ode leftBlock) (rightAutomatonBody) ψpostG)` from `GuardSettlingH`: the
staying obligation quantifies only over guard-region bases (where the settling margin discharges
it by construction — `GuardSettlingB_of_margin_const` / `_of_contract` below), the junction is
trivial (landing in a guard ⊆ the shared envelope), the precondition asks the initial state to
be in some mode's GUARD (`inModeGuardR` — every well-formed benchmark config). Mirrors
`theorem3_faithful_landing_clocked` with the guard-threaded invariant. -/
theorem theorem3_faithful_settling (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (mv : Var n) (g : Term (Var n)) (fL : Fin n → Term (Var n))
    (domL evolShared : Formula (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ) (lam : Term (Var n))
    (ϕinv : RFormula (Var n)) (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hH : GuardSettlingH G Gd mv g lam tg dt fL evolShared)
    (htgb : tg ∉ (leftBlock fL).bound) (htgr : tg ∉ (leftBlock fL).readVars)
    (htgϕ : tg ∉ domL.fv)
    (htgR : tg ∉ ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))).fv)
    (htgφ : tg ∉ (starInvGF G Gd mv g).fv)
    (hdis : Disjoint (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg dt)))
    (hdMULTI : Disjoint (Program.vars (Program.ode (leftBlock fL) domL))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hbudgetAll : ∀ (σ' : State (Var n)), ∀ {r : ℝ} {Φ : ℝ → State (Var n)},
        ODESol (leftBlock fL) domL σ' r Φ → r ≤ (k : ℝ) * dt)
    (hddF : Disjoint (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostG G Gd mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostG G Gd mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (Program.ode (leftBlock fL) domL)
      (rightAutomatonBody G mv) (ψpostG G Gd mv ϕinv)) := by
  set ψpost := ψpostG G Gd mv ϕinv with hψpost
  set Lp := Program.star (Program.ode (leftBlock fL) domL)
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
    rw [← hencψ]; exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  have hphys := multiseg_clocked_physical_gen G mv (starInvGF G Gd mv g) fL domL tg dt k
    htgb htgr htgϕ hH.1 htgR htgφ
    (hHcoupleG_of_GuardSettlingH G Gd mv g lam tg dt fL domL evolShared hH)
    hdis hdMULTI hbudgetAll hInvν
  refine faModal_to_faShape (Equiv.refl (Var n)) Lp Rp ψpost ν bs hddF hbdg ?_
  rw [hencψ]
  exact hphys

/-! ## THE MARGIN-CLASS DISCHARGE — `GuardSettlingB` by construction

The geometry the settling discipline enforces (guard band `[a, cap]`, envelope `[lo, hi]`,
margin `cap + c·dt ≤ hi`, successor guard covering the one-step image), proven with the explicit
affine witness — the staying H is a CONSEQUENCE, not an assumption, for this shape. -/

/-- The constant-rate field on coordinate `Rv j` (`v' = c`), other coordinates frozen. -/
noncomputable def constF (j : Fin n) (c : ℝ) : Fin n → Term (Var n) :=
  fun i => if i = j then Term.const c else Term.const 0

/-- The affine flow `v(t) = v₀ + c·t`, other coordinates frozen. -/
noncomputable def affineΦ (j : Fin n) (c : ℝ) (base : State (Var n)) (t : ℝ) : State (Var n) :=
  fun x => if x = Rv j then base (Rv j) + c * t else base x

theorem affineΦ_other (j : Fin n) (c : ℝ) (base : State (Var n)) (t : ℝ)
    {x : Var n} (hx : x ≠ Rv j) : affineΦ j c base t x = base x := by
  simp [affineΦ, hx]

/-- **The margin-class discharge.** A single-coordinate constant-rate mode (`v' = c ≥ 0`) with
guard band `[a, cap]`, shared envelope band `[lo, hi]`, settling margin `cap + c·dt ≤ hi`
(and `lo ≤ a`), whose one-step image `[a + c·dt, cap + c·dt]` is covered by the guard band
`[a', cap']` of a self-or-successor mode `q'` — satisfies `GuardSettlingB` BY CONSTRUCTION:
the affine witness stays in the envelope (margin) and lands in `Gd q'` (cover). -/
theorem GuardSettlingB_of_margin_const (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (j : Fin n) (q q' : ℕ) (a cap a' cap' lo hi c dt : ℝ)
    (hc : 0 ≤ c) (hdt : 0 ≤ dt)
    (hq' : q' ∈ q :: G.retainedSucc q)
    (hGdq : Gd q = bandDom j a cap) (hGdq' : Gd q' = bandDom j a' cap')
    (hlo : lo ≤ a) (hmargin : cap + c * dt ≤ hi)
    (hcovlo : a' ≤ a + c * dt) (hcovhi : cap + c * dt ≤ cap') :
    GuardSettlingB G Gd (constF j c) (Term.const 1) (bandDom j lo hi) dt q := by
  intro base hb
  rw [hGdq] at hb
  have hba : a ≤ base (Rv j) := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.1
  have hbcap : base (Rv j) ≤ cap := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.2
  refine ⟨affineΦ j c base, ?_, ?_, ?_, ?_, q', hq', ?_⟩
  · -- Φ 0 = base
    funext x
    by_cases hx : x = Rv j
    · subst hx; simp [affineΦ]
    · exact affineΦ_other j c base 0 hx
  · -- derivatives over rightBlock (constF j c) (const 1)
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = j
    · subst hij
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (constF i c i))
          (affineΦ i c base t) = c := by
        simp [constF, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ i c base u (Rv i))
          = fun u => base (Rv i) + c * u := by
        funext u; simp [affineΦ]
      rw [hcurve]
      have h := ((hasDerivAt_id t).const_mul c).const_add (base (Rv i))
      simp only [id, mul_one] at h
      exact h.hasDerivWithinAt
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (constF j c i))
          (affineΦ j c base t) = 0 := by
        simp [constF, hij, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ j c base u (Rv i)) = fun _ => base (Rv i) := by
        funext u
        exact affineΦ_other j c base u
          (fun hc' => hij (by simpa [Rv, Prod.ext_iff] using hc'))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · -- mask
    intro t ht x hx
    have hxj : x ≠ Rv j := by
      intro hcx; subst hcx
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    exact affineΦ_other j c base t hxj
  · -- staying in the envelope band [lo, hi] — the MARGIN argument
    intro t ht
    have hct : 0 ≤ c * t := mul_nonneg hc ht.1
    have hctdt : c * t ≤ c * dt := mul_le_mul_of_nonneg_left ht.2 hc
    constructor
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
      linarith
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
      linarith
  · -- landing: the endpoint is in the covering guard band [a', cap']
    rw [hGdq']
    constructor
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
      linarith
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
      linarith

/-- **The margin-class discharge, two-band form (the realistic shape).** The one-step image
`[a + c·dt, cap + c·dt]` of a growing mode's guard band usually straddles the band itself and
its successor's (arm `Approach [0,0.7] → Return [0.7,…]`, rover `Drive [0.3,0.75] → Safe
[0.75,1.0]`). `GuardSettlingB`'s landing witness is chosen PER BASE, so a case split suffices:
endpoint still `≤ cap` → self-land; endpoint past the cap → land in the successor band (which
starts at or below `cap` and extends past `cap + c·dt`). Margin (`cap + c·dt ≤ hi`) gives the
envelope staying as before. -/
theorem GuardSettlingB_of_margin_const_two (G : SearchGraph (Var n))
    (Gd : ℕ → Formula (Var n)) (j : Fin n) (q q₂ : ℕ) (a cap a₂ cap₂ lo hi c dt : ℝ)
    (hc : 0 ≤ c) (hdt : 0 ≤ dt)
    (hq₂ : q₂ ∈ q :: G.retainedSucc q)
    (hGdq : Gd q = bandDom j a cap) (hGdq₂ : Gd q₂ = bandDom j a₂ cap₂)
    (hlo : lo ≤ a) (hmargin : cap + c * dt ≤ hi)
    (ha₂ : a₂ ≤ cap) (hcap₂ : cap + c * dt ≤ cap₂) :
    GuardSettlingB G Gd (constF j c) (Term.const 1) (bandDom j lo hi) dt q := by
  intro base hb
  rw [hGdq] at hb
  have hba : a ≤ base (Rv j) := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.1
  have hbcap : base (Rv j) ≤ cap := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.2
  have hland : ∃ q' ∈ q :: G.retainedSucc q, Formula.sat (Gd q') (affineΦ j c base dt) := by
    rcases le_or_gt (base (Rv j) + c * dt) cap with hend | hend
    · -- endpoint still under the cap: self-land in [a, cap]
      refine ⟨q, List.mem_cons_self .., ?_⟩
      rw [hGdq]
      have hct : 0 ≤ c * dt := mul_nonneg hc hdt
      constructor
      · show Formula.sat _ _
        simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
        linarith
      · show Formula.sat _ _
        simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
        linarith
    · -- endpoint past the cap: land in the successor band [a₂, cap₂]
      refine ⟨q₂, hq₂, ?_⟩
      rw [hGdq₂]
      have hendhi : base (Rv j) + c * dt ≤ cap + c * dt := by linarith
      constructor
      · show Formula.sat _ _
        simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
        linarith
      · show Formula.sat _ _
        simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
        linarith
  obtain ⟨q', hq'mem, hq'land⟩ := hland
  refine ⟨affineΦ j c base, ?_, ?_, ?_, ?_, q', hq'mem, hq'land⟩
  · funext x
    by_cases hx : x = Rv j
    · subst hx; simp [affineΦ]
    · exact affineΦ_other j c base 0 hx
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = j
    · subst hij
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (constF i c i))
          (affineΦ i c base t) = c := by
        simp [constF, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ i c base u (Rv i))
          = fun u => base (Rv i) + c * u := by
        funext u; simp [affineΦ]
      rw [hcurve]
      have h := ((hasDerivAt_id t).const_mul c).const_add (base (Rv i))
      simp only [id, mul_one] at h
      exact h.hasDerivWithinAt
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (constF j c i))
          (affineΦ j c base t) = 0 := by
        simp [constF, hij, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => affineΦ j c base u (Rv i)) = fun _ => base (Rv i) := by
        funext u
        exact affineΦ_other j c base u
          (fun hc' => hij (by simpa [Rv, Prod.ext_iff] using hc'))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have hxj : x ≠ Rv j := by
      intro hcx; subst hcx
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    exact affineΦ_other j c base t hxj
  · intro t ht
    have hct : 0 ≤ c * t := mul_nonneg hc ht.1
    have hctdt : c * t ≤ c * dt := mul_le_mul_of_nonneg_left ht.2 hc
    constructor
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
      linarith
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval, affineΦ, if_pos rfl, if_true]
      linarith

/-- **The contractive-class discharge (self-landing).** A contractive coordinate
(`v' = k(c − v)`, equilibrium `c` inside the mode's OWN guard band `[a, cap]` ⊆ envelope
`[lo, hi]`) satisfies `GuardSettlingB` by construction: the exponential flow stays between the
base and the equilibrium — inside the guard band, hence inside the envelope — and self-lands. -/
theorem GuardSettlingB_of_contract (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (j : Fin n) (q : ℕ) (a cap lo hi k c dt : ℝ)
    (hk : 0 ≤ k) (hdt : 0 ≤ dt)
    (hGdq : Gd q = bandDom j a cap)
    (hca : a ≤ c) (hccap : c ≤ cap) (hlo : lo ≤ a) (hhi : cap ≤ hi) :
    GuardSettlingB G Gd (contractF j k c) (Term.const 1) (bandDom j lo hi) dt q := by
  intro base hb
  rw [hGdq] at hb
  have hba : a ≤ base (Rv j) := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.1
  have hbcap : base (Rv j) ≤ cap := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.2
  -- the flow stays in the guard band [a, cap] for all t ≥ 0 (between base and equilibrium)
  have hband : ∀ t, 0 ≤ t → a ≤ contractΦ j k c base t (Rv j)
      ∧ contractΦ j k c base t (Rv j) ≤ cap := by
    intro t ht
    have hθpos : 0 < Real.exp (-(k * t)) := Real.exp_pos _
    have hθle : Real.exp (-(k * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [contractΦ_Rvj]
    constructor
    · rcases le_or_gt c (base (Rv j)) with hbc | hbc
      · nlinarith
      · nlinarith
    · rcases le_or_gt c (base (Rv j)) with hbc | hbc
      · nlinarith
      · nlinarith
  -- the explicit exponential witness (same construction as `WellFormedFlowB_contract`)
  refine ⟨contractΦ j k c base, ?_, ?_, ?_, ?_, q, List.mem_cons_self .., ?_⟩
  · funext x
    by_cases hx : x = Rv j
    · subst hx; simp [contractΦ]
    · exact contractΦ_other j k c base 0 hx
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = j
    · subst hij
      have hd := (contractΦ_hasDeriv i k c base t).hasDerivWithinAt (s := Icc 0 dt)
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (contractF i k c i))
          (contractΦ i k c base t) = k * (c - contractΦ i k c base t (Rv i)) := by
        simp [contractF, Term.eval, AOp.interp]
      rw [heval]
      exact hd
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (contractF j k c i))
          (contractΦ j k c base t) = 0 := by
        simp [contractF, hij, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => contractΦ j k c base u (Rv i)) = fun _ => base (Rv i) := by
        funext u
        exact contractΦ_other j k c base u
          (fun hc' => hij (by simpa [Rv, Prod.ext_iff] using hc'))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · intro t ht x hx
    have hxj : x ≠ Rv j := by
      intro hcx; subst hcx
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    exact contractΦ_other j k c base t hxj
  · -- staying in the envelope: the guard band [a,cap] ⊆ [lo,hi] and the flow stays in it
    intro t ht
    obtain ⟨h1, h2⟩ := hband t ht.1
    constructor
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval]
      linarith
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval]
      linarith
  · -- self-landing: the endpoint is still in the OWN guard band [a, cap]
    rw [hGdq]
    obtain ⟨h1, h2⟩ := hband dt hdt
    constructor
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval]
      linarith
    · show Formula.sat _ _
      simp only [bandDom, Formula.sat, CompOp.interp, Term.eval]
      linarith

end RelCertifier
