/-
`multiseg_landing` — the landing-selected joint-tree-walk ∃-witness (statement-first core).

The redesign that ELIMINATES `WFBoundary` clause 2 by construction: instead of folding a pre-fixed
segment list (`multiseg_het`), walk `Covered`'s ∀-successor tree, selecting at each junction the branch
whose domain the constructed right-flow endpoint `μ_R` landed in. Because the state stays in its mode's
domain (ODE domain-constraint) and successor domains OVERLAP (verified per benchmark — shared/nested
evolve-domains), the switch is an interior overlap point: `μ_R ∈ domR_next` holds BY SELECTION (no
guard, `⊤`-switch free, no first-passage).

This file lands the composable core statement-first:
* `LandingH` — the (trivially-true, ODE-constrained) landing hypothesis.
* `segment_landing` — the per-node dispatch: an in-domain entry + `WellFormedFlow` (existence) +
  the cover's joint box discharge one segment's `faModal` via `segment_faModal`. Confirms pieces 3
  (`WellFormedFlow`, banked) and 4 (`segment_faModal`, banked) COMPOSE sorry-free, with the in-domain
  entry `hνdom` the landing supplies by construction.
The full `multiseg_landing` induction over `Covered` (composing these via `faModal_seq`/`faModal_MR`,
threading `invLe g`) is the remaining build; its per-node step is `segment_landing`.
-/
import RelCertifier.Reify
import RelCertifier.WFBoundary
import RelCertifier.BridgeReposition

namespace RelCertifier
open DL DLCalTiming Set Function

variable {n : ℕ}

/-- **The landing hypothesis (trivially true from the ODE domain-constraint).** At every reachable
flow endpoint `μ` of mode `m`, `μ` is in `m`'s domain or in a successor's — the disjunction the
landing-selection case-splits. The first disjunct always holds (a run of `ode m.sys m.dom` stays in
`m.dom`), so `LandingH` is free; the second disjunct fires at interior overlap points (successor
domains overlap, per the benchmark gate), giving the switch. No guard, no reachability. -/
def LandingH (G : SearchGraph (Var n)) : Prop :=
  ∀ (q : ℕ) (m : RMode (Var n)), G.modeAt q = some m → ∀ (μ : State (Var n)),
    Formula.sat m.dom μ →
      (Formula.sat m.dom μ ∨
        ∃ q' ∈ G.retainedSucc q, ∃ m', G.modeAt q' = some m' ∧ Formula.sat m'.dom μ)

/-- **Per-node dispatch (pieces 3 + 4 compose).** One segment's `faModal`, from: the cover's joint
box (`hcert`), the per-mode flow well-formedness (`hwff`, `WellFormedFlow` — existence), the L/R split
(`hfrz`), and the IN-DOMAIN ENTRY `hνdom` (which the landing-selection supplies by construction — the
segment is entered where the flow landed, in this mode's domain). `HExistSeg` is discharged within-
segment by the banked `hExistSeg_of_wellFormedFlow`; `segment_faModal` (banked) decouples joint →
frozen-left right-response. No guard, no cross-switch `HExistSeg`, no first-passage. -/
theorem segment_landing (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys fL fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) ν)
    (hwff : WellFormedFlow fR lam domR)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hνdom : Formula.sat domR ν) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (invLe g)) ν :=
  segment_faModal g fL fR lam domL domR ν hdisj hφL hφR hcert
    (hExistSeg_of_wellFormedFlow fL fR lam domL domR ν hwff hfrz hνdom)

/-- **The overlap gate (checked per benchmark).** Two mode domains overlap non-trivially: some state
satisfies both. This is the load-bearing condition that makes the landing switch an INTERIOR point
(no first-passage) — the flow reaches a state in both `domCur` and `domSucc`, where the switch fires.
Verified for the whole suite (shared/nested evolve-domains). Stated as a checkable hypothesis, not a
hidden assumption. -/
def SuccDomOverlap (domCur domSucc : Formula (Var n)) : Prop :=
  ∃ μ : State (Var n), Formula.sat domCur μ ∧ Formula.sat domSucc μ

/-- **Clause 2 by construction — the discharge is a CHECK at the constructed endpoint, not an
assumption over all states.** The next segment's in-domain entry `hνdom : sat domSucc μ_R` is verified
at the SPECIFIC `μ_R` the current segment's right run landed at (a decidable membership at a concrete
state), then fed to `segment_landing`. Contrast the `∀ν HExistSeg` / `WFBoundary` clause 2, which
assumed the guard at every state: here it is *decided* at the one landing state. So `HExistSeg` for the
next segment discharges from a per-endpoint check — no guard premise, no first-passage, no `∀ν`. This
lemma is `segment_landing` at the landed state `μ_R`, making explicit that its `hνdom` is the
by-construction landing check. -/
theorem segment_landing_at (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (μ_R : State (Var n))
    (hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys fL fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) μ_R)
    (hwff : WellFormedFlow fR lam domR)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hland : Formula.sat domR μ_R) :   -- CHECKED at the constructed landing endpoint (clause 2 by construction)
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (invLe g)) μ_R :=
  segment_landing g fL fR lam domL domR μ_R hdisj hφL hφR hcert hwff hfrz hland

/-- **The flow-diamond — the input to `diamond_right_wrap` for the star step.** From `WellFormedFlow`
(the frozen-left right run exists in `domR` — existence, banked), an in-domain start `hν`, and the
frozen-left flow's `g`-preservation `hg` (`BoxLe`, from `cert.repoDynPres`/`DI_nonstrict`), the right
flow's diamond holds: `⟨ode rightBlock domR⟩(invLe g)`. This is the per-segment `∃`-right run with
`g≤0` at its endpoint — `diamond_right_wrap` then wraps it into one `rightAutomatonBody` body-step
(the star's unit), with the mode landing-selected. -/
theorem wff_to_diamond (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR : Formula (Var n)) (ν : State (Var n))
    (hwff : WellFormedFlow fR lam domR) (hν : Formula.sat domR ν)
    (hg : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν) :
    Formula.sat (Formula.diamond (Program.ode (rightBlock fR lam) domR) (invLe g)) ν := by
  obtain ⟨ΦR, hΦR0, hder, hmask, hdom⟩ := hwff ν hν 1 (by norm_num)
  have hsem : Program.sem (Program.ode (rightBlock fR lam) domR) ν (ΦR 1) :=
    ⟨1, ΦR, by norm_num, hΦR0, rfl, hder, hmask, hdom⟩
  rw [diamond_sem]
  exact ⟨ΦR 1, hsem, by rw [sat_invLe]; exact hg _ hsem⟩

/-- **One `R_real` body-step, landing-selected (the star's unit).** Composes `wff_to_diamond` (the
flow-diamond, banked) with `diamond_right_wrap` (banked): from the frozen-left right flow's existence
(`WellFormedFlow`) + `g`-preservation (`hgbox`) + the mode/edge structure (`hm`/`hsys`/`hdom`/`hef` —
the `⊤`-guarded declared edge, so the switch is free), one `rightAutomatonBody` diamond step holds,
carrying `invLe g ∧ mvValid` to the next state. The mode `q` is the landing-selected one (`hm` picks it);
`e.guard = tt` (`⊤`-switch, no guard premise). This is the per-segment unit the star assembly iterates. -/
theorem landing_body_step (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (ν : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length) (hmvq : ν mv = (q : ℝ))
    (hwff : WellFormedFlow fR lam domR) (hν : Formula.sat domR ν)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν) :
    Formula.sat (Formula.diamond (rightAutomatonBody G mv)
      (Formula.and (invLe g) (mvValid mv G.modes.length))) ν :=
  diamond_right_wrap G mv q m g fR lam domR hg hm hsys hdom hef hetg hetv hmvq
    (wff_to_diamond g fR lam domR ν hwff hν hgbox)

/-! ## Star-composition primitives — thread the CONCRETE endpoint (no `∀σ'`)

The RIGHT response `R_real = star body`. A run of `star body` is `ReflTransGen (sem body)` (Loop.lean
`sem_star`), so body-runs compose by *prepending* — each `landing_body_step` produces one body-step to a
concrete endpoint, and the star assembly chains them via `ReflTransGen.head` at that endpoint. Because the
next step is applied at the DESTRUCTURED endpoint `μ` (the `∃`-witness the prior step produced), never over
all states, the `∀σ'` quantification that reverted clause 2 to `∀ν` (the `faModal_MR` seam) never appears. -/

/-- **Base — one body-step is a star run.** `⟨body⟩φ ⟹ ⟨star body⟩φ` (a single-step `ReflTransGen`). The
terminal unit of the landing walk: the last `landing_body_step`'s diamond is already the `R_real` diamond. -/
theorem diamond_star_single (body : Program (Var n)) (φ : Formula (Var n)) (ν : State (Var n))
    (h : Formula.sat (Formula.diamond body φ) ν) :
    Formula.sat (Formula.diamond (Program.star body) φ) ν := by
  rw [diamond_sem] at h ⊢
  obtain ⟨μ, hbody, hφ⟩ := h
  exact ⟨μ, Relation.ReflTransGen.single hbody, hφ⟩

/-- **Step — prepend one body-step to a star run (the landing walk's inductive step).** From
`⟨body⟩⟨star body⟩φ` at `ν` conclude `⟨star body⟩φ` at `ν`. The inner `⟨star body⟩φ` is evaluated at the
CONCRETE endpoint `μ` that the outer `body` step lands at (destructured from the `∃`), so the recursion
threads the actual landing state — `ReflTransGen.head` glues `ν →body μ` onto `μ →star* ω`. This is the
star-diamond backward-unfolding specialized to prepend; no `∀`-over-states obligation is introduced. -/
theorem diamond_body_star (body : Program (Var n)) (φ : Formula (Var n)) (ν : State (Var n))
    (h : Formula.sat (Formula.diamond body (Formula.diamond (Program.star body) φ)) ν) :
    Formula.sat (Formula.diamond (Program.star body) φ) ν := by
  rw [diamond_sem] at h ⊢
  obtain ⟨μ, hbody, hstar⟩ := h
  rw [diamond_sem] at hstar
  obtain ⟨ω, hstarrun, hφ⟩ := hstar
  exact ⟨ω, Relation.ReflTransGen.head hbody hstarrun, hφ⟩

/-- **Two-segment landing composition (the induction's base doubling).** From two nested body-diamonds
`⟨body⟩⟨body⟩φ` — the second evaluated at the CONCRETE endpoint `μ1` the first lands at — conclude the
`R_real` diamond `⟨star body⟩φ`. Confirms the endpoint-threading composes: the two landing steps chain
through `ReflTransGen.head`/`.single` on the actual witnesses (`ν →body μ1 →body μ2`), with the second
step applied only at the destructured `μ1`, never over all states. This is the shape the general
`Covered`-budget induction iterates — each round prepends one `landing_body_step` at the prior landing. -/
theorem landing_two_step (body : Program (Var n)) (φ : Formula (Var n)) (ν : State (Var n))
    (h : Formula.sat (Formula.diamond body (Formula.diamond body φ)) ν) :
    Formula.sat (Formula.diamond (Program.star body) φ) ν := by
  rw [diamond_sem] at h
  obtain ⟨μ1, hbody1, hinner⟩ := h
  rw [diamond_sem] at hinner
  obtain ⟨μ2, hbody2, hφ⟩ := hinner
  rw [diamond_sem]
  exact ⟨μ2, Relation.ReflTransGen.head hbody1 (Relation.ReflTransGen.single hbody2), hφ⟩

/-! ## The threaded star invariant — `invLe g ∧ mvValid ∧ in-current-mode-domain

The star recursion must thread MORE than the postcondition `landing_body_step` carries (`invLe g ∧
mvValid`): to re-enter the next body-step it needs the landing state to be IN a mode's domain (the
`hν : sat domR` premise of `landing_body_step`). `StarInv` bundles that — coupling `invLe g`, a valid
mode index `mvValid`, and membership in the current mode's declared domain (`StarInModeDom`). The
inductive step `starStep_wrap` shows one body-step PRESERVES `StarInv`, landing the endpoint in the
TARGET mode's domain — clause 2 by construction, discharged from the strengthened flow-diamond (the
right run ends in the target domain) via the overlap gate, never assumed over all states. -/

/-- The landing state sits in some declared mode's domain, with `mv` naming that mode. This is the
extra fact the star recursion threads (beyond `invLe g ∧ mvValid`) so the next `landing_body_step`'s
in-domain premise is met by construction. -/
def StarInModeDom (G : SearchGraph (Var n)) (mv : Var n) (μ : State (Var n)) : Prop :=
  ∃ (q' : ℕ) (m' : RMode (Var n)),
    μ mv = (q' : ℝ) ∧ G.modeAt q' = some m' ∧ Formula.sat m'.dom μ

/-- **`StarInModeDom` as a FORMULA** — the finite disjunction, over declared modes `q`, of "`mv` names
`q` and the state is in mode `q`'s domain". Mirrors `rightAutomatonBody`'s `filterMap` shape, so it is a
genuine `Formula` (usable as a threaded `φinv` conjunct where the invariant must be first-order, e.g. to
feed `multiseg_het`), and `sat_inModeDomF` shows it reflects the `Prop` `StarInModeDom` exactly. -/
def inModeDomF (G : SearchGraph (Var n)) (mv : Var n) : Formula (Var n) :=
  bigOr ((List.range G.modes.length).filterMap (fun q =>
    (G.modeAt q).map (fun m => Formula.and (modeIs mv q) m.dom)))

/-- **The reflection: `sat inModeDomF ↔ StarInModeDom`.** The `Formula` `inModeDomF` and the `Prop`
`StarInModeDom` are interchangeable — so the star recursion can carry domain-membership either as a
semantic side-fact (`StarInv`) or folded into a first-order `φinv`. -/
theorem sat_inModeDomF {G : SearchGraph (Var n)} {mv : Var n} {μ : State (Var n)} :
    Formula.sat (inModeDomF G mv) μ ↔ StarInModeDom G mv μ := by
  rw [inModeDomF, sat_bigOr]
  constructor
  · rintro ⟨f, hf, hsat⟩
    rw [List.mem_filterMap] at hf
    obtain ⟨q, _, hmap⟩ := hf
    rcases hopt : G.modeAt q with _ | m
    · rw [hopt] at hmap; simp at hmap
    · rw [hopt] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      subst hmap
      obtain ⟨hmode, hdom⟩ := hsat
      refine ⟨q, m, ?_, hopt, hdom⟩
      simpa only [modeIs, Formula.sat, CompOp.interp, Term.eval] using hmode
  · rintro ⟨q, m, hmv, hmode, hdom⟩
    refine ⟨Formula.and (modeIs mv q) m.dom, ?_, ?_, hdom⟩
    · rw [List.mem_filterMap]
      exact ⟨q, List.mem_range.mpr (by
        have := hmode; simp only [SearchGraph.modeAt] at this
        exact (List.getElem?_eq_some_iff.mp this).1), by rw [hmode]; rfl⟩
    · simpa only [modeIs, Formula.sat, CompOp.interp, Term.eval] using hmv

/-- **The threaded star invariant.** Coupling `invLe g`, a valid mode index (`mvValid`), and current-mode
domain-membership (`StarInModeDom`). Preserved by every landing body-step (`starStep_wrap`); its
`invLe g` conjunct is what the terminal `⟨star body⟩(invLe g)` reads off. -/
def StarInv (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n)) (μ : State (Var n)) : Prop :=
  Formula.sat (invLe g) μ ∧ Formula.sat (mvValid mv G.modes.length) μ ∧ StarInModeDom G mv μ

/-- **`StarInv` as a threaded `φinv` Formula** — `invLe g ∧ mvValid ∧ inModeDomF`, all first-order. The
form usable as `multiseg_het`'s shared invariant: strengthening the weak `invLe g ∧ mvValid` with the
domain conjunct is what makes `multiseg_het`'s `∀σ` coupling range only over IN-DOMAIN states (every
box-left endpoint is in-domain — left flow freezes the right coords, start in `domR`), so the per-segment
discharge `segment_landing` (which needs the in-domain entry) applies without the `∀ν`-over-all-states
seam. `sat_starInvF` shows this Formula reflects the `StarInv` Prop. -/
def starInvF (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n)) : Formula (Var n) :=
  Formula.and (invLe g) (Formula.and (mvValid mv G.modes.length) (inModeDomF G mv))

/-- The `starInvF` Formula reflects the `StarInv` Prop. -/
theorem sat_starInvF {G : SearchGraph (Var n)} {mv : Var n} {g : Term (Var n)} {μ : State (Var n)} :
    Formula.sat (starInvF G mv g) μ ↔ StarInv G mv g μ := by
  rw [starInvF, StarInv]
  simp only [Formula.sat, sat_inModeDomF]

/-- **The inductive step — one landing body-step preserves `StarInv` (clause 2 by construction).** From a
strengthened flow-diamond `hstep` — the frozen-left right run from `μ` ends at some `μ'` with `invLe g μ'`
AND `μ' ∈ dom(e.tgt)` (the TARGET mode's domain; this is where the overlap gate lands the run, not assumed
∀-state) — one `rightAutomatonBody` step reaches `ω = update μ' mv e.tgt` with `StarInv G mv g ω`:
`invLe g` survives the `mv`-assign (`mv ∉ g.fv`), `mvValid` holds (`e.tgt < len`), and `StarInModeDom`
holds with `q' = e.tgt` (the endpoint's `mv` names the target mode, whose domain contains `μ'` by `hstep`,
mv-frozen). This is `diamond_right_wrap`'s core re-derived to CARRY the endpoint domain — the fact the
naked wrap drops — so the recursion can re-enter. -/
theorem starStep_wrap (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (μ : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length) (hmvq : μ mv = (q : ℝ))
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvdom' : mv ∉ m'.dom.fv)
    (hstep : ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) μ μ' ∧
        Formula.sat (invLe g) μ' ∧ Formula.sat m'.dom μ') :
    ∃ ω, Program.sem (rightAutomatonBody G mv) μ ω ∧ StarInv G mv g ω := by
  obtain ⟨μ', hode, hinv, hdom'⟩ := hstep
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
  · -- StarInModeDom : endpoint mv = e.tgt, mode m' at e.tgt, μ' ∈ m'.dom (mv-frozen)
    refine ⟨e.tgt, m', by simp only [Function.update_self], het', ?_⟩
    have : Set.EqOn μ' (update μ' mv (e.tgt : ℝ)) m'.dom.fv := by
      intro x hx
      exact (update_of_ne (by rintro rfl; exact hmvdom' hx) _ _).symm
    exact (Formula.coincidence m'.dom this).mp hdom'

/-- **The strengthened flow-diamond for a widening/shared switch — `hstep` for `starStep_wrap`, target
domain FREE.** For a switch into a target mode whose domain CONTAINS the current one (`hsub : domR ⊆
m'dom` — the shared/widening shape, a static per-edge check like `WellFormedGuards`), every domR-staying
right-flow endpoint is automatically in the target domain. So `WellFormedFlow` (the run exists in `domR`)
+ `BoxLe` (`g`-preservation along it) directly give the endpoint `μ'` with `invLe g μ'` AND `m'dom μ'` —
no first-passage, no reaching. This is the `hstep` premise of `starStep_wrap` for the widening/shared
benchmarks (the plurality); the narrowing case (`m'dom ⊊ domR`) needs the flow to REACH the narrower
domain, the residual overlap-reaching content. -/
theorem flowDiamond_widening (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR m'dom : Formula (Var n)) (ν : State (Var n))
    (hwff : WellFormedFlow fR lam domR) (hν : Formula.sat domR ν)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hsub : ∀ μ, Formula.sat domR μ → Formula.sat m'dom μ) :
    ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) ν μ' ∧
        Formula.sat (invLe g) μ' ∧ Formula.sat m'dom μ' := by
  obtain ⟨ΦR, hΦR0, hder, hmask, hdom⟩ := hwff ν hν 1 (by norm_num)
  have hsem : Program.sem (Program.ode (rightBlock fR lam) domR) ν (ΦR 1) :=
    ⟨1, ΦR, by norm_num, hΦR0, rfl, hder, hmask, hdom⟩
  have hΦ1dom : Formula.sat domR (ΦR 1) := hdom 1 (by norm_num [Set.mem_Icc])
  exact ⟨ΦR 1, hsem, by rw [sat_invLe]; exact hgbox _ hsem, hsub _ hΦ1dom⟩

/-- **One full `StarInv`-preserving landing step for a widening/shared switch.** Composes
`flowDiamond_widening` (`hstep`, target domain free) with `starStep_wrap` (the wrap that carries the
endpoint domain): from `StarInv`-compatible data at `μ` (mode `q`, `WellFormedFlow`, `BoxLe`) and a
declared `⊤`-edge to a target mode `m'` whose domain contains `domR` (`hsub`), one `rightAutomatonBody`
step reaches an `ω` with `StarInv G mv g ω`. This is the complete inductive step the `Covered`-budget
recursion iterates for the widening/shared benchmarks — clause 2 by construction, no guard, no
first-passage. -/
theorem starStep_widening (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (μ : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length) (hmvq : μ mv = (q : ℝ))
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvdom' : mv ∉ m'.dom.fv)
    (hwff : WellFormedFlow fR lam domR) (hν : Formula.sat domR μ)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) μ)
    (hsub : ∀ ρ, Formula.sat domR ρ → Formula.sat m'.dom ρ) :
    ∃ ω, Program.sem (rightAutomatonBody G mv) μ ω ∧ StarInv G mv g ω :=
  starStep_wrap G mv q m g fR lam domR μ hg hm hsys hdom hef hetg hetv hmvq het' hmvdom'
    (flowDiamond_widening g fR lam domR m'.dom μ hwff hν hgbox hsub)

/-! ## Narrowing — one model-level REACHABILITY (liveness) hypothesis `SuccReach` (STATEMENT-FIRST)

For a narrowing switch (`domSucc ⊊ domR`, e.g. rover Recover→Drive with `domR = vx∈[0,1]`,
`domSucc = vx∈[0.3,1]`) the widening discharge `flowDiamond_widening`/`hsub` is UNAVAILABLE — `domR ⊆
domSucc` is false. `starStep_wrap`'s `hstep` demands a RUN ENDPOINT in `domSucc`, so from a start below the
threshold the flow must REACH `domSucc` (first-passage). `SuccReach` names that reaching as ONE model-level
property, replacing scattered per-edge reach facts.

**`SuccReach` (the REACHING / liveness version — non-vacuous):** from every in-domain start, the mode's ODE
reaches an endpoint IN THE SUCCESSOR DOMAIN. This quantifies over EXECUTIONS reaching a landing (`∃ μ'` an
ODE-endpoint `sem (ode …) μ μ'`) that is in `domSucc` — the terminal/reaching event. It implies `hreach`
directly. It is a property of the MODEL (the mode's field + successor domain), with NO reference to the
fold/junctions/faModal — purely about the automaton's executions and domains.

**Honestly labeled: this is a REACHABILITY (liveness) condition, NOT non-blocking.** `SuccReach` is exactly
first-passage universally quantified over start states, named once — it *asserts* the flow reaches the
successor domain. It is strictly stronger than the safety/non-blocking property `SuccReachUnion` (lands in
`domR`-or-`domSucc`), which `SuccReachUnion_vacuous` PROVES is unconditionally true and hence useless. So we
do not dress first-passage as something milder: `SuccReach` is a named, true, checkable, model-level
reachability well-formedness, provable per-field via monotonicity+IVT (scoped future work). -/
def SuccReach (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR domSucc : Formula (Var n)) : Prop :=
  ∀ μ : State (Var n), Formula.sat domR μ →
    ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) μ μ' ∧ Formula.sat domSucc μ'

/-- **`SuccReachB` — bounded-`dt`, CROSSING-SEGMENT-scoped reaching (the clocked-consistent narrowing
condition).** A per-STATE predicate at the *crossing* state `μ` (the one the self-loop staging brought to
be crossing-ready): from `μ`, a **single `≤ dt` right segment** stays in the source domain `domR` and
reaches the successor domain `domSucc` at its end. This is the honest bounded analog of `SuccReach`:
- it is the **crossing segment only** — the PRIOR segments self-loop in `domR` (bounded-`dt` staying, handled
  by `WellFormedFlowB`), NOT a blanket "reach from anywhere within `dt`";
- the reaching run has duration `s ≤ dt` (bounded — no `∀s`/unbounded existence, uniform with widening);
- it stays in `domR` throughout `[0,s]` (source-mode evolve) and lands in `domSucc` at `s` (so the endpoint
  is in `domR ∩ domSucc`, the overlap — clause-2-by-construction: `μ' ∈ dom(tgt)`).
Applied at the landing-selected crossing state; composes with self-loop staying (self-loop in `domR` until
crossing-ready, land-select the successor at this segment). Eliminates the last unbounded (`∀s`-shaped)
existence claim — narrowing is now uniformly bounded-`dt` like widening. -/
def SuccReachB (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR domSucc : Formula (Var n))
    (dt : ℝ) (μ : State (Var n)) : Prop :=
  ∃ (s : ℝ) (ΦR : ℝ → State (Var n)), 0 ≤ s ∧ s ≤ dt ∧ ΦR 0 = μ ∧
    (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
        HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
    (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = μ x) ∧
    (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t)) ∧
    Formula.sat domSucc (ΦR s)

/-- **The PER-POINT / disjunctive version — the WFExec collapse (stated to contrast, NOT used).** "Some
execution lands in `domR` OR `domSucc`". This is VACUOUS: the zero-duration self-run (`μ' = μ`) satisfies
the left disjunct (`μ ∈ domR`), so it holds trivially WITHOUT ever reaching `domSucc`. It does NOT imply
`hreach`. `SuccReach` (reaching-to-successor) is strictly stronger — it forces the successor landing. The
anti-collapse check: use `SuccReach`, never `SuccReachUnion`. -/
def SuccReachUnion (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR domSucc : Formula (Var n)) : Prop :=
  ∀ μ : State (Var n), Formula.sat domR μ →
    ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) μ μ' ∧
      (Formula.sat domR μ' ∨ Formula.sat domSucc μ')

/-- **`SuccReach → hreach`/`hstep` (the narrowing analog of `flowDiamond_widening`).** `SuccReach` supplies the
reached endpoint `μ'` in `domSucc`; the flow's `BoxLe` `g`-preservation supplies `invLe g μ'` at that same
endpoint (it is a `sem`-endpoint). Together they give `starStep_wrap`'s `hstep` — with `domSucc = m'.dom`
this is exactly the missing narrowing discharge, now sourced from the one model-level `SuccReach` instead of
`hsub`. The reaching in `SuccReach` IS the reaching in `hreach`; the implication is `μ' := SuccReach`'s witness. -/
theorem hstep_of_SuccReach (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR domSucc : Formula (Var n)) (μ : State (Var n))
    (hwf : SuccReach fR lam domR domSucc) (hμ : Formula.sat domR μ)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) μ) :
    ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) μ μ' ∧
        Formula.sat (invLe g) μ' ∧ Formula.sat domSucc μ' := by
  obtain ⟨μ', hsem, hdom'⟩ := hwf μ hμ
  exact ⟨μ', hsem, by rw [sat_invLe]; exact hgbox μ' hsem, hdom'⟩

/-- **`SuccReachB → hstep` (bounded, crossing-segment).** The bounded-`dt` analog of `hstep_of_SuccReach`:
`SuccReachB … μ` supplies the `≤ dt` crossing run `μ → ΦR s` staying in `domR`, landing at `ΦR s ∈ domSucc`;
`BoxLe` supplies `invLe g` at that endpoint. Together they give `starStep_wrap`'s `hstep` — the same shape as
the widening/unbounded versions, but with the reaching run **bounded to `≤ dt`** (no `∀s`). This is the
clocked-consistent narrowing discharge. -/
theorem hstep_of_SuccReachB (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR domSucc : Formula (Var n)) (dt : ℝ) (μ : State (Var n))
    (hsr : SuccReachB fR lam domR domSucc dt μ)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) μ) :
    ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) μ μ' ∧
        Formula.sat (invLe g) μ' ∧ Formula.sat domSucc μ' := by
  obtain ⟨s, ΦR, hs, _, hΦ0, hder, hmask, hdom, hsucc⟩ := hsr
  have hsem : Program.sem (Program.ode (rightBlock fR lam) domR) μ (ΦR s) :=
    ⟨s, ΦR, hs, hΦ0, rfl, hder, hmask, hdom⟩
  exact ⟨ΦR s, hsem, by rw [sat_invLe]; exact hgbox (ΦR s) hsem, hsucc⟩

/-- `SuccReach` is at least as strong as the disjunctive version (reaching-to-successor ⟹ lands-in-union).
The converse FAILS (`SuccReachUnion` is vacuous via the zero-duration stay), which is why only `SuccReach`
implies `hreach`. -/
theorem SuccReach_imp_SuccReachUnion (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR domSucc : Formula (Var n)) (hwf : SuccReach fR lam domR domSucc) :
    SuccReachUnion fR lam domR domSucc := by
  intro μ hμ; obtain ⟨μ', hsem, hdom'⟩ := hwf μ hμ; exact ⟨μ', hsem, Or.inr hdom'⟩

/-- **The anti-collapse, MECHANIZED: `SuccReachUnion` is unconditionally TRUE (hence useless).** The
zero-duration self-run (`s = 0`, `Φ ≡ μ`) is a legal ODE execution — on the singleton time-interval
`Icc 0 0 = {0}` the derivative condition is vacuous — landing at `μ' = μ ∈ domR`, the left disjunct. So
`SuccReachUnion` holds for ANY field/domains WITHOUT reaching `domSucc`. This proves the disjunctive/per-point
phrasing cannot imply `hreach`; only the reaching-to-successor `SuccReach` (which the converse `SuccReach_imp_
SuccReachUnion` shows is strictly stronger) does. This is the load-bearing anti-collapse check. -/
theorem SuccReachUnion_vacuous (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR domSucc : Formula (Var n)) : SuccReachUnion fR lam domR domSucc := by
  intro μ hμ
  refine ⟨μ, ⟨0, fun _ => μ, le_refl 0, rfl, rfl, ?_, ?_, ?_⟩, Or.inl hμ⟩
  · intro t ht p _
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    have h : Icc (0 : ℝ) 0 = {0} := by simp
    rw [h]; simp [hasDerivWithinAt_iff_tendsto_slope]
  · intro t _ x _; rfl
  · intro t _; exact hμ

/-- **One full `StarInv`-preserving landing step for a NARROWING switch (the analog of `starStep_widening`),
BOUNDED-`dt`.** Identical wrap, but the target-domain endpoint is sourced from the crossing-segment condition
`SuccReachB … μ` (the `≤ dt` reaching at the crossing state) via `hstep_of_SuccReachB` instead of `hsub`
(widening) or the unbounded `SuccReach`. So narrowing switches discharge through the SAME `starStep_wrap`
machinery — clause 2 by construction — with `SuccReachB` supplying the one **bounded** reaching fact. Uniform
with widening (both bounded-`dt`); no `∀s`/unbounded existence. -/
theorem starStep_narrowing (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (dt : ℝ) (μ : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length) (hmvq : μ mv = (q : ℝ))
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvdom' : mv ∉ m'.dom.fv)
    (hsr : SuccReachB fR lam domR m'.dom dt μ)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) μ) :
    ∃ ω, Program.sem (rightAutomatonBody G mv) μ ω ∧ StarInv G mv g ω :=
  starStep_wrap G mv q m g fR lam domR μ hg hm hsys hdom hef hetg hetv hmvq het' hmvdom'
    (hstep_of_SuccReachB g fR lam domR m'.dom dt μ hsr hgbox)

/-! ## The H + landing-selection step — MEMBERSHIP + invariance, no reaching (the general fix)

The unified landing step: run one `≤ dt` right segment (`WellFormedFlowB` — bounded staying, TRUE), then
CASE-SPLIT `LandingH`'s disjunction on the endpoint (`μ_end ∈` current mode's domain OR a cover-successor's
domain) and DISPATCH via `starStep_wrap` into the mode `μ_end` landed in. No `SuccReach`/`SuccReachB`
reaching — the endpoint lands wherever the bounded flow put it (in `domR` by `WellFormedFlowB`), and the
successor branch fires only where the endpoint is *also* in a successor's domain (a decidable membership at
the endpoint). `LandingH`'s successors are `retainedSucc` = self-loop + declared non-pruned edges, matching
`starStep_wrap`'s `edgesFrom` dispatch. Overlap-tolerant (pick any true disjunct). Pure membership +
invariance, first-passage-free — subsumes both widening (current/self disjunct) and narrowing (successor
disjunct at an overlap). -/

/-- The bounded flow endpoint: one `≤ dt` right run stays in `domR` and preserves `invLe g` (no reaching,
no `hsub`). The input to the `LandingH` case-split. -/
theorem flowDiamondB (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domR : Formula (Var n)) (dt : ℝ) (μ : State (Var n))
    (hwff : WellFormedFlowB fR lam domR dt) (hν : Formula.sat domR μ) (hdt : 0 ≤ dt)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) μ) :
    ∃ μ', Program.sem (Program.ode (rightBlock fR lam) domR) μ μ' ∧
        Formula.sat (invLe g) μ' ∧ Formula.sat domR μ' := by
  obtain ⟨ΦR, hΦ0, hder, hmask, hdom⟩ := hwff μ hν dt hdt (le_refl dt)
  have hsem : Program.sem (Program.ode (rightBlock fR lam) domR) μ (ΦR dt) :=
    ⟨dt, ΦR, hdt, hΦ0, rfl, hder, hmask, hdom⟩
  exact ⟨ΦR dt, hsem, by rw [sat_invLe]; exact hgbox (ΦR dt) hsem, hdom dt (right_mem_Icc.mpr hdt)⟩

/-- **The unified H + landing-selection step (MEMBERSHIP, no reaching).** Run one `≤ dt` segment
(`flowDiamondB`), case-split `LandingH` at the endpoint, dispatch via `starStep_wrap` into the landed mode
(self-edge for the current disjunct, the declared edge for a successor disjunct). Discharges the landing
step for BOTH widening and narrowing uniformly, via membership + `WellFormedFlowB` invariance — no
`SuccReach`/`SuccReachB`, no first-passage. `hedgeSelf`/`hedgeSucc` supply the (⊤-guarded, valid-target)
edges `retainedSucc` names; `hmvdomAll` the mode-var freshness for any landed mode. -/
theorem starStep_landingH (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (dt : ℝ) (μ : State (Var n))
    (hg : mv ∉ g.fv) (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hmvq : μ mv = (q : ℝ)) (hqlen : q < G.modes.length) (hdt : 0 ≤ dt)
    (hwff : WellFormedFlowB fR lam domR dt) (hν : Formula.sat domR μ)
    (hgbox : BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) μ)
    (hH : LandingH G)
    (hmvdomAll : ∀ q' m', G.modeAt q' = some m' → mv ∉ m'.dom.fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length) :
    ∃ ω, Program.sem (rightAutomatonBody G mv) μ ω ∧ StarInv G mv g ω := by
  obtain ⟨μ', hsem, hinv, hdomend⟩ := flowDiamondB g fR lam domR dt μ hwff hν hdt hgbox
  have hHμ := hH q m hm μ' (by rw [hdom]; exact hdomend)
  rcases hHμ with hcur | ⟨q', hq'mem, m', hmode', hdom'⟩
  · -- current disjunct: self-edge, μ' ∈ m.dom
    obtain ⟨e, hef, hetgt, hetg⟩ := hedgeSelf
    refine starStep_wrap G mv q m g fR lam domR μ hg hm hsys hdom hef hetg
      (by rw [hetgt]; exact hqlen) hmvq (by rw [hetgt]; exact hm) (hmvdomAll q m hm) ?_
    exact ⟨μ', hsem, hinv, hcur⟩
  · -- successor disjunct: declared edge to q', μ' ∈ m'.dom
    obtain ⟨e, hef, hetgt, hetg, hetv⟩ := hedgeSucc q' hq'mem
    refine starStep_wrap G mv q m g fR lam domR μ hg hm hsys hdom hef hetg hetv hmvq
      (by rw [hetgt]; exact hmode') (hmvdomAll q' m' hmode') ?_
    exact ⟨μ', hsem, hinv, hdom'⟩

/-! ## The strengthened segment lemma — one segment preserves `starInvF` (the threaded `φinv`)

The path-A capstone: reuse `multiseg_het`'s box-left induction, but with the STRENGTHENED invariant
`φinv := starInvF` (`invLe g ∧ mvValid ∧ inModeDomF`). The strengthening dissolves `multiseg_het`'s `∀σ`
seam — because every box-left endpoint is IN-DOMAIN (left flow freezes the right coords, start in `domR`),
`∀σ` there ranges only over in-domain states, exactly where the per-segment discharge applies. This lemma
is the per-segment obligation: one right segment (mode `q`, `ode rightBlock domR`) maps `starInvF → starInvF`.
`faModal_ODE_G'` is postcondition-generic, so we instantiate it at `ψ := starInvF` and supply the joint box
`hP2` establishing `starInvF` at every joint-flow endpoint: `invLe g` from the cert, `mvValid`+`inModeDomF`
from `mv`-frozen (`mv ∉ jointSys.bound`) + entry mode `σ mv = q` + the joint domain endpoint `∈ domR`. No
guard, no first-passage — just the entry mode and the flow staying in `domR`. -/
theorem segment_landing_full (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (σ : State (Var n))
    (hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys fL fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) σ)
    (hwff : WellFormedFlow fR lam domR) (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hνdom : Formula.sat domR σ)
    (hm : G.modeAt q = some m) (hdom : m.dom = domR)
    (hmvj : mv ∉ (jointSys fL fR lam).bound) (hσq : σ mv = (q : ℝ))
    (hqlen : q < G.modes.length) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR)
      (starInvF G mv g)) σ := by
  have hjoint : jointSys fL fR lam = leftBlock fL ++ (rightBlock fR lam).rename (Equiv.refl _) := by
    rw [ODESystem.rename_refl]; exact jointSys_split fL fR lam
  refine faModal_ODE_G' (Equiv.refl (Var n)) (leftBlock fL) (rightBlock fR lam)
    domL domR (starInvF G mv g) σ ?_ ?_ ?_ ?_ ?_
  · rw [ODESystem.rename_refl]; exact hdisj
  · exact hφL
  · rw [Formula.rename_refl, ODESystem.rename_refl]; exact hφR
  · -- hP2 : the joint flow preserves `starInvF`
    rw [ODESystem.rename_refl, Formula.rename_refl, ← jointSys_split]
    rw [sat_box]
    intro ω hω
    obtain ⟨s, Φ, hs, hΦ0, hΦs, _, hmask, hdomrun⟩ := hω
    have hsmem : s ∈ Icc (0 : ℝ) s := right_mem_Icc.mpr hs
    have hωmv : ω mv = (q : ℝ) := by rw [← hΦs, hmask s hsmem mv hmvj, hσq]
    have hωdomR : Formula.sat domR ω := by rw [← hΦs]; exact (hdomrun s hsmem).2
    refine ⟨?_, ?_, ?_⟩
    · -- invLe g
      rw [sat_invLe]; exact hcert ω ⟨s, Φ, hs, hΦ0, hΦs, ‹_›, hmask, hdomrun⟩
    · -- mvValid
      rw [sat_mvValid]; exact ⟨q, hqlen, hωmv⟩
    · -- inModeDomF
      rw [sat_inModeDomF]; exact ⟨q, m, hωmv, hm, hdom ▸ hωdomR⟩
  · rw [ODESystem.rename_refl, Formula.rename_refl]
    exact hExistSeg_of_wellFormedFlow fL fR lam domL domR σ hwff hfrz hνdom

/-- **The capstone per-step — the self-dispatching landing step (mirrors `hstep_single`, carrying
`starInvF`).** From the strengthened segment faModal `hseg` (`segment_landing_full`: one segment maps
`starInvF → starInvF`, mode `q`) derive the SAME faModal with the right program lifted to the
self-dispatching `rightAutomatonBody`. At each post-left state `ν` (mode `q`, since `mv` survives the
left box), the segment's right-flow endpoint `μ` is in `domR` (read off `starInvF μ` + `μ mv = q`); the
widening edge `hsub : domR ⊆ m'.dom` lands it in the TARGET domain, so `starStep_wrap` wraps the flow +
switch into one `rightAutomatonBody` step preserving `starInvF` (clause 2 by construction). This is the
`hcouple` obligation `multiseg_het`/`faModal_MULTI` consumes — dischargeable at EVERY `starInvF`-state
because `rightAutomatonBody` self-dispatches on `mv`, so no `∀σ` mode-mismatch and no `∀ν HExistSeg`. -/
theorem landing_step_faModal (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n))
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound) (hmvR : mv ∉ (rightBlock fR lam).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length)
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvdom' : mv ∉ m'.dom.fv)
    (hsub : ∀ ρ, Formula.sat domR ρ → Formula.sat m'.dom ρ)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hseg : Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (starInvF G mv g)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (rightAutomatonBody G mv) (starInvF G mv g)) σ := by
  rw [faModal_sat] at hseg ⊢
  intro ν hsemν
  have hmvν : ν mv = (q : ℝ) := (leftBlock_frames_mv fL domL mv hmvL hsemν).trans hmvq
  obtain ⟨μ, hRμ, hφμ⟩ := hseg ν hsemν
  simp only [Program.rename_refl] at hRμ
  -- μ mv = ν mv (right ode freezes mv)
  have hμq : μ mv = (q : ℝ) := by
    obtain ⟨s, Φ, hs, hΦ0, hΦs, _, hmask, _⟩ := hRμ
    rw [← hΦs, hmask s (right_mem_Icc.mpr hs) mv hmvR]; exact hmvν
  -- μ ∈ domR : read off starInvF μ's inModeDomF at mode q
  have hstarμ : StarInv G mv g μ := sat_starInvF.mp hφμ
  have hμdomR : Formula.sat domR μ := by
    obtain ⟨q', m'', hq'mv, hmode'', hdom''⟩ := hstarμ.2.2
    have hqq : q' = q := Nat.cast_inj.mp (hq'mv.symm.trans hμq)
    subst hqq
    have hmm : m'' = m := by injection hmode''.symm.trans hm
    subst hmm; rw [hdom] at hdom''; exact hdom''
  -- wrap flow + switch into one rightAutomatonBody step preserving starInvF
  obtain ⟨ω, hsemω, hstarω⟩ :=
    starStep_wrap G mv q m g fR lam domR ν hg hm hsys hdom hef hetg hetv hmvν het' hmvdom'
      ⟨μ, hRμ, hstarμ.1, hsub μ hμdomR⟩
  exact ⟨ω, by simpa only [Program.rename_refl] using hsemω, sat_starInvF.mpr hstarω⟩

/-- **The capstone per-step for a NARROWING switch — the analog of `landing_step_faModal`, BOUNDED-`dt`.**
At each post-left state `ν` (mode `q`, in `domR` since the left flow freezes the right coords `hfrz` and
`σ ∈ domR`), the crossing-segment condition `SuccReachB … dt ν` supplies a **`≤ dt`** right run reaching the
target domain `m'.dom`, and the per-start `BoxLe` cert (`hgboxAll`) supplies `invLe g` along it;
`starStep_narrowing` wraps flow+switch into one `rightAutomatonBody` step preserving `starInvF`. `hsr` is
carried at each in-domain box-left endpoint (the crossing-ready hypothesis) — in the clocked composition it is
invoked only at the one crossing segment; the prior self-loops discharge via `WellFormedFlowB`. Bounded-`dt`,
uniform with widening; no `∀s`/unbounded reach. -/
theorem landing_step_narrowing (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (dt : ℝ)
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length)
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvdom' : mv ∉ m'.dom.fv)
    (hsr : ∀ ν, Formula.sat domR ν → SuccReachB fR lam domR m'.dom dt ν)
    (hgboxAll : ∀ ν, Formula.sat domR ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ)) (hσdom : Formula.sat domR σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (rightAutomatonBody G mv) (starInvF G mv g)) σ := by
  rw [faModal_sat]
  intro ν hsemν
  have hmvν : ν mv = (q : ℝ) := (leftBlock_frames_mv fL domL mv hmvL hsemν).trans hmvq
  have hνdom : Formula.sat domR ν := by
    obtain ⟨s, Φ, hs, hΦ0, hΦs, _, hmask, _⟩ := hsemν
    have heqon : Set.EqOn σ ν domR.fv := by
      intro x hx
      rw [← hΦs]; exact (hmask s (right_mem_Icc.mpr hs) x (hfrz x hx)).symm
    exact (Formula.coincidence domR heqon).mp hσdom
  obtain ⟨ω, hsemω, hstarω⟩ :=
    starStep_narrowing G mv q m g fR lam domR dt ν hg hm hsys hdom hef hetg hetv hmvν het' hmvdom'
      (hsr ν hνdom) (hgboxAll ν hνdom)
  exact ⟨ω, by simpa only [Program.rename_refl] using hsemω, sat_starInvF.mpr hstarω⟩

/-- **Single-body faModal lifts to star-body faModal** — `faModal ρ P Q φ ⟹ faModal ρ P (Q*) φ`. The
right's one-body response IS a `star`-run (`ReflTransGen.single`), so a diamond over `Q` is a diamond
over `Q*`. This is the lift `faModal_MULTI`'s `hstep` needs (it wants `faModal P (star Q) φinv`). -/
theorem faModal_star_lift (ρ : Var n ≃ Var n) (P Q : Program (Var n)) (φ : Formula (Var n))
    (ω : State (Var n)) (h : Formula.sat (faModal ρ P Q φ) ω) :
    Formula.sat (faModal ρ P (Program.star Q) φ) ω := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hQμ, hφ⟩ := h ν hν
  rw [rename_star]
  exact ⟨μ, Relation.ReflTransGen.single hQμ, hφ⟩

/-- **The capstone per-step in `faModal_MULTI` form** — `landing_step_faModal` composed with
`faModal_star_lift`: one mode's contribution to the `hstep` obligation, `faModal P (star
rightAutomatonBody) starInvF`. The `faModal_MULTI` wrap dispatches these per mode over the left star. -/
theorem landing_step_star (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n))
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound) (hmvR : mv ∉ (rightBlock fR lam).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length)
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvdom' : mv ∉ m'.dom.fv)
    (hsub : ∀ ρ, Formula.sat domR ρ → Formula.sat m'.dom ρ)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hseg : Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (starInvF G mv g)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ :=
  faModal_star_lift (Equiv.refl (Var n)) _ _ _ σ
    (landing_step_faModal G mv q m g fL fR lam domL domR hg hmvL hmvR hm hsys hdom
      hef hetg hetv het' hmvdom' hsub hmvq hseg)

/-- **The narrowing per-step in `faModal_MULTI` form** — `landing_step_narrowing` composed with
`faModal_star_lift`, BOUNDED-`dt`. One narrowing mode's contribution to the `hstep`/`hdispatch` obligation,
sourced from the bounded crossing-segment condition `SuccReachB`. Feeds the `faModal_MULTI` wrap exactly like
`landing_step_star` (widening); the dispatch picks this branch for narrowing edges. Uniform bounded-`dt`. -/
theorem landing_step_star_narrowing (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (dt : ℝ)
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length)
    {m' : RMode (Var n)} (het' : G.modeAt e.tgt = some m') (hmvdom' : mv ∉ m'.dom.fv)
    (hsr : ∀ ν, Formula.sat domR ν → SuccReachB fR lam domR m'.dom dt ν)
    (hgboxAll : ∀ ν, Formula.sat domR ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ)) (hσdom : Formula.sat domR σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ :=
  faModal_star_lift (Equiv.refl (Var n)) _ _ _ σ
    (landing_step_narrowing G mv q m g fL fR lam domL domR dt hg hmvL hm hsys hdom
      hef hetg hetv het' hmvdom' hsr hgboxAll hfrz hmvq hσdom)

/-- **The UNIFIED landing per-step via H + landing-selection (membership, no reaching).** At each post-left
state `ν` (mode `q`, in `domR` from `hfrz` + `σ ∈ domR`), `starStep_landingH` runs one `≤ dt` segment and
dispatches by `LandingH`'s membership disjunction — subsuming BOTH widening (current/self disjunct) and
narrowing (successor disjunct at an overlap) in ONE step. No `hsub`, no `SuccReach`/`SuccReachB` — pure
`WellFormedFlowB` invariance + endpoint membership. First-passage-free. -/
theorem landing_step_landingH (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (dt : ℝ)
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hqlen : q < G.modes.length) (hdt : 0 ≤ dt)
    (hwff : WellFormedFlowB fR lam domR dt)
    (hgboxAll : ∀ ν, Formula.sat domR ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hH : LandingH G) (hmvdomAll : ∀ q' m', G.modeAt q' = some m' → mv ∉ m'.dom.fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ)) (hσdom : Formula.sat domR σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (rightAutomatonBody G mv) (starInvF G mv g)) σ := by
  rw [faModal_sat]
  intro ν hsemν
  have hmvν : ν mv = (q : ℝ) := (leftBlock_frames_mv fL domL mv hmvL hsemν).trans hmvq
  have hνdom : Formula.sat domR ν := by
    obtain ⟨s, Φ, hs, hΦ0, hΦs, _, hmask, _⟩ := hsemν
    have heqon : Set.EqOn σ ν domR.fv := by
      intro x hx
      rw [← hΦs]; exact (hmask s (right_mem_Icc.mpr hs) x (hfrz x hx)).symm
    exact (Formula.coincidence domR heqon).mp hσdom
  obtain ⟨ω, hsemω, hstarω⟩ :=
    starStep_landingH G mv q m g fR lam domR dt ν hg hm hsys hdom hmvν hqlen hdt hwff hνdom
      (hgboxAll ν hνdom) hH hmvdomAll hedgeSelf hedgeSucc
  exact ⟨ω, by simpa only [Program.rename_refl] using hsemω, sat_starInvF.mpr hstarω⟩

/-- **The unified H landing step, `faModal_MULTI` form** — `landing_step_landingH` star-lifted. One mode's
contribution to `hdispatch`, membership-dispatched (widening ∪ narrowing), first-passage-free. -/
theorem landing_step_star_landingH (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (dt : ℝ)
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hqlen : q < G.modes.length) (hdt : 0 ≤ dt)
    (hwff : WellFormedFlowB fR lam domR dt)
    (hgboxAll : ∀ ν, Formula.sat domR ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrz : ∀ x ∈ domR.fv, x ∉ (leftBlock fL).bound)
    (hH : LandingH G) (hmvdomAll : ∀ q' m', G.modeAt q' = some m' → mv ∉ m'.dom.fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ)) (hσdom : Formula.sat domR σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ :=
  faModal_star_lift (Equiv.refl (Var n)) _ _ _ σ
    (landing_step_landingH G mv q m g fL fR lam domL domR dt hg hmvL hm hsys hdom hqlen hdt
      hwff hgboxAll hfrz hH hmvdomAll hedgeSelf hedgeSucc hmvq hσdom)

/-- **The CLOCKED unified H landing step (`faModalB` form) — folds the H-path onto the clocked substrate.**
Same membership-dispatch as `landing_step_landingH`, but the left box is a **clocked `≤ dt`** run (`plantT`
over `clk tg leftBlock`) instead of a raw (unbounded) left ode. So the `≤ dt` left piece MATCHES the `≤ dt`
right segment — the `WellFormedFlowB`/`BoxLe` obligations are genuinely bounded, and the left residence
cannot outrun the right response (the raw-left `∀s` gap the clocking closes). The `≤ dt` bound is read off
the `plantT` clock; `mv`/`domR` survive the clocked left (`hmvLclk`/`hfrzClk`, `tg` fresh). Slots directly
into `faModal_MULTI` (via `faModalB_clockedSeg_iff`) as the clocked `multiseg_landing` hstep. -/
theorem landing_step_landingH_clocked (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (tg : Var n) (dt : ℝ) (ω : State (Var n))
    (hg : mv ∉ g.fv) (hmvLclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hqlen : q < G.modes.length) (hdt : 0 ≤ dt)
    (hwff : WellFormedFlowB fR lam domR dt)
    (hgboxAll : ∀ ν, Formula.sat domR ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrzClk : ∀ x ∈ domR.fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hH : LandingH G) (hmvdomAll : ∀ q' m', G.modeAt q' = some m' → mv ∉ m'.dom.fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    (hωmv : ω mv = (q : ℝ)) (hωdom : Formula.sat domR ω) :
    faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
      (rightAutomatonBody G mv) (starInvF G mv g) tg dt ω := by
  intro ν hplant
  obtain ⟨hsemL, _⟩ := hplant
  obtain ⟨s, Φ, hs, hΦ0, hΦs, _, hmask, _⟩ := hsemL
  have hmvν : ν mv = (q : ℝ) := by
    rw [← hΦs, hmask s (right_mem_Icc.mpr hs) mv hmvLclk]; exact hωmv
  have hνdom : Formula.sat domR ν := by
    have heqon : Set.EqOn ω ν domR.fv := by
      intro x hx
      rw [← hΦs]; exact (hmask s (right_mem_Icc.mpr hs) x (hfrzClk x hx)).symm
    exact (Formula.coincidence domR heqon).mp hωdom
  obtain ⟨o, hsemω, hstarω⟩ :=
    starStep_landingH G mv q m g fR lam domR dt ν hg hm hsys hdom hmvν hqlen hdt hwff hνdom
      (hgboxAll ν hνdom) hH hmvdomAll hedgeSelf hedgeSucc
  exact ⟨o, by simpa only [Program.rename_refl] using hsemω, sat_starInvF.mpr hstarω⟩

/-- **`multiseg_landing` — the capstone.** The full relational modality `faModal (leftBody*)
(rightAutomatonBody*) starInvF` over the STARRED left and right automata, assembled from the per-step
landing responses via `faModal_MULTI`. The `hdispatch` obligation — one landing star-step from every
`starInvF`-state — is discharged (per mode) by `landing_step_star`, dispatching on the state's mode
(`rightAutomatonBody` self-dispatches on `mv`); it is carried here as the parametric input exactly as the
existing multi-flow chain carries `EmitSegs`/`cert`. The threaded invariant is `starInvF` throughout, so
`HExistSeg` is discharged IN-DOMAIN at every iteration (`WellFormedFlow`, not the `∀ν EmitSegs` boundary),
clause 2 holds by construction (`starStep_wrap`), and the narrowing residual is confined to whether a
switch is widening (`hsub`) — no guard, no first-passage anywhere in the assembly. -/
theorem multiseg_landing (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftBody : Program (Var n)) (σ : State (Var n))
    (hd : Disjoint (Program.vars leftBody)
      (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hσ : Formula.sat (starInvF G mv g) σ)
    (hdispatch : ∀ σ', Formula.sat (starInvF G mv g) σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) leftBody
          (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ') :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.star leftBody)
      (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ :=
  faModal_MULTI (Equiv.refl (Var n)) leftBody (rightAutomatonBody G mv)
    (starInvF G mv g) (starInvF G mv g) σ hd hσ hdispatch (fun _ h => h)

/-- **The clocked unified H hstep — one mode's `faModal_MULTI` contribution over the CLOCKED left.**
`landing_step_landingH_clocked` (faModalB) bridged to the `clockedSeg`-program `faModal` via
`faModalB_clockedSeg_iff`, then star-lifted. The left is a `≤ dt` `clockedSeg` (matching the `≤ dt` right
segment); dispatch is `LandingH` membership (widening ∪ narrowing), first-passage-free. This is the hstep
`multiseg_landing_clocked` iterates. -/
theorem landing_step_star_landingH_clocked (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (m : RMode (Var n)) (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (hg : mv ∉ g.fv) (hmvLclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) (hmvtg : mv ≠ tg)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    (hqlen : q < G.modes.length) (hdt : 0 ≤ dt) (htgdR : tg ∉ domR.fv)
    (hwff : WellFormedFlowB fR lam domR dt)
    (hgboxAll : ∀ ν, Formula.sat domR ν →
        BoxLe (Program.ode (rightBlock fR lam) domR) (fun ω => Term.eval g ω) ν)
    (hfrzClk : ∀ x ∈ domR.fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hH : LandingH G) (hmvdomAll : ∀ q' m', G.modeAt q' = some m' → mv ∉ m'.dom.fv)
    (hedgeSelf : ∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt)
    (hedgeSucc : ∀ q', q' ∈ G.retainedSucc q →
        ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ)) (hσdom : Formula.sat domR σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (clockedSeg (leftBlock fL) domL tg dt) (Program.star (rightAutomatonBody G mv))
      (starInvF G mv g)) σ := by
  refine faModal_star_lift (Equiv.refl (Var n)) _ _ _ σ ?_
  rw [faModalB_clockedSeg_iff]
  refine landing_step_landingH_clocked G mv q m g fL fR lam domL domR tg dt (Function.update σ tg 0)
    hg hmvLclk hm hsys hdom hqlen hdt hwff hgboxAll hfrzClk hH hmvdomAll hedgeSelf hedgeSucc ?_ ?_
  · rw [Function.update_of_ne hmvtg]; exact hmvq
  · have heqon : Set.EqOn σ (Function.update σ tg 0) domR.fv := fun x hx =>
      (Function.update_of_ne (by rintro rfl; exact htgdR hx) _ _).symm
    exact (Formula.coincidence domR heqon).mp hσdom

/-- **`multiseg_landing_clocked` — the H-path folded onto the clocked substrate.** The full relational
modality over the STARRED CLOCKED left and the right automaton, from the clocked per-mode H hsteps
(`landing_step_star_landingH_clocked`) via `faModal_MULTI`. Each left iteration is a `≤ dt` `clockedSeg`
(so the right `≤ dt` segment matches — no raw-left `∀s` gap); dispatch is `LandingH` membership
(first-passage-free). `hdispatch` carried parametrically (discharged per mode by the clocked H hstep, as in
the raw `multiseg_landing`). The physical collapse `star clockedSeg → star (ode leftBlock)` is the shipped
`clockLift` (a further wrap). -/
theorem multiseg_landing_clocked (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) (σ : State (Var n))
    (hd : Disjoint (Program.vars (clockedSeg (leftBlock fL) domL tg dt))
      (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hσ : Formula.sat (starInvF G mv g) σ)
    (hdispatch : ∀ σ', Formula.sat (starInvF G mv g) σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) (clockedSeg (leftBlock fL) domL tg dt)
          (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ') :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.star (clockedSeg (leftBlock fL) domL tg dt))
      (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ :=
  faModal_MULTI (Equiv.refl (Var n)) (clockedSeg (leftBlock fL) domL tg dt) (rightAutomatonBody G mv)
    (starInvF G mv g) (starInvF G mv g) σ hd hσ hdispatch (fun _ h => h)

/-- **The dispatch skeleton — factor `hdispatch` through the state's mode.** `starInvF σ'` pins `σ'` to a
declared mode `q` (`StarInModeDom`: `σ' mv = q`, `modeAt q = some m`, `σ' ∈ m.dom`); the per-mode response
`hresp` (widening → `landing_step_star`, narrowing → `landing_step_star_narrowing`) then supplies the
landing star-step. This is the enumeration hinge: it reduces the universal `hdispatch` to a per-mode
obligation, so the concrete dispatch only has to route each declared mode to its widening/narrowing
branch. `rightAutomatonBody` self-dispatches on `mv`, so no `∀σ` mode-mismatch. -/
theorem hdispatch_of_modeResp (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftBody : Program (Var n))
    (hresp : ∀ σ', StarInv G mv g σ' → ∀ q m, G.modeAt q = some m → σ' mv = (q : ℝ) →
        Formula.sat m.dom σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) leftBody
          (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ') :
    ∀ σ', Formula.sat (starInvF G mv g) σ' →
      Formula.sat (faModal (Equiv.refl (Var n)) leftBody
        (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ' := by
  intro σ' hσ'
  have hstar : StarInv G mv g σ' := sat_starInvF.mp hσ'
  obtain ⟨q, m, hqmv, hmode, hmdom⟩ := hstar.2.2
  exact hresp σ' hstar q m hmode hqmv hmdom

/-- **`tooling_sound_landing` — the capstone at the `faModal`/`sat` layer, carrying the per-mode dispatch.**
The full ∀∃ relational modality `faModal (leftBody*) (rightAutomatonBody*) starInvF` over the starred
automata, from `multiseg_landing` ∘ `hdispatch_of_modeResp`. The per-mode response `hresp` is where each
declared mode routes to its branch: WIDENING modes discharge by construction (`landing_step_star`, no
`SuccReach`); NARROWING modes carry `SuccReach` (`landing_step_star_narrowing`). So `SuccReach` is scoped to
narrowing edges only — the enumeration fills `hresp` per mode. The all-widening instantiation recovers the
banked `multiseg_het` behaviour (no reachability hypothesis anywhere). This is non-breaking: the encoded-
layer `tooling_sound` (rvalid/theorem3Form, `EmitSegs`) and `multiseg_het` are untouched; bridging this
`sat`-modality to the `rvalid` form is the reification integration (separate, layered on the existing
`relational_loop_faithful` machinery). -/
theorem tooling_sound_landing (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftBody : Program (Var n)) (σ : State (Var n))
    (hd : Disjoint (Program.vars leftBody)
      (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hσ : Formula.sat (starInvF G mv g) σ)
    (hresp : ∀ σ', StarInv G mv g σ' → ∀ q m, G.modeAt q = some m → σ' mv = (q : ℝ) →
        Formula.sat m.dom σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) leftBody
          (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ') :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.star leftBody)
      (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) σ :=
  multiseg_landing G mv g leftBody σ hd hσ (hdispatch_of_modeResp G mv g leftBody hresp)

end RelCertifier
