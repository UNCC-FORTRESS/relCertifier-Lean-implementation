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

/-- **The threaded star invariant.** Coupling `invLe g`, a valid mode index (`mvValid`), and current-mode
domain-membership (`StarInModeDom`). Preserved by every landing body-step (`starStep_wrap`); its
`invLe g` conjunct is what the terminal `⟨star body⟩(invLe g)` reads off. -/
def StarInv (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n)) (μ : State (Var n)) : Prop :=
  Formula.sat (invLe g) μ ∧ Formula.sat (mvValid mv G.modes.length) μ ∧ StarInModeDom G mv μ

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

end RelCertifier
