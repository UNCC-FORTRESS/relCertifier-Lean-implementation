/-
The transition-faithful right automaton (`rightAutomatonBody`/`R_real`) — definitions + the
Transition-faithful right automaton (mode variable) so the ∃-right diamond is a real G-run.
-/
import RelCertifier.Cover
import RelCertifier.Cover.Coexec
import DLRel

namespace RelCertifier
open DL DLRel Function

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Declared edges out of mode `q`. -/
def SearchGraph.edgesFrom (G : SearchGraph V) (q : ℕ) : List (REdge V) :=
  G.edges.filter (fun e => decide (e.src = q))

/-- Joint fragment gate: no mode carries a reposition certificate. -/
def NoRepoModes (G : SearchGraph V) : Prop :=
  ∀ q m, G.modeAt q = some m →
    m.repoPreOK = false ∧ m.repoPostOK = false ∧
    m.repoDynPreOK = false ∧ m.repoDynPostOK = false

/-- `mode = q` test on the fresh mode variable `mv`. -/
def modeIs (mv : V) (q : ℕ) : Formula V :=
  Formula.cmp CompOp.eq (Term.var mv) (Term.const (q : ℝ))

/-- Nondeterministic choice over a program list. -/
def bigChoiceP : List (Program V) → Program V
  | []      => Program.test (Formula.neg Formula.tt)
  | p :: ps => Program.choice p (bigChoiceP ps)

/-- One transition step at mode `q`: `test mode=q ; flow ; (declared-edge: test guard ; mode := tgt)`. -/
def modeStep (G : SearchGraph V) (mv : V) (q : ℕ) (m : RMode V) : Program V :=
  Program.seq (Program.test (modeIs mv q))
    (Program.seq (Program.ode m.sys m.dom)
      (bigChoiceP ((G.edgesFrom q).map (fun e =>
        Program.seq (Program.test e.guard) (Program.assign mv (Term.const (e.tgt : ℝ)))))))

/-- The transition-faithful right automaton body: choice over all modes' steps. -/
def rightAutomatonBody (G : SearchGraph V) (mv : V) : Program V :=
  bigChoiceP ((List.range G.modes.length).filterMap (fun q =>
    (G.modeAt q).map (fun m => modeStep G mv q m)))

/-- `R_real = (body)*`. -/
def R_real (G : SearchGraph V) (mv : V) : Program V :=
  Program.star (rightAutomatonBody G mv)

/-! ## Witness lemma helpers -/

/-- Freshness of `mv`: occurs in no mode flow and no edge guard. -/
def MVFresh (G : SearchGraph V) (mv : V) : Prop :=
  (∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv) ∧
  (∀ e ∈ G.edges, mv ∉ (e.guard).fv)

/-- Every joint-covered mode has a declared `q→q` self-edge with guard `⊤`. -/
def SelfEdges (G : SearchGraph V) : Prop :=
  ∀ q m, G.modeAt q = some m → m.jointOK = true →
    ∃ e ∈ G.edges, e.src = q ∧ e.tgt = q ∧ e.guard = Formula.tt

/-- `bigChoiceP` admits any member's run. -/
theorem bigChoiceP_sem_of_mem {ps : List (Program V)} {p : Program V} (hp : p ∈ ps)
    {ν ω : State V} (h : Program.sem p ν ω) : Program.sem (bigChoiceP ps) ν ω := by
  induction ps with
  | nil => exact absurd hp (List.not_mem_nil)
  | cons a as ih =>
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact Or.inl h
      · exact Or.inr (ih hmem)

/-- ODE frame-lift: updating the fresh `mv` on both endpoints preserves an ODE run. -/
theorem sem_ode_frame_upd {sys : ODESystem V} {ψ : Formula V} (mv : V) (c : ℝ)
    (hfv : mv ∉ (Program.ode sys ψ).fv) {ν ω : State V}
    (h : Program.sem (Program.ode sys ψ) ν ω) :
    Program.sem (Program.ode sys ψ) (update ν mv c) (update ω mv c) := by
  have hEq : Set.EqOn ν (update ν mv c) {x | x ≠ mv} := by
    intro x hx; exact (Function.update_of_ne (by simpa using hx) _ _).symm
  obtain ⟨ω₂, hrun, hag⟩ :=
    Program.coincidence (Program.ode sys ψ) (W := {x | x ≠ mv})
      (by intro x hx; exact fun hxmv => hfv (by simpa [hxmv] using hx)) hEq h
  have hmvbound : mv ∉ sys.bound := by
    intro hb; exact hfv (Or.inl (Or.inl (by simpa [ODESystem.boundSet] using hb)))
  have hω2mv : ω₂ mv = c := by
    obtain ⟨r, Φ, hr, hΦ0, rfl, _, hmask, _⟩ := hrun
    have := hmask r ⟨hr, le_refl r⟩ mv hmvbound
    rw [this, Function.update_self]
  have hω2 : ω₂ = update ω mv c := by
    funext z
    by_cases hz : z = mv
    · subst hz; rw [hω2mv, Function.update_self]
    · rw [Function.update_of_ne hz]; exact (hag (Or.inl hz)).symm
  rwa [hω2] at hrun

/-- A single automaton step: flow `ν→μ` at mode `q`, then declared edge `e` (with its guard
satisfied) to mode `e.tgt`, with the mode variable tracking `q ↦ e.tgt`. -/
theorem modeStep_sem (G : SearchGraph V) (mv : V) (q : ℕ) (m : RMode V)
    (hfv : mv ∉ (Program.ode m.sys m.dom).fv)
    {e : REdge V} (hef : e ∈ G.edgesFrom q) {ν μ : State V}
    (hode : Program.sem (Program.ode m.sys m.dom) ν μ)
    (hg : Formula.sat e.guard (update μ mv (q : ℝ))) :
    Program.sem (modeStep G mv q m) (update ν mv (q : ℝ)) (update μ mv (e.tgt : ℝ)) := by
  refine ⟨update ν mv (q : ℝ), ⟨rfl, ?_⟩, ⟨update μ mv (q : ℝ), ?_, ?_⟩⟩
  · -- test (mode = q)
    simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, Function.update_self]
  · -- flow, mode framed
    exact sem_ode_frame_upd mv (q : ℝ) hfv hode
  · -- declared-edge branch: (test guard ; mv := tgt)
    refine bigChoiceP_sem_of_mem (List.mem_map_of_mem hef) ?_
    refine ⟨update μ mv (q : ℝ), ⟨rfl, hg⟩, ?_, ?_⟩
    · simp only [Term.eval, Function.update_self]
    · intro y hy; simp only [Function.update_of_ne hy]

/-- **Witness lemma.** Every joint-fragment `RightReach` gives a real run of the
transition-faithful right automaton `R_real` (mode variable tracks the config's mode). -/
theorem rightReach_is_R_real_run (G : SearchGraph V) (mv : V)
    (hnorepo : NoRepoModes G) (hfresh : MVFresh G mv) (hself : SelfEdges G) :
    ∀ {cfg : Config} {ν ω : State V}, RightReach G cfg ν ω →
      ∃ qf : ℕ, Program.sem (R_real G mv)
        (update ν mv (cfg.q : ℝ)) (update ω mv (qf : ℝ)) := by
  intro cfg ν ω hreach
  induction hreach with
  | @refl q B σ ν => exact ⟨q, Relation.ReflTransGen.refl⟩
  | @evolve q B σ ν μ ω m hm hj hsem _ ih =>
      obtain ⟨qf, ihrun⟩ := ih
      obtain ⟨e, he, hsrc, htgt, hgtt⟩ := hself q m hm hj
      have hef : e ∈ G.edgesFrom q :=
        List.mem_filter.mpr ⟨he, by simp [hsrc]⟩
      have hstep : Program.sem (modeStep G mv q m)
          (update ν mv (q : ℝ)) (update μ mv (q : ℝ)) := by
        have := modeStep_sem G mv q m (hfresh.1 q m hm) hef hsem
          (by rw [hgtt]; trivial)
        rwa [htgt] at this
      have hbody : Program.sem (rightAutomatonBody G mv)
          (update ν mv (q : ℝ)) (update μ mv (q : ℝ)) := by
        refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
        · exact List.mem_range.mpr (by
            have := hm; simp only [SearchGraph.modeAt] at this
            exact List.getElem?_eq_some_iff.mp this |>.1)
        · rw [hm]; rfl
      exact ⟨qf, Relation.ReflTransGen.head hbody ihrun⟩
  | @jump q B σ ν μ ω m hm hj e he hsrc hlt hsem hguard _ ih =>
      obtain ⟨qf, ihrun⟩ := ih
      have hef : e ∈ G.edgesFrom q :=
        List.mem_filter.mpr ⟨he, by simp [hsrc]⟩
      have hEq : Set.EqOn μ (update μ mv (q : ℝ)) (e.guard).fv := by
        intro x hx
        have hxne : x ≠ mv := by intro h; subst h; exact hfresh.2 e he hx
        exact (Function.update_of_ne hxne _ _).symm
      have hg : Formula.sat e.guard (update μ mv (q : ℝ)) :=
        (Formula.coincidence e.guard hEq).mp hguard
      have hstep := modeStep_sem G mv q m (hfresh.1 q m hm) hef hsem hg
      have hbody : Program.sem (rightAutomatonBody G mv)
          (update ν mv (q : ℝ)) (update μ mv (e.tgt : ℝ)) := by
        refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
        · exact List.mem_range.mpr (by
            have := hm; simp only [SearchGraph.modeAt] at this
            exact List.getElem?_eq_some_iff.mp this |>.1)
        · rw [hm]; rfl
      exact ⟨qf, Relation.ReflTransGen.head hbody ihrun⟩
  | @repositionPre q B ν ω m hm hrepo _ _ _ _ _ _ ih =>
      exact absurd hrepo (by rw [(hnorepo q m hm).1]; simp)
  | @repositionPost q B ν ω m hm hrepo _ _ _ _ _ _ ih =>
      exact absurd hrepo (by rw [(hnorepo q m hm).2.1]; simp)
  | @repositionDynPre q B ν μ ω m hm hrepo _ _ _ _ _ _ ih =>
      exact absurd hrepo (by rw [(hnorepo q m hm).2.2.1]; simp)
  | @repositionDynPost q B ν μ ω m hm hrepo _ _ _ _ _ _ ih =>
      exact absurd hrepo (by rw [(hnorepo q m hm).2.2.2]; simp)


/-! ## Piece 1 — the mode variable is invisible to the invariant (framing from freshness) -/

/-- Modality-free relational formulas — the fragment the invariant `ϕinv` lives in. -/
def noRbox {V : Type*} : RFormula V → Prop
  | .cmp _ _ _ => True
  | .neg ϕ     => noRbox ϕ
  | .and ϕ ψ   => noRbox ϕ ∧ noRbox ψ
  | .rbox _ _  => False
  | .proj _ _  => True

/-- Bi-state term coincidence: an `RTerm`'s value depends only on `.1` through `varsL`
and `.2` through `varsR`. -/
theorem rterm_coincidence (t : RTerm V) {ω ω' : BiState V}
    (hL : Set.EqOn ω.1 ω'.1 t.varsL) (hR : Set.EqOn ω.2 ω'.2 t.varsR) :
    RTerm.eval t ω = RTerm.eval t ω' := by
  induction t with
  | proj sd θ =>
      cases sd with
      | L => simpa only [RTerm.eval] using Term.coincidence θ hL
      | R => simpa only [RTerm.eval] using Term.coincidence θ hR
  | binop op a b iha ihb =>
      simp only [RTerm.eval]
      rw [iha (hL.mono Set.subset_union_left) (hR.mono Set.subset_union_left),
          ihb (hL.mono Set.subset_union_right) (hR.mono Set.subset_union_right)]

/-- Bi-state formula coincidence (modality-free), by structural recursion on the formula. -/
theorem rformula_coincidence : ∀ (ϕ : RFormula V), noRbox ϕ →
    ∀ (ω ω' : BiState V), Set.EqOn ω.1 ω'.1 ϕ.varsL → Set.EqOn ω.2 ω'.2 ϕ.varsR →
    (RFormula.sat ϕ ω ↔ RFormula.sat ϕ ω')
  | .cmp op a b, _, ω, ω', hL, hR => by
      simp only [RFormula.sat,
        rterm_coincidence a (hL.mono Set.subset_union_left) (hR.mono Set.subset_union_left),
        rterm_coincidence b (hL.mono Set.subset_union_right) (hR.mono Set.subset_union_right)]
  | .neg ϕ, hnb, ω, ω', hL, hR => by
      simp only [RFormula.sat, rformula_coincidence ϕ hnb ω ω' hL hR]
  | .and ϕ ψ, hnb, ω, ω', hL, hR => by
      simp only [RFormula.sat,
        rformula_coincidence ϕ hnb.1 ω ω' (hL.mono Set.subset_union_left) (hR.mono Set.subset_union_left),
        rformula_coincidence ψ hnb.2 ω ω' (hL.mono Set.subset_union_right) (hR.mono Set.subset_union_right)]
  | .rbox _ _, hnb, _, _, _, _ => absurd hnb (by simp [noRbox])
  | .proj sd ϕ, _, ω, ω', hL, hR => by
      cases sd with
      | L => simpa only [RFormula.sat] using Formula.coincidence ϕ hL
      | R => simpa only [RFormula.sat] using Formula.coincidence ϕ hR

/-- **(b) ψ ignores the mode variable** — proven from freshness (`mv ∉ ψ.varsL ∪ ψ.varsR`):
updating `mv` on either bi-state component leaves the invariant's truth unchanged. -/
theorem psi_ignores_mv (mv : V) (ϕ : RFormula V) (hnb : noRbox ϕ)
    (hL : mv ∉ ϕ.varsL) (hR : mv ∉ ϕ.varsR) {ωL ωR : State V} (a b : ℝ) :
    RFormula.sat ϕ (update ωL mv a, update ωR mv b) ↔ RFormula.sat ϕ (ωL, ωR) :=
  rformula_coincidence ϕ hnb (update ωL mv a, update ωR mv b) (ωL, ωR)
    (fun x hx => update_of_ne (by intro h; subst h; exact hL hx) a ωL)
    (fun x hx => update_of_ne (by intro h; subst h; exact hR hx) b ωR)

/-- **Piece 1 — the projection/commutation lemma.** The witness run is the diamond's `.2`
run, and the invariant at its endpoint reduces to the cover's observable endpoint `ω`
(the mode variable, threaded on `.2`, is invisible to `ψ`). Built on the verified witness. -/
theorem witness_endpoint_obs (G : SearchGraph V) (mv : V)
    (hnorepo : NoRepoModes G) (hfresh : MVFresh G mv) (hself : SelfEdges G)
    (ϕ : RFormula V) (hnb : noRbox ϕ) (hRϕ : mv ∉ ϕ.varsR)
    {cfg : Config} {ν ω : State V} (hreach : RightReach G cfg ν ω) (νL : State V) :
    ∃ μR, Program.sem (R_real G mv) (update ν mv (cfg.q : ℝ)) μR ∧
      (RFormula.sat ϕ (νL, μR) ↔ RFormula.sat ϕ (νL, ω)) := by
  obtain ⟨qf, hrun⟩ := rightReach_is_R_real_run G mv hnorepo hfresh hself hreach
  refine ⟨update ω mv (qf : ℝ), hrun, ?_⟩
  exact rformula_coincidence ϕ hnb (νL, update ω mv (qf:ℝ)) (νL, ω) (Set.eqOn_refl _ _)
    (fun x hx => update_of_ne (by intro h; subst h; exact hRϕ hx) (qf:ℝ) ω)


end RelCertifier
