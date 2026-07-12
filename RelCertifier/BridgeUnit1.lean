/-
The right-wrapping (single-flow bridge, unit 1): turn the bare ⟨ode rightBlock⟩ φinv that
segment_faModal produces into ⟨rightAutomatonBody⟩ φinv (the mv-decorated transition body
faModal_LOCK loops). The mv test/jump/assign are invisible to the host invariant φinv
(mv ∉ φinv.fv), and the mode-q branch is selected by the state's mv value.
-/
import RelCertifier.JointBridge
import RelCertifier.Reify

namespace RelCertifier
open DL DLCalTiming Function

variable {n : ℕ}

/-- Finite disjunction of formulas. -/
def bigOr : List (Formula (Var n)) → Formula (Var n)
  | []      => Formula.neg Formula.tt
  | f :: fs => Formula.neg (Formula.and (Formula.neg f) (Formula.neg (bigOr fs)))

theorem sat_bigOr {fs : List (Formula (Var n))} {ν : State (Var n)} :
    Formula.sat (bigOr fs) ν ↔ ∃ f ∈ fs, Formula.sat f ν := by
  induction fs with
  | nil => simp [bigOr, Formula.sat]
  | cons a as ih =>
      simp only [bigOr, Formula.sat, not_and, not_not, List.mem_cons]
      constructor
      · intro h; by_cases ha : Formula.sat a ν
        · exact ⟨a, Or.inl rfl, ha⟩
        · obtain ⟨f, hf, hsf⟩ := ih.mp (h ha); exact ⟨f, Or.inr hf, hsf⟩
      · rintro ⟨f, hf | hf, hsf⟩ hna
        · exact absurd (hf ▸ hsf) hna
        · exact ih.mpr ⟨f, hf, hsf⟩

/-- `mv` holds a valid (declared) mode index. -/
def mvValid (mv : Var n) (numModes : ℕ) : Formula (Var n) :=
  bigOr ((List.range numModes).map (fun q => modeIs mv q))

theorem sat_mvValid {mv : Var n} {numModes : ℕ} {ν : State (Var n)} :
    Formula.sat (mvValid mv numModes) ν ↔ ∃ q < numModes, ν mv = (q : ℝ) := by
  simp only [mvValid, sat_bigOr, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨f, ⟨q, hq, rfl⟩, hf⟩
    exact ⟨q, hq, by simpa only [modeIs, Formula.sat, CompOp.interp, Term.eval] using hf⟩
  · rintro ⟨q, hq, hν⟩
    exact ⟨modeIs mv q, ⟨q, hq, rfl⟩, by simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, hν]⟩

/-- Declared edges point to declared modes (NOT SearchGraph-guaranteed — the cover emits
sentinel targets for uncertified successors — so carried as an explicit structural fact). -/
def EdgeTargetsValid (G : SearchGraph (Var n)) : Prop :=
  ∀ e ∈ G.edges, e.tgt < G.modes.length

/-- A member's diamond lifts to the choice's diamond. -/
theorem diamond_bigChoiceP_of_mem {ps : List (Program (Var n))} {p : Program (Var n)}
    (hp : p ∈ ps) {φ : Formula (Var n)} {ν : State (Var n)}
    (h : Formula.sat (Formula.diamond p φ) ν) :
    Formula.sat (Formula.diamond (bigChoiceP ps) φ) ν := by
  rw [diamond_sem] at h ⊢
  obtain ⟨ν', hsem, hφ⟩ := h
  exact ⟨ν', bigChoiceP_sem_of_mem hp hsem, hφ⟩

/-- **The right-wrapping (unit 1 core).** From the responding mode `q`'s bare right-flow
diamond `⟨ode (rightBlock fR lam) domR⟩ (invLe g)` at a state whose mode variable reads `q`,
plus a declared `⊤`-guarded edge out of `q`, derive the transition-body diamond
`⟨rightAutomatonBody G mv⟩ (invLe g)`. The `mv` test/jump/assign are invisible to `invLe g`
because `mv ∉ g.fv`. -/
theorem diamond_right_wrap (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domR : Formula (Var n))
    (hg : mv ∉ g.fv)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length)
    {ν : State (Var n)} (hmvq : ν mv = (q : ℝ))
    (h : Formula.sat (Formula.diamond (Program.ode (rightBlock fR lam) domR) (invLe g)) ν) :
    Formula.sat (Formula.diamond (rightAutomatonBody G mv)
      (Formula.and (invLe g) (mvValid mv G.modes.length))) ν := by
  rw [diamond_sem] at h
  obtain ⟨μ, hode, hφμ⟩ := h
  -- build the mode-q modeStep run: test(mode=q) ; ode ; (test e.guard ; mv := e.tgt)
  have hjump : Program.sem
      (bigChoiceP ((G.edgesFrom q).map (fun e =>
        Program.seq (Program.test e.guard) (Program.assign mv (Term.const (e.tgt : ℝ))))))
      μ (update μ mv (e.tgt : ℝ)) := by
    refine bigChoiceP_sem_of_mem (List.mem_map_of_mem hef) ?_
    exact ⟨μ, ⟨rfl, by rw [hetg]; trivial⟩,
      ⟨by simp only [Term.eval, Function.update_self], fun y hy => update_of_ne hy _ _⟩⟩
  have hstep : Program.sem (modeStep G mv q m) ν (update μ mv (e.tgt : ℝ)) := by
    refine ⟨ν, ⟨rfl, ?_⟩, μ, ?_, ?_⟩
    · simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, hmvq]
    · rw [hsys, hdom]; exact hode
    · exact hjump
  -- invLe g survives the mv-assign (mv ∉ g.fv); mvValid holds since e.tgt is a valid mode
  have hφ' : Formula.sat (Formula.and (invLe g) (mvValid mv G.modes.length))
      (update μ mv (e.tgt : ℝ)) := by
    refine ⟨?_, ?_⟩
    · have : Set.EqOn μ (update μ mv (e.tgt : ℝ)) (invLe g).fv := by
        intro x hx
        have hxg : x ≠ mv := by
          intro hxmv; subst hxmv
          exact hg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
        exact (update_of_ne hxg _ _).symm
      exact (Formula.coincidence (invLe g) this).mp hφμ
    · rw [sat_mvValid]
      exact ⟨e.tgt, hetv, by simp only [Function.update_self]⟩
  rw [diamond_sem]
  refine ⟨update μ mv (e.tgt : ℝ), ?_, hφ'⟩
  refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
  · exact List.mem_range.mpr (by
      have := hm; simp only [SearchGraph.modeAt] at this
      exact (List.getElem?_eq_some_iff.mp this).1)
  · rw [hm]; rfl


/-- The mode variable is **outside the left block** (`mv ∉ leftBlock.bound`): the left flow does not
evolve it, so it is held constant (carries the right automaton's mode index across the left residence).
Satisfiable once the state space has a coordinate outside `Lv ∪ Rv` — the auxiliary (`Aux`) slot `mv`
shares with the clock `tg`. NB: this SUPERSEDES the frozen-coordinate route (`∃ j, mv = Lv j ∧ …`),
which — while it satisfies the three freshness uses — makes `mv` a bound left coordinate, so it lands
in `Program.vars` of the left program and the `∀∃` disjointness (`hd : Disjoint (vars left) (vars
right)`, with the right automaton reading/assigning `mv`) becomes UNSATISFIABLE. The `∉ bound`/`Aux`
form is compatible with `hd` (disjointness holds by side split: left = `Lv`, right = `Rv ∪ Aux`). -/
theorem leftBlock_frames_mv (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (mv : Var n)
    (hmv : mv ∉ (leftBlock fL).bound) {σ ν : State (Var n)}
    (h : Program.sem (Program.ode (leftBlock fL) domL) σ ν) : ν mv = σ mv := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, _, hmask, _⟩ := h
  rw [← hΦr, hmask r ⟨hr, le_refl r⟩ mv hmv]

/-- **Unit 1-finish — the box wrapping.** From `segment_faModal`'s bare
`faModal (ode leftBlock) (ode rightBlock) (invLe g)` at `σ` (with `σ mv = q`), derive
`faModal (ode leftBlock) (rightAutomatonBody G mv) (invLe g)`. The mode variable survives
the left-block box (`mv ∉ leftBlock.bound`), so `ν mv = q` at each post-left state and
`diamond_right_wrap` applies. -/
theorem hstep_single (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n))
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound)
    (hm : G.modeAt q = some m) (hsys : m.sys = rightBlock fR lam) (hdom : m.dom = domR)
    {e : REdge (Var n)} (hef : e ∈ G.edgesFrom q) (hetg : e.guard = Formula.tt)
    (hetv : e.tgt < G.modes.length)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hseg : Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (invLe g)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (rightAutomatonBody G mv)
      (Formula.and (invLe g) (mvValid mv G.modes.length))) σ := by
  rw [faModal_sat] at hseg ⊢
  intro ν hsemν
  have hmvν : ν mv = (q : ℝ) := by rw [leftBlock_frames_mv fL domL mv hmvL hsemν]; exact hmvq
  have hdia : Formula.sat (Formula.diamond (Program.ode (rightBlock fR lam) domR) (invLe g)) ν := by
    rw [diamond_sem]
    obtain ⟨μ, hRμ, hφμ⟩ := hseg ν hsemν
    simp only [Program.rename_refl] at hRμ
    exact ⟨μ, hRμ, hφμ⟩
  have := diamond_right_wrap G mv q m g fR lam domR hg hm hsys hdom hef hetg hetv hmvν hdia
  rw [diamond_sem] at this
  obtain ⟨μ', hsem', hφ'⟩ := this
  exact ⟨μ', by simpa only [Program.rename_refl] using hsem', hφ'⟩


end RelCertifier
