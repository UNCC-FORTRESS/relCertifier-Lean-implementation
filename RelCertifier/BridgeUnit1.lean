/-
Part B unit 1 (core) — the right-wrapping: turn the bare ⟨ode rightBlock⟩ φinv that
segment_faModal produces into ⟨rightAutomatonBody⟩ φinv (the mv-decorated transition body
faModal_LOCK loops). The mv test/jump/assign are invisible to the host invariant φinv
(mv ∉ φinv.fv), and the mode-q branch is selected by the state's mv value.
-/
import RelCertifier.JointBridge
import RelCertifier.Reify

namespace RelCertifier
open DL DLCalTiming Function

variable {n : ℕ}

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
    {ν : State (Var n)} (hmvq : ν mv = (q : ℝ))
    (h : Formula.sat (Formula.diamond (Program.ode (rightBlock fR lam) domR) (invLe g)) ν) :
    Formula.sat (Formula.diamond (rightAutomatonBody G mv) (invLe g)) ν := by
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
  -- invariant survives the mv-assign (mv ∉ g.fv)
  have hφ' : Formula.sat (invLe g) (update μ mv (e.tgt : ℝ)) := by
    have : Set.EqOn μ (update μ mv (e.tgt : ℝ)) (invLe g).fv := by
      intro x hx
      have hxg : x ≠ mv := by
        intro hxmv; subst hxmv
        exact hg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
      exact (update_of_ne hxg _ _).symm
    exact (Formula.coincidence (invLe g) this).mp hφμ
  rw [diamond_sem]
  refine ⟨update μ mv (e.tgt : ℝ), ?_, hφ'⟩
  refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
  · exact List.mem_range.mpr (by
      have := hm; simp only [SearchGraph.modeAt] at this
      exact (List.getElem?_eq_some_iff.mp this).1)
  · rw [hm]; rfl

end RelCertifier
