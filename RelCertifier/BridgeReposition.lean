/-
GAP 1 (A) — the static-reposition step-lemma.

A static-reposition mode carries `m.sys = []` (zero motion): its `modeStep` is
`test(mode=q); ode [] dom; test e.guard; assign mv := e.tgt` — a state-preserving discrete mode
switch along a DECLARED edge. It preserves `invLe g` by two banked/trivial facts: the empty ODE is
the identity on the continuous state, and the `mv`-assign is invisible to `invLe g` (`mv ∉ g.fv`).
No `RegionInvOn`, no analysis (see the C.2 resolution: `region` references the left guard, is not a
right-automaton transition, and drops out post-tightening). ∃-right jump-faithfulness is the same as
the flow case: the target is a declared `G`-edge (`e ∈ edgesFrom q`).
-/
import RelCertifier.JointBridge
import RelCertifier.Reify

namespace RelCertifier
open DL DLCalTiming Function Set

variable {n : ℕ}

/-- Forward direction: a `bigChoiceP` run is a run of one of its branches (the dispatch used to
case a `rightAutomatonBody` step onto its firing mode). -/
theorem bigChoiceP_sem_forward {ps : List (Program (Var n))} {ν μ : State (Var n)}
    (h : Program.sem (bigChoiceP ps) ν μ) : ∃ p ∈ ps, Program.sem p ν μ := by
  induction ps with
  | nil => exact absurd h (by simp [bigChoiceP, Program.sem, Formula.sat])
  | cons a as ih =>
      rcases h with h | h
      · exact ⟨a, List.mem_cons_self, h⟩
      · obtain ⟨p, hp, hsem⟩ := ih h; exact ⟨p, List.mem_cons_of_mem _ hp, hsem⟩

/-- The empty ODE system is the identity: every variable is unbound, so the mask freezes it. -/
theorem sem_ode_nil {dom : Formula (Var n)} {ν μ : State (Var n)}
    (h : Program.sem (Program.ode [] dom) ν μ) : μ = ν := by
  obtain ⟨r, Φ, hr, _, hΦr, _, hmask, _⟩ := h
  funext x
  rw [← hΦr, hmask r ⟨hr, le_refl r⟩ x (by simp [ODESystem.bound])]

/-- **(A) — static reposition preserves `invLe g`.** A `modeStep` at a zero-motion (`m.sys = []`)
mode is a state-preserving declared-edge mode switch; `invLe g` survives because the continuous
state is unchanged and the `mv`-assign is invisible to `g` (`mv ∉ g.fv`). -/
theorem reposition_step_pres (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (hg : mv ∉ g.fv) (hsys : m.sys = [])
    {ν μ : State (Var n)} (hsem : Program.sem (modeStep G mv q m) ν μ)
    (hinv : Formula.sat (invLe g) ν) : Formula.sat (invLe g) μ := by
  -- modeStep = test(mode=q) ; ode m.sys dom ; bigChoiceP (edges)
  obtain ⟨κ1, htest, κ2, hode, hjump⟩ := hsem
  -- test passes: κ1 = ν
  have e1 : κ1 = ν := htest.1.symm
  -- empty ODE is the identity: κ2 = ν
  rw [hsys, e1] at hode
  have e2 : κ2 = ν := sem_ode_nil hode
  rw [e2] at hjump
  -- the jump is a declared edge's `test e.guard ; assign mv := e.tgt`
  obtain ⟨p, hpmem, hpsem⟩ := bigChoiceP_sem_forward hjump
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpmem
  obtain ⟨κ3, hg3, hasgn⟩ := hpsem
  have e3 : κ3 = ν := hg3.1.symm
  rw [e3] at hasgn
  -- `assign` sem is pointwise: `hasgn.2 : ∀ y ≠ mv, μ y = ν y`; on `g.fv` (which excludes `mv`)
  -- `μ` agrees with `ν`, so `invLe g` transfers by coincidence.
  have heq : Set.EqOn ν μ (invLe g).fv := by
    intro x hx
    have hxne : x ≠ mv := by
      rintro rfl
      exact hg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
    exact (hasgn.2 x hxne).symm
  exact (Formula.coincidence (invLe g) heq).mp hinv

/-- **(B) — dynamic reposition = flow machinery with `fL = 0`.** The dynamic reposition's right
segment evolves under the frozen-left field `m.dynSys = jointSys (0) fR lam` (`ṡ_L = 0`); its cert
`repoDynPresPre : SegPreservesOn g m.dynSys m.dynDomPre` is exactly the joint `BoxLe` that
`segment_faModal` consumes with `fL := 0`. So its modality image is the SAME `⟨ode rightBlock⟩`
diamond as the flow case — genuine reuse, NOT a new lemma. This wrapper makes the instantiation
explicit and confirms `fL = 0` presents no obstruction (the `hdisj`/footprint side-conditions hold:
`leftBlock 0` reads nothing, so it is disjoint from the right block). -/
theorem dynreposition_faModal (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hdisj : Disjoint ((leftBlock (fun _ => Term.const 0)).boundSet ∪
                        (leftBlock (fun _ => Term.const 0)).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock (fun _ => Term.const 0)).boundSet ∪
             (leftBlock (fun _ => Term.const 0)).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys (fun _ => Term.const 0) fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) ν)
    (hExist : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock (fun _ => Term.const 0),
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock (fun _ => Term.const 0)).bound → ΦL t x = ν x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock (fun _ => Term.const 0)) domL)
      (Program.ode (rightBlock fR lam) domR) (invLe g)) ν :=
  segment_faModal g (fun _ => Term.const 0) fR lam domL domR ν hdisj hφL hφR hcert hExist

end RelCertifier
