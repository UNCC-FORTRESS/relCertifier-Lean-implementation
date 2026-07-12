/-
The per-segment ODE decoupling (run-level projection route, reserved).
A jointSys run projects to a rightBlock (right-only) run: freeze Lv, keep Rv.
The derivative decoupling rests on RightAutonomous (fR/lam/domR read only Rv).

STATUS: proven; RESERVED for the run-level projection route (feeds `rightReach_project`). The
end-to-end certificate discharge (`BridgeDischarge`) does NOT use it — that path decouples at the
CERTIFICATE level via `segment_faModal`. Kept as an alternate route: the reposition/multi-flow lift (GAP 1-3) was closed via the
certificate-level path, not this run-level projection. Not dead code — a run-level soundness argument.
-/
import RelCertifier.Reify
import RelCertifier.FlowCert

namespace RelCertifier
open DL Function

variable {n : ℕ}

/-- The right coordinate set of `Var n`. -/
def RvSet (n : ℕ) : Set (Var n) := {v | ∃ j : Fin n, v = Rv j}

/-- Freeze the left coordinates at `ν`, keep the right coordinates from `s`. -/
def freezeL (ν s : State (Var n)) : State (Var n) :=
  fun v => match v.1 with | Side.L => ν v | Side.R => s v | Side.Aux => ν v

@[simp] theorem freezeL_R (ν s : State (Var n)) (j : Fin n) : freezeL ν s (Rv j) = s (Rv j) := rfl
@[simp] theorem freezeL_L (ν s : State (Var n)) (j : Fin n) : freezeL ν s (Lv j) = ν (Lv j) := rfl

/-- `Φ t` and `freezeL ν (Φ t)` agree on the right coordinates. -/
theorem eqOn_Rv (ν : State (Var n)) (s : State (Var n)) :
    Set.EqOn s (freezeL ν s) (RvSet n) := by
  rintro v ⟨j, rfl⟩; rfl

/-- **Per-segment ODE decoupling.** A `jointSys` run projects to a `rightBlock` run,
freezing the left coordinates. `RightAutonomous` (fR/lam/domR read only Rv) is the
load-bearing hypothesis: it lets the right derivatives drop the (frozen) Lv-dependence. -/
theorem ode_project_right (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n))
    (hfR : ∀ i, (fR i).fv ⊆ RvSet n) (hlam : lam.fv ⊆ RvSet n)
    (hdomR : Formula.fv domR ⊆ RvSet n)
    (cL : State (Var n)) {ν μ : State (Var n)}
    (h : Program.sem (Program.ode (jointSys fL fR lam) (Formula.and domL domR)) ν μ) :
    Program.sem (Program.ode (rightBlock fR lam) domR) (freezeL cL ν) (freezeL cL μ) := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hderiv, hmask, hdom⟩ := h
  refine ⟨r, fun t => freezeL cL (Φ t), hr, ?_, ?_, ?_, ?_, ?_⟩
  · -- Φ 0 initial: freezeL cL (Φ 0) = freezeL cL ν
    show freezeL cL (Φ 0) = freezeL cL ν; rw [hΦ0]
  · -- endpoint: freezeL cL (Φ r) = freezeL cL μ
    show freezeL cL (Φ r) = freezeL cL μ; rw [hΦr]
  · -- derivatives: each right equation, value decoupled from Lv via RightAutonomous
    intro t ht p hp
    -- p ∈ rightBlock ⟹ p = (Rv i, lam * fR i); the L-frozen curve's Rv-component is Φ's
    simp only [rightBlock, List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    -- from the joint run: derivative of Φ·(Rv i) with value (lam*fR i).eval (Φ t)
    have hpj : (Rv i, Term.binop AOp.mul lam (fR i)) ∈ jointSys fL fR lam := by
      rw [jointSys_split]; exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have hd := hderiv t ht _ hpj
    -- value at Φ t equals value at freezeL ν (Φ t): lam, fR i read only Rv
    have hval : (Term.binop AOp.mul lam (fR i)).eval (Φ t)
        = (Term.binop AOp.mul lam (fR i)).eval (freezeL cL (Φ t)) := by
      simp only [Term.eval]
      rw [Term.coincidence lam ((eqOn_Rv cL (Φ t)).mono hlam),
          Term.coincidence (fR i) ((eqOn_Rv cL (Φ t)).mono (hfR i))]
    have hfun : (fun s => (freezeL cL (Φ s)) (Rv i)) = (fun s => Φ s (Rv i)) := by
      funext s; rfl
    show HasDerivWithinAt (fun s => (freezeL cL (Φ s)) (Rv i))
      ((Term.binop AOp.mul lam (fR i)).eval (freezeL cL (Φ t))) (Set.Icc 0 r) t
    rw [hfun, ← hval]; exact hd
  · -- masking: non-right vars held at ν
    intro t ht x hx
    rcases x with ⟨sd, i⟩; cases sd with
    | L => show freezeL cL (Φ t) (Side.L, i) = freezeL cL ν (Side.L, i); rfl
    | Aux => show freezeL cL (Φ t) (Side.Aux, i) = freezeL cL ν (Side.Aux, i); rfl
    | R => exact absurd (List.mem_map.mpr ⟨(Rv i, Term.binop AOp.mul lam (fR i)),
        List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, rfl⟩) hx
  · -- domain: domR holds along the frozen curve (domR reads only Rv)
    intro t ht
    have := (hdom t ht).2
    exact (Formula.coincidence domR ((eqOn_Rv cL (Φ t)).mono hdomR)).mp this

end RelCertifier
