/-
Run-level projection (reserved route): the cover's jointSys RightReach projects to a right-only
RightReach over the rightBlock-projected graph, threading freezeL at a global cL.
Assembles ode_project_right along the run by structural induction.

STATUS: proven; RESERVED for the run-level route. `rightReach_project`'s per-mode alignment
hypothesis (`hmode`) is the SAME joint↔right relation the end-to-end discharge carries as the
structural `RightProjAlign` (`BridgeDischarge`) — but that discharge is CERTIFICATE-level
(`cert.segPres` → `segment_faModal`) and does not run the projection. Kept as an alternate route: reposition/multi-flow (GAP 1-3) was closed at the certificate level,
not via this run-level projection. Not dead code — a run-level soundness argument.
-/
import RelCertifier.Proofs.Encoding.JointBridge
import RelCertifier.Archive.OdeProject

namespace RelCertifier
open DL Function

variable {n : ℕ}

/-- Per-mode jointSys data (the fL/fR/λ/domains a cover mode's system decomposes into). -/
structure JointData (n : ℕ) where
  fL : Fin n → Term (Var n)
  fR : Fin n → Term (Var n)
  lam : Term (Var n)
  domL : Formula (Var n)
  domR : Formula (Var n)

/-- **Run-level projection.** A `jointSys` `RightReach` over `G` projects to a right-only
`RightReach` over `G'` (the rightBlock-projected graph), freezing the left coordinates at a
global `cL`. `ode_project_right` discharges the flow steps; guards (reading only `Rv`) transfer
by `Formula.coincidence`; reposition steps are impossible under `NoRepoModes`. -/
theorem rightReach_project (G G' : SearchGraph (Var n)) (dat : ℕ → JointData n)
    (cL : State (Var n))
    (hedge : G'.edges = G.edges)
    (hmode : ∀ q m, G.modeAt q = some m → ∃ m',
        G'.modeAt q = some m' ∧ m'.sys = rightBlock (dat q).fR (dat q).lam ∧
        m'.dom = (dat q).domR ∧ m'.jointOK = m.jointOK ∧ m'.weight = m.weight ∧
        m.sys = jointSys (dat q).fL (dat q).fR (dat q).lam ∧
        m.dom = Formula.and (dat q).domL (dat q).domR)
    (hRauto : ∀ q, (∀ i, ((dat q).fR i).fv ⊆ RvSet n) ∧
        (dat q).lam.fv ⊆ RvSet n ∧ (dat q).domR.fv ⊆ RvSet n)
    (hguard : ∀ e ∈ G.edges, (e.guard).fv ⊆ RvSet n)
    (hnorepo : NoRepoModes G) :
    ∀ {cfg : Config} {ν ω : State (Var n)}, RightReach G cfg ν ω →
      RightReach G' cfg (freezeL cL ν) (freezeL cL ω) := by
  intro cfg ν ω hreach
  induction hreach with
  | @refl q B σ ν => exact RightReach.refl
  | @evolve q B σ ν μ ω m hm hj hsem _ ih =>
      obtain ⟨m', hm', hsys', hdom', hjoint', _, hsysJ, hdomJ⟩ := hmode q m hm
      obtain ⟨hfR, hlam, hdomR⟩ := hRauto q
      have hstep : Program.sem (Program.ode m'.sys m'.dom)
          (freezeL cL ν) (freezeL cL μ) := by
        rw [hsys', hdom']
        rw [hsysJ, hdomJ] at hsem
        exact ode_project_right _ _ _ _ _ hfR hlam hdomR cL hsem
      exact RightReach.evolve m' hm' (by rw [hjoint']; exact hj) hstep ih
  | @jump q B σ ν μ ω m hm hj e he hsrc hlt hsem hgud _ ih =>
      obtain ⟨m', hm', hsys', hdom', hjoint', hw', hsysJ, hdomJ⟩ := hmode q m hm
      obtain ⟨hfR, hlam, hdomR⟩ := hRauto q
      have hstep : Program.sem (Program.ode m'.sys m'.dom)
          (freezeL cL ν) (freezeL cL μ) := by
        rw [hsys', hdom']; rw [hsysJ, hdomJ] at hsem
        exact ode_project_right _ _ _ _ _ hfR hlam hdomR cL hsem
      have hgud' : Formula.sat e.guard (freezeL cL μ) :=
        (Formula.coincidence e.guard ((eqOn_Rv cL μ).mono (hguard e he))).mp hgud
      have hlt' : m'.weight < B := by rw [hw']; exact hlt
      refine RightReach.jump m' hm' (by rw [hjoint']; exact hj) e (by rw [hedge]; exact he)
        hsrc hlt' hstep hgud' ?_
      rw [hw']; exact ih
  | @repositionDynPre q B ν μ ω m hm hrepo _ _ _ _ _ _ _ =>
      exact absurd hrepo (by rw [(hnorepo q m hm).1]; simp)
  | @repositionDynPost q B ν μ ω m hm hrepo _ _ _ _ _ _ _ =>
      exact absurd hrepo (by rw [(hnorepo q m hm).2]; simp)

end RelCertifier
