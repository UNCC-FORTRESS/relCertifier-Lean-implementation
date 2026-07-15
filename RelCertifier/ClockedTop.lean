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

end RelCertifier
