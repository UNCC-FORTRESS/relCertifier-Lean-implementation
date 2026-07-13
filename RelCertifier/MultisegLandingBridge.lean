/-
LIFT 1 — the `sat`→`rvalid` reification bridge for the landing-selected proof.

`multiseg_landing`/`tooling_sound_landing` prove the ∀∃ modality at the `sat`/`faModal` layer with the
strengthened invariant `starInvF = invLe g ∧ mvValid ∧ inModeDomF`. The shipped soundness theorem
(`theorem3_faithful`) is at the encoded `rvalid`/`theorem3Form` layer with the WEAKER invariant `phiInv =
invLe g ∧ mvValid`, whose `hstep` quantifies over ALL `phiInv`-states (incl. out-of-domain ones) — which
the landing discharge cannot cover (it needs the in-domain `inModeDomF`).

The bridge re-uses the EXISTING reification machinery (`faModal_LOCK`, `faModal_to_faShape`,
`encoding_correct`, `exists_bridge`) verbatim, only STRENGTHENING the threaded loop invariant from
`phiInv` to `starInvF`. The strengthened precondition is carried in the RFormula `ψpostL = ϕinv ∧ mvValidR
∧ inModeDomR`, which encodes exactly to `starInvF` (`encode_ψpostL`). So the shipped `rvalid(theorem3Form
… ψpostL)` conclusion is now produced from the landing `hstep` (at `starInvF`) — narrowing discharged via
landing-selection all the way to the encoded layer. The cost is an honest, satisfiable stronger
precondition: the tool's user provides an initial state in some mode's domain (`inModeDomR`), which every
well-formed benchmark config is.
-/
import RelCertifier.MultisegLanding
import RelCertifier.BridgeFinish

namespace RelCertifier
open DL DLCalTiming DLRel Function

variable {n : ℕ}

/-- `inModeDomF` as a right-projection rel formula (mirrors `mvValidR`). -/
def inModeDomR (G : SearchGraph (Var n)) (mv : Var n) : RFormula (Var n) :=
  RFormula.proj DLRel.Side.R (inModeDomF G mv)

/-- The right-projection of `inModeDomF` encodes (`ρ = id`) to the host `inModeDomF`. -/
theorem encode_inModeDomR (G : SearchGraph (Var n)) (mv : Var n) :
    encode (Equiv.refl (Var n)) (inModeDomR G mv) = inModeDomF G mv := by
  unfold encode inModeDomR
  simp only [RFormula.renameR, RFormula.enc, Formula.rename_refl]

/-- The strengthened precondition, carrying the domain conjunct as an RFormula. -/
def ψpostL (G : SearchGraph (Var n)) (mv : Var n) (ϕinv : RFormula (Var n)) : RFormula (Var n) :=
  RFormula.and ϕinv (RFormula.and (mvValidR mv G.modes.length) (inModeDomR G mv))

/-- **`ψpostL` encodes exactly to `starInvF`.** So the encoded loop invariant is the landing invariant. -/
theorem encode_ψpostL (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (ϕinv : RFormula (Var n)) (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g) :
    encode (Equiv.refl (Var n)) (ψpostL G mv ϕinv) = starInvF G mv g := by
  have hand : ∀ a b : RFormula (Var n), encode (Equiv.refl (Var n)) (RFormula.and a b)
      = Formula.and (encode (Equiv.refl (Var n)) a) (encode (Equiv.refl (Var n)) b) := by
    intro a b; unfold encode; simp only [RFormula.renameR, RFormula.enc]
  unfold ψpostL starInvF
  rw [hand, hand, hψ, encode_mvValidR, encode_inModeDomR]

/-- **The loop close at the landing invariant** — `relational_loop_faithful` with `φinv := starInvF`.
Same `faModal_LOCK` + `faModal_to_faShape` body; only the threaded invariant is strengthened. -/
theorem relational_loop_faithful_landing (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ψpost : RFormula (Var n))
    (ν : State (Var n)) (bs : BiState (Var n))
    (hψp : encode (Equiv.refl (Var n)) ψpost = starInvF G mv g)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hinv : Formula.sat (starInvF G mv g) ν)
    (hstep : ∀ σ, Formula.sat (starInvF G mv g) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs) (rightAutomatonBody G mv)
        (starInvF G mv g)) σ)
    (hdd : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψpost).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψpost).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψpost).varsL
        (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψpost).varsR bs ν) :
    RFormula.sat (faShape (Program.star (bigChoice leftProgs))
      (Program.star (rightAutomatonBody G mv)) ψpost) bs := by
  refine faModal_to_faShape (Equiv.refl (Var n)) (Program.star (bigChoice leftProgs))
    (Program.star (rightAutomatonBody G mv)) ψpost ν bs hdd hb ?_
  rw [hψp]
  exact faModal_LOCK (Equiv.refl (Var n)) (bigChoice leftProgs) (rightAutomatonBody G mv)
    (starInvF G mv g) (starInvF G mv g) ν hd hinv hstep (fun _ h => h)

/-- **LIFT 1 — the landing-selected transition-faithful Theorem 3, `rvalid` form.** The shipped encoded
soundness conclusion `rvalid(theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv) ψpostL)`, produced
from the landing `hstep` (single-body `faModal` at `starInvF` — what `hdispatch_of_modeResp`/the per-mode
dispatch supplies). Mirrors `theorem3_faithful`'s body with the strengthened invariant. This is the endpoint
that connects `tooling_sound_landing`'s `sat` output to the `rvalid` layer the tool consumes: narrowing
discharged by landing-selection, reified to the encoded theorem. -/
theorem theorem3_faithful_landing (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (starInvF G mv g) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs) (rightAutomatonBody G mv)
        (starInvF G mv g)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (ψpostL G mv ϕinv)) := by
  set ψpost := ψpostL G mv ϕinv with hψpost
  set Lp := Program.star (bigChoice leftProgs)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost = starInvF G mv g := encode_ψpostL G mv g ϕinv hψ
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
  have hInvν : Formula.sat (starInvF G mv g) ν := by
    rw [← hencψ]; exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_faithful_landing G mv g leftProgs ψpost ν bs hencψ hd hInvν hstep hddF hbdg

/-! ## LIFT 2 Phase A — single-left-mode enumeration (the wiring proof)

Discharge `theorem3_faithful_landing`'s `hstep` (∀`starInvF`-state, single-body `faModal` at `starInvF`)
for ONE left mode, with the right dispatching over all its modes. `hresp` is the per-(right-)mode response —
widening edges via `landing_step_faModal` (by construction), narrowing edges via `landing_step_narrowing`
(under `SuccReach`). `faModal_bigChoiceL` folds the singleton left choice (with its dead `[]`-branch
vacuous), and the dispatch reads the right mode off `StarInModeDom`. Both switch shapes wire through. -/

/-- `hstep` for a single left mode, from the per-mode dispatch `hresp`. -/
theorem hstep_landing_single (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (hresp : ∀ σ', StarInv G mv g σ' → ∀ q m, G.modeAt q = some m → σ' mv = (q : ℝ) →
        Formula.sat m.dom σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
          (rightAutomatonBody G mv) (starInvF G mv g)) σ') :
    ∀ σ, Formula.sat (starInvF G mv g) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice [Program.ode (leftBlock fL) domL])
        (rightAutomatonBody G mv) (starInvF G mv g)) σ := by
  intro σ hσ
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (rightAutomatonBody G mv) (starInvF G mv g) σ
    [Program.ode (leftBlock fL) domL] ?_
  intro P hP
  rw [List.mem_singleton] at hP; subst hP
  have hstar := sat_starInvF.mp hσ
  obtain ⟨q, m, hqmv, hmode, hmdom⟩ := hstar.2.2
  exact hresp σ hstar q m hmode hqmv hmdom

/-- **LIFT 2 Phase A — the single-left-mode end-to-end (wiring proof).** Composes the FULL path
`dispatch (hresp) → hstep_landing_single → theorem3_faithful_landing (faModal_LOCK + reification bridge) →
rvalid`. Produces the shipped encoded conclusion `rvalid(theorem3Form …)` for one left mode, with narrowing
discharged via landing-selection under `SuccReach` (inside `hresp`'s narrowing branch) and widening by
construction. Confirms the landing-selected proof reaches the tool's `rvalid` layer sorry-free. -/
theorem tooling_sound_landing_rvalid (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hd : Disjoint (Program.vars (bigChoice [Program.ode (leftBlock fL) domL]))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hresp : ∀ σ', StarInv G mv g σ' → ∀ q m, G.modeAt q = some m → σ' mv = (q : ℝ) →
        Formula.sat m.dom σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
          (rightAutomatonBody G mv) (starInvF G mv g)) σ')
    (hddF : Disjoint (faShape (Program.star (bigChoice [Program.ode (leftBlock fL) domL]))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice [Program.ode (leftBlock fL) domL]))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice [Program.ode (leftBlock fL) domL])
      (rightAutomatonBody G mv) (ψpostL G mv ϕinv)) :=
  theorem3_faithful_landing G mv g [Program.ode (leftBlock fL) domL] ϕinv hψ hd
    (hstep_landing_single G mv g fL domL hresp) hddF

end RelCertifier
