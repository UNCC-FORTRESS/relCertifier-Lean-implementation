/-
The `sat`→`rvalid` reification bridge for the landing-selected proof.

`multiseg_landing`/`tooling_sound_landing` prove the ∀∃ modality at the `sat`/`faModal` layer with the
invariant `starInvF = invLe g ∧ mvValid ∧ inModeDomF`. `theorem3_faithful` states the encoded
`rvalid`/`theorem3Form` claim (the shape of Eq. (10)) with the weaker invariant `phiInv = invLe g ∧
mvValid`, whose `hstep` quantifies over all `phiInv`-states, including out-of-domain ones, which the
landing discharge cannot cover (it needs `inModeDomF`).

This file reuses the reification machinery (`faModal_LOCK`, `faModal_to_faShape`,
`encoding_correct`, `exists_bridge`) with the loop invariant strengthened from `phiInv` to
`starInvF`, carried in the RFormula `ψpostL = ϕinv ∧ mvValidR ∧ inModeDomR`, which encodes exactly to
`starInvF` (`encode_ψpostL`). The `rvalid(theorem3Form … ψpostL)` conclusion is then produced from the
landing `hstep` at `starInvF`. The stronger precondition asks the initial state to lie in some
mode's domain (`inModeDomR`); the strengthened invariant of Eq. (10) includes the stored domains.

These statements feed `UniformEvol.lean`; the paper's Theorem 3 is mechanized by
`theorem3_of_coverX` (Appendix B.1).
-/
import RelCertifier.Proofs.Flow.MultisegLanding
import RelCertifier.Proofs.Encoding.BridgeFinish

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

/-- **The landing-selected encoded claim, `rvalid` form.** If every `starInvF`-state satisfies the
single-body `faModal` of `bigChoice leftProgs` and `rightAutomatonBody G mv` at `starInvF` (`hstep`,
what the per-mode dispatch supplies), then `rvalid(theorem3Form (bigChoice leftProgs)
(rightAutomatonBody G mv) ψpostL)`, under the variable-disjointness side conditions. Mirrors
`theorem3_faithful`'s body with the strengthened invariant, connecting `tooling_sound_landing`'s
`sat` output to the encoded layer. -/
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

/-! ## Single left mode

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

/-- **The single-left-mode encoded claim.** Composes `dispatch (hresp) → hstep_landing_single →
theorem3_faithful_landing (faModal_LOCK + reification bridge) → rvalid`: the encoded conclusion
`rvalid(theorem3Form …)` for one left mode, with narrowing edges discharged by landing-selection under
`SuccReach` (inside `hresp`'s narrowing branch) and widening edges by construction. -/
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

/-! ## The full left family

`leftBody = bigChoice leftProgs` over the WHOLE left automaton (multiple left modes). `hstep` folds via
`faModal_bigChoiceL` over `leftProgs`: for each left mode `P`, the right dispatches on `σ`'s mode
(`StarInModeDom`) and responds (widening → `landing_step_faModal`, narrowing → `landing_step_narrowing`).
`hresp` is the per-(left-mode × right-mode) response bundle, the family analog of the chain's
`Hmulti`, with `SuccReach` inside its narrowing responses. -/

/-- `hstep` for the full left family, from the per-(left-mode × right-mode) dispatch `hresp`. -/
theorem hstep_landing_family (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n)))
    (hresp : ∀ P ∈ leftProgs, ∀ σ', StarInv G mv g σ' → ∀ q m, G.modeAt q = some m → σ' mv = (q : ℝ) →
        Formula.sat m.dom σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) P (rightAutomatonBody G mv) (starInvF G mv g)) σ') :
    ∀ σ, Formula.sat (starInvF G mv g) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (rightAutomatonBody G mv) (starInvF G mv g)) σ := by
  intro σ hσ
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (rightAutomatonBody G mv) (starInvF G mv g) σ
    leftProgs ?_
  intro P hP
  have hstar := sat_starInvF.mp hσ
  obtain ⟨q, m, hqmv, hmode, hmdom⟩ := hstar.2.2
  exact hresp P hP σ hstar q m hmode hqmv hmdom

/-- **The full-family encoded claim.** `rvalid(theorem3Form (bigChoice leftProgs)
(rightAutomatonBody G mv) ψpostL)` over all left and right modes, from the landing-selected proof:
`hstep_landing_family` (per-(left×right) dispatch, folded by `faModal_bigChoiceL`) →
`theorem3_faithful_landing` (`faModal_LOCK` + reification bridge) → `rvalid`. Narrowing edges discharge
under `SuccReach` (inside `hresp`'s narrowing branch), shared/widening ones by construction; there is
no `∀ν HExistSeg` and no `WFBoundary` hypothesis. The encoded `tooling_sound` and `multiseg_het` are
the all-widening / `EmitSegs` special cases. -/
theorem tooling_sound_landing_family (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hresp : ∀ P ∈ leftProgs, ∀ σ', StarInv G mv g σ' → ∀ q m, G.modeAt q = some m → σ' mv = (q : ℝ) →
        Formula.sat m.dom σ' →
        Formula.sat (faModal (Equiv.refl (Var n)) P (rightAutomatonBody G mv) (starInvF G mv g)) σ')
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs)
      (rightAutomatonBody G mv) (ψpostL G mv ϕinv)) :=
  theorem3_faithful_landing G mv g leftProgs ϕinv hψ hd
    (hstep_landing_family G mv g leftProgs hresp) hddF

/-! ## The clocked combiner

The clocked physical modality `multiseg_landing_clocked_physical` already produces `faModal (star (ode
leftBlock))(star R) starInvF` (the star is built, so no `faModal_LOCK` is needed). The reification is
`faModal_to_faShape` (lift the pre-starred `faModal` to the bi-state `faShape`) plus the bridge
machinery. `theorem3_faithful_landing_clocked` routes it to `rvalid(theorem3Form …)` from
`LandingH`-membership and duration-bounded (`≤ dt`) invariance `WellFormedFlowB`. -/

/-- The pre-starred bridge: lift `faModal (star L)(star R) starInvF` to `faShape (star L)(star R) ψpost`
(reification, `tg`/encoding-free — skips `faModal_LOCK` since the star is already present). -/
theorem faShape_of_faModal_landing (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (L : Program (Var n)) (ψpost : RFormula (Var n)) (ν : State (Var n)) (bs : BiState (Var n))
    (hψp : encode (Equiv.refl (Var n)) ψpost = starInvF G mv g)
    (hdd : Disjoint (faShape (Program.star L) (Program.star (rightAutomatonBody G mv)) ψpost).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star L)
          (Program.star (rightAutomatonBody G mv)) ψpost).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star L) (Program.star (rightAutomatonBody G mv)) ψpost).varsL
        (faShape (Program.star L) (Program.star (rightAutomatonBody G mv)) ψpost).varsR bs ν)
    (hphys : Formula.sat (faModal (Equiv.refl (Var n)) (Program.star L)
        (Program.star (rightAutomatonBody G mv)) (starInvF G mv g)) ν) :
    RFormula.sat (faShape (Program.star L) (Program.star (rightAutomatonBody G mv)) ψpost) bs := by
  refine faModal_to_faShape (Equiv.refl (Var n)) (Program.star L)
    (Program.star (rightAutomatonBody G mv)) ψpost ν bs hdd hb ?_
  rw [hψp]; exact hphys

/-- **The encoded claim on the clocked combiner.** `rvalid(theorem3Form (ode leftBlock fL domL)
(rightAutomatonBody G mv) ψpostL)`, produced from `multiseg_landing_clocked_physical` via
`faModal_to_faShape` + the bridge. Hypotheses: `hHcouple`, the clocked dispatch (a `faModalB` with the
left clocked by `tg` and capped at `dt`, from every `starInvF`-state), and `hbudgetAll`, every left run's
duration is at most `k·dt` (the budget of `k` equal segments, Appendix B.2), plus clock freshness
and variable disjointness. The statement holds wherever the flow lands; it does not assert that a
narrowing switch is taken. -/
theorem theorem3_faithful_landing_clocked (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ)
    (ϕinv : RFormula (Var n)) (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (htgb : tg ∉ (leftBlock fL).bound) (htgr : tg ∉ (leftBlock fL).readVars) (htgϕ : tg ∉ domL.fv)
    (hdt : 0 ≤ dt)
    (htgR : tg ∉ ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))).fv)
    (htgφ : tg ∉ (starInvF G mv g).fv)
    (hHcouple : ∀ σ', Formula.sat (starInvF G mv g) σ' →
      faModalB (Equiv.refl (Var n)) (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
        (rightAutomatonBody G mv) (starInvF G mv g) tg dt (Function.update σ' tg 0))
    (hdis : Disjoint (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg dt)))
    (hdMULTI : Disjoint (Program.vars (Program.ode (leftBlock fL) domL))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hbudgetAll : ∀ (σ' : State (Var n)), ∀ {r : ℝ} {Φ : ℝ → State (Var n)},
        ODESol (leftBlock fL) domL σ' r Φ → r ≤ (k : ℝ) * dt)
    (hddF : Disjoint (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (Program.ode (leftBlock fL) domL)
      (rightAutomatonBody G mv) (ψpostL G mv ϕinv)) := by
  set ψpost := ψpostL G mv ϕinv with hψpost
  set Lp := Program.star (Program.ode (leftBlock fL) domL)
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
  have hphys := multiseg_landing_clocked_physical G mv g fL domL tg dt k htgb htgr htgϕ hdt htgR htgφ
    hHcouple hdis hdMULTI hbudgetAll hInvν
  exact faShape_of_faModal_landing G mv g (Program.ode (leftBlock fL) domL) ψpost ν bs hencψ hddF hbdg hphys

/-- **The encoded claim from `LandingWellFormed`.** `theorem3_faithful_landing_clocked` with the
dispatch bundle `hHcouple` replaced by the model-level `LandingWellFormed` (for every mode:
duration-bounded staying + `LandingH` membership over its retained successors `retainedSucc`).
`hHcouple` is derived (`hHcouple_of_LandingWellFormed`); the remaining hypotheses (clock freshness,
the budget `r ≤ k·dt`, disjointness) are clocking and bridge side conditions. `UniformEvol.lean`
discharges `LandingWellFormed`. -/
theorem theorem3_faithful_landing_clocked_wf (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ)
    (lam : Term (Var n)) (ϕinv : RFormula (Var n)) (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hlwf : LandingWellFormed G mv g lam tg dt fL domL)
    (htgb : tg ∉ (leftBlock fL).bound) (htgr : tg ∉ (leftBlock fL).readVars) (htgϕ : tg ∉ domL.fv)
    (htgR : tg ∉ ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))).fv)
    (htgφ : tg ∉ (starInvF G mv g).fv)
    (hdis : Disjoint (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg dt)))
    (hdMULTI : Disjoint (Program.vars (Program.ode (leftBlock fL) domL))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hbudgetAll : ∀ (σ' : State (Var n)), ∀ {r : ℝ} {Φ : ℝ → State (Var n)},
        ODESol (leftBlock fL) domL σ' r Φ → r ≤ (k : ℝ) * dt)
    (hddF : Disjoint (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (Program.ode (leftBlock fL) domL)
      (rightAutomatonBody G mv) (ψpostL G mv ϕinv)) :=
  theorem3_faithful_landing_clocked G mv g fL domL tg dt k ϕinv hψ htgb htgr htgϕ hlwf.1 htgR htgφ
    (hHcouple_of_LandingWellFormed G mv g lam tg dt fL domL hlwf) hdis hdMULTI hbudgetAll hddF

end RelCertifier
