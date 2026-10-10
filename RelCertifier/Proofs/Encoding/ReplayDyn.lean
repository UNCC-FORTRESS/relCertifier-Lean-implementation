/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The dynamic-reposition verdict pack (certificate 3), stated and consumed

An emitted cover flags a right mode `q` of a left window `l` as a dynamic-reposition node
(`dynPre` before the first joint segment, `dynPost` after one) when `OracleAPI.checkDynRepo`
found every invariant component's route-A query `UNSAT`: the right moves alone under `q`'s own
field (the left frozen, `fL = 0`, stretch 1), over the evolve domains narrowed by both modes'
kept cut atoms and the proven strata, and, before the first joint segment, the left mode's
guard (the left has not moved since it passed that guard). This file states that pack at the
host level exactly as `checkDynRepo` builds it (`VerdDynCore`, `modalVerdDynX`, read off the
IR and the extended cut certificate like `modalVerdX`) and turns it into the box invariant the
cover replay consumes (`couple_box_dyn`): along every right-only run of `q` (left frozen), from
a state satisfying the rows and both sides' kept atoms (and the left guard, before the first
joint segment), the rows and the atoms hold at the end.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.SyncSwitch

namespace RelCertifier

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## The pack, as `checkDynRepo` builds it -/

/-- The query domain of component `i` of a reposition pack: the cut-narrowed base narrowed by
the proven strata, then (before the first joint segment, `pre`) the left guard (the tool's
`dom := if withGuardL then dom0 ∧ gL else dom0`). -/
noncomputable def dynDomHost (pre : Bool) (D gL : Formula (Var n)) (prev : List (Term (Var n))) :
    Formula (Var n) :=
  if pre then Formula.and (strataDomHost D prev) gL else strataDomHost D prev

/-- **The stratified route-A pack of a dynamic reposition.** Per component (in the cover's
`dynPreOrder` / `dynPostOrder`), the route-A query `domain ∧ ġ > 0` with the left frozen
(`fL = 0`) and stretch 1 is `UNSAT`. -/
def VerdDynCore (pre : Bool) (comps : List (Term (Var n))) (fR : Fin n → Term (Var n))
    (D gL : Formula (Var n)) : Prop :=
  ∀ i (hi : i < comps.length),
    z3solve (flowQuery ⟨comps[i], fun _ => Term.const 0, fR, Term.const 1,
      dynDomHost pre D gL (comps.take i)⟩) = Verdict.unsat

/-- **The suite_v2 reposition pack, read off the IR and the extended certificate.** Left mode
`l` (its guard, its kept atoms, its evolve domain), right mode `m` (its field, its kept atoms,
its evolve domain), the invariant row `invRow`'s components in the cover's reposition strata
`order`; `pre` selects the pre-joint form (the left guard conjoined). Exactly the queries
`OracleAPI.checkDynRepo` sends (`segPartsRO`, `andCuts`, `strataDomIR`, route A). -/
noncomputable def modalVerdDynX (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (pre : Bool) (l m : ℕ) : Prop :=
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let comps0 := hostComps vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let comps := order.map (fun i => comps0.getD i (Term.const 0))
  let base := Formula.and (hostEvolve vars n Side.L mL) (hostEvolve vars n Side.R mR)
  let cL := cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)
  let cR := cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)
  VerdDynCore pre comps (hostDyn vars n Side.R mR) (domCutX base cL cR)
    (hostGuard vars n Side.L mL)

/-! ## From the pack to preservation along the frozen-left flow -/

/-- The base domain of a reposition run: the evolve domains, and (pre-joint) the left guard. -/
noncomputable def dynBase (pre : Bool) (dom gL : Formula (Var n)) : Formula (Var n) :=
  if pre then Formula.and dom gL else dom

theorem sat_dynDomHost (pre : Bool) (D gL : Formula (Var n)) (prev : List (Term (Var n)))
    (ν : State (Var n)) :
    Formula.sat (dynDomHost pre D gL prev) ν ↔
      Formula.sat (Formula.and (dynBase pre D gL) (bigLe prev)) ν := by
  unfold dynDomHost dynBase
  cases pre <;> simp only [Bool.false_eq_true, if_false, if_true, Formula.sat,
    sat_strataDomHost, sat_bigLe_iff] <;> tauto

/-- The reposition pack gives simultaneous preservation of the components along the frozen-left
right flow, on the (cut-narrowed) base domain. -/
theorem segPresAll_dyn (pre : Bool) (comps : List (Term (Var n))) (fR : Fin n → Term (Var n))
    (D gL : Formula (Var n)) (hv : VerdDynCore pre comps fR D gL) :
    SegPreservesAllOn comps (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (dynBase pre D gL) := by
  intro ν hinit
  refine stratified_barrier_boxle _ (dynBase pre D gL) comps ?_ hinit
  intro i hi ν' hν'
  have hcong : ∀ x, Formula.sat (Formula.and (dynBase pre D gL) (bigLe (comps.take i))) x ↔
      Formula.sat (dynDomHost pre D gL (comps.take i)) x :=
    fun x => (sat_dynDomHost pre D gL _ x).symm
  refine boxle_dom_congr hcong ?_
  exact flow_cert_sound ⟨comps[i], fun _ => Term.const 0, fR, Term.const 1,
    dynDomHost pre D gL (comps.take i)⟩ (z3_unsat_sound (hv i hi)) hν'

/-- Left coordinates are frozen at every instant of a frozen-left run. -/
theorem frozen_left_all {fR : Fin n → Term (Var n)} {lam : Term (Var n)} {dom : Formula (Var n)}
    {ν : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (hr : 0 ≤ r) (hΦ0 : Φ 0 = ν)
    (hder : ∀ t ∈ Icc (0 : ℝ) r, ∀ p ∈ jointSys (fun _ => Term.const 0) fR lam,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t)
    (hmask : ∀ t ∈ Icc (0 : ℝ) r, ∀ x, x ∉ (jointSys (fun _ => Term.const 0) fR lam).bound →
      Φ t x = ν x)
    (hdom : ∀ t ∈ Icc (0 : ℝ) r, Formula.sat dom (Φ t)) :
    ∀ t ∈ Icc (0 : ℝ) r, ∀ i : Fin n, Φ t (Lv i) = ν (Lv i) := by
  intro t ht i
  have hrun : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam) dom) ν (Φ t) :=
    DLCalTiming.sem_ode_restrict ⟨hr, hΦ0, hder, hmask, hdom⟩ ht.1 ht.2
  exact frozen_left_constant hrun i

/-- A frozen-left run keeps every left-only formula: it is a run of the narrowed ode. -/
theorem frozen_run_narrow {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {dom φ : Formula (Var n)} (hφ : φ.fv ⊆ range Lv) {ν μ : State (Var n)}
    (h : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam) dom) ν μ)
    (hν : Formula.sat φ ν) :
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam) (Formula.and dom φ)) ν μ := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  have hfz := frozen_left_all (dom := dom) hr hΦ0 hder hmask hdom
  refine ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, fun t ht => ⟨hdom t ht, ?_⟩⟩
  refine (Formula.coincidence φ (fun v hv => ?_)).mpr hν
  obtain ⟨i, rfl⟩ := hφ hv
  exact hfz t ht i

/-- Left atoms stay along a frozen-left run (their terms read left coordinates only). -/
theorem atomsStayC_frozenL {cL : List (CutAtomP n)} (hiff : AtomsIff cL)
    (hfv : ∀ a ∈ cL, a.2.fv ⊆ range Lv) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (dom : Formula (Var n)) :
    AtomsStayC cL (jointSys (fun _ => Term.const 0) fR lam) dom := by
  intro a ha ν hν ω hω
  have hval : Term.eval a.2 ω = Term.eval a.2 ν := by
    refine Term.coincidence a.2 (fun v hv => ?_)
    obtain ⟨i, rfl⟩ := hfv a ha hv
    exact frozen_left_constant hω i
  show Term.eval a.2 ω ≤ 0
  rw [hval]
  exact (hiff a ha ν).mp (hν a ha)

/-- **The reposition anchor is a box invariant of the frozen-left right flow.** From the
reposition pack of `(l, q)` (`VerdDynCore`, the domain the cut-narrowed evolves, and the left
guard before the first joint segment), the right atoms' staying along `q`'s right-only flow,
and the left atoms reading left coordinates only: along every frozen-left run of `q` from a
state satisfying the rows and both sides' atoms (and the left guard, pre-joint), the rows and
the atoms hold at the end. -/
theorem couple_box_dyn (pre : Bool) (g : Term (Var n)) (gs comps : List (Term (Var n)))
    (cL cR : List (CutAtomP n)) (fR : Fin n → Term (Var n)) (domL domR gL : Formula (Var n))
    (hsub1 : ∀ c ∈ comps, c ∈ g :: gs) (hsub2 : ∀ g' ∈ g :: gs, g' ∈ comps)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR) (hLfv : ∀ a ∈ cL, a.2.fv ⊆ range Lv)
    (hgL : gL.fv ⊆ range Lv)
    (hstayR : AtomsStayC cR (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (dynBase pre (Formula.and domL domR) gL))
    (hverd : VerdDynCore pre comps fR (domCutX (Formula.and domL domR) cL cR) gL) :
    ∀ σ ω, Formula.sat (FM g (gs ++ atomTerms cL cR)) σ → (pre = true → Formula.sat gL σ) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
        (Formula.and domL domR)) σ ω →
      Formula.sat (FM g (gs ++ atomTerms cL cR)) ω := by
  intro σ ω hσ hgσ hω
  set sys := jointSys (fun _ => Term.const 0) fR (Term.const 1) with hsys
  have hrun : Program.sem (Program.ode sys (dynBase pre (Formula.and domL domR) gL)) σ ω := by
    unfold dynBase
    cases pre with
    | false => simpa using hω
    | true => simpa using frozen_run_narrow hgL hω (hgσ rfl)
  have hnarrow : SegPreservesAllOn comps sys
      (dynBase pre (domCutX (Formula.and domL domR) cL cR) gL) :=
    segPresAll_dyn pre comps fR _ gL hverd
  have hnarrow' : SegPreservesAllOn comps sys
      (Formula.and (dynBase pre (Formula.and domL domR) gL)
        (Formula.and (cutF cL) (cutF cR))) := by
    refine segPresAll_congr (fun x => ?_) hnarrow
    unfold dynBase
    cases pre <;> simp only [Bool.false_eq_true, if_false, if_true, Formula.sat,
      sat_domCutX, sat_cutF] <;> tauto
  have hlift := segPresAll_cut_liftX hiffL hiffR
    (atomsStayC_frozenL hiffL hLfv fR (Term.const 1) _) hstayR hnarrow'
  obtain ⟨hFσ, hatσ⟩ := (sat_FM_append g gs _ σ).mp hσ
  obtain ⟨hLσ, hRσ⟩ := (atomTerms_iff hiffL hiffR σ).mp hatσ
  have hcompsσ : ∀ c ∈ comps, Term.eval c σ ≤ 0 :=
    fun c hc => (sat_FM_iff g gs σ).mp hFσ c (hsub1 c hc)
  obtain ⟨hcω, hLω, hRω⟩ := hlift σ hLσ hRσ hcompsσ ω hrun
  refine (sat_FM_append g gs _ ω).mpr ⟨(sat_FM_iff g gs ω).mpr ?_,
    (atomTerms_iff hiffL hiffR ω).mpr ⟨hLω, hRω⟩⟩
  intro g' hg'
  exact hcω g' (hsub2 g' hg')

/-- The anchor of a pair passes to the entered mode's anchor at a switch point where the
entered mode's atoms hold (the rows and the left atoms are shared). -/
theorem anchor_hand {g : Term (Var n)} {gs : List (Term (Var n))} {cL cR cR' : List (CutAtomP n)}
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR) (hiffR' : AtomsIff cR') {y : State (Var n)}
    (hA : Formula.sat (FM g (gs ++ atomTerms cL cR)) y) (hR' : CutSat cR' y) :
    Formula.sat (FM g (gs ++ atomTerms cL cR')) y := by
  obtain ⟨hF, hat⟩ := (sat_FM_append g gs _ y).mp hA
  obtain ⟨hL, -⟩ := (atomTerms_iff hiffL hiffR y).mp hat
  exact (sat_FM_append g gs _ y).mpr ⟨hF, (atomTerms_iff hiffL hiffR' y).mpr ⟨hL, hR'⟩⟩

end RelCertifier
