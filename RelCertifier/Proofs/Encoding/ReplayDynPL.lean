/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The PRE-LANDING reposition verdict pack (opt-in `prelanding = true`), stated and consumed

`ReplayDyn.lean` states the whole-domain right-only pack (`VerdDynCore`, route A only) that
`OracleAPI.checkDynRepo` checks. Under the opt-in key the tool checks instead
`OracleAPI.checkDynRepoPL`: the same stratified pack with the base domain narrowed by a region
`B` (the half-open region before the progress certificate's last threshold), and any of the
three routes A, B, C per component. This file states that pack (`VerdDynCorePL`,
`modalVerdDynPLX`) and turns it into a box invariant of the frozen-left right flow ON THE
NARROWED DOMAIN (`couple_box_dynPL`): along every frozen-left run of `q` that stays in `B` (its
end point included), from a state satisfying the rows and both sides' kept atoms (and the left
guard, before the first joint segment), the rows and the atoms hold at the end. The half-open
extension (a run that is in `B` only before its last instant) is `Emitted/Prelanding.lean`'s
(continuity of the row and atom terms).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.ReplayDyn

namespace RelCertifier

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-- **The stratified three-route pre-landing pack.** Per component (in the node's strata
order), one of the route queries A (`dom ∧ ġ > 0`), B (`dom ∧ g = 0 ∧ ġ ≥ 0`), C
(`dom ∧ g ≥ 0 ∧ ġ > 0`) is `UNSAT`, the left frozen (`fL = 0`) at stretch 1, over the domain
`D ∧ B` narrowed by the proven strata and (pre-joint) the left guard. -/
def VerdDynCorePL (pre : Bool) (comps : List (Term (Var n))) (fR : Fin n → Term (Var n))
    (D gL B : Formula (Var n)) : Prop :=
  ∀ i (hi : i < comps.length),
    z3solve (flowQuery ⟨comps[i], fun _ => Term.const 0, fR, Term.const 1,
      dynDomHost pre (Formula.and D B) gL (comps.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨comps[i], fun _ => Term.const 0, fR, Term.const 1,
      dynDomHost pre (Formula.and D B) gL (comps.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨comps[i], fun _ => Term.const 0, fR, Term.const 1,
      dynDomHost pre (Formula.and D B) gL (comps.take i)⟩) = Verdict.unsat

/-- **The suite_v2 pre-landing pack, read off the IR and the extended certificate**
(`modalVerdDynX` with the region `B` and the three routes): exactly the queries
`OracleAPI.checkDynRepoPL` sends. -/
noncomputable def modalVerdDynPLX (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (pre : Bool) (l m : ℕ) (B : Formula (Var n)) : Prop :=
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let comps0 := hostComps vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let comps := order.map (fun i => comps0.getD i (Term.const 0))
  let base := Formula.and (hostEvolve vars n Side.L mL) (hostEvolve vars n Side.R mR)
  let cL := cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)
  let cR := cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)
  VerdDynCorePL pre comps (hostDyn vars n Side.R mR) (domCutX base cL cR)
    (hostGuard vars n Side.L mL) B

/-- The pre-landing pack gives simultaneous preservation of the components along the
frozen-left right flow, on the base domain narrowed by `B`. -/
theorem segPresAll_dynPL (pre : Bool) (comps : List (Term (Var n))) (fR : Fin n → Term (Var n))
    (D gL B : Formula (Var n)) (hv : VerdDynCorePL pre comps fR D gL B) :
    SegPreservesAllOn comps (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (dynBase pre (Formula.and D B) gL) := by
  intro ν hinit
  refine stratified_barrier_boxle _ (dynBase pre (Formula.and D B) gL) comps ?_ hinit
  intro i hi ν' hν'
  have hcong : ∀ x, Formula.sat (Formula.and (dynBase pre (Formula.and D B) gL)
      (bigLe (comps.take i))) x ↔
      Formula.sat (dynDomHost pre (Formula.and D B) gL (comps.take i)) x :=
    fun x => (sat_dynDomHost pre (Formula.and D B) gL _ x).symm
  refine boxle_dom_congr hcong ?_
  rcases hv i hi with h | h | h
  · exact flow_cert_sound _ (z3_unsat_sound h) hν'
  · exact flow_cert_sound_strict _ (z3_unsat_sound h) hν'
  · exact flow_cert_sound_superlevel _ (z3_unsat_sound h) hν'

/-- **The anchor is a box invariant of the frozen-left right flow ON THE PRE-LANDING DOMAIN.**
`couple_box_dyn` with the run's domain narrowed by `B` (a right-only formula; its end point
included) and the pre-landing pack. -/
theorem couple_box_dynPL (pre : Bool) (g : Term (Var n)) (gs comps : List (Term (Var n)))
    (cL cR : List (CutAtomP n)) (fR : Fin n → Term (Var n)) (domL domR gL B : Formula (Var n))
    (hsub1 : ∀ c ∈ comps, c ∈ g :: gs) (hsub2 : ∀ g' ∈ g :: gs, g' ∈ comps)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR) (hLfv : ∀ a ∈ cL, a.2.fv ⊆ range Lv)
    (hgL : gL.fv ⊆ range Lv)
    (hstayR : AtomsStayC cR (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (dynBase pre (Formula.and domL (Formula.and domR B)) gL))
    (hverd : VerdDynCorePL pre comps fR (domCutX (Formula.and domL domR) cL cR) gL B) :
    ∀ σ ω, Formula.sat (FM g (gs ++ atomTerms cL cR)) σ → (pre = true → Formula.sat gL σ) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
        (Formula.and domL (Formula.and domR B))) σ ω →
      Formula.sat (FM g (gs ++ atomTerms cL cR)) ω := by
  intro σ ω hσ hgσ hω
  set sys := jointSys (fun _ => Term.const 0) fR (Term.const 1) with hsys
  have hrun : Program.sem (Program.ode sys
      (dynBase pre (Formula.and domL (Formula.and domR B)) gL)) σ ω := by
    unfold dynBase
    cases pre with
    | false => simpa using hω
    | true => simpa using frozen_run_narrow hgL hω (hgσ rfl)
  have hnarrow : SegPreservesAllOn comps sys
      (dynBase pre (Formula.and (domCutX (Formula.and domL domR) cL cR) B) gL) :=
    segPresAll_dynPL pre comps fR _ gL B hverd
  have hnarrow' : SegPreservesAllOn comps sys
      (Formula.and (dynBase pre (Formula.and domL (Formula.and domR B)) gL)
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

end RelCertifier
