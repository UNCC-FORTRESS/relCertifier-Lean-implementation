/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 reposition verdict queries, rebuilt at the SMT-IR level, pinned

`ReplayDyn.modalVerdDynX` states, at the host level, the stratified route-A pack of one
dynamic reposition (left mode `l`, right mode `m`, the left frozen) exactly as
`OracleAPI.checkDynRepo` builds it. The runner rebuilds the pack at the IR level
(`modalVerdDynXQueries`, from the same `Run.*` lowerings, the emitted extended certificate and
the shared combinators) and prints it with `toScript`; `modalVerdDynX_of_queries` proves, once
for every benchmark, that the rebuilt queries denote exactly the hypothesis: if every printed
query came back `unsat`, the instance's reposition pack holds. Same discipline as
`ModalX.modalVerdX_of_queries` for the joint packs.
-/
import RelCertifier.Proofs.Encoding.ReplayDyn
import RelCertifier.VerdictsV2.ModalX

namespace RelCertifier

open DL Parse RelCertifier.Oracle

variable {n : ℕ}

/-- The reposition pack, rebuilt: per component (in the cover's reposition strata order), the
route-A query over the cut-narrowed, strata-narrowed domain, with the left guard conjoined
before the first joint segment (`pre`); the left field frozen, stretch 1. `none` if anything
fails to lower (the runner reports a SKIP, never a pass). -/
def modalVerdDynXQueries (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (pre : Bool) (l m : ℕ) : Option (List (IForm n)) := do
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let comps0 ← Oracle.invComponents vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let comps := order.map (fun i => comps0.getD i (.rat 0))
  let fR ← Run.dynOf vars n Side.R mR
  let evL ← Run.lowerF vars n Side.L mL.evolve
  let evR ← Run.lowerF vars n Side.R mR.evolve
  let aL ← ((cutAtomsOfX cX.L mL.name).map (·.atom)).mapM (Run.lowerF vars n Side.L)
  let aR ← ((cutAtomsOfX cX.R mR.name).map (·.atom)).mapM (Run.lowerF vars n Side.R)
  let gL := (Run.lowerF vars n Side.L mL.guard).getD IForm.tt
  let base := IForm.and evL evR
  let b1 := if aL.isEmpty then base else IForm.and base (icutF aL)
  let D := if aR.isEmpty then b1 else IForm.and b1 (icutF aR)
  pure ((List.range comps.length).map (fun i =>
    let dom0 := istrataDomHost D (comps.take i)
    iflowQuery (comps.getD i (.rat 0)) (fun _ => .rat 0) fR (.rat 1)
      (if pre then IForm.and dom0 gL else dom0)))

theorem hostGuard_getD (vars : List String) (side : Side) (m : PMode) :
    hostGuard vars n side m = ((Run.lowerF vars n side m.guard).getD IForm.tt).toHost := by
  unfold hostGuard
  rcases Run.lowerF vars n side m.guard with _ | g <;> rfl

/-- **The v2 reposition pin.** If the runner's rebuild succeeds and every printed query is
`unsat`, the instance's reposition hypothesis `modalVerdDynX` holds. -/
theorem modalVerdDynX_of_queries {p : PProblem} {cX : EvolStrengtheningX} {invRow : ℕ}
    {order : List ℕ} {pre : Bool} {l m : ℕ} {qs : List (IForm n)}
    (hq : modalVerdDynXQueries p cX n invRow order pre l m = some qs)
    (hz3 : ∀ i (hi : i < qs.length), z3solve (qs[i]).toHost = Verdict.unsat) :
    modalVerdDynX p cX n invRow order pre l m := by
  unfold modalVerdDynXQueries at hq
  simp only [Option.bind_eq_bind] at hq
  set vars := p.L.stateVars
  set mL := p.L.modes.getD l ⟨"", [], .tt, .tt, []⟩
  set mR := p.R.modes.getD m ⟨"", [], .tt, .tt, []⟩
  rcases hc : Oracle.invComponents vars n (p.invariants.getD invRow ("", PForm.tt)).2
    with _ | comps0 <;> rw [hc] at hq
  · simp at hq
  rcases hfR : Run.dynOf vars n Side.R mR with _ | fR <;> rw [Option.bind_some, hfR] at hq
  · simp at hq
  rcases heL : Run.lowerF vars n Side.L mL.evolve with _ | evL <;>
    rw [Option.bind_some, heL] at hq
  · simp at hq
  rcases heR : Run.lowerF vars n Side.R mR.evolve with _ | evR <;>
    rw [Option.bind_some, heR] at hq
  · simp at hq
  rcases haL : ((cutAtomsOfX cX.L mL.name).map (·.atom)).mapM (Run.lowerF vars n Side.L)
    with _ | aL <;> rw [Option.bind_some, haL] at hq
  · simp at hq
  rcases haR : ((cutAtomsOfX cX.R mR.name).map (·.atom)).mapM (Run.lowerF vars n Side.R)
    with _ | aR <;> rw [Option.bind_some, haR] at hq
  · simp at hq
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hq
  subst hq
  have hcomps : hostComps vars n (p.invariants.getD invRow ("", PForm.tt)).2
      = comps0.map ITerm.toHost := hostComps_pin hc
  have hgetD : ∀ i, (comps0.map ITerm.toHost).getD i (Term.const 0)
      = (comps0.getD i (ITerm.rat 0)).toHost := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases comps0[i]? with _ | c
    · simp [ITerm.toHost]
    · rfl
  have hcL : cutF (cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)) = (icutF aL).toHost := by
    rw [cutFold_pin _ aL haL]
    simp [cutPairsX, List.map_map, Function.comp_def]
  have hcR : cutF (cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)) = (icutF aR).toHost := by
    rw [cutFold_pin _ aR haR]
    simp [cutPairsX, List.map_map, Function.comp_def]
  have hlenL : (cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)).isEmpty = aL.isEmpty := by
    have hl := mapM_length haL
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff, ← List.length_eq_zero_iff,
      ← List.length_eq_zero_iff]
    simp only [cutPairsX, List.length_map] at hl ⊢
    omega
  have hlenR : (cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)).isEmpty = aR.isEmpty := by
    have hl := mapM_length haR
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff, ← List.length_eq_zero_iff,
      ← List.length_eq_zero_iff]
    simp only [cutPairsX, List.length_map] at hl ⊢
    omega
  set base := IForm.and evL evR
  set b1 := if aL.isEmpty then base else IForm.and base (icutF aL)
  set D := if aR.isEmpty then b1 else IForm.and b1 (icutF aR)
  have hD : domCutX (Formula.and (hostEvolve vars n Side.L mL) (hostEvolve vars n Side.R mR))
      (cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name))
      (cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)) = D.toHost := by
    unfold domCutX
    rw [hostEvolve_pin heL, hostEvolve_pin heR, hlenL, hlenR, hcL, hcR]
    simp only [D, b1, base]
    by_cases h1 : aL.isEmpty <;> by_cases h2 : aR.isEmpty <;> simp [h1, h2, IForm.toHost]
  set comps := order.map (fun i => comps0.getD i (ITerm.rat 0))
  have hcompsH : order.map (fun i => (hostComps vars n
      (p.invariants.getD invRow ("", PForm.tt)).2).getD i (Term.const 0))
      = comps.map ITerm.toHost := by
    rw [hcomps]
    simp only [comps, List.map_map, Function.comp_def, hgetD]
  set gLI := (Run.lowerF vars n Side.L mL.guard).getD IForm.tt
  have hgL : hostGuard vars n Side.L mL = gLI.toHost := hostGuard_getD vars Side.L mL
  show VerdDynCore _ _ _ _ _
  unfold VerdDynCore
  rw [hD, hcompsH, hostDyn_pin hfR, hgL]
  intro i hi
  rw [List.length_map] at hi
  have hi' : i < ((List.range comps.length).map (fun i =>
      iflowQuery (comps.getD i (ITerm.rat 0)) (fun _ => ITerm.rat 0) fR (ITerm.rat 1)
        (if pre then IForm.and (istrataDomHost D (comps.take i)) gLI
         else istrataDomHost D (comps.take i)))).length := by simpa using hi
  have hz := hz3 i hi'
  simp only [List.getElem_map, List.getElem_range] at hz
  have hgi : (comps.map ITerm.toHost)[i]'(by simpa using hi)
      = (comps.getD i (ITerm.rat 0)).toHost := by
    rw [List.getElem_map, List.getD_eq_getElem _ _ hi]
  have htk : (comps.map ITerm.toHost).take i = (comps.take i).map ITerm.toHost := by
    rw [List.map_take]
  have hone : (ITerm.rat 1 : ITerm n).toHost = Term.const 1 := by
    show Term.const ((1:ℚ):ℝ) = Term.const 1
    norm_num
  rw [hgi, htk]
  have hdom : (if pre then IForm.and (istrataDomHost D (comps.take i)) gLI
      else istrataDomHost D (comps.take i)).toHost
      = dynDomHost pre D.toHost gLI.toHost ((comps.take i).map ITerm.toHost) := by
    unfold dynDomHost
    cases pre <;> simp [IForm.toHost, istrataDomHost_toHost]
  rw [iflowQuery_toHost, hdom, zeroField_toHost, hone] at hz
  exact hz

end RelCertifier
