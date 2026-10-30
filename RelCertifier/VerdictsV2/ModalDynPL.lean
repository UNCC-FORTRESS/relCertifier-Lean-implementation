/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The pre-landing reposition verdict queries, rebuilt at the SMT-IR level, pinned

`ReplayDynPL.modalVerdDynPLX` states, at the host level, the stratified three-route pack of one
PRE-LANDING reposition (opt-in `prelanding = true`, `docs/PRELANDING.md`) exactly as
`OracleAPI.checkDynRepoPL` builds it. The runner rebuilds the pack at the IR level
(`modalVerdDynPLXQueries`: per component one group of the three route queries, over the
cut-narrowed domain conjoined with the region `BI`, narrowed by the strata and, pre-joint, the
left guard), and `modalVerdDynPLX_of_queries` proves once for every benchmark that a group with
an `unsat` member per component is the hypothesis. Same discipline as `ModalDynX` (route A) and
`ModalX` (three routes).
-/
import RelCertifier.Proofs.Encoding.ReplayDynPL
import RelCertifier.VerdictsV2.ModalDynX

namespace RelCertifier

open DL Parse RelCertifier.Oracle

variable {n : ℕ}

/-- The pre-landing pack, rebuilt: per component one group `[A, B, C]` of route queries over
`D ∧ BI` narrowed by the strata and (pre-joint) the left guard; the left field frozen,
stretch 1. `none` if anything fails to lower. -/
def modalVerdDynPLXQueries (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (pre : Bool) (l m : ℕ) (BI : IForm n) : Option (List (List (IForm n))) := do
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
    let dom0 := istrataDomHost (IForm.and D BI) (comps.take i)
    let dom := if pre then IForm.and dom0 gL else dom0
    let g := comps.getD i (.rat 0)
    [iflowQuery g (fun _ => .rat 0) fR (.rat 1) dom,
     iflowQueryStrict g (fun _ => .rat 0) fR (.rat 1) dom,
     iflowQuerySuperlevel g (fun _ => .rat 0) fR (.rat 1) dom]))

/-- **The pre-landing pin.** If the runner's rebuild succeeds and every group has an `unsat`
member, the instance's pre-landing hypothesis `modalVerdDynPLX` holds (at the host form of the
region). -/
theorem modalVerdDynPLX_of_queries {p : PProblem} {cX : EvolStrengtheningX} {invRow : ℕ}
    {order : List ℕ} {pre : Bool} {l m : ℕ} {BI : IForm n} {qss : List (List (IForm n))}
    (hq : modalVerdDynPLXQueries p cX n invRow order pre l m BI = some qss)
    (hz3 : ∀ i (hi : i < qss.length), ∃ q ∈ qss[i], z3solve q.toHost = Verdict.unsat) :
    modalVerdDynPLX p cX n invRow order pre l m BI.toHost := by
  unfold modalVerdDynPLXQueries at hq
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
  show VerdDynCorePL _ _ _ _ _ _
  unfold VerdDynCorePL
  rw [hD, hcompsH, hostDyn_pin hfR, hgL]
  intro i hi
  rw [List.length_map] at hi
  have hi' : i < ((List.range comps.length).map (fun i =>
      [iflowQuery (comps.getD i (ITerm.rat 0)) (fun _ => ITerm.rat 0) fR (ITerm.rat 1)
        (if pre then IForm.and (istrataDomHost (IForm.and D BI) (comps.take i)) gLI
         else istrataDomHost (IForm.and D BI) (comps.take i)),
       iflowQueryStrict (comps.getD i (ITerm.rat 0)) (fun _ => ITerm.rat 0) fR (ITerm.rat 1)
        (if pre then IForm.and (istrataDomHost (IForm.and D BI) (comps.take i)) gLI
         else istrataDomHost (IForm.and D BI) (comps.take i)),
       iflowQuerySuperlevel (comps.getD i (ITerm.rat 0)) (fun _ => ITerm.rat 0) fR (ITerm.rat 1)
        (if pre then IForm.and (istrataDomHost (IForm.and D BI) (comps.take i)) gLI
         else istrataDomHost (IForm.and D BI) (comps.take i))])).length := by simpa using hi
  obtain ⟨q, hqmem, hqz⟩ := hz3 i hi'
  simp only [List.getElem_map, List.getElem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hqmem
  have hgi : (comps.map ITerm.toHost)[i]'(by simpa using hi)
      = (comps.getD i (ITerm.rat 0)).toHost := by
    rw [List.getElem_map, List.getD_eq_getElem _ _ hi]
  have htk : (comps.map ITerm.toHost).take i = (comps.take i).map ITerm.toHost := by
    rw [List.map_take]
  have hone : (ITerm.rat 1 : ITerm n).toHost = Term.const 1 := by
    show Term.const ((1:ℚ):ℝ) = Term.const 1
    norm_num
  have hdom : (if pre then IForm.and (istrataDomHost (IForm.and D BI) (comps.take i)) gLI
      else istrataDomHost (IForm.and D BI) (comps.take i)).toHost
      = dynDomHost pre (Formula.and D.toHost BI.toHost) gLI.toHost
          ((comps.take i).map ITerm.toHost) := by
    unfold dynDomHost
    cases pre <;> simp [IForm.toHost, istrataDomHost_toHost]
  rw [hgi, htk]
  rcases hqmem with rfl | rfl | rfl
  · left
    rw [iflowQuery_toHost, hdom, zeroField_toHost, hone] at hqz
    exact hqz
  · right; left
    rw [iflowQueryStrict_toHost, hdom, zeroField_toHost, hone] at hqz
    exact hqz
  · right; right
    rw [iflowQuerySuperlevel_toHost, hdom, zeroField_toHost, hone] at hqz
    exact hqz

end RelCertifier
