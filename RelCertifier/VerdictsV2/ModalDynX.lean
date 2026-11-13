/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 right-only flow-certificate queries, rebuilt at the SMT-IR level, pinned

`ReplayDyn.modalVerdDynX` states, at the host level, the stratified route-A pack of one
right-only flow certificate (Definition 5, kind right-only: left mode `l`, right mode `m`, the
left frozen, the product program of Eq. (15)) exactly as
`OracleAPI.checkDynRepo` builds it. The runner rebuilds the pack at the IR level
(`modalVerdDynXQueries`, from the same `Run.*` lowerings, the emitted extended certificate and
the shared combinators) and prints it with `toScript`; `modalVerdDynX_of_queries` proves, once
for every benchmark, that the rebuilt queries denote exactly the hypothesis: if every printed
query came back `unsat`, the instance's right-only pack holds. Same discipline as
`ModalX.modalVerdX_of_queries` for the joint packs.
-/
import RelCertifier.Proofs.Encoding.ReplayDyn
import RelCertifier.VerdictsV2.ModalX

namespace RelCertifier

open DL Parse RelCertifier.Oracle

variable {n : ℕ}

/-- The right-only pack, rebuilt: per component (in the cover's right-only strata order), the
route-A query over the domain narrowed by the mode facts and the earlier rounds, with the left
guard conjoined before the first joint segment (`pre`), at every escalation level of that domain
(`sliceFlowLevels`: the slices at `k`, `k+1`, … hops, then the full domain; `k = none` the full
domain alone), as `checkDynRepo` sends them; the left field frozen, stretch 1. `none` if
anything fails to lower (the runner reports a SKIP, never a pass). -/
def modalVerdDynXQueries (k : Option ℕ) (p : PProblem) (cX : EvolStrengtheningX)
    (n invRow : ℕ) (order : List ℕ) (pre : Bool) (l m : ℕ) : Option (List (List (IForm n))) := do
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
    let g := comps.getD i (.rat 0)
    (sliceFlowLevels k g (ilieDeriv g (fun _ => .rat 0) fR (.rat 1))
      (if pre then IForm.and dom0 gL else dom0)).map (fun dom =>
        iflowQuery g (fun _ => .rat 0) fR (.rat 1) dom)))

theorem hostGuard_getD (vars : List String) (side : Side) (m : PMode) :
    hostGuard vars n side m = ((Run.lowerF vars n side m.guard).getD IForm.tt).toHost := by
  unfold hostGuard
  rcases Run.lowerF vars n side m.guard with _ | g <;> rfl

/-- **The v2 right-only pin.** If the runner's rebuild succeeds and, for every component, one
of its printed queries (one per level) is `unsat`, the instance's right-only hypothesis
`modalVerdDynX` holds. -/
theorem modalVerdDynX_of_queries {O : UnsatOracle (Var n)} {k : Option ℕ} {p : PProblem}
    {cX : EvolStrengtheningX} {invRow : ℕ} {order : List ℕ} {pre : Bool} {l m : ℕ}
    {qss : List (List (IForm n))}
    (hq : modalVerdDynXQueries k p cX n invRow order pre l m = some qss)
    (hz3 : ∀ i (hi : i < qss.length), ∃ q ∈ qss[i], O.solve q.toHost = Verdict.unsat) :
    modalVerdDynX p cX n invRow order pre l m .whole O := by
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
  show VerdDynCore _ _ _ _ _ .whole O
  unfold VerdDynCore
  rw [hD, hcompsH, hostDyn_pin hfR, hgL]
  intro i hi
  rw [List.length_map] at hi
  have hi' : i < ((List.range comps.length).map (fun i =>
      let dom0 := istrataDomHost D (comps.take i)
      let g := comps.getD i (ITerm.rat 0)
      (sliceFlowLevels k g (ilieDeriv g (fun _ => ITerm.rat 0) fR (ITerm.rat 1))
        (if pre then IForm.and dom0 gLI else dom0)).map (fun dom =>
          iflowQuery g (fun _ => ITerm.rat 0) fR (ITerm.rat 1) dom))).length := by simpa using hi
  obtain ⟨q, hqmem, hz⟩ := hz3 i hi'
  simp only [List.getElem_map, List.getElem_range, List.mem_map] at hqmem
  obtain ⟨d, hd, rfl⟩ := hqmem
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
  have h1 := OracleUnsat_iflowQuery_of_level hd hz
  rw [iflowQuery_toHost, hdom, zeroField_toHost, hone] at h1
  exact h1

/-- The pack on the pre-landing region, the domain of the restricted mode `m|¬T` with `T` the
closed landing target (Lemma 4), rebuilt: per component, a strict one (`mask`) the group
`[A]` over `D ∧ BcI`, a non-strict one the group `[A, B, C]` over `D ∧ BoI`, each narrowed by the
strata and (pre-joint) the left guard; the left field frozen, stretch 1. `none` if anything
fails to lower. -/
def modalVerdDynXQueriesPre (k : Option ℕ) (p : PProblem) (cX : EvolStrengtheningX)
    (n invRow : ℕ) (order : List ℕ) (pre : Bool) (l m : ℕ) (BoI BcI : IForm n)
    (mask : List Bool) : Option (List (List (IForm n))) := do
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
    let g := comps.getD i (.rat 0)
    let gdot := ilieDeriv g (fun _ => .rat 0) fR (.rat 1)
    let domc0 := istrataDomHost (IForm.and D BcI) (comps.take i)
    let dom0 := istrataDomHost (IForm.and D BoI) (comps.take i)
    if mask.getD i false then
      (sliceFlowLevels k g gdot (if pre then IForm.and domc0 gL else domc0)).map (fun domc =>
        iflowQuery g (fun _ => .rat 0) fR (.rat 1) domc)
    else
      (sliceFlowLevels k g gdot (if pre then IForm.and dom0 gL else dom0)).flatMap (fun dom =>
        [iflowQuery g (fun _ => .rat 0) fR (.rat 1) dom,
         iflowQueryStrict g (fun _ => .rat 0) fR (.rat 1) dom,
         iflowQuerySuperlevel g (fun _ => .rat 0) fR (.rat 1) dom])))

/-- **The pin on the pre-landing region** (the restricted mode of Lemma 4). If the rebuild succeeds and every group has an
`unsat` member, the instance's hypothesis `modalVerdDynX` holds on the region (at the host forms
of `BoI`, `BcI`). -/
theorem modalVerdDynX_of_queriesPre {O : UnsatOracle (Var n)} {k : Option ℕ} {p : PProblem}
    {cX : EvolStrengtheningX} {invRow : ℕ} {order : List ℕ} {pre : Bool} {l m : ℕ}
    {BoI BcI : IForm n} {mask : List Bool} {qss : List (List (IForm n))}
    (hq : modalVerdDynXQueriesPre k p cX n invRow order pre l m BoI BcI mask = some qss)
    (hz3 : ∀ i (hi : i < qss.length), ∃ q ∈ qss[i], O.solve q.toHost = Verdict.unsat)
    (hmono : ∀ x, Formula.sat BoI.toHost x → Formula.sat BcI.toHost x)
    (hclosed : ∀ (f : ℝ → State (Var n)) (T : ℝ), 0 < T → ContinuousOn f (Set.Icc 0 T) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, Formula.sat BoI.toHost (f t)) → Formula.sat BcI.toHost (f T)) :
    modalVerdDynX p cX n invRow order pre l m (.pre BoI.toHost BcI.toHost mask hmono hclosed) O := by
  unfold modalVerdDynXQueriesPre at hq
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
  show VerdDynCore _ _ _ _ _ (DynRegion.pre BoI.toHost BcI.toHost mask hmono hclosed) O
  unfold VerdDynCore
  rw [hD, hcompsH, hostDyn_pin hfR, hgL]
  intro i hi
  rw [List.length_map] at hi
  have hi' : i < ((List.range comps.length).map (fun i =>
      let g := comps.getD i (.rat 0)
      let gdot := ilieDeriv g (fun _ => .rat 0) fR (.rat 1)
      let domc0 := istrataDomHost (IForm.and D BcI) (comps.take i)
      let dom0 := istrataDomHost (IForm.and D BoI) (comps.take i)
      if mask.getD i false then
        (sliceFlowLevels k g gdot (if pre then IForm.and domc0 gLI else domc0)).map (fun domc =>
          iflowQuery g (fun _ => .rat 0) fR (.rat 1) domc)
      else
        (sliceFlowLevels k g gdot (if pre then IForm.and dom0 gLI else dom0)).flatMap (fun dom =>
          [iflowQuery g (fun _ => .rat 0) fR (.rat 1) dom,
           iflowQueryStrict g (fun _ => .rat 0) fR (.rat 1) dom,
           iflowQuerySuperlevel g (fun _ => .rat 0) fR (.rat 1) dom]))).length := by
    simpa using hi
  obtain ⟨q, hqmem, hqz⟩ := hz3 i hi'
  simp only [List.getElem_map, List.getElem_range] at hqmem
  have hgi : (comps.map ITerm.toHost)[i]'(by simpa using hi)
      = (comps.getD i (ITerm.rat 0)).toHost := by
    rw [List.getElem_map, List.getD_eq_getElem _ _ hi]
  have htk : (comps.map ITerm.toHost).take i = (comps.take i).map ITerm.toHost := by
    rw [List.map_take]
  have hone : (ITerm.rat 1 : ITerm n).toHost = Term.const 1 := by
    show Term.const ((1:ℚ):ℝ) = Term.const 1
    norm_num
  have hdomB : ∀ B : IForm n, (if pre then IForm.and (istrataDomHost (IForm.and D B) (comps.take i)) gLI
      else istrataDomHost (IForm.and D B) (comps.take i)).toHost
      = dynDomHost pre (Formula.and D.toHost B.toHost) gLI.toHost
          ((comps.take i).map ITerm.toHost) := by
    intro B
    unfold dynDomHost
    cases pre <;> simp [IForm.toHost, istrataDomHost_toHost]
  rw [hgi, htk]
  split_ifs with hm
  · simp only [hm, if_true, List.mem_map] at hqmem
    obtain ⟨d, hd, rfl⟩ := hqmem
    have h1 := OracleUnsat_iflowQuery_of_level hd hqz
    rw [iflowQuery_toHost, hdomB, zeroField_toHost, hone] at h1
    exact h1
  · simp only [hm, Bool.false_eq_true, if_false, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hqmem
    obtain ⟨d, hd, hqmem⟩ := hqmem
    rcases hqmem with rfl | rfl | rfl
    · left
      have h1 := OracleUnsat_iflowQuery_of_level hd hqz
      rw [iflowQuery_toHost, hdomB, zeroField_toHost, hone] at h1
      exact h1
    · right; left
      have h1 := OracleUnsat_iflowQueryStrict_of_level hd hqz
      rw [iflowQueryStrict_toHost, hdomB, zeroField_toHost, hone] at h1
      exact h1
    · right; right
      have h1 := OracleUnsat_iflowQuerySuperlevel_of_level hd hqz
      rw [iflowQuerySuperlevel_toHost, hdomB, zeroField_toHost, hone] at h1
      exact h1

/-- **The right-only pack's query groups, on a region** (`none`: the whole domain, the route-A
query of each component alone, `modalVerdDynXQueries`; `some (BoI, BcI, mask)`: the
pre-landing region, `modalVerdDynXQueriesPre`). The bridge's `dynGroups` sends exactly these. -/
def modalVerdDynXGroups (k : Option ℕ) (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (pre : Bool) (l m : ℕ) (rg : Option (IForm n × IForm n × List Bool)) :
    Option (List (List (IForm n))) :=
  match rg with
  | none => modalVerdDynXQueries k p cX n invRow order pre l m
  | some (BoI, BcI, mask) => modalVerdDynXQueriesPre k p cX n invRow order pre l m BoI BcI mask

end RelCertifier
