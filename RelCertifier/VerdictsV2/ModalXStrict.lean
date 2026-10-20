/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The modal verdict queries at strict rows, rebuilt at the SMT-IR level, pinned
(extension `strict-atoms`)

`modalVerdXQueriesS` is `modalVerdXQueries` with the row's strictness mask
(`Oracle.invStrictFlags`, in the cover's strata order): a strict component's group is
[route A, route B] (route C does not preserve `< 0`), every other group is the existing
[A, B, C]. Each printed query is the existing string for that component (same component,
same fields, same closure-narrowed domain). `modalVerdXS_of_queries` pins the rebuilt
queries to `modalVerdXS`; `modalVerdXQueriesS_eq_of_allFalse`: without strict atoms the
groups are the existing ones.

New leaf; no upstream edits.
-/
import RelCertifier.VerdictsV2.ModalX
import RelCertifier.Proofs.Encoding.StrictCouple

namespace RelCertifier

open DL Parse RelCertifier.Oracle

variable {n : ℕ}

/-- The flagged pack, rebuilt: per component (strata order), [A, B] if strict, else [A, B, C]. -/
def modalVerdXQueriesS (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (lam : ℚ) (l m : ℕ) : Option (List (List (IForm n))) := do
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let comps0 ← Oracle.invComponents vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let fs ← Oracle.invStrictFlags vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let comps := order.map (fun i => comps0.getD i (.rat 0))
  let flags := order.map (fun i => fs.getD i false)
  let fL ← Run.dynOf vars n Side.L mL
  let fR ← Run.dynOf vars n Side.R mR
  let evL ← Run.lowerF vars n Side.L mL.evolve
  let evR ← Run.lowerF vars n Side.R mR.evolve
  let aL ← ((cutAtomsOfX cX.L mL.name).map (·.atom)).mapM (Run.lowerF vars n Side.L)
  let aR ← ((cutAtomsOfX cX.R mR.name).map (·.atom)).mapM (Run.lowerF vars n Side.R)
  let base := IForm.and evL evR
  let b1 := if aL.isEmpty then base else IForm.and base (icutF aL)
  let D := if aR.isEmpty then b1 else IForm.and b1 (icutF aR)
  pure ((List.range comps.length).map (fun i =>
    let g := comps.getD i (.rat 0)
    let dom := istrataDomHost D (comps.take i)
    if flags.getD i false then
      [iflowQuery g fL fR (.rat lam) dom, iflowQueryStrict g fL fR (.rat lam) dom]
    else
      [iflowQuery g fL fR (.rat lam) dom, iflowQueryStrict g fL fR (.rat lam) dom,
       iflowQuerySuperlevel g fL fR (.rat lam) dom]))

/-- The flag of a tagged component, read by index (the mask no longer than the list). -/
theorem tagS_getD_fst (cs : List (Term (Var n))) (m : List Bool) (hm : m.length ≤ cs.length)
    (j : ℕ) (d : Term (Var n)) : ((tagS cs m).getD j (false, d)).1 = m.getD j false := by
  induction cs generalizing m j with
  | nil =>
      have : m = [] := List.eq_nil_of_length_eq_zero (by simpa using hm)
      subst this; simp
  | cons c cs ih =>
      cases j with
      | zero => cases m <;> simp
      | succ j =>
          have hm' : m.tail.length ≤ cs.length := by simp at hm ⊢; omega
          have := ih m.tail hm' j
          cases m <;> simp_all

theorem getD_map_toHost (comps0 : List (ITerm n)) (j : ℕ) :
    (comps0.map ITerm.toHost).getD j (Term.const 0) = (comps0.getD j (ITerm.rat 0)).toHost := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases comps0[j]? with _ | c
  · simp [ITerm.toHost]
  · rfl

/-- The IR groups of a flagged pack denote `StrataVerdS` over the ordered flagged components. -/
theorem strataVerdS_of_IR (comps0 : List (ITerm n)) (fs : List Bool)
    (hfsl : fs.length ≤ comps0.length) (order : List ℕ) (fL fR : Fin n → ITerm n) (lam : ℚ)
    (D : IForm n)
    (hz3 : ∀ i (hi : i < ((List.range (order.map (fun i => comps0.getD i (ITerm.rat 0))).length).map
      (fun i => if (order.map (fun i => fs.getD i false)).getD i false then
          [iflowQuery ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i)),
           iflowQueryStrict ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i))]
        else
          [iflowQuery ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i)),
           iflowQueryStrict ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i)),
           iflowQuerySuperlevel ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0))
            fL fR (ITerm.rat lam)
            (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i))])).length),
      ∃ q ∈ ((List.range (order.map (fun i => comps0.getD i (ITerm.rat 0))).length).map
      (fun i => if (order.map (fun i => fs.getD i false)).getD i false then
          [iflowQuery ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i)),
           iflowQueryStrict ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i))]
        else
          [iflowQuery ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i)),
           iflowQueryStrict ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)) fL fR
            (ITerm.rat lam) (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i)),
           iflowQuerySuperlevel ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0))
            fL fR (ITerm.rat lam)
            (istrataDomHost D ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i))]))[i],
        z3solve q.toHost = Verdict.unsat) :
    StrataVerdS (fun i => (fL i).toHost) (fun i => (fR i).toHost) (Term.const (lam : ℝ)) D.toHost
      (orderTag (comps0.map ITerm.toHost) fs order) := by
  intro i hi
  have hio : i < order.length := by simpa [orderTag] using hi
  obtain ⟨q, hqmem, hqz⟩ := hz3 i (by simpa using hio)
  simp only [List.getElem_map, List.getElem_range] at hqmem
  have hA : (orderTag (comps0.map ITerm.toHost) fs order)[i].2
      = ((order.map (fun i => comps0.getD i (ITerm.rat 0))).getD i (ITerm.rat 0)).toHost := by
    simp only [orderTag, List.getElem_map]
    rw [tagS_getD_snd, getD_map_toHost,
      List.getD_eq_getElem (order.map (fun i => comps0.getD i (ITerm.rat 0))) (ITerm.rat 0)
        (by simpa using hio), List.getElem_map]
  have hB : ((orderTag (comps0.map ITerm.toHost) fs order).take i).map Prod.snd
      = ((order.map (fun i => comps0.getD i (ITerm.rat 0))).take i).map ITerm.toHost := by
    rw [List.map_take, orderTag_map_snd, List.map_take, List.map_map]
    congr 1
    exact List.map_congr_left (fun j _ => getD_map_toHost comps0 j)
  have hC : (orderTag (comps0.map ITerm.toHost) fs order)[i].1
      = (order.map (fun i => fs.getD i false)).getD i false := by
    simp only [orderTag, List.getElem_map]
    rw [tagS_getD_fst _ _ (by simpa using hfsl),
      List.getD_eq_getElem (order.map (fun i => fs.getD i false)) false
        (by simpa using hio), List.getElem_map]
  have hlam : (ITerm.rat lam : ITerm n).toHost = Term.const (lam : ℝ) := rfl
  unfold strataObS
  rw [hA, hB]
  rcases hb : (order.map (fun i => fs.getD i false)).getD i false with _ | _
  · rw [hb] at hqmem
    simp only [Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil, or_false] at hqmem
    rcases hqmem with rfl | rfl | rfl
    · left
      rw [imodalQuery_toHost, hlam] at hqz; exact hqz
    · right; left
      rw [imodalQueryStrict_toHost, hlam] at hqz; exact hqz
    · right; right
      refine ⟨by rw [hC, hb], ?_⟩
      rw [imodalQuerySuperlevel_toHost, hlam] at hqz; exact hqz
  · rw [hb] at hqmem
    simp only [if_true, List.mem_cons, List.not_mem_nil, or_false] at hqmem
    rcases hqmem with rfl | rfl
    · left
      rw [imodalQuery_toHost, hlam] at hqz; exact hqz
    · right; left
      rw [imodalQueryStrict_toHost, hlam] at hqz; exact hqz

/-- **The strict pin.** If the rebuild succeeds and every group has an `unsat` member, the
instance's hypothesis `modalVerdXS` holds. -/
theorem modalVerdXS_of_queries {p : PProblem} {cX : EvolStrengtheningX} {invRow : ℕ}
    {order : List ℕ} {lam : ℚ} {l m : ℕ} {qss : List (List (IForm n))}
    (hq : modalVerdXQueriesS p cX n invRow order lam l m = some qss)
    (hz3 : ∀ i (hi : i < qss.length), ∃ q ∈ qss[i], z3solve q.toHost = Verdict.unsat) :
    modalVerdXS p cX n invRow order (lam : ℝ) l m := by
  unfold modalVerdXQueriesS at hq
  simp only [Option.bind_eq_bind] at hq
  set vars := p.L.stateVars
  set mL := p.L.modes.getD l ⟨"", [], .tt, .tt, []⟩
  set mR := p.R.modes.getD m ⟨"", [], .tt, .tt, []⟩
  rcases hc : Oracle.invComponents vars n (p.invariants.getD invRow ("", PForm.tt)).2
    with _ | comps0 <;> rw [hc] at hq
  · simp at hq
  rcases hfs : Oracle.invStrictFlags vars n (p.invariants.getD invRow ("", PForm.tt)).2
    with _ | fs <;> rw [Option.bind_some, hfs] at hq
  · simp at hq
  rcases hfL : Run.dynOf vars n Side.L mL with _ | fL <;> rw [Option.bind_some, hfL] at hq
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
  -- the host-level pieces, pinned
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
  have hfsl : fs.length = comps0.length := by
    obtain ⟨fs', hfs', hl'⟩ := Oracle.invStrictFlags_length vars n _ comps0 hc
    rw [hfs] at hfs'; cases hfs'; exact hl'
  show VerdXCoreS _ _ _ _ _
  rw [hcomps, hfs, Option.getD_some, hD, hostDyn_pin hfL, hostDyn_pin hfR]
  exact strataVerdS_of_IR comps0 fs hfsl.le order fL fR lam D hz3

/-- **Collapse**: a row without strict atoms gives the existing groups, query for query. -/
theorem modalVerdXQueriesS_eq_of_allFalse (p : PProblem) (cX : EvolStrengtheningX)
    (n invRow : ℕ) (order : List ℕ) (lam : ℚ) (l m : ℕ)
    (h : ∀ fs, Oracle.invStrictFlags p.L.stateVars n (p.invariants.getD invRow ("", PForm.tt)).2
      = some fs → ∀ b ∈ fs, b = false) :
    modalVerdXQueriesS p cX n invRow order lam l m = modalVerdXQueries p cX n invRow order lam l m := by
  unfold modalVerdXQueriesS modalVerdXQueries
  dsimp only
  rcases hc : Oracle.invComponents p.L.stateVars n (p.invariants.getD invRow ("", PForm.tt)).2
    with _ | comps0
  · simp
  obtain ⟨fs, hfs, -⟩ := Oracle.invStrictFlags_length _ n _ comps0 hc
  have hf0 : ∀ j, fs.getD j false = false := by
    intro j
    rw [List.getD_eq_getElem?_getD]
    rcases hj : fs[j]? with _ | b
    · rfl
    · exact h fs hfs b (List.mem_of_getElem? hj)
  have hf : ∀ i, (order.map (fun i => fs.getD i false)).getD i false = false := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases order[i]? with _ | j
    · rfl
    · exact hf0 j
  simp only [hfs, hf, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, if_false]

end RelCertifier
