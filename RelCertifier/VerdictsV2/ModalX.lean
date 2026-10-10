/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 modal verdict queries, rebuilt at the SMT-IR level, pinned

`CutRespond.modalVerdX` states, at the host level, the narrowed stratified verdict pack
of one pairing exactly as the tool's `checkSeg` builds it. A runner can only send text,
so it rebuilds the pack at the IR level (`modalVerdXQueries`, from the same `Run.*`
lowerings, the emitted extended certificate and the shared combinators) and prints it
with `toScript`. `modalVerdX_of_queries` proves, once and for every benchmark, that the
rebuilt queries denote exactly the hypothesis: if each component has a route the runner
saw come back `unsat`, the instance's `Verd` holds. So a green runner line is evidence
about the theorem's own hypothesis, not about a lookalike (the legacy discipline of
`Verdicts/ModalPins.lean`, generic here because the v2 packs share one shape).
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Verdicts.ModalPins
import RelCertifier.Verdicts.GenericPins

namespace RelCertifier

open DL Parse RelCertifier.Oracle

variable {n : ℕ}

/-- The pack, rebuilt: per component (in the cover's strata order), the three route
queries A, B, C over the cut-narrowed, strata-narrowed domain. `none` if anything fails
to lower (the runner reports that as a SKIP, never as a pass). -/
def modalVerdXQueries (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (lam : ℚ) (l m : ℕ) : Option (List (List (IForm n))) := do
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let comps0 ← Oracle.invComponents vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let comps := order.map (fun i => comps0.getD i (.rat 0))
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
    [iflowQuery g fL fR (.rat lam) dom, iflowQueryStrict g fL fR (.rat lam) dom,
     iflowQuerySuperlevel g fL fR (.rat lam) dom]))

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length := by
  intro l
  induction l with
  | nil => intro r h; simp [List.mapM, List.mapM.loop] at h; subst h; rfl
  | cons a t ih =>
      intro r h
      rw [List.mapM_cons] at h
      rcases ha : f a with _ | b <;> rw [ha] at h
      · simp at h
      rcases ht : t.mapM f with _ | r' <;> rw [ht] at h
      · simp at h
      simp only [Option.bind_eq_bind, Option.bind] at h
      injection h with h
      subst h
      simp [ih ht]

/-- **The v2 pin.** If the runner's rebuild succeeds and, for every component, one of
its three printed queries is `unsat`, the instance's hypothesis `modalVerdX` holds. -/
theorem modalVerdX_of_queries {p : PProblem} {cX : EvolStrengtheningX} {invRow : ℕ}
    {order : List ℕ} {lam : ℚ} {l m : ℕ} {qss : List (List (IForm n))}
    (hq : modalVerdXQueries p cX n invRow order lam l m = some qss)
    (hz3 : ∀ i (hi : i < qss.length), ∃ q ∈ qss[i], z3solve q.toHost = Verdict.unsat) :
    modalVerdX p cX n invRow order (lam : ℝ) l m := by
  unfold modalVerdXQueries at hq
  simp only [Option.bind_eq_bind] at hq
  set vars := p.L.stateVars
  set mL := p.L.modes.getD l ⟨"", [], .tt, .tt, []⟩
  set mR := p.R.modes.getD m ⟨"", [], .tt, .tt, []⟩
  rcases hc : Oracle.invComponents vars n (p.invariants.getD invRow ("", PForm.tt)).2
    with _ | comps0 <;> rw [hc] at hq
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
  set comps := order.map (fun i => comps0.getD i (ITerm.rat 0))
  have hcompsH : order.map (fun i => (hostComps vars n
      (p.invariants.getD invRow ("", PForm.tt)).2).getD i (Term.const 0))
      = comps.map ITerm.toHost := by
    rw [hcomps]
    simp only [comps, List.map_map, Function.comp_def, hgetD]
  -- the pack
  show VerdXCore _ _ _ _ _
  unfold VerdXCore
  rw [hD, hcompsH, hostDyn_pin hfL, hostDyn_pin hfR]
  intro i hi
  rw [List.length_map] at hi
  have hi' : i < ((List.range comps.length).map (fun i =>
      [iflowQuery (comps.getD i (ITerm.rat 0)) fL fR (ITerm.rat lam)
        (istrataDomHost D (comps.take i)),
       iflowQueryStrict (comps.getD i (ITerm.rat 0)) fL fR (ITerm.rat lam)
        (istrataDomHost D (comps.take i)),
       iflowQuerySuperlevel (comps.getD i (ITerm.rat 0)) fL fR (ITerm.rat lam)
        (istrataDomHost D (comps.take i))])).length := by simpa using hi
  obtain ⟨q, hqmem, hqz⟩ := hz3 i hi'
  simp only [List.getElem_map, List.getElem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hqmem
  have hgi : (comps.map ITerm.toHost)[i]'(by simpa using hi)
      = (comps.getD i (ITerm.rat 0)).toHost := by
    rw [List.getElem_map, List.getD_eq_getElem _ _ hi]
  have htk : (comps.map ITerm.toHost).take i = (comps.take i).map ITerm.toHost := by
    rw [List.map_take]
  have hlam : (ITerm.rat lam : ITerm n).toHost = Term.const (lam : ℝ) := rfl
  rcases hqmem with rfl | rfl | rfl
  · left
    rw [imodalQuery_toHost, hlam] at hqz
    rw [hgi, htk]; exact hqz
  · right; left
    rw [imodalQueryStrict_toHost, hlam] at hqz
    rw [hgi, htk]; exact hqz
  · right; right
    rw [imodalQuerySuperlevel_toHost, hlam] at hqz
    rw [hgi, htk]; exact hqz

end RelCertifier
