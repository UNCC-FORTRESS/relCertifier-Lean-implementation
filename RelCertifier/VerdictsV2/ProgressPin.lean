/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The progress pin: an emitted certificate's verdict, read at the host level

`progressVerd_one` turns `ProgressVerd` of a single-stage upward certificate (the runner's
queries all `unsat`) into the facts `repoProgress_one` consumes, stated over the host
denotations the instances use (`hostEvolve`, `hostGuard`, the checked cuts as `cutPairsX`,
the invariant components as `hostComps`, the field as `hostDyn`): the rate on the region, and
the landing on the crossing line and at an already-crossed start. The rebuild's `Option`
binds are unpacked symbolically (as `modalVerdDynX_of_queries` does).
-/
import RelCertifier.VerdictsV2.ProgressX
import RelCertifier.Verdicts.GenericPins

namespace RelCertifier.Progress

open DL Parse RelCertifier RelCertifier.Oracle RelCertifier.Run

variable {n : ℕ}

/-- The region, read at the host level. -/
def RegionSat (vars : List String) (n : ℕ) (cX : EvolStrengtheningX) (mL mR : PMode)
    (row : PForm) (pre : Bool) (y : State (Var n)) : Prop :=
  Formula.sat (hostEvolve vars n Side.L mL) y ∧
  CutSat (cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)) y ∧
  (∀ c ∈ hostComps vars n row, Term.eval c y ≤ 0) ∧
  (pre = true → Formula.sat (hostGuard vars n Side.L mL) y) ∧
  Formula.sat (hostEvolve vars n Side.R mR) y ∧
  CutSat (cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)) y

theorem sat_invI (comps : List (ITerm n)) (y : State (Var n)) :
    Formula.sat (comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) IForm.tt).toHost
      y ↔ ∀ c ∈ comps.map ITerm.toHost, Term.eval c y ≤ 0 := by
  induction comps using List.reverseRecOn with
  | nil => simp [IForm.toHost, Formula.sat]
  | append_singleton l a ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [sat_toHost_and, ih, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩ c (hc | rfl)
        · exact h1 c hc
        · simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval] using h2
      · intro h
        refine ⟨fun c hc => h c (Or.inl hc), ?_⟩
        have := h a.toHost (Or.inr rfl)
        simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval] using this

theorem sat_cutF_iff (cs : List (CutAtomP n)) (y : State (Var n)) :
    Formula.sat (cutF cs) y ↔ CutSat cs y := sat_cutF cs y

/-- **The single-stage pin.** -/
theorem progressVerd_one {p : PProblem} {cX : EvolStrengtheningX} {c : ProgressE}
    (hv : ProgressVerd p cX n c) (st : ProgressStageE) (hst : c.stages = [st])
    (hup : st.up = true) :
    let vars := p.L.stateVars
    let dm : PMode := ⟨"", [], .tt, .tt, []⟩
    let mL := p.L.modes.getD (modeIdx p.L.modes c.mL) dm
    let mR := p.R.modes.getD (modeIdx p.R.modes c.mR) dm
    let row := (p.invariants.getD (invRowOf p (modeIdx p.L.modes c.mL)) ("", PForm.tt)).2
    ∃ v : Var n, Run.resolveVar vars n Side.R st.var = some v ∧
      (∀ y, RegionSat vars n cX mL mR row c.pre y → y v < (st.theta : ℝ) →
        (st.rate : ℝ) ≤ Term.eval (hostDyn vars n Side.R mR v.2) y) ∧
      (∀ y, RegionSat vars n cX mL mR row c.pre y → y v = (st.theta : ℝ) →
        ∃ nm ∈ c.exits, ∃ md ∈ p.R.modes, md.name = nm ∧
          Formula.sat (hostGuard vars n Side.R md) y) ∧
      (∀ y, RegionSat vars n cX mL mR row c.pre y → Formula.sat (hostGuard vars n Side.R mR) y →
        (st.theta : ℝ) ≤ y v →
        ∃ nm ∈ c.exits, ∃ md ∈ p.R.modes, md.name = nm ∧
          Formula.sat (hostGuard vars n Side.R md) y) := by
  intro vars dm mL mR row
  obtain ⟨qs, hqs, hz3⟩ := hv
  unfold progressQueriesOf at hqs
  simp only [Option.bind_eq_bind] at hqs
  rcases hreg : regionOf p cX n (invRowOf p (modeIdx p.L.modes c.mL)) c.pre
      (modeIdx p.L.modes c.mL) (modeIdx p.R.modes c.mR) with _ | R <;> rw [hreg] at hqs
  · simp at hqs
  rcases hfR : Run.dynOf vars n Side.R mR with _ | fR <;> rw [Option.bind_some, hfR] at hqs
  · simp at hqs
  rcases hgq : Run.lowerF vars n Side.R mR.guard with _ | gq <;> rw [Option.bind_some, hgq] at hqs
  · simp at hqs
  simp only [Option.bind_some] at hqs
  unfold progressQueries at hqs
  rw [hst, List.mapM_cons, List.mapM_nil] at hqs
  simp only [Option.bind_eq_bind] at hqs
  rcases hres : Run.resolveVar vars n Side.R st.var with _ | v <;> rw [hres] at hqs
  · simp at hqs
  simp only [Option.map_some, Option.bind_some, Option.pure_def] at hqs
  generalize hex : c.exits = exits at hqs
  rcases hguards : exits.mapM (fun nm => (p.R.modes.find? (·.name == nm)).bind
      (fun md => Run.lowerF vars n Side.R md.guard)) with _ | guards <;> rw [hguards] at hqs
  · simp at hqs
  simp only [Option.bind_some, stageQueries, Option.some.injEq] at hqs
  -- the region, unpacked
  unfold regionOf at hreg
  simp only [Option.bind_eq_bind] at hreg
  rcases hc : Oracle.invComponents vars n row with _ | comps0 <;> rw [hc] at hreg
  · simp at hreg
  rcases heL : Run.lowerF vars n Side.L mL.evolve with _ | evL <;> rw [Option.bind_some, heL] at hreg
  · simp at hreg
  rcases heR : Run.lowerF vars n Side.R mR.evolve with _ | evR <;> rw [Option.bind_some, heR] at hreg
  · simp at hreg
  rcases haL : ((cutAtomsOfX cX.L mL.name).map (·.atom)).mapM (Run.lowerF vars n Side.L)
    with _ | aL <;> rw [Option.bind_some, haL] at hreg
  · simp at hreg
  rcases haR : ((cutAtomsOfX cX.R mR.name).map (·.atom)).mapM (Run.lowerF vars n Side.R)
    with _ | aR <;> rw [Option.bind_some, haR] at hreg
  · simp at hreg
  rcases hgL : Run.lowerF vars n Side.L mL.guard with _ | gL <;> rw [Option.bind_some, hgL] at hreg
  · simp at hreg
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hreg
  subst hreg
  set Rg : IForm n := IForm.and (IForm.and (IForm.and (IForm.and evL (icutF aL))
    (comps0.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) IForm.tt))
    (if c.pre then gL else IForm.tt)) (IForm.and evR (icutF aR)) with hRg
  have hcL : cutF (cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)) = (icutF aL).toHost := by
    rw [cutFold_pin _ aL haL]
    simp [cutPairsX, List.map_map, Function.comp_def]
  have hcR : cutF (cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)) = (icutF aR).toHost := by
    rw [cutFold_pin _ aR haR]
    simp [cutPairsX, List.map_map, Function.comp_def]
  have hRsat : ∀ y, RegionSat vars n cX mL mR row c.pre y → Formula.sat Rg.toHost y := by
    rintro y ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩
    · rwa [hostEvolve_pin heL] at h1
    · rwa [← sat_cutF_iff, hcL] at h2
    · rw [sat_invI]; rwa [hostComps_pin hc] at h3
    · cases hp : c.pre
      · simp [IForm.toHost, Formula.sat]
      · simp only [if_true]; rw [← hostGuard_pin hgL]; exact h4 hp
    · rwa [hostEvolve_pin heR] at h5
    · rwa [← sat_cutF_iff, hcR] at h6
  have hexit : ∀ y, (∃ g ∈ guards, Formula.sat g.toHost y) →
      ∃ nm ∈ exits, ∃ md ∈ p.R.modes, md.name = nm ∧
        Formula.sat (hostGuard vars n Side.R md) y := by
    intro y ⟨g, hg, hsat⟩
    clear hqs hz3 hRsat hex
    induction exits generalizing guards with
    | nil =>
        rw [List.mapM_nil, Option.pure_def, Option.some.injEq] at hguards
        subst hguards; simp at hg
    | cons nm rest ih =>
        rw [List.mapM_cons] at hguards
        simp only [Option.bind_eq_bind] at hguards
        rcases hf : p.R.modes.find? (·.name == nm) with _ | md <;> rw [hf] at hguards
        · simp at hguards
        simp only [Option.bind_some] at hguards
        rcases hgm : Run.lowerF vars n Side.R md.guard with _ | gm <;> rw [hgm] at hguards
        · simp at hguards
        rcases hrest : rest.mapM (fun nm => (p.R.modes.find? (·.name == nm)).bind
            (fun md => Run.lowerF vars n Side.R md.guard)) with _ | gs <;> rw [hrest] at hguards
        · simp at hguards
        simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hguards
        subst hguards
        rcases List.mem_cons.mp hg with rfl | hg'
        · refine ⟨nm, List.mem_cons_self, md, List.mem_of_find?_eq_some hf, ?_, ?_⟩
          · simpa using List.find?_some hf
          · rwa [hostGuard_pin hgm]
        · obtain ⟨nm', hnm', md', hmd', hname, hs⟩ := ih gs hrest hg'
          exact ⟨nm', List.mem_cons_of_mem _ hnm', md', hmd', hname, hs⟩
  refine ⟨v, rfl, ?_, ?_, ?_⟩
  · intro y hRy hlt
    have hmem : rateQuery Rg fR [(v, st)] 0 v st ∈ qs := by rw [← hqs]; simp
    have h := rate_of_unsat Rg fR [(v, st)] 0 v st hup (hz3 _ hmem) y (hRsat y hRy)
      (by simp [crossedBefore, IForm.toHost, Formula.sat]) hlt
    rwa [hostDyn_pin hfR]
  · intro y hRy hline
    have hmem : guards.foldl (fun d g => IForm.and d (IForm.neg g)) (IForm.and Rg (onLine v st))
        ∈ qs := by rw [← hqs]; simp [landQueries]
    refine hexit y (land_of_unsat (IForm.and Rg (onLine v st)) guards (hz3 _ hmem) y
      ⟨hRsat y hRy, ?_⟩)
    rw [sat_onLine]; exact hline
  · intro y hRy hg hθ
    have hmem : guards.foldl (fun d g => IForm.and d (IForm.neg g))
        (IForm.and (IForm.and Rg gq) (crossed v st)) ∈ qs := by rw [← hqs]; simp [landQueries]
    refine hexit y (land_of_unsat (IForm.and (IForm.and Rg gq) (crossed v st)) guards (hz3 _ hmem)
      y ⟨⟨hRsat y hRy, ?_⟩, ?_⟩)
    · rwa [hostGuard_pin hgq] at hg
    · rw [sat_crossed_up v st hup]; exact hθ

end RelCertifier.Progress
