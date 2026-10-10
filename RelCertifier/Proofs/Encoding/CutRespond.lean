/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cut-narrowed segment coupling, generic (suite_v2 modal instances)

The suite_v2 benchmarks certify their joint segments with the WIDENED cut channel
(`RELCERT_IMPLIED_CUT=1`): the flow queries of a pairing `(m_L, m_R)` are narrowed by the
kept atoms of BOTH modes (`OracleAPI.andCuts` over `segParts`' `evolve_L ∧ evolve_R`),
stratified per component (`strataDomIR`). This file states that query family at the host
level (`domCutX`, `VerdXCore`, `modalVerdX` — the latter read off the parser-emitted IR
and the emitted extended certificate exactly as the tool builds it) and turns it into the
per-piece coupling the modal chain consumes (`couple_cutX`):

* the stratified verdicts give preservation of the components over the NARROWED domain
  (`segPresAll_from_strata_verdicts'`);
* the atoms' conditional staying (`CutLiftX`: O2 per kind, stratified) lifts that to the
  BARE domain from every base where the atoms hold, and keeps the atoms
  (`segPresAll_cut_liftX`);
* the anchor formula carries the invariant components AND the atoms
  (`FM g (gs ++ atomTerms)`), so the coupling preserves both, and the λ-stretched right
  response is re-read as a run of the real (λ = 1) automaton mode (`sem_rightBlock_reparam`).

The O1 side (atoms hold at the window start / at a right mode's entry) is the
instance's: from the left guard (`gwindowSeg`'s test, `CutLiftX.evolStrengtheningWFX_entryL`)
and from the right mode's region conjunct (`mvRegionR`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Soundness.CutLiftX
import RelCertifier.Proofs.Encoding.WindowRF
import RelCertifier.Proofs.Encoding.EnvelopeChainR
import RelCertifier.Proofs.Encoding.Reparam

namespace RelCertifier

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## The narrowed query family, as the tool builds it -/

/-- The host pairs (lowered formula, safe-side term) of a list of extended-certificate
atoms (the same `hostAtomF`/`hostAtomG` the legacy cut instances use). -/
noncomputable def cutPairsX (vars : List String) (n : ℕ) (side : Side)
    (atoms : List CutAtomX) : List (CutAtomP n) :=
  atoms.map (fun x => (hostAtomF vars n side x.atom, hostAtomG vars n side x.atom))

/-- The kept atoms of the mode named `name` on one side of the extended certificate. -/
def cutAtomsOfX (mcs : List (String × List CutAtomX)) (name : String) : List CutAtomX :=
  ((mcs.find? (·.1 == name)).map (·.2)).getD []

/-- `OracleAPI.andCuts`, host level: an empty family leaves the base unchanged. -/
noncomputable def domCutX (dom : Formula (Var n)) (cL cR : List (CutAtomP n)) :
    Formula (Var n) :=
  let b1 := if cL.isEmpty then dom else Formula.and dom (cutF cL)
  if cR.isEmpty then b1 else Formula.and b1 (cutF cR)

theorem sat_domCutX (dom : Formula (Var n)) (cL cR : List (CutAtomP n))
    (ν : State (Var n)) :
    Formula.sat (domCutX dom cL cR) ν ↔
      Formula.sat dom ν ∧ CutSat cL ν ∧ CutSat cR ν := by
  unfold domCutX
  by_cases hL : cL.isEmpty <;> by_cases hR : cR.isEmpty <;>
    simp only [hL, hR, if_true, if_false, Bool.false_eq_true, Formula.sat, sat_cutF] <;>
    · have hL' : cL.isEmpty = true → CutSat cL ν := by
        intro h; rw [List.isEmpty_iff] at h; subst h; intro a ha; simp at ha
      have hR' : cR.isEmpty = true → CutSat cR ν := by
        intro h; rw [List.isEmpty_iff] at h; subst h; intro a ha; simp at ha
      tauto

/-- The stratified three-route verdict pack of one pairing (the hypothesis of
`segPresAll_from_strata_verdicts'`). -/
def VerdXCore (comps : List (Term (Var n))) (fL fR : Fin n → Term (Var n)) (lam : ℝ)
    (D : Formula (Var n)) : Prop :=
  ∀ i (hi : i < comps.length),
    z3solve (flowQuery ⟨comps[i], fL, fR, Term.const lam,
      strataDomHost D (comps.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨comps[i], fL, fR, Term.const lam,
      strataDomHost D (comps.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨comps[i], fL, fR, Term.const lam,
      strataDomHost D (comps.take i)⟩) = Verdict.unsat

/-- **The suite_v2 modal verdict pack, read off the IR and the extended certificate.**
Left mode `l`, right mode `m`, stretch `lam`, the invariant row `invRow`'s components in
the cover's strata `order`; the domain is the two modes' evolves narrowed by both modes'
kept atoms (`andCuts`), the fields the two modes' own. Exactly the queries `checkSeg`
sends (`segParts`, `andCuts`, `strataDomIR`, `routeQueries`). -/
noncomputable def modalVerdX (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (lam : ℝ) (l m : ℕ) : Prop :=
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let comps0 := hostComps vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let comps := order.map (fun i => comps0.getD i (Term.const 0))
  let base := Formula.and (hostEvolve vars n Side.L mL) (hostEvolve vars n Side.R mR)
  let cL := cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)
  let cR := cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)
  VerdXCore comps (hostDyn vars n Side.L mL) (hostDyn vars n Side.R mR) lam
    (domCutX base cL cR)

/-! ## Preservation over the narrowed domain, lifted -/

/-- Domain congruence for `SegPreservesAllOn`. -/
theorem segPresAll_congr {gs : List (Term (Var n))} {sys : ODESystem (Var n)}
    {D D' : Formula (Var n)} (hDD : ∀ x, Formula.sat D' x ↔ Formula.sat D x)
    (h : SegPreservesAllOn gs sys D) : SegPreservesAllOn gs sys D' := by
  intro ν hν ω hω
  exact h ν hν ω (sem_ode_congr (fun x => hDD x) hω)

/-- `FM` over an appended list. -/
theorem sat_FM_append (g : Term (Var n)) (gs ts : List (Term (Var n))) (ν : State (Var n)) :
    Formula.sat (FM g (gs ++ ts)) ν ↔
      Formula.sat (FM g gs) ν ∧ ∀ t ∈ ts, Term.eval t ν ≤ 0 := by
  rw [sat_FM_iff, sat_FM_iff]
  constructor
  · intro h
    refine ⟨fun g' hg' => h g' ?_, fun t ht => h t ?_⟩
    · rcases List.mem_cons.mp hg' with rfl | hg'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hg')
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ ht)
  · rintro ⟨h1, h2⟩ g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact h1 _ List.mem_cons_self
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact h1 g' (List.mem_cons_of_mem _ hg')
      · exact h2 g' hg'

/-- Atom terms of two families. -/
def atomTerms (cL cR : List (CutAtomP n)) : List (Term (Var n)) :=
  (cL ++ cR).map Prod.snd

theorem atomTerms_iff {cL cR : List (CutAtomP n)} (hiffL : AtomsIff cL)
    (hiffR : AtomsIff cR) (ν : State (Var n)) :
    (∀ t ∈ atomTerms cL cR, Term.eval t ν ≤ 0) ↔ CutSat cL ν ∧ CutSat cR ν := by
  unfold atomTerms
  constructor
  · intro h
    refine ⟨fun a ha => (hiffL a ha ν).mpr (h a.2 ?_),
      fun a ha => (hiffR a ha ν).mpr (h a.2 ?_)⟩
    · exact List.mem_map.mpr ⟨a, List.mem_append_left _ ha, rfl⟩
    · exact List.mem_map.mpr ⟨a, List.mem_append_right _ ha, rfl⟩
  · rintro ⟨hL, hR⟩ t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    rcases List.mem_append.mp ha with ha | ha
    · exact (hiffL a ha ν).mp (hL a ha)
    · exact (hiffR a ha ν).mp (hR a ha)

/-! ## The coupling -/

/-- **The cut-narrowed segment coupling.** Left `fL` on `domL` (clocked by `tg`), right
`fR` at stretch `lamv` on `domR`, read back as the λ = 1 automaton mode. The anchor
carries the invariant components and the atoms of both families; it is preserved by the
coupling (components: the narrowed verdicts lifted by the atoms' staying; atoms: their
staying), and the joint envelope is re-established at the end. -/
theorem couple_cutX (g : Term (Var n)) (gs comps : List (Term (Var n)))
    (cL cR : List (CutAtomP n)) (fL fR : Fin n → Term (Var n)) (lamv : ℝ) (hlam : 0 < lamv)
    (domL domR : Formula (Var n)) (b : Fin n) (dt : ℝ)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    (hcompsLR : ∀ g' ∈ g :: gs ++ atomTerms cL cR, g'.fv ⊆ range Lv ∪ range Rv)
    (hsub1 : ∀ c ∈ comps, c ∈ g :: gs) (hsub2 : ∀ g' ∈ g :: gs, g' ∈ comps)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR)
    (hstayL : AtomsStayC cL (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hstayR : AtomsStayC cR (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hverd : VerdXCore comps fL fR lamv (domCutX (Formula.and domL domR) cL cR))
    (hES : ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms cL cR))
        (Formula.and domL domR)) σ →
      HExistSegB fL fR (Term.const lamv) domL domR dt
        (Function.update σ ((Side.Aux, b) : Var n) 0)) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms cL cR))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, b) : Var n) (leftBlock fL)) domL)
        (Program.ode (rightBlock fR (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms cL cR)) (Formula.and domL domR))
        ((Side.Aux, b) : Var n) dt (Function.update σ ((Side.Aux, b) : Var n) 0) := by
  intro σ hσ
  set tg : Var n := ((Side.Aux, b) : Var n) with htgdef
  set A := FM g (gs ++ atomTerms cL cR) with hA
  have htgA : tg ∉ (Formula.and A (Formula.and domL domR)).fv := by
    intro h
    rcases h with h | h | h
    · exact notMem_FM_fv (fun g' hg' hx => by
        rcases hcompsLR g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
        · exact aux_ne_Lv b i hi.symm
        · exact aux_ne_Rv b i hi.symm) h
    · exact aux_notin_range_Lv b (hdomL h)
    · exact aux_notin_range_Rv b (hdomR h)
  set σ' := Function.update σ tg 0 with hσ'def
  have hσ' : Formula.sat (Formula.and A (Formula.and domL domR)) σ' := by
    rwa [(Formula.coincidence (Formula.and A (Formula.and domL domR)) (fun v hv =>
      Function.update_of_ne (fun hc => htgA (by rw [← hc]; exact hv)) _ _) :
        Formula.sat (Formula.and A (Formula.and domL domR)) _ ↔ _)]
  -- the narrowed preservation, lifted to the bare domain
  have hnarrow : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (domCutX (Formula.and domL domR) cL cR) :=
    segPresAll_from_strata_verdicts' fL fR (Term.const lamv) _ comps hverd
  have hnarrow' : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (Formula.and (Formula.and domL domR) (Formula.and (cutF cL) (cutF cR))) := by
    refine segPresAll_congr (fun x => ?_) hnarrow
    rw [sat_domCutX]
    simp only [Formula.sat, sat_cutF]
  have hlift := segPresAll_cut_liftX hiffL hiffR hstayL hstayR hnarrow'
  obtain ⟨hFσ, hatσ⟩ := (sat_FM_append g gs _ σ').mp hσ'.1
  obtain ⟨hLσ, hRσ⟩ := (atomTerms_iff hiffL hiffR σ').mp hatσ
  have hcompsσ : ∀ c ∈ comps, Term.eval c σ' ≤ 0 :=
    fun c hc => (sat_FM_iff g gs σ').mp hFσ c (hsub1 c hc)
  have hboxes : ∀ g' ∈ g :: (gs ++ atomTerms cL cR), Formula.sat (Formula.box
      (Program.ode (leftBlock fL ++ rightBlock fR (Term.const lamv))
        (Formula.and domL domR)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    rw [← jointSys_split] at hω
    obtain ⟨hcω, hLω, hRω⟩ := hlift σ' hLσ hRσ hcompsσ ω hω
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hcω _ (hsub2 _ List.mem_cons_self)
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact hcω _ (hsub2 _ (List.mem_cons_of_mem _ hg'))
      · exact (atomTerms_iff hiffL hiffR ω).mpr ⟨hLω, hRω⟩ g' hg'
  have hbase := segment_faModalB_from_certB_list g (gs ++ atomTerms cL cR) fL fR
    (Term.const lamv) domL domR tg dt
    (LR_blocks_disjoint _ _ _ hfL hfR (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomL hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomR hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
      exact aux_ne_Lv b i hi)
    (fun h => aux_notin_range_Lv b (leftBlock_readVars_sub fL hfL h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub fR (Term.const lamv) _ h
      exact aux_ne_Rv b i hi)
    (fun h => aux_notin_range_Rv b (rightBlock_readVars_sub fR
      (Term.const lamv) hfR (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv b (rightBlock_boundSet_sub fR (Term.const lamv) h))
    (fun h => aux_notin_range_Lv b (hdomL h))
    (fun h => aux_notin_range_Rv b (hdomR h))
    (fun g' hg' hx => by
      rcases hcompsLR g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact aux_ne_Lv b i hi.symm
      · exact aux_ne_Rv b i hi.symm)
    hboxes (by
      have := hES σ hσ
      rwa [show Function.update σ' tg 0 = σ' from by
        rw [hσ'def, Function.update_idem]] at *)
  have hupd : Function.update σ' tg (0 : ℝ) = σ' := by
    rw [hσ'def, Function.update_idem]
  rw [hupd] at hbase
  have hstr : faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL)) domL)
      (Program.ode (rightBlock fR (Term.const lamv)) domR)
      (Formula.and A (Formula.and domL domR)) tg dt σ' := by
    refine faModalB_strengthen_plant ?_ hbase
    intro ν μ hplant hsem
    have hdomLν : Formula.sat domL ν := sem_ode_ends_in_domain hplant.1
    have hdomRμ : Formula.sat domR μ := sem_ode_ends_in_domain hsem
    have hdomLμ : Formula.sat domL μ := by
      rwa [(Formula.coincidence domL (fun v hv' => sem_ode_mask hsem (by
        obtain ⟨i, rfl⟩ := hdomL hv'
        intro hb
        obtain ⟨j, hj⟩ := rightBlock_bound_sub fR (Term.const lamv) _ hb
        exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
          Formula.sat domL μ ↔ Formula.sat domL ν)]
    exact ⟨hdomLμ, hdomRμ⟩
  refine faModalB_monoQ ?_ hstr
  intro ν μ hsem
  exact sem_rightBlock_reparam lamv 1 hlam one_pos hsem

/-! ## Threshold atoms: staying from the sign of the own field -/

theorem boxle_thrGe_L (j : Fin n) (K : ℝ) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (dom D : Formula (Var n)) (hdomImp : ∀ x, Formula.sat dom x → Formula.sat D x)
    (hf : ∀ z, Formula.sat D z → z (Lv j) ≤ K → 0 ≤ Term.eval (fL j) z)
    {ν : State (Var n)} (hinit : Term.eval (thrGe (Lv j) K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval (thrGe (Lv j) K) ω) ν := by
  refine boxle_L_of_super _ fL fR lam dom D (fun i h => by
    simp [thrGe, Term.fv, Lv, Rv, Prod.ext_iff] at h) hdomImp ?_ hinit
  intro z hz hge
  rw [eval_lie1L_thr j _ (-1) (fun w z => tderiv_thrGe _ _ w z)]
  have hzK : z (Lv j) ≤ K := by simpa [thrGe, Term.eval, AOp.interp] using hge
  have := hf z hz hzK
  linarith

theorem boxle_thrLe_L (j : Fin n) (K : ℝ) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (dom D : Formula (Var n)) (hdomImp : ∀ x, Formula.sat dom x → Formula.sat D x)
    (hf : ∀ z, Formula.sat D z → K ≤ z (Lv j) → Term.eval (fL j) z ≤ 0)
    {ν : State (Var n)} (hinit : Term.eval (thrLe (Lv j) K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval (thrLe (Lv j) K) ω) ν := by
  refine boxle_L_of_super _ fL fR lam dom D (fun i h => by
    simp [thrLe, Term.fv, Lv, Rv, Prod.ext_iff] at h) hdomImp ?_ hinit
  intro z hz hge
  rw [eval_lie1L_thr j _ 1 (fun w z => tderiv_thrLe _ _ w z)]
  have hzK : K ≤ z (Lv j) := by simpa [thrLe, Term.eval, AOp.interp] using hge
  have := hf z hz hzK
  linarith

theorem boxle_thrGe_R (j : Fin n) (K : ℝ) (fL fR : Fin n → Term (Var n)) (c : ℝ) (hc : 0 ≤ c)
    (dom D : Formula (Var n)) (hdomImp : ∀ x, Formula.sat dom x → Formula.sat D x)
    (hf : ∀ z, Formula.sat D z → z (Rv j) ≤ K → 0 ≤ Term.eval (fR j) z)
    {ν : State (Var n)} (hinit : Term.eval (thrGe (Rv j) K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const c)) dom)
      (fun ω => Term.eval (thrGe (Rv j) K) ω) ν := by
  refine boxle_R_of_super _ fL fR c hc dom D (fun i h => by
    simp [thrGe, Term.fv, Lv, Rv, Prod.ext_iff] at h) hdomImp ?_ hinit
  intro z hz hge
  rw [eval_lie1R_thr j _ (-1) (fun w z => tderiv_thrGe _ _ w z)]
  have hzK : z (Rv j) ≤ K := by simpa [thrGe, Term.eval, AOp.interp] using hge
  have := hf z hz hzK
  linarith

theorem boxle_thrLe_R (j : Fin n) (K : ℝ) (fL fR : Fin n → Term (Var n)) (c : ℝ) (hc : 0 ≤ c)
    (dom D : Formula (Var n)) (hdomImp : ∀ x, Formula.sat dom x → Formula.sat D x)
    (hf : ∀ z, Formula.sat D z → K ≤ z (Rv j) → Term.eval (fR j) z ≤ 0)
    {ν : State (Var n)} (hinit : Term.eval (thrLe (Rv j) K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const c)) dom)
      (fun ω => Term.eval (thrLe (Rv j) K) ω) ν := by
  refine boxle_R_of_super _ fL fR c hc dom D (fun i h => by
    simp [thrLe, Term.fv, Lv, Rv, Prod.ext_iff] at h) hdomImp ?_ hinit
  intro z hz hge
  rw [eval_lie1R_thr j _ 1 (fun w z => tderiv_thrLe _ _ w z)]
  have hzK : K ≤ z (Rv j) := by simpa [thrLe, Term.eval, AOp.interp] using hge
  have := hf z hz hzK
  linarith

/-! ## `hiff` and O1 for an emitted extended certificate -/

/-- Nonstrict comparison atoms have the `≤ 0`-normal form their `cutAtomG` term gives. -/
theorem atomsIff_cutPairsX {vars : List String} {side : Side} {atoms : List CutAtomX}
    (h : ∀ x ∈ atoms, ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=")) :
    AtomsIff (cutPairsX vars n side atoms) := by
  intro a ha ν
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨op, e1, e2, hat, hop⟩ := h x hx
  simp only
  rw [hat]
  exact hostAtom_iff hop ν

/-- **O1 from the extended certificate, left side**: every kept atom of left mode `m`
holds wherever `m`'s lowered guard holds — by `evolStrengtheningWFX_entryL` on the
kernel-checked certificate, given that the atoms and the guard lower and no atom took the
`z3` entry. -/
theorem cutSatL_of_guard {p : PProblem} {cX : EvolStrengtheningX}
    (hwf : evolStrengtheningWFX p cX = true) {vars : List String} (m : PMode)
    (hm : p.L.modes.find? (·.name == m.name) = some m)
    (hz3 : ∀ x ∈ cutAtomsOfX cX.L m.name, x.entry ≠ CutEntry.z3)
    (hlow : ∀ x ∈ cutAtomsOfX cX.L m.name, (Run.lowerF vars n Side.L x.atom).isSome)
    (hg : (Run.lowerF vars n Side.L m.guard).isSome) :
    ∀ ν, Formula.sat (hostGuard vars n Side.L m) ν →
      CutSat (cutPairsX vars n Side.L (cutAtomsOfX cX.L m.name)) ν := by
  intro ν hsat a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have hx' := hx
  unfold cutAtomsOfX at hx'
  rcases hf : cX.L.find? (·.1 == m.name) with _ | ⟨nm, atoms⟩
  · rw [hf] at hx'; simp at hx'
  rw [hf] at hx'
  simp only [Option.map_some, Option.getD_some] at hx'
  have hmem : (nm, atoms) ∈ cX.L := List.mem_of_find?_eq_some hf
  have hnm : nm = m.name := by simpa using List.find?_some hf
  subst hnm
  obtain ⟨m', hm', hent⟩ := evolStrengtheningWFX_entryL hwf hmem
  rw [hm] at hm'
  injection hm' with hmm
  subst hmm
  obtain ⟨gI, hgI⟩ := Option.isSome_iff_exists.mp hg
  obtain ⟨aI, haI⟩ := Option.isSome_iff_exists.mp (hlow x hx)
  have hsatg : Formula.sat gI.toHost ν := by
    simpa [hostGuard, hgI] using hsat
  have := hent vars Side.L gI hgI (fun y hy hy3 => absurd hy3 (hz3 y (by
      simpa [cutAtomsOfX, hf] using hy))) ν hsatg x hx' aI haI
  simpa [hostAtomF, haI] using this

/-- **O1 from the extended certificate, right side.** -/
theorem cutSatR_of_guard {p : PProblem} {cX : EvolStrengtheningX}
    (hwf : evolStrengtheningWFX p cX = true) {vars : List String} (m : PMode)
    (hm : p.R.modes.find? (·.name == m.name) = some m)
    (hz3 : ∀ x ∈ cutAtomsOfX cX.R m.name, x.entry ≠ CutEntry.z3)
    (hlow : ∀ x ∈ cutAtomsOfX cX.R m.name, (Run.lowerF vars n Side.R x.atom).isSome)
    (hg : (Run.lowerF vars n Side.R m.guard).isSome) :
    ∀ ν, Formula.sat (hostGuard vars n Side.R m) ν →
      CutSat (cutPairsX vars n Side.R (cutAtomsOfX cX.R m.name)) ν := by
  intro ν hsat a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have hx' := hx
  unfold cutAtomsOfX at hx'
  rcases hf : cX.R.find? (·.1 == m.name) with _ | ⟨nm, atoms⟩
  · rw [hf] at hx'; simp at hx'
  rw [hf] at hx'
  simp only [Option.map_some, Option.getD_some] at hx'
  have hmem : (nm, atoms) ∈ cX.R := List.mem_of_find?_eq_some hf
  have hnm : nm = m.name := by simpa using List.find?_some hf
  subst hnm
  obtain ⟨m', hm', hent⟩ := evolStrengtheningWFX_entryR hwf hmem
  rw [hm] at hm'
  injection hm' with hmm
  subst hmm
  obtain ⟨gI, hgI⟩ := Option.isSome_iff_exists.mp hg
  obtain ⟨aI, haI⟩ := Option.isSome_iff_exists.mp (hlow x hx)
  have hsatg : Formula.sat gI.toHost ν := by
    simpa [hostGuard, hgI] using hsat
  have := hent vars Side.R gI hgI (fun y hy hy3 => absurd hy3 (hz3 y (by
      simpa [cutAtomsOfX, hf] using hy))) ν hsatg x hx' aI haI
  simpa [hostAtomF, haI] using this

/-! ## Side of a lowered formula (guards, atoms) -/

theorem hostForm_side {vars : List String} {s : Side} {bad : String}
    (hres : ResolvesTo vars n s bad) (f : PForm) (hfree : PForm.namesFree bad f = true) :
    ∀ x ∈ (((Run.lowerF vars n s f).map IForm.toHost).getD Formula.tt).fv, x.1 = s := by
  rcases hlow : Run.lowerF vars n s f with _ | ff
  · intro x hx
    simp [Formula.fv] at hx
  · intro x hx
    rw [Option.map_some, Option.getD_some] at hx
    exact Run.lowerF_fv_side hres hfree hlow x hx

end RelCertifier
