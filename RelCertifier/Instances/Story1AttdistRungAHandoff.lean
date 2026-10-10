/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_a_6to8` — the DECLARED mode-dependent invariant, composed

`Story1AttdistRungAModal.story1_attdist_rung_a_modal` states Theorem 3 at the rows'
COMMON part (the two attitude-energy conjuncts, `invariants.getD 1`) for every left
window. The file declares `STEEP = v[l] ≤ v[r] ∧ common` and `MODER = FLAT = common`.
This leaf states that: one row per LEFT mode, keyed by `u_L = (Aux, 2)`, as a ∀∃
invariant of the left automaton over the file's `next` lists. Ingredients:

* `MODER`/`FLAT` windows: the base instance's own in-place steps, whose row IS the
  declared one (`FRow 1`, `FRow 2` are the common row — `FRow 2 = FRow 1` since the two
  declared formulas are syntactically identical);
* the `STEEP` window: a new verdict pack `VerdS m` at the full three-component STEEP row
  (`v`, `ψ`, `θ` in the stratified order), the base instance's existence lemma (whose
  invariant hypothesis it only reads for the right envelope), and the same in-place
  response;
* the handoffs, in-kernel: `STEEP → MODER` drops the `v` conjunct, `MODER → FLAT` is an
  identical row, self-loops are trivial (`FM_mono`).

Residuals: the base instance's nine `VerdD` packs for the `MODER`/`FLAT` windows (six
used) plus three `VerdS` packs — every one re-run by `relcert --run-verdicts-v2` (phase
"copied benchmarks") and pinned to the runner's query in `Verdicts/ModalPinTable.lean`.
-/
import RelCertifier.Instances.Story1AttdistRungAModal
import RelCertifier.Proofs.Encoding.ModeHandoff

namespace RelCertifier
namespace Story1AttdistRungAHandoff

open DL DLCalTiming DLRel Parse Set Story1AttdistRungAModal

set_option maxHeartbeats 12800000

/-- The left mode variable — the third auxiliary (`mv = (Aux, 0)`, `tg = (Aux, 1)`). -/
abbrev ulD : Var 8 := (Side.Aux, 2)

/-! ## The declared rows -/

def invRowPF (r : ℕ) : Parse.PForm :=
  (story1_attdist_rung_a_6to8_IR.invariants.getD r ("", Parse.PForm.tt)).2

noncomputable def gRowAt (r i : ℕ) : Term (Var 8) :=
  ((Run.invToG vsD 8 ((atomsOf (invRowPF r)).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

/-- The STEEP row's components, in the stratified order the runner checks: `v`, `ψ`, `θ`. -/
noncomputable def gS : Term (Var 8) := gRowAt 0 0
noncomputable def gsS : List (Term (Var 8)) := [gRowAt 0 1, gRowAt 0 2]

/-- Row `r`'s component list: STEEP has three, the others two. -/
noncomputable def rowGs (r : ℕ) : List (Term (Var 8)) :=
  if r = 0 then gsS else [gRowAt r 1]

noncomputable def FRow (r : ℕ) : Formula (Var 8) := FM (gRowAt r 0) (rowGs r)
noncomputable def ϕRow (r : ℕ) : RFormula (Var 8) := canonInvM (gRowAt r 0) (rowGs r)

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 8)) (ϕRow r) = FRow r :=
  encode_canonInvM _ _

/-- The MODER row is the base instance's row (`invariants.getD 1`), term for term. -/
theorem gRowAt_one_zero : gRowAt 1 0 = gD := rfl
theorem gRowAt_one_one : gRowAt 1 1 = gAt 1 := rfl

/-- The FLAT row is syntactically the MODER row. -/
theorem atoms_two_zero : (atomsOf (invRowPF 2)).getD 0 .tt = (atomsOf invDPF).getD 0 .tt := by
  decide
theorem atoms_two_one : (atomsOf (invRowPF 2)).getD 1 .tt = (atomsOf invDPF).getD 1 .tt := by
  decide
theorem gRowAt_two_zero : gRowAt 2 0 = gD := by
  unfold gRowAt gD gAt; rw [atoms_two_zero]
theorem gRowAt_two_one : gRowAt 2 1 = gAt 1 := by
  unfold gRowAt gAt; rw [atoms_two_one]

/-- STEEP's second and third components are the common row's two. -/
theorem atoms_zero_one : (atomsOf (invRowPF 0)).getD 1 .tt = (atomsOf invDPF).getD 0 .tt := by
  decide
theorem atoms_zero_two : (atomsOf (invRowPF 0)).getD 2 .tt = (atomsOf invDPF).getD 1 .tt := by
  decide
theorem gRowAt_zero_one : gRowAt 0 1 = gD := by
  unfold gRowAt gD gAt; rw [atoms_zero_one]
theorem gRowAt_zero_two : gRowAt 0 2 = gAt 1 := by
  unfold gRowAt gAt; rw [atoms_zero_two]

theorem FRow_one : FRow 1 = FM gD gsD := rfl
theorem FRow_two : FRow 2 = FM gD gsD := by
  unfold FRow rowGs; simp only [show (2:ℕ) ≠ 0 by decide, if_false]
  rw [gRowAt_two_zero, gRowAt_two_one]; rfl
theorem FRow_zero : FRow 0 = FM gS gsS := rfl

theorem hgRowAt (r i : ℕ) : (gRowAt r i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem aux_notin_gRowAt (a : Fin 8) (r i : ℕ) : ((Side.Aux, a) : Var 8) ∉ (gRowAt r i).fv := by
  intro h
  rcases hgRowAt r i h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem mem_rowGs {r : ℕ} {g : Term (Var 8)} (hg : g ∈ gRowAt r 0 :: rowGs r) :
    ∃ i, g = gRowAt r i := by
  unfold rowGs at hg
  split_ifs at hg with hr
  · subst hr
    simp only [gsS, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

theorem aux_notin_FRow (a : Fin 8) (r : ℕ) : ((Side.Aux, a) : Var 8) ∉ (FRow r).fv :=
  notMem_FM_fv (fun g' hg' => by
    obtain ⟨i, rfl⟩ := mem_rowGs hg'
    exact aux_notin_gRowAt a r i)

theorem htggS : ∀ g' ∈ gS :: gsS, tgD ∉ g'.fv := by
  intro g' hg'
  simp only [gS, gsS, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl <;> exact aux_notin_gRowAt 1 0 _

theorem htgFS : tgD ∉ (FM gS gsS).fv := notMem_FM_fv htggS

theorem htgFS_mv : mvD ∉ (FM gS gsS).fv :=
  notMem_FM_fv (fun g' hg' => by
    simp only [gS, gsS, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl <;> exact aux_notin_gRowAt 0 0 _)

/-- STEEP's row implies the common row (its last two components). -/
theorem FM_steep_common {ν : State (Var 8)} (h : Formula.sat (FM gS gsS) ν) :
    Formula.sat (FM gD gsD) ν := by
  refine FM_mono ?_ h
  intro g hg
  simp only [gsD, List.mem_cons, List.not_mem_nil, or_false] at hg
  simp only [gS, gsS, List.mem_cons, List.not_mem_nil, or_false]
  rcases hg with rfl | rfl
  · exact Or.inr (Or.inl gRowAt_zero_one.symm)
  · exact Or.inr (Or.inr gRowAt_zero_two.symm)

/-! ## The STEEP window at its own row: verdicts, coupling, response -/

/-- The three-component STEEP pack against right mode `m`, at λ = 1, in the stratified
order (`v` first, then the two energies). -/
def VerdS (m : ℕ) : Prop :=
  ∀ i (hi : i < (gS :: gsS).length),
    z3solve (flowQuery ⟨(gS :: gsS)[i], fLD 0, fRD m, Term.const (1),
      strataDomHost (Formula.and domLD domRD) ((gS :: gsS).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(gS :: gsS)[i], fLD 0, fRD m, Term.const (1),
      strataDomHost (Formula.and domLD domRD) ((gS :: gsS).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(gS :: gsS)[i], fLD 0, fRD m, Term.const (1),
      strataDomHost (Formula.and domLD domRD) ((gS :: gsS).take i)⟩) = Verdict.unsat

theorem coupleS (m : ℕ) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdS m) :
    ∀ σ', Formula.sat (Formula.and (FM gS gsS) envD) σ' → σ' tgD = 0 →
      faModalB (Equiv.refl (Var 8))
        (Program.ode (DLCalTiming.clk tgD (leftBlock (fLD 0))) domLD)
        (Program.ode (rightBlock (fRD m) (Term.const (1))) domRD)
        (Formula.and (FM gS gsS) envD) tgD dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgD (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgD
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLD 0) (fRD m) (Term.const (1))
    (Formula.and domLD domRD) (gS :: gsS) hv
  have hboxes : ∀ g' ∈ gS :: gsS, Formula.sat (Formula.box (Program.ode
      (leftBlock (fLD 0) ++ rightBlock (fRD m) (Term.const (1)))
      (Formula.and domLD domRD)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff gS gsS σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list gS gsS (fLD 0) (fRD m)
    (Term.const (1)) domLD domRD tgD dt
    (LR_blocks_disjoint _ _ _ (hfLD 0 (by norm_num)) (hfRD m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLD hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRD hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD 0) _ h
      exact aux_ne_Lv aD i hi)
    (fun h => aux_notin_range_Lv aD (leftBlock_readVars_sub (fLD 0) (hfLD 0 (by norm_num)) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRD m) (Term.const (1)) _ h
      exact aux_ne_Rv aD i hi)
    (fun h => aux_notin_range_Rv aD (rightBlock_readVars_sub (fRD m)
      (Term.const (1)) (hfRD m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aD (rightBlock_boundSet_sub (fRD m)
      (Term.const (1)) h))
    (fun h => aux_notin_range_Lv aD (hdomLD h))
    (fun h => aux_notin_range_Rv aD (hdomRD h))
    htggS hboxes
    (esD 0 m (by norm_num) hm dt hdt σ' ⟨FM_steep_common hσ'.1, hσ'.2⟩)
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLD ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRD μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLD μ := by
    rwa [(Formula.coincidence domLD (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLD hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRD m) (Term.const (1)) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLD μ ↔ Formula.sat domLD ν)]
  exact ⟨hdomLμ, hdomRμ⟩

theorem couple1S (m : ℕ) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdS m) :
    ∀ σ, Formula.sat (Formula.and (FM gS gsS) envD) σ →
      faModalB (Equiv.refl (Var 8))
        (Program.ode (DLCalTiming.clk tgD (leftBlock (fLD 0))) domLD)
        (Program.ode (rightBlock (fRD m) (Term.const 1)) domRD) (Formula.and (FM gS gsS) envD) tgD dt
        (Function.update σ tgD 0) := by
  intro σ hσ
  have htgφ : tgD ∉ (Formula.and (FM gS gsS) envD).fv := by
    intro h
    rcases h with h | h
    · exact htgFS h
    · exact htgenvD h
  have hupdφ : Formula.sat (Formula.and (FM gS gsS) envD)
      (Function.update σ tgD 0) := by
    rwa [(Formula.coincidence (Formula.and (FM gS gsS) envD) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (FM gS gsS) envD) _ ↔ _)]
  refine faModalB_monoQ ?_ (coupleS m hm dt hdt hv
    (Function.update σ tgD 0) hupdφ (Function.update_self _ _ _))
  intro ν μ hsem
  exact sem_rightBlock_reparam (1) 1 (by norm_num) one_pos hsem

theorem respondS (m : ℕ) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdS m)
    {σ : State (Var 8)}
    (hσ : Formula.sat (Formula.and (FM gS gsS) envD) σ) :
    Formula.sat (faModal (Equiv.refl (Var 8))
      (windowSeg (leftBlock (fLD 0)) domLD tgD dt 1)
      (bigSeq [Program.ode (rightBlock (fRD m) (Term.const 1)) domRD])
      (Formula.and (FM gS gsS) envD)) σ := by
  have hfa := Hmulti_windowRF_prefixed (fLD 0) domLD (FM gS gsS) envD
    aD dt 1 htgFS htgenvD [] (by simp) (fun σ' hσ' => hσ'.2.1) (by simp)
    (hfLD 0 (by norm_num)) hdomLD
    (List.replicate 1 (Program.ode (rightBlock (fRD m) (Term.const 1)) domRD)) (by simp) (by norm_num)
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ, Program.rename_refl]
      exact hdisH_progR (⟨fRD m, Term.const 1, domRD⟩ : RepoHop 8)
        (hfRD m hm) (by simp [Term.fv]) hdomRD (hfLD 0 (by norm_num)) hdomLD)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact couple1S m hm dt hdt hv σ' hσ')
    hσ
  simpa [List.replicate] using hfa

/-- The STEEP window's step provider: in place at the current right mode. -/
theorem HmultiS (dt : ℝ) (hdt : 0 ≤ dt) (hv0 : VerdS 0) (hv1 : VerdS 1) (hv2 : VerdS 2) :
    ∀ (q : ℕ), q < GrD.modes.length → ∀ σ, σ mvD = (q : ℝ) →
      Formula.sat (Formula.and (FM gS gsS) envD) σ →
      ∃ segs : List (ℕ × RMode (Var 8) × REdge (Var 8)),
        (∀ s ∈ segs, GrD.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrD.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 8))
          (windowSeg (leftBlock (fLD 0)) domLD tgD dt 1)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gS gsS) envD)) σ := by
  intro q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrD] using hq
  have hhead1 : ∀ (a : ℕ × RMode (Var 8) × REdge (Var 8)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tgt : ℕ, st < 3 → tgt < 3 → edgeD st tgt ∈ GrD.edges →
      GrD.modeAt st = some (modeD st) ∧ edgeD st tgt ∈ GrD.edgesFrom st :=
    fun st tgt hs ht he => ⟨GrD_modeAt st hs, edgeD_mem st tgt he⟩
  interval_cases q
  · refine ⟨[(0, modeD 0, edgeD 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 0 0 (by norm_num) (by norm_num) (by simp [GrD])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondS 0 (by norm_num) dt hdt hv0 hσ
      simpa [modeD] using this
  · refine ⟨[(1, modeD 1, edgeD 1 1)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrD])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondS 1 (by norm_num) dt hdt hv1 hσ
      simpa [modeD] using this
  · refine ⟨[(2, modeD 2, edgeD 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrD])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondS 2 (by norm_num) dt hdt hv2 hσ
      simpa [modeD] using this

/-! ## The left automaton, from the file -/

def nextD : List (List ℕ) :=
  (List.range 3).map (fun l =>
    (mLD l).next.filterMap (Handoff.leftModeIndex story1_attdist_rung_a_6to8_IR))

/-- `STEEP → [MODER, STEEP]`, `MODER → [FLAT, MODER]`, `FLAT → [FLAT]`. -/
theorem nextD_eq : nextD = [[1, 0], [2, 1], [2]] := by decide

theorem nextD_transitions :
    ((List.range 3).flatMap (fun m' => (nextD.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions story1_attdist_rung_a_6to8_IR := by decide

noncomputable def guardsD : List (Formula (Var 8)) :=
  (List.range 3).map (fun l => hostGuard vsD 8 Side.L (mLD l))

noncomputable def AD (dt : ℝ) : LeftAut 8 :=
  { windows := (List.range 3).map (fun l => windowSeg (leftBlock (fLD l)) domLD tgD dt 1),
    guards := guardsD,
    next := nextD }

theorem AD_numModes (dt : ℝ) : (AD dt).numModes = 3 := rfl

theorem AD_window (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AD dt).window t = windowSeg (leftBlock (fLD t)) domLD tgD dt 1 := by
  interval_cases t <;> rfl

theorem AD_guard (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AD dt).guard t = hostGuard vsD 8 Side.L (mLD t) := by
  interval_cases t <;> rfl

theorem AD_succ (dt : ℝ) (m' : ℕ) : (AD dt).succ m' = nextD.getD m' [] := rfl

theorem hnextD (dt : ℝ) : ∀ m' < (AD dt).numModes, ∀ t ∈ (AD dt).succ m', t < (AD dt).numModes := by
  intro m' hm' t ht
  rw [AD_numModes] at hm' ⊢
  rw [AD_succ, nextD_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hguardD (t : ℕ) (ht : t < 3) : (hostGuard vsD 8 Side.L (mLD t)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vsD (mLD t) ?_
  interval_cases t <;>
    simp [mLD, story1_attdist_rung_a_6to8_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem hgrdD (dt : ℝ) : ∀ t < (AD dt).numModes, ((AD dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [AD_numModes] at ht
  rw [AD_guard dt t ht]
  exact hguardD t ht

theorem hwinD (dt : ℝ) : ∀ t < (AD dt).numModes,
    Program.vars ((AD dt).window t) ⊆ {((Side.Aux, 1) : Var 8)} ∪ range Lv := by
  intro t ht
  rw [AD_numModes] at ht
  rw [AD_window dt t ht]
  exact vars_windowSegL_sub (fLD t) domLD 1 dt 1 (hfLD t ht) hdomLD

/-! ## Freshness of `u_L` -/

theorem hulenvD : ulD ∉ envD.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRD h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

theorem hulBkD : ulD ∉ (mvValid mvD GrD.modes.length).fv := fun h => by
  have := mvValid_fv_sub mvD GrD.modes.length h
  exact absurd (Set.mem_singleton_iff.mp this) (by decide)

theorem hulGD (dt : ℝ) : ∀ t, ulD ∉ ((AD dt).guard t).fv := by
  intro t h
  by_cases ht : t < 3
  · exact aux_notin_range_Lv 2 (hgrdD dt t ht h)
  · have : (AD dt).guard t = Formula.tt := by
      unfold LeftAut.guard AD guardsD
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUlD (dt : ℝ) : ∀ t, FramesMv ((AD dt).window t) ulD := by
  intro t
  by_cases ht : t < 3
  · rw [AD_window dt t ht]
    refine framesMv_window (leftBlock (fLD t)) domLD tgD dt 1 ulD (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD t) _ h
    exact aux_ne_Lv 2 i hi
  · have : (AD dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window AD
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulRD : ulD ∉ (rightAutomatonBody GrD mvD).bv :=
  notMem_bv_rightAutomatonBody GrD mvD ulD (by decide) (aux_notin_range_Rv 2) httD hRvD

/-! ## The handoff: nested rows, in-kernel -/

theorem handoffD (dt : ℝ) : ∀ m' < (AD dt).numModes, ∀ t ∈ (AD dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat envD ω → Formula.sat ((AD dt).guard t) ω → Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [AD_numModes] at hm'
  rw [AD_succ, nextD_eq] at ht
  have hm3 : m' < 3 := hm'
  interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl
  · -- STEEP → MODER: drop the `v` conjunct
    rw [FRow_one]; rw [FRow_zero] at hF
    exact FM_steep_common hF
  · exact hF
  · -- MODER → FLAT: identical rows
    rw [FRow_two]; rw [FRow_one] at hF; exact hF
  · exact hF
  · exact hF

/-! ## The per-mode steps -/

/-- The base instance's in-place step provider, restricted to one window `l` at the common
row (the MODER/FLAT rows), from that window's three packs. -/
theorem HmultiCommon (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv0 : VerdD l 0) (hv1 : VerdD l 1) (hv2 : VerdD l 2) :
    ∀ (q : ℕ), q < GrD.modes.length → ∀ σ, σ mvD = (q : ℝ) →
      Formula.sat (Formula.and (FM gD gsD) envD) σ →
      ∃ segs : List (ℕ × RMode (Var 8) × REdge (Var 8)),
        (∀ s ∈ segs, GrD.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrD.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 8))
          (windowSeg (leftBlock (fLD l)) domLD tgD dt 1)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gD gsD) envD)) σ := by
  intro q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrD] using hq
  have hhead1 : ∀ (a : ℕ × RMode (Var 8) × REdge (Var 8)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tgt : ℕ, st < 3 → tgt < 3 → edgeD st tgt ∈ GrD.edges →
      GrD.modeAt st = some (modeD st) ∧ edgeD st tgt ∈ GrD.edgesFrom st :=
    fun st tgt hs ht he => ⟨GrD_modeAt st hs, edgeD_mem st tgt he⟩
  interval_cases q
  · refine ⟨[(0, modeD 0, edgeD 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 0 0 (by norm_num) (by norm_num) (by simp [GrD])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondD l 0 hl (by norm_num) dt hdt hv0 [] (by simp) hσ
      simpa [modeD, List.replicate] using this
  · refine ⟨[(1, modeD 1, edgeD 1 1)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrD])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondD l 1 hl (by norm_num) dt hdt hv1 [] (by simp) hσ
      simpa [modeD, List.replicate] using this
  · refine ⟨[(2, modeD 2, edgeD 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrD])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondD l 2 hl (by norm_num) dt hdt hv2 [] (by simp) hσ
      simpa [modeD, List.replicate] using this

theorem hstepMD (dt : ℝ) (hdt : 0 ≤ dt)
    (hvS0 : VerdS 0) (hvS1 : VerdS 1) (hvS2 : VerdS 2)
    (hv10 : VerdD 1 0) (hv11 : VerdD 1 1) (hv12 : VerdD 1 2)
    (hv20 : VerdD 2 0) (hv21 : VerdD 2 1) (hv22 : VerdD 2 2) :
    ∀ t < (AD dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envD) (mvValid mvD GrD.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 8)) ((AD dt).window t)
      (Program.star (rightAutomatonBody GrD mvD))
      (Formula.and (Formula.and (FRow t) envD) (mvValid mvD GrD.modes.length))) σ := by
  intro t ht
  rw [AD_numModes] at ht
  rw [AD_window dt t ht]
  have hframe : FramesMv (windowSeg (leftBlock (fLD t)) domLD tgD dt 1) mvD := by
    refine framesMv_window (leftBlock (fLD t)) domLD tgD dt 1 mvD (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD t) _ h
    exact aux_ne_Lv 0 i hi
  interval_cases t
  · rw [FRow_zero]
    exact hstepMode_multiF GrD mvD (FM gS gsS) envD _ htgFS_mv hmvenvD hfreshD httD hltD hframe
      (HmultiS dt hdt hvS0 hvS1 hvS2)
  · rw [FRow_one]
    exact hstepMode_multiF GrD mvD (FM gD gsD) envD _ hmvFD hmvenvD hfreshD httD hltD hframe
      (HmultiCommon 1 (by norm_num) dt hdt hv10 hv11 hv12)
  · rw [FRow_two]
    exact hstepMode_multiF GrD mvD (FM gD gsD) envD _ hmvFD hmvenvD hfreshD httD hltD hframe
      (HmultiCommon 2 (by norm_num) dt hdt hv20 hv21 hv22)

/-! ## The composed theorem -/

/-- **`story1_attdist_rung_a_6to8`, Theorem 3 at the DECLARED mode-dependent invariant.**
`u_L`-keyed: the STEEP window at `v[l] ≤ v[r] ∧ D_ψ ∧ D_θ`, the MODER and FLAT windows at
`D_ψ ∧ D_θ`, over the left automaton `STEEP → MODER → FLAT` (with self-loops). Residuals:
the three STEEP packs `VerdS` and the six MODER/FLAT packs `VerdD`. -/
theorem story1_attdist_rung_a_modeKeyed (dt : ℝ) (hdt : 0 ≤ dt)
    (hvS0 : VerdS 0) (hvS1 : VerdS 1) (hvS2 : VerdS 2)
    (hv10 : VerdD 1 0) (hv11 : VerdD 1 1) (hv12 : VerdD 1 2)
    (hv20 : VerdD 2 0) (hv21 : VerdD 2 1) (hv22 : VerdD 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AD dt) ulD)
      (rightAutomatonBody GrD mvD)
      (psiK ulD ϕRow (AD dt).numModes domLD domRD
        (mvValidR mvD GrD.modes.length))) := by
  refine theorem3_modeKeyed (AD dt) ulD GrD mvD FRow ϕRow domLD domRD
    (mvValid mvD GrD.modes.length) (mvValidR mvD GrD.modes.length)
    encode_ϕRow (encode_mvValidR _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (AD dt) GrD 0 1 2 (by decide) (by decide) (hwinD dt) (hgrdD dt)
      (hnextD dt) httD hRvD
  · exact hstep_modeKeyed (AD dt) ulD (rightAutomatonBody GrD mvD) FRow envD
      (mvValid mvD GrD.modes.length) (aux_notin_FRow 2) hulenvD hulBkD (hulGD dt)
      (hframesUlD dt) hulRD (hnextD dt)
      (hstepMD dt hdt hvS0 hvS1 hvS2 hv10 hv11 hv12 hv20 hv21 hv22) (handoffD dt)
  · exact hddF_modeKeyed (AD dt) GrD 0 1 2 (by decide) (by decide) ϕRow domLD domRD
      (mvValidR mvD GrD.modes.length) (hwinD dt) (hgrdD dt) (hnextD dt) httD hRvD
      (fun m _ => canonInvM_varsL (gRowAt m 0) (rowGs m) (fun g' hg' => by
        obtain ⟨i, rfl⟩ := mem_rowGs hg'
        exact hgRowAt m i))
      (fun m _ => canonInvM_varsR (gRowAt m 0) (rowGs m)) hdomLD hdomRD rfl
      (fun v hv => Or.inl (mvValid_fv_sub mvD GrD.modes.length hv))

end Story1AttdistRungAHandoff
end RelCertifier
