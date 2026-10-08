/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` — the DECLARED mode-dependent invariant, composed

`Story3RolloverRungBModal.story3_rollover_rung_b_modal` states Theorem 3 at the rows'
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

Residuals: the base instance's nine `VerdV` packs for the `MODER`/`FLAT` windows (six
used) plus three `VerdS` packs — every one re-run by `relcert --run-verdicts` and pinned
to the runner's query in `Verdicts/ModalPinTable.lean`.
-/
import RelCertifier.Instances.Story3RolloverRungBModal
import RelCertifier.Proofs.Encoding.ModeHandoff

namespace RelCertifier
namespace Story3RolloverRungBHandoff

open DL DLCalTiming DLRel Parse Set Story3RolloverRungBModal

set_option maxHeartbeats 12800000

/-- The left mode variable — the third auxiliary (`mv = (Aux, 0)`, `tg = (Aux, 1)`). -/
abbrev ulV : Var 12 := (Side.Aux, 2)

/-! ## The declared rows -/

def invRowPF (r : ℕ) : Parse.PForm :=
  (story3_rollover_ladder_rung_b_IR.invariants.getD r ("", Parse.PForm.tt)).2

noncomputable def gRowAt (r i : ℕ) : Term (Var 12) :=
  ((Run.invToG vsV 12 ((atomsOf (invRowPF r)).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

/-- The STEEP row's components, in the stratified order the runner checks: `v`, `ψ`, `θ`. -/
noncomputable def gS : Term (Var 12) := gRowAt 0 0
noncomputable def gsS : List (Term (Var 12)) := [gRowAt 0 1, gRowAt 0 2]

/-- Row `r`'s component list: STEEP has three, the others two. -/
noncomputable def rowGs (r : ℕ) : List (Term (Var 12)) :=
  if r = 0 then gsS else [gRowAt r 1]

noncomputable def FRow (r : ℕ) : Formula (Var 12) := FM (gRowAt r 0) (rowGs r)
noncomputable def ϕRow (r : ℕ) : RFormula (Var 12) := canonInvM (gRowAt r 0) (rowGs r)

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 12)) (ϕRow r) = FRow r :=
  encode_canonInvM _ _

/-- The MODER row is the base instance's row (`invariants.getD 1`), term for term. -/
theorem gRowAt_one_zero : gRowAt 1 0 = gV := rfl
theorem gRowAt_one_one : gRowAt 1 1 = gAt 1 := rfl

/-- The FLAT row is syntactically the MODER row. -/
theorem atoms_two_zero : (atomsOf (invRowPF 2)).getD 0 .tt = (atomsOf invVPF).getD 0 .tt := by
  decide
theorem atoms_two_one : (atomsOf (invRowPF 2)).getD 1 .tt = (atomsOf invVPF).getD 1 .tt := by
  decide
theorem gRowAt_two_zero : gRowAt 2 0 = gV := by
  unfold gRowAt gV gAt; rw [atoms_two_zero]
theorem gRowAt_two_one : gRowAt 2 1 = gAt 1 := by
  unfold gRowAt gAt; rw [atoms_two_one]

/-- STEEP's second and third components are the common row's two. -/
theorem atoms_zero_one : (atomsOf (invRowPF 0)).getD 1 .tt = (atomsOf invVPF).getD 0 .tt := by
  decide
theorem atoms_zero_two : (atomsOf (invRowPF 0)).getD 2 .tt = (atomsOf invVPF).getD 1 .tt := by
  decide
theorem gRowAt_zero_one : gRowAt 0 1 = gV := by
  unfold gRowAt gV gAt; rw [atoms_zero_one]
theorem gRowAt_zero_two : gRowAt 0 2 = gAt 1 := by
  unfold gRowAt gAt; rw [atoms_zero_two]

theorem FRow_one : FRow 1 = FM gV gsV := rfl
theorem FRow_two : FRow 2 = FM gV gsV := by
  unfold FRow rowGs; simp only [show (2:ℕ) ≠ 0 by decide, if_false]
  rw [gRowAt_two_zero, gRowAt_two_one]; rfl
theorem FRow_zero : FRow 0 = FM gS gsS := rfl

theorem hgRowAt (r i : ℕ) : (gRowAt r i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem aux_notin_gRowAt (a : Fin 12) (r i : ℕ) : ((Side.Aux, a) : Var 12) ∉ (gRowAt r i).fv := by
  intro h
  rcases hgRowAt r i h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem mem_rowGs {r : ℕ} {g : Term (Var 12)} (hg : g ∈ gRowAt r 0 :: rowGs r) :
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

theorem aux_notin_FRow (a : Fin 12) (r : ℕ) : ((Side.Aux, a) : Var 12) ∉ (FRow r).fv :=
  notMem_FM_fv (fun g' hg' => by
    obtain ⟨i, rfl⟩ := mem_rowGs hg'
    exact aux_notin_gRowAt a r i)

theorem htggS : ∀ g' ∈ gS :: gsS, tgV ∉ g'.fv := by
  intro g' hg'
  simp only [gS, gsS, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl <;> exact aux_notin_gRowAt 1 0 _

theorem htgFS : tgV ∉ (FM gS gsS).fv := notMem_FM_fv htggS

theorem htgFS_mv : mvV ∉ (FM gS gsS).fv :=
  notMem_FM_fv (fun g' hg' => by
    simp only [gS, gsS, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl <;> exact aux_notin_gRowAt 0 0 _)

/-- STEEP's row implies the common row (its last two components). -/
theorem FM_steep_common {ν : State (Var 12)} (h : Formula.sat (FM gS gsS) ν) :
    Formula.sat (FM gV gsV) ν := by
  refine FM_mono ?_ h
  intro g hg
  simp only [gsV, List.mem_cons, List.not_mem_nil, or_false] at hg
  simp only [gS, gsS, List.mem_cons, List.not_mem_nil, or_false]
  rcases hg with rfl | rfl
  · exact Or.inr (Or.inl gRowAt_zero_one.symm)
  · exact Or.inr (Or.inr gRowAt_zero_two.symm)

/-! ## The STEEP window at its own row: verdicts, coupling, response -/

/-- The three-component STEEP pack against right mode `m`, at λ = 1, in the stratified
order (`v` first, then the two energies). -/
def VerdS (m : ℕ) : Prop :=
  ∀ i (hi : i < (gS :: gsS).length),
    z3solve (flowQuery ⟨(gS :: gsS)[i], fLV 0, fRV m, Term.const (1),
      strataDomHost (Formula.and domLV domRV) ((gS :: gsS).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(gS :: gsS)[i], fLV 0, fRV m, Term.const (1),
      strataDomHost (Formula.and domLV domRV) ((gS :: gsS).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(gS :: gsS)[i], fLV 0, fRV m, Term.const (1),
      strataDomHost (Formula.and domLV domRV) ((gS :: gsS).take i)⟩) = Verdict.unsat

theorem coupleS (m : ℕ) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdS m) :
    ∀ σ', Formula.sat (Formula.and (FM gS gsS) envV) σ' → σ' tgV = 0 →
      faModalB (Equiv.refl (Var 12))
        (Program.ode (DLCalTiming.clk tgV (leftBlock (fLV 0))) domLV)
        (Program.ode (rightBlock (fRV m) (Term.const (1))) domRV)
        (Formula.and (FM gS gsS) envV) tgV dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgV (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgV
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLV 0) (fRV m) (Term.const (1))
    (Formula.and domLV domRV) (gS :: gsS) hv
  have hboxes : ∀ g' ∈ gS :: gsS, Formula.sat (Formula.box (Program.ode
      (leftBlock (fLV 0) ++ rightBlock (fRV m) (Term.const (1)))
      (Formula.and domLV domRV)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff gS gsS σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list gS gsS (fLV 0) (fRV m)
    (Term.const (1)) domLV domRV tgV dt
    (LR_blocks_disjoint _ _ _ (hfLV 0 (by norm_num)) (hfRV m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLV hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRV hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLV 0) _ h
      exact aux_ne_Lv aV i hi)
    (fun h => aux_notin_range_Lv aV (leftBlock_readVars_sub (fLV 0) (hfLV 0 (by norm_num)) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRV m) (Term.const (1)) _ h
      exact aux_ne_Rv aV i hi)
    (fun h => aux_notin_range_Rv aV (rightBlock_readVars_sub (fRV m)
      (Term.const (1)) (hfRV m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aV (rightBlock_boundSet_sub (fRV m)
      (Term.const (1)) h))
    (fun h => aux_notin_range_Lv aV (hdomLV h))
    (fun h => aux_notin_range_Rv aV (hdomRV h))
    htggS hboxes
    (esV 0 m (by norm_num) hm dt hdt σ' ⟨FM_steep_common hσ'.1, hσ'.2⟩)
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLV ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRV μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLV μ := by
    rwa [(Formula.coincidence domLV (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLV hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRV m) (Term.const (1)) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLV μ ↔ Formula.sat domLV ν)]
  exact ⟨hdomLμ, hdomRμ⟩

theorem couple1S (m : ℕ) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdS m) :
    ∀ σ, Formula.sat (Formula.and (FM gS gsS) envV) σ →
      faModalB (Equiv.refl (Var 12))
        (Program.ode (DLCalTiming.clk tgV (leftBlock (fLV 0))) domLV)
        (Program.ode (rightBlock (fRV m) (Term.const 1)) domRV) (Formula.and (FM gS gsS) envV) tgV dt
        (Function.update σ tgV 0) := by
  intro σ hσ
  have htgφ : tgV ∉ (Formula.and (FM gS gsS) envV).fv := by
    intro h
    rcases h with h | h
    · exact htgFS h
    · exact htgenvV h
  have hupdφ : Formula.sat (Formula.and (FM gS gsS) envV)
      (Function.update σ tgV 0) := by
    rwa [(Formula.coincidence (Formula.and (FM gS gsS) envV) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (FM gS gsS) envV) _ ↔ _)]
  refine faModalB_monoQ ?_ (coupleS m hm dt hdt hv
    (Function.update σ tgV 0) hupdφ (Function.update_self _ _ _))
  intro ν μ hsem
  exact sem_rightBlock_reparam (1) 1 (by norm_num) one_pos hsem

theorem respondS (m : ℕ) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdS m)
    {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FM gS gsS) envV) σ) :
    Formula.sat (faModal (Equiv.refl (Var 12))
      (windowSeg (leftBlock (fLV 0)) domLV tgV dt 1)
      (bigSeq [Program.ode (rightBlock (fRV m) (Term.const 1)) domRV])
      (Formula.and (FM gS gsS) envV)) σ := by
  have hfa := Hmulti_windowRF_prefixed (fLV 0) domLV (FM gS gsS) envV
    aV dt 1 htgFS htgenvV [] (by simp) (fun σ' hσ' => hσ'.2.1) (by simp)
    (hfLV 0 (by norm_num)) hdomLV
    (List.replicate 1 (Program.ode (rightBlock (fRV m) (Term.const 1)) domRV)) (by simp) (by norm_num)
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ, Program.rename_refl]
      exact hdisH_progR (⟨fRV m, Term.const 1, domRV⟩ : RepoHop 12)
        (hfRV m hm) (by simp [Term.fv]) hdomRV (hfLV 0 (by norm_num)) hdomLV)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact couple1S m hm dt hdt hv σ' hσ')
    hσ
  simpa [List.replicate] using hfa

/-- The STEEP window's step provider: in place at the current right mode. -/
theorem HmultiS (dt : ℝ) (hdt : 0 ≤ dt) (hv0 : VerdS 0) (hv1 : VerdS 1) (hv2 : VerdS 2) :
    ∀ (q : ℕ), q < GrV.modes.length → ∀ σ, σ mvV = (q : ℝ) →
      Formula.sat (Formula.and (FM gS gsS) envV) σ →
      ∃ segs : List (ℕ × RMode (Var 12) × REdge (Var 12)),
        (∀ s ∈ segs, GrV.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrV.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 12))
          (windowSeg (leftBlock (fLV 0)) domLV tgV dt 1)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gS gsS) envV)) σ := by
  intro q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrV] using hq
  have hhead1 : ∀ (a : ℕ × RMode (Var 12) × REdge (Var 12)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tgt : ℕ, st < 3 → tgt < 3 → edgeV st tgt ∈ GrV.edges →
      GrV.modeAt st = some (modeV st) ∧ edgeV st tgt ∈ GrV.edgesFrom st :=
    fun st tgt hs ht he => ⟨GrV_modeAt st hs, edgeV_mem st tgt he⟩
  interval_cases q
  · refine ⟨[(0, modeV 0, edgeV 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 0 0 (by norm_num) (by norm_num) (by simp [GrV])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondS 0 (by norm_num) dt hdt hv0 hσ
      simpa [modeV] using this
  · refine ⟨[(1, modeV 1, edgeV 1 1)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrV])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondS 1 (by norm_num) dt hdt hv1 hσ
      simpa [modeV] using this
  · refine ⟨[(2, modeV 2, edgeV 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrV])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondS 2 (by norm_num) dt hdt hv2 hσ
      simpa [modeV] using this

/-! ## The left automaton, from the file -/

def nextV : List (List ℕ) :=
  (List.range 3).map (fun l =>
    (mLV l).next.filterMap (Handoff.leftModeIndex story3_rollover_ladder_rung_b_IR))

/-- `STEEP → [MODER, STEEP]`, `MODER → [FLAT, MODER]`, `FLAT → [FLAT]`. -/
theorem nextV_eq : nextV = [[1, 0], [2, 1], [2]] := by decide

theorem nextV_transitions :
    ((List.range 3).flatMap (fun m' => (nextV.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions story3_rollover_ladder_rung_b_IR := by decide

noncomputable def guardsV : List (Formula (Var 12)) :=
  (List.range 3).map (fun l => hostGuard vsV 12 Side.L (mLV l))

noncomputable def AV (dt : ℝ) : LeftAut 12 :=
  { windows := (List.range 3).map (fun l => windowSeg (leftBlock (fLV l)) domLV tgV dt 1),
    guards := guardsV,
    next := nextV }

theorem AV_numModes (dt : ℝ) : (AV dt).numModes = 3 := rfl

theorem AV_window (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AV dt).window t = windowSeg (leftBlock (fLV t)) domLV tgV dt 1 := by
  interval_cases t <;> rfl

theorem AV_guard (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AV dt).guard t = hostGuard vsV 12 Side.L (mLV t) := by
  interval_cases t <;> rfl

theorem AV_succ (dt : ℝ) (m' : ℕ) : (AV dt).succ m' = nextV.getD m' [] := rfl

theorem hnextV (dt : ℝ) : ∀ m' < (AV dt).numModes, ∀ t ∈ (AV dt).succ m', t < (AV dt).numModes := by
  intro m' hm' t ht
  rw [AV_numModes] at hm' ⊢
  rw [AV_succ, nextV_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hguardV (t : ℕ) (ht : t < 3) : (hostGuard vsV 12 Side.L (mLV t)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vsV (mLV t) ?_
  interval_cases t <;>
    simp [mLV, story3_rollover_ladder_rung_b_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem hgrdV (dt : ℝ) : ∀ t < (AV dt).numModes, ((AV dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [AV_numModes] at ht
  rw [AV_guard dt t ht]
  exact hguardV t ht

theorem hwinV (dt : ℝ) : ∀ t < (AV dt).numModes,
    Program.vars ((AV dt).window t) ⊆ {((Side.Aux, 1) : Var 12)} ∪ range Lv := by
  intro t ht
  rw [AV_numModes] at ht
  rw [AV_window dt t ht]
  exact vars_windowSegL_sub (fLV t) domLV 1 dt 1 (hfLV t ht) hdomLV

/-! ## Freshness of `u_L` -/

theorem hulenvV : ulV ∉ envV.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLV h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRV h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

theorem hulBkV : ulV ∉ (mvValid mvV GrV.modes.length).fv := fun h => by
  have := mvValid_fv_sub mvV GrV.modes.length h
  exact absurd (Set.mem_singleton_iff.mp this) (by decide)

theorem hulGV (dt : ℝ) : ∀ t, ulV ∉ ((AV dt).guard t).fv := by
  intro t h
  by_cases ht : t < 3
  · exact aux_notin_range_Lv 2 (hgrdV dt t ht h)
  · have : (AV dt).guard t = Formula.tt := by
      unfold LeftAut.guard AV guardsV
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUlV (dt : ℝ) : ∀ t, FramesMv ((AV dt).window t) ulV := by
  intro t
  by_cases ht : t < 3
  · rw [AV_window dt t ht]
    refine framesMv_window (leftBlock (fLV t)) domLV tgV dt 1 ulV (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLV t) _ h
    exact aux_ne_Lv 2 i hi
  · have : (AV dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window AV
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulRV : ulV ∉ (rightAutomatonBody GrV mvV).bv :=
  notMem_bv_rightAutomatonBody GrV mvV ulV (by decide) (aux_notin_range_Rv 2) httV hRvV

/-! ## The handoff: nested rows, in-kernel -/

theorem handoffV (dt : ℝ) : ∀ m' < (AV dt).numModes, ∀ t ∈ (AV dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat ((AV dt).guard t) ω → Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _
  rw [AV_numModes] at hm'
  rw [AV_succ, nextV_eq] at ht
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
    (hv0 : VerdV l 0) (hv1 : VerdV l 1) (hv2 : VerdV l 2) :
    ∀ (q : ℕ), q < GrV.modes.length → ∀ σ, σ mvV = (q : ℝ) →
      Formula.sat (Formula.and (FM gV gsV) envV) σ →
      ∃ segs : List (ℕ × RMode (Var 12) × REdge (Var 12)),
        (∀ s ∈ segs, GrV.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrV.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 12))
          (windowSeg (leftBlock (fLV l)) domLV tgV dt 1)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM gV gsV) envV)) σ := by
  intro q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrV] using hq
  have hhead1 : ∀ (a : ℕ × RMode (Var 12) × REdge (Var 12)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tgt : ℕ, st < 3 → tgt < 3 → edgeV st tgt ∈ GrV.edges →
      GrV.modeAt st = some (modeV st) ∧ edgeV st tgt ∈ GrV.edgesFrom st :=
    fun st tgt hs ht he => ⟨GrV_modeAt st hs, edgeV_mem st tgt he⟩
  interval_cases q
  · refine ⟨[(0, modeV 0, edgeV 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 0 0 (by norm_num) (by norm_num) (by simp [GrV])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondV l 0 hl (by norm_num) dt hdt hv0 [] (by simp) hσ
      simpa [modeV, List.replicate] using this
  · refine ⟨[(1, modeV 1, edgeV 1 1)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrV])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondV l 1 hl (by norm_num) dt hdt hv1 [] (by simp) hσ
      simpa [modeV, List.replicate] using this
  · refine ⟨[(2, modeV 2, edgeV 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrV])
    · simp
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondV l 2 hl (by norm_num) dt hdt hv2 [] (by simp) hσ
      simpa [modeV, List.replicate] using this

theorem hstepMV (dt : ℝ) (hdt : 0 ≤ dt)
    (hvS0 : VerdS 0) (hvS1 : VerdS 1) (hvS2 : VerdS 2)
    (hv10 : VerdV 1 0) (hv11 : VerdV 1 1) (hv12 : VerdV 1 2)
    (hv20 : VerdV 2 0) (hv21 : VerdV 2 1) (hv22 : VerdV 2 2) :
    ∀ t < (AV dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envV) (mvValid mvV GrV.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 12)) ((AV dt).window t)
      (Program.star (rightAutomatonBody GrV mvV))
      (Formula.and (Formula.and (FRow t) envV) (mvValid mvV GrV.modes.length))) σ := by
  intro t ht
  rw [AV_numModes] at ht
  rw [AV_window dt t ht]
  have hframe : FramesMv (windowSeg (leftBlock (fLV t)) domLV tgV dt 1) mvV := by
    refine framesMv_window (leftBlock (fLV t)) domLV tgV dt 1 mvV (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLV t) _ h
    exact aux_ne_Lv 0 i hi
  interval_cases t
  · rw [FRow_zero]
    exact hstepMode_multiF GrV mvV (FM gS gsS) envV _ htgFS_mv hmvenvV hfreshV httV hltV hframe
      (HmultiS dt hdt hvS0 hvS1 hvS2)
  · rw [FRow_one]
    exact hstepMode_multiF GrV mvV (FM gV gsV) envV _ hmvFV hmvenvV hfreshV httV hltV hframe
      (HmultiCommon 1 (by norm_num) dt hdt hv10 hv11 hv12)
  · rw [FRow_two]
    exact hstepMode_multiF GrV mvV (FM gV gsV) envV _ hmvFV hmvenvV hfreshV httV hltV hframe
      (HmultiCommon 2 (by norm_num) dt hdt hv20 hv21 hv22)

/-! ## The composed theorem -/

/-- **`story3_rollover_ladder_rung_b`, Theorem 3 at the DECLARED mode-dependent invariant.**
`u_L`-keyed: the STEEP window at `v[l] ≤ v[r] ∧ D_ψ ∧ D_θ`, the MODER and FLAT windows at
`D_ψ ∧ D_θ`, over the left automaton `STEEP → MODER → FLAT` (with self-loops). Residuals:
the three STEEP packs `VerdS` and the six MODER/FLAT packs `VerdV`. -/
theorem story3_rollover_rung_b_modeKeyed (dt : ℝ) (hdt : 0 ≤ dt)
    (hvS0 : VerdS 0) (hvS1 : VerdS 1) (hvS2 : VerdS 2)
    (hv10 : VerdV 1 0) (hv11 : VerdV 1 1) (hv12 : VerdV 1 2)
    (hv20 : VerdV 2 0) (hv21 : VerdV 2 1) (hv22 : VerdV 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AV dt) ulV)
      (rightAutomatonBody GrV mvV)
      (psiK ulV ϕRow (AV dt).numModes domLV domRV
        (mvValidR mvV GrV.modes.length))) := by
  refine theorem3_modeKeyed (AV dt) ulV GrV mvV FRow ϕRow domLV domRV
    (mvValid mvV GrV.modes.length) (mvValidR mvV GrV.modes.length)
    encode_ϕRow (encode_mvValidR _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (AV dt) GrV 0 1 2 (by decide) (by decide) (hwinV dt) (hgrdV dt)
      (hnextV dt) httV hRvV
  · exact hstep_modeKeyed (AV dt) ulV (rightAutomatonBody GrV mvV) FRow envV
      (mvValid mvV GrV.modes.length) (aux_notin_FRow 2) hulenvV hulBkV (hulGV dt)
      (hframesUlV dt) hulRV (hnextV dt)
      (hstepMV dt hdt hvS0 hvS1 hvS2 hv10 hv11 hv12 hv20 hv21 hv22) (handoffV dt)
  · exact hddF_modeKeyed (AV dt) GrV 0 1 2 (by decide) (by decide) ϕRow domLV domRV
      (mvValidR mvV GrV.modes.length) (hwinV dt) (hgrdV dt) (hnextV dt) httV hRvV
      (fun m _ => canonInvM_varsL (gRowAt m 0) (rowGs m) (fun g' hg' => by
        obtain ⟨i, rfl⟩ := mem_rowGs hg'
        exact hgRowAt m i))
      (fun m _ => canonInvM_varsR (gRowAt m 0) (rowGs m)) hdomLV hdomRV rfl
      (fun v hv => Or.inl (mvValid_fv_sub mvV GrV.modes.length hv))

end Story3RolloverRungBHandoff
end RelCertifier
