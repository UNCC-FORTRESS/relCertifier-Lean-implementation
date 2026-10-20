/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge at strict rows: Theorem 3 from the records (extension `strict-atoms`)

`theorem3_keyed_strict_of_records` and `theorem3_window_strict_of_records`: the mode-keyed and
one-row Theorem 3 of a benchmark whose rows may contain strict atoms, the statement carrying
the strict rows (`ϕRowS`, `canonInvMS`). The verdicts (`VerdictsS`) are the existing ones
except the flow packs (`JointVerdS`: a strict component's group is [route A, route B]) and the
handoffs (`HandoffVerdS`: the target row negated with its strictness). Admissibility, stays,
non-connection, reposition packs, progress and coverage are the existing verdicts: there the
row is only an assumption, read through the weakening `FMS → FM`.

Collapse: for a benchmark without strict atoms (`noStrictRows`, decidable) the strict claims
are the existing claims (`keyedClaimS_iff`, `windowClaimS_iff`) and the existing verdicts are
the strict ones (`VerdictsS.ofVerdicts`), so the existing theorems are the special case.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.StrictAnchor
import RelCertifier.Proofs.Encoding.Theorem3GeneralS

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLRel DLCalTiming Parse Run Set Oracle Progress Choice

variable {n : ℕ}

section Defs

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
  (prog : ProgressEmitE) (ce : ChoiceEmitE)

def JointAllS : Prop :=
  ∀ l < nL p, ∀ q < nR p, (flagsOf p cov l q).jointOK = true → JointVerdS p n cX cov l q
def HandoffAllS : Prop := ∀ m' < nL p, ∀ t ∈ (nextL p).getD m' [], HandoffVerdS p n (m', t)

/-- Every verdict a benchmark's instance rests on, at strict rows. -/
structure VerdictsS : Prop where
  stay : StayAll p n cX
  nonconn : NonConnAll p n cX cov
  joint : JointAllS p n cX cov
  dyn : DynAll p n cX cov
  adm : AdmAll p n cov
  handoff : HandoffAllS p n
  prog : ProgAll p n cX prog
  coverage : CoverageAll p n cX ce

/-- No declared row has a strict atom (decided in the kernel). -/
def noStrictRows : Bool :=
  p.invariants.all (fun kv => (hostFlags (vars p) n kv.2).all (fun b => !b))

end Defs

/-! ## Collapse -/

section Collapse

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  {ce : ChoiceEmitE}

theorem hostFlags_tt (vars : List String) : hostFlags vars n PForm.tt = [] := rfl

theorem maskOf_allFalse (h : noStrictRows p n = true) (l : ℕ) :
    ∀ b ∈ maskOf p n l, b = false := by
  simp only [noStrictRows, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  intro b hb
  unfold maskOf rowOf at hb
  by_cases hl : rowIdx p l < p.invariants.length
  · rw [List.getD_eq_getElem _ _ hl] at hb
    exact h _ (List.getElem_mem hl) b hb
  · rw [List.getD_eq_default _ _ (by omega)] at hb
    simp [hostFlags_tt] at hb

theorem invRow_allFalse (h : noStrictRows p n = true) {m : PMode} {rowT : PForm}
    (hT : Handoff.invRowOf p m = some rowT) :
    ∀ fs, invStrictFlags p.L.stateVars n rowT = some fs → ∀ b ∈ fs, b = false := by
  simp only [noStrictRows, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  intro fs hfs b hb
  unfold Handoff.invRowOf at hT
  obtain ⟨kv, hkv, rfl⟩ := Option.map_eq_some_iff.mp hT
  have hmem := List.mem_of_find?_eq_some hkv
  have := h kv hmem b
  rw [show hostFlags (vars p) n kv.2 = fs from hostFlags_of_lower hfs] at this
  exact this hb

/-- The existing verdicts are the strict ones for a benchmark without strict atoms. -/
theorem VerdictsS.ofVerdicts (h : noStrictRows p n = true) (hv : Verdicts p n cX cov prog ce) :
    VerdictsS p n cX cov prog ce where
  stay := hv.stay
  nonconn := hv.nonconn
  joint := fun l hl q hq hj => jointVerdS_of_allFalse (maskOf_allFalse h l) (hv.joint l hl q hq hj)
  dyn := hv.dyn
  adm := hv.adm
  handoff := fun m' hm' t ht =>
    handoffVerdS_of_allFalse (fun _ hS => invRow_allFalse h hS) (fun _ hT => invRow_allFalse h hT)
      (hv.handoff m' hm' t ht)
  prog := hv.prog
  coverage := hv.coverage

end Collapse

section Proofs

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  {ce : ChoiceEmitE} (hs : structOK p n cov cX = true)

include hs

theorem AGS_fv_any {l : ℕ} (hl : l < nL p) (q : ℕ) :
    (AGS p n cX cov l q).fv ⊆ range Lv ∪ range Rv := by
  rw [AGS_fv_eq]; exact AG_fv_any hs hl q

theorem AGrS_fv_any {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv) {l : ℕ} (hl : l < nL p)
    (q : ℕ) : (AGrS p n cX cov reg l q).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  rcases hv with hv | hv
  · exact AGS_fv_any hs hl q hv
  · exact Or.inr (hregR hv)

theorem AGS_post_any {l : ℕ} (hl : l < nL p) (q : ℕ) (y : State (Var n))
    (h : Formula.sat (AGS p n cX cov l q) y) :
    Formula.sat (Formula.and (Formula.and (FRowS p n l) (env p n)) (cuts p n cX q)) y := by
  obtain ⟨hFA, -⟩ := (sat_FMS_append _ _ _ _ (maskOf_len_app _) y).mp h.1
  obtain ⟨hF, hat⟩ := (sat_FMS_append _ _ _ _ (maskOf_len p n l) y).mp hFA
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL hs hl) (hiffR_any hs q) y).mp hat
  exact ⟨⟨hF, h.2⟩, (sat_cutF _ _).mpr hR⟩

omit hs in
theorem FRowS_fv_any (l : ℕ) : (FRowS p n l).fv ⊆ range Lv ∪ range Rv := by
  rw [FRowS_fv_eq]; exact FRow_fv_any l

/-- `cov_of_entry`, from the coverage verdicts alone. -/
theorem cov_of_entryS (hcovg : CoverageAll p n cX ce) (hpo : progOK p n cov prog = true)
    {l q : ℕ} (hl : l < nL p) {k : ChoiceKind} {pre : Bool} {S : List ℕ}
    (hS : S ∈ (entriesAt p ce l q k pre).map (fun e => e.S.map (tgtIdx p)))
    (y : State (Var n)) (hreg : q < nR p → Formula.sat (regionF p n cX l q (if k = .joint then false else pre)) y)
    (hg : k = .hop → Formula.sat (guardR p n q) y) :
    ∃ q' ∈ S, Formula.sat (guardR p n q') y := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hS
  obtain ⟨hq, hmem, hmL, hq', hk, hpre⟩ := mem_entriesAt he
  obtain ⟨hidxL, hidxR, -⟩ := progOK_at hpo hl hq
  have hpre' : entryPre e = (if k = .joint then false else pre) := by
    unfold entryPre
    rcases hpre with rfl | rfl
    · simp [hk]
    · rcases hk' : e.kind <;> simp_all
  refine guard_of_named hs hmL hq' hidxL hidxR (hcovg e hmem) y ?_ (fun hh => hg (hk ▸ hh))
  rw [hpre']
  exact regionSat_of_regionF hs hl _ y (hreg hq)

/-- **The certificates of window `l` at its strict row**, as `CoverHyps` (anchor `AGrS`). -/
theorem coverHyps_ofS (hv : VerdictsS p n cX cov prog ce) (hpo : progOK p n cov prog = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p)) {l : ℕ}
    (hl : l < nL p) :
    CoverHyps (grOf p n (prunedOf cov)) (chOfC p cov ce l) (fR p n) (domR p n) (fL p n l) (domL p n)
      (guardL p n l) (guardR p n) (epsR p) (δ p cov l) (lamOf p cov l) (AGrS p n cX cov reg l)
      (RJof p n cX l) (RRof p n cX l) (RSof p n cX l) where
  hδ := δ_pos hs hl
  hlam := lamOf_pos hs hl
  hspan := lamOf_span hs hl
  hAfv := AGrS_fv_any hs hregR hl
  hAdom := fun q y h => h.1.2.2
  hbox := fun q m hm hj σ ω hA hω => by
    obtain ⟨hq, -⟩ := grOf_modeAt_inv hm
    rw [lamOf_eq hq] at hω
    exact ⟨AGS_box hs hv.nonconn hv.stay hl hq (by simpa [chOfC] using hj)
      (hv.joint l hl q hq (by simpa [chOfC] using hj)) σ ω hA.1 hω,
      reg_kept_joint hinv hregR (fR_fv (hnames hs) q) (domR_fv (hnames hs)) hm (grOf_sys hm)
        (grOf_dom hm) _ (lam_pos hs hl hq) hω hA.2⟩
  hhand := fun q e he y hA hleg => by
    obtain ⟨hq, -, -, -⟩ := edgesFrom_grOf he
    exact ⟨AGS_hand hs hv.nonconn hl hq e he y hA.1 hleg, hA.2⟩
  hprune := fun q m hm e he hp σ ω hA hω => by
    obtain ⟨hq, -⟩ := grOf_modeAt_inv hm
    rw [lamOf_eq hq] at hω
    exact AGS_prune hs hv.nonconn hv.stay hl hq e he hp σ ω hA.1 hω
  hrepoProg := fun q m hm pre hflag =>
    hrepoProg_ofS hs hv.nonconn hv.stay hv.prog hpo hregR hinv hwf hv.dyn hl q m hm pre
      (by cases pre <;> simpa [chOfC, chOf] using hflag)
  hRJ := fun q y hA => by
    unfold RJof; split_ifs with hq
    · exact AGS_regionF hs hl hq false y hA.1 (by simp)
    · trivial
  hcovJ := fun q S hS y hy => by
    refine cov_of_entryS hs hv.coverage hpo hl hS y (fun hq => ?_) (by simp)
    unfold RJof at hy; rw [if_pos hq] at hy; simpa using hy
  hRR := fun q σ y hA hgL => by
    unfold RRof; split_ifs with hq
    · exact AGS_regionF hs hl hq (preOf σ) y hA.1 (fun hp => hgL (by cases σ <;> simp_all [preOf]))
    · trivial
  hcovR := fun q σ S hS y hy => by
    refine cov_of_entryS hs hv.coverage hpo hl hS y (fun hq => ?_) (by simp)
    unfold RRof at hy; rw [if_pos hq] at hy; simpa using hy
  hRS := fun q σ y hA hg hgL => by
    unfold RSof; split_ifs with hq
    · exact ⟨AGS_regionF hs hl hq (preOf σ) y hA.1 (fun hp => hgL (by cases σ <;> simp_all [preOf])), hg⟩
    · trivial
  hcovS := fun q σ S hS y hy => by
    refine cov_of_entryS hs hv.coverage hpo hl hS y (fun hq => ?_) (fun _ => ?_)
    · unfold RSof at hy; rw [if_pos hq] at hy; simpa using hy.1
    · by_cases hq : q < nR p
      · unfold RSof at hy; rw [if_pos hq] at hy; exact hy.2
      · obtain ⟨e, he, -⟩ := List.mem_map.mp hS
        exact absurd (mem_entriesAt he).1 hq

/-- `hcov_of` at a strict row: a strict admissible start is a closure admissible start, so
the existing admissibility verdicts apply. -/
theorem hcov_ofS (hv : VerdictsS p n cX cov prog ce) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} {l : ℕ}
    (hl : l < nL p) (q : ℕ) (hq : q < (grOf p n (prunedOf cov)).modes.length)
    (hadm : AdmissibleStart (guardL p n l) (FRowS p n l) (env p n) (guardR p n q) (cutsR p n cX reg q)) :
    CoveredX (grOf p n (prunedOf cov)) (chOfC p cov ce l) ⟨q, B p cov l, SrcSetting.preJ⟩ := by
  rw [grOf_len] at hq
  by_cases hmem : q ∈ admissibleOf p cov l
  · simp only [coversOK, List.all_eq_true, List.mem_range] at hcovers
    exact decideCoveredX_sound _ _ _ _ (hcovers l hl q hmem)
  · exfalso
    obtain ⟨σ, hgL, hσ, hg, -⟩ := hadm
    refine adm_sound (hv.adm l hl q hq hmem) σ hgL hg ?_
    have := (sat_FM_iff _ _ σ).mp (FRowS_weaken hσ.1)
    rwa [cons_g_gs p n l (rowsOK_at (hrows hs) hl)] at this

/-- The response of window `l` at its strict row from every admissible start. -/
theorem HwindowS (hv : VerdictsS p n cX cov prog ce) (hpo : progOK p n cov prog = true)
    (hcovers : coversOK p n cov ce = true) {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p)) (b : Fin n) (dt : ℝ)
    (hdt : dt ≤ epsL p) {l : ℕ} (hl : l < nL p) :
    ∀ (q : ℕ), q < (grOf p n (prunedOf cov)).modes.length → ∀ σ,
      Formula.sat (Formula.and (FRowS p n l) (env p n)) σ →
      Formula.sat (guardR p n q) σ → Formula.sat (cutsR p n cX reg q) σ →
      GResp (grOf p n (prunedOf cov)) q (windowOf p n ((Side.Aux, b) : Var n) dt l)
        (fun qf => Formula.and (Formula.and (FRowS p n l) (env p n)) (cutsR p n cX reg qf)) σ := by
  intro q hq σ hσ hg hc
  have H := coverHyps_ofS hs hv hpo hregR hinv hwf hl
  have hq' : q < nR p := by rwa [grOf_len] at hq
  refine coverX_gresp (grOf p n (prunedOf cov)) (chOfC p cov ce l) (fR p n) (domR p n) (fL p n l)
    (domL p n) (guardL p n l) b (guardR p n) (grOf_guardsRight (hnames hs)) grOf_guards
    (guardR_fv (hnames hs)) (fL_fv (hnames hs) l) (domL_fv (hnames hs)) (domR_fv (hnames hs))
    (guardL_fv (hnames hs) l) (fun q _ => fR_fv (hnames hs) q) (fun _ _ hm => grOf_sys hm)
    (fun _ _ hm => grOf_dom hm) (fun _ _ hm => grOf_weight hm)
    (epsR p) (δ p cov l) H.hδ (lamOf p cov l) H.hlam H.hspan (AGrS p n cX cov reg l) H.hAfv H.hAdom
    H.hbox H.hhand reg hregR (fun _ _ h => h.2) hwf H.hprune H.hrepoProg _ H.hRJ H.hcovJ _ H.hRR
    H.hcovR _ H.hRS H.hcovS dt
    (B p cov l) (hdt.trans (budget_span hs hl)) q σ hg
    (fun hgate => hcov_ofS hs hv hcovers hl q hq ⟨σ, hgate, hσ, hg, hc⟩)
    (fun hgate => ⟨AGS_start hs hv.nonconn hl hq' σ hgate hσ hg hc.1, hc.2⟩) _ ?_
  intro ν _ q' μ hμL hgq' hAq'
  have hpostm : Formula.sat (Formula.and (Formula.and (FRowS p n l) (env p n))
      (cutsR p n cX reg q')) (mergeLR σ ν μ) :=
    ⟨(AGS_post_any hs hl q' _ hAq'.1).1, (AGS_post_any hs hl q' _ hAq'.1).2, hAq'.2⟩
  have hfv : (Formula.and (Formula.and (FRowS p n l) (env p n)) (cutsR p n cX reg q')).fv ⊆
      range Lv ∪ range Rv := by
    intro v hv'
    rcases hv' with (hv' | hv' | hv') | hv'
    · by_contra hcon
      have hcg := cons_g_gs p n l (rowsOK_at (hrows hs) hl)
      refine notMem_FMS_fv (fun g' hg' hx => hcon ?_) hv'
      rw [hcg] at hg'
      exact hostComps_fv _ _ _ hg' hx
    · exact Or.inl (domL_fv (hnames hs) hv')
    · exact Or.inr (domR_fv (hnames hs) hv')
    · exact Or.inr (cutsR_fv hs hregR q' hv')
  refine (sat_of_agree hfv (y := μ) (fun i => ?_) (fun i => ?_)).mp hpostm
  · rw [mergeLR_L, hμL i]
  · rw [mergeLR_R]

omit hs in
/-- `keyedClaim` at the strict rows (`ϕRowS`). -/
def keyedClaimS (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
    (reg : Formula (Var n)) (a b c : Fin n) (dt : ℝ) : Prop :=
  RFormula.rvalid (theorem3Form
    (leftAutomatonBody (leftAutOf p n ((Side.Aux, b) : Var n) dt) ((Side.Aux, c) : Var n))
    (rightAutomatonBody (grOf p n (prunedOf cov)) ((Side.Aux, a) : Var n))
    (psiK ((Side.Aux, c) : Var n) (ϕRowS p n) (leftAutOf p n ((Side.Aux, b) : Var n) dt).numModes
      (domL p n) (domR p n)
      (mvRegionR ((Side.Aux, a) : Var n) (gregion p n cX reg) (grOf p n (prunedOf cov)).modes.length)))

/-- **Theorem 3 of a benchmark, mode-keyed, at its strict rows, from its records.** The rows
are read through their strictness masks (`ϕRowS`): a strict atom is proved `< 0`. -/
theorem theorem3_keyed_strict_of_records (hv : VerdictsS p n cX cov prog ce)
    (hpo : progOK p n cov prog = true) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (a b c : Fin n) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (dt : ℝ) (hdt : dt ≤ epsL p) :
    keyedClaimS p n cX cov reg a b c dt := by
  unfold keyedClaimS
  set A := leftAutOf p n ((Side.Aux, b) : Var n) dt with hA
  set Gr := grOf p n (prunedOf cov) with hGr
  set mv : Var n := ((Side.Aux, a) : Var n) with hmv
  set uL : Var n := ((Side.Aux, c) : Var n) with huL
  set tg : Var n := ((Side.Aux, b) : Var n) with htg
  have hnum : A.numModes = nL p := leftAutOf_numModes _ _
  have hgR : GuardsRight Gr := grOf_guardsRight (hnames hs)
  have hRv := grOf_Rv (pr := prunedOf cov) hs
  have hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes := by
    intro m' hm' t ht
    rw [hnum] at hm' ⊢
    rw [leftAutOf_succ] at ht
    exact nextL_lt m' hm' t ht
  have hwin : ∀ t < A.numModes, Program.vars (A.window t) ⊆ {tg} ∪ range Lv := by
    intro t ht
    rw [hnum] at ht
    rw [hA, leftAutOf_window _ _ ht]
    exact vars_gwindowSegL_sub _ (fL p n t) (domL p n) b dt 1 (guardL_fv (hnames hs) t)
      (fL_fv (hnames hs) t) (domL_fv (hnames hs))
  have hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv := by
    intro t ht
    rw [hnum] at ht
    rw [hA, leftAutOf_guard _ _ ht]
    exact guardL_fv (hnames hs) t
  have hlt := grOf_lt (n := n) (hres hs) (pruned := prunedOf cov)
  have hmvenv : mv ∉ (env p n).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv a (domL_fv (hnames hs) h)
    · exact aux_notin_range_Rv a (domR_fv (hnames hs) h)
  have hulenv : uL ∉ (env p n).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv c (domL_fv (hnames hs) h)
    · exact aux_notin_range_Rv c (domR_fv (hnames hs) h)
  have hmvreg : ∀ q, mv ∉ (gregion p n cX reg q).fv := fun q h =>
    aux_notin_range_Rv a (gregion_fv hs hregR q h)
  have hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
    intro q m hm hmv'
    exact aux_notin_range_Rv a (hRv q m hm (vars_ode_sub _ _ (Or.inl hmv')))
  refine theorem3_modeKeyed A uL Gr mv (FRowS p n) (ϕRowS p n) (domL p n) (domR p n)
    (mvRegion mv (gregion p n cX reg) Gr.modes.length) (mvRegionR mv (gregion p n cX reg) Gr.modes.length)
    (encode_ϕRowS p n) (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G A Gr a b c hba hca hwin hgrd hnext hgR hRv
  · refine hstep_modeKeyed A uL (rightAutomatonBody Gr mv) (FRowS p n) (env p n)
      (mvRegion mv (gregion p n cX reg) Gr.modes.length)
      (fun m h => aux_notin_range_Lv c (by
        rcases FRowS_fv_any (p := p) (n := n) m h with h' | h'
        · exact h'
        · exact absurd h' (aux_notin_range_Rv c)))
      hulenv ?_ ?_ ?_ ?_ hnext ?_ ?_
    · intro h
      rcases mvRegion_fv_sub mv (gregion p n cX reg) Gr.modes.length
          (fun q _ => gregion_fv hs hregR q) h with h | h
      · exact hca (by simpa [huL, hmv, Prod.ext_iff] using Set.mem_singleton_iff.mp h)
      · exact aux_notin_range_Rv c h
    · intro t h
      by_cases ht : t < A.numModes
      · exact aux_notin_range_Lv c (hgrd t ht h)
      · rw [hnum] at ht
        have : A.guard t = Formula.tt := by
          simp [hA, leftAutOf, LeftAut.guard, List.getD_eq_default, ht]
        rw [this] at h; simp [Formula.fv] at h
    · intro t
      by_cases ht : t < A.numModes
      · rw [hnum] at ht
        rw [hA, leftAutOf_window _ _ ht]
        refine framesMv_gwindow _ (fL p n t) (domL p n) tg dt 1 uL
          (by simp [huL, htg, Prod.ext_iff, hcb]) ?_
        intro h
        obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL p n t) _ h
        exact aux_ne_Lv c i hi
      · rw [hnum] at ht
        have : A.window t = Program.test (Formula.neg Formula.tt) := by
          simp [hA, leftAutOf, LeftAut.window, List.getD_eq_default, ht]
        rw [this]; exact framesMv_test _ _
    · exact notMem_bv_rightAutomatonBody_G Gr mv uL (by simp [huL, hmv, Prod.ext_iff, hca])
        (aux_notin_range_Rv c) hgR hRv
    · -- the windows
      intro t ht σ hσ
      rw [hnum] at ht
      rw [hA, leftAutOf_window _ _ ht]
      have hframe : FramesMv (windowOf p n tg dt t) mv := by
        refine framesMv_gwindow _ (fL p n t) (domL p n) tg dt 1 mv
          (by simp [hmv, htg, Prod.ext_iff, hba.symm]) ?_
        intro h
        obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL p n t) _ h
        exact aux_ne_Lv a i hi
      refine hstepMode_GR Gr mv (FRowS p n t) (env p n) (gregion p n cX reg) _
        (fun h => aux_notin_range_Lv a (by
          rcases FRowS_fv_any (p := p) (n := n) t h with h' | h'
          · exact h'
          · exact absurd h' (aux_notin_range_Rv a)))
        hmvenv hmvreg hfresh (guardsFresh_of_right Gr a hgR) hlt hframe
        (HMode_regionG Gr mv (guardR p n) (cutsR p n cX reg) grOf_guards (FRowS p n t) (env p n) _
          (fun q _ σ' ν hrun => frames_right (b := b)
            (by have := hwin t (by rw [hnum]; exact ht); rwa [hA, leftAutOf_window _ _ ht] at this)
            (guardR_fv (hnames hs) q) hrun)
          (fun q hq σ' _ hσ' hg hc =>
            HwindowS hs hv hpo hcovers hregR hinv hwf b dt hdt ht q hq σ' hσ' hg hc)) σ hσ
    · -- the handoffs
      intro m' hm' t ht ω hF henv hg
      rw [hnum] at hm'
      rw [leftAutOf_succ] at ht
      have htlt := nextL_lt m' hm' t ht
      have hrow := (structOK_iff.mp hs).2.2.2.2.2.2.1
      have hres' := handoff_soundS (hv.handoff m' hm' t ht) (rowsByName_at hrow hm')
        (rowsByName_at hrow htlt) ω
      rw [hA, leftAutOf_guard _ _ htlt] at hg
      have hcg := cons_g_gs p n m' (rowsOK_at (hrows hs) hm')
      have hct := cons_g_gs p n t (rowsOK_at (hrows hs) htlt)
      have hcomps : ∀ c' ∈ tagS (hostComps (vars p) n (rowOf p t))
          (hostFlags (vars p) n (rowOf p t)), HoldsAt c'.1 c'.2 ω := by
        refine hres' ?_ ?_ hg ?_
        · have := (sat_FMS_iff _ _ _ ω).mp hF
          rwa [hcg] at this
        · show Formula.sat (hostEvolve (vars p) n Side.L (mLof p m')) ω
          rw [hostEvolve_L (hu hs) hm']; exact henv.1
        · rw [evolveR_eq hs]
          exact henv.2
      refine (sat_FMS_iff _ _ _ ω).mpr ?_
      rw [hct]
      exact hcomps
  · exact hddF_modeKeyed_G A Gr a b c hba hca (ϕRowS p n) (domL p n) (domR p n)
      (mvRegionR mv (gregion p n cX reg) Gr.modes.length) hwin hgrd hnext hgR hRv
      (fun m _ => canonInvMS_varsL (g p n m) (gs p n m) (maskOf p n m)
        (comps_fv_any (p := p) (n := n) m))
      (fun m _ => canonInvMS_varsR (g p n m) (gs p n m) (maskOf p n m)) (domL_fv (hnames hs))
      (domR_fv (hnames hs)) rfl
      (fun v hv => mvRegion_fv_sub mv (gregion p n cX reg) Gr.modes.length
        (fun q _ => gregion_fv hs hregR q) hv)

end Proofs

/-! ## The one-row form -/

theorem FRowS_same {p : PProblem} (h : rowsSame p = true) (l : ℕ) :
    FRowS p n l = FRowS p n 0 := by
  unfold FRowS g gs comps maskOf; rw [rowOf_same h]

/-- `windowClaim` at the strict row (`canonInvMS`). -/
def windowClaimS (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
    (reg : Formula (Var n)) (a b : Fin n) (dt : ℝ) : Prop :=
  RFormula.rvalid (theorem3Form
    (bigChoice (leftProgsOf b dt (domL p n) (nL p) (guardL p n) (fL p n)))
    (rightAutomatonBody (grOf p n (prunedOf cov)) ((Side.Aux, a) : Var n))
    (RFormula.and (RFormula.and (canonInvMS (g p n 0) (gs p n 0) (maskOf p n 0))
      (envLR (domL p n) (domR p n)))
      (mvRegionR ((Side.Aux, a) : Var n) (regionG (guardR p n) (cutsR p n cX reg))
        (grOf p n (prunedOf cov)).modes.length)))

section WindowProofs

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  {ce : Choice.ChoiceEmitE} (hs : structOK p n cov cX = true)

include hs

theorem AGS_start_any (hnc : NonConnAll p n cX cov) {l : ℕ} (hl : l < nL p) (q : ℕ)
    (σ : State (Var n)) (hgL : Formula.sat (guardL p n l) σ)
    (hσ : Formula.sat (Formula.and (FRowS p n l) (env p n)) σ)
    (hg : Formula.sat (guardR p n q) σ) (hc : Formula.sat (cuts p n cX q) σ) :
    Formula.sat (AGS p n cX cov l q) σ := by
  by_cases hq : q < nR p
  · exact AGS_start hs hnc hl hq σ hgL hσ hg hc
  refine ⟨(sat_FMS_append _ _ _ _ (maskOf_len_app _) σ).mpr
    ⟨(sat_FMS_append _ _ _ _ (maskOf_len p n l) σ).mpr ⟨hσ.1, ?_⟩, ?_⟩, hσ.2⟩
  · exact (atomTerms_iff (hiffL hs hl) (hiffR_any hs q) σ).mpr
      ⟨cutsL_of_guard hs hl σ hgL, (sat_cutF _ _).mp hc⟩
  · rw [barriers_dm hq]; simp

/-- **Theorem 3 of a benchmark with one declared row, at its strict row, from its records.** -/
theorem theorem3_window_strict_of_records (hv : VerdictsS p n cX cov prog ce)
    (hpo : progOK p n cov prog = true) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (hsame : rowsSame p = true) (a b : Fin n) (hab : a ≠ b) (dt : ℝ) (hdt : dt ≤ epsL p) :
    windowClaimS p n cX cov reg a b dt := by
  unfold windowClaimS
  refine theorem3_of_coverXS (grOf p n (prunedOf cov)) a b hab dt (g p n 0) (gs p n 0)
    (maskOf p n 0)
    (comps_fv_any (p := p) (n := n) 0) (domL p n) (domR p n) (domL_fv (hnames hs))
    (domR_fv (hnames hs)) (guardR p n) (cutsR p n cX reg) grOf_guards (grOf_guardsRight (hnames hs))
    (guardR_fv (hnames hs)) (cutsR_fv hs hregR) (fR p n) (fun q _ => fR_fv (hnames hs) q)
    (fun _ _ hm => grOf_sys hm) (fun _ _ hm => grOf_dom hm) (fun _ _ hm => grOf_weight hm)
    (grOf_lt (n := n) (hres hs)) (nL p) (guardL p n) (fL p n) (fun l _ => guardL_fv (hnames hs) l)
    (fun l _ => fL_fv (hnames hs) l) (epsR p) reg hregR hwf (chOfC p cov ce) (B p cov) (δ p cov)
    (lamOf p cov) (AGrS p n cX cov reg) (fun _ _ _ _ h => h.2) (RJof p n cX) (RRof p n cX)
    (RSof p n cX)
    (fun l hl => coverHyps_ofS hs hv hpo hregR hinv hwf hl) (fun l hl => hdt.trans (budget_span hs hl))
    ?_ ?_ ?_
  · intro l hl q hq hadm
    refine hcov_ofS hs hv hcovers (reg := reg) hl q hq ?_
    obtain ⟨σ, h1, h2, h3, h4⟩ := hadm
    refine ⟨σ, h1, ⟨?_, h2.2⟩, h3, h4⟩
    show Formula.sat (FRowS p n l) σ
    rw [FRowS_same hsame]; exact h2.1
  · intro l hl q σ hgL hσ hg hc
    refine ⟨AGS_start_any hs hv.nonconn hl q σ hgL ⟨?_, hσ.2⟩ hg hc.1, hc.2⟩
    show Formula.sat (FRowS p n l) σ
    rw [FRowS_same hsame]; exact hσ.1
  · intro l hl q' y hA
    have := AGS_post_any hs hl q' y hA.1
    refine ⟨⟨?_, this.1.2⟩, this.2, hA.2⟩
    have hF : Formula.sat (FRowS p n l) y := this.1.1
    rw [FRowS_same hsame] at hF; exact hF

end WindowProofs

/-! ## The strict claims collapse to the existing claims -/

theorem keyedClaimS_iff {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE}
    (h : noStrictRows p n = true) (reg : Formula (Var n)) (a b c : Fin n) (dt : ℝ) :
    keyedClaimS p n cX cov reg a b c dt ↔ keyedClaim p n cX cov reg a b c dt := by
  unfold keyedClaimS keyedClaim
  have hϕ : ϕRowS p n = ϕRow p n := funext (fun l => ϕRowS_allFalse (maskOf_allFalse h l))
  rw [hϕ]

theorem windowClaimS_iff {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE}
    (h : noStrictRows p n = true) (reg : Formula (Var n)) (a b : Fin n) (dt : ℝ) :
    windowClaimS p n cX cov reg a b dt ↔ windowClaim p n cX cov reg a b dt := by
  unfold windowClaimS windowClaim
  rw [canonInvMS_allFalse _ _ (maskOf_allFalse h 0)]

/-- **The existing keyed theorem is the special case**: without strict atoms, the strict
theorem on the existing verdicts gives the existing claim. -/
theorem theorem3_keyed_of_records_via_strict {p : PProblem} {cX : EvolStrengtheningX}
    {cov : CoverEmitE} {prog : ProgressEmitE} {ce : ChoiceEmitE}
    (hs : structOK p n cov cX = true) (hno : noStrictRows p n = true)
    (hv : Verdicts p n cX cov prog ce)
    (hpo : progOK p n cov prog = true) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (a b c : Fin n) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (dt : ℝ) (hdt : dt ≤ epsL p) :
    keyedClaim p n cX cov reg a b c dt :=
  (keyedClaimS_iff hno reg a b c dt).mp
    (theorem3_keyed_strict_of_records hs (VerdictsS.ofVerdicts hno hv) hpo hcovers hregR hinv hwf
      a b c hba hca hcb dt hdt)

end Emitted
end RelCertifier
