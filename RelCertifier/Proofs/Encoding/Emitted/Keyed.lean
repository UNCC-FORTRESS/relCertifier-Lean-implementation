/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 6: Theorem 3 of a benchmark, mode-keyed, from its records

`theorem3_keyed_of_records`: the ∀∃ relational invariance of the declared rows (one per left
mode, `u_L`-keyed) with the evolve envelope and the right mode's region, over the left
automaton of the file and the guarded right automaton of the file, from

* the structural bundle `structOK` and the certificate-shape bundle `progOK`, decided in the
  kernel;
* the covers of every admissible start, decided in the kernel (`coversOK`, the extended
  checker on the semantic right automaton);
* Assumption 1 (`WellFormedR`);
* the verdicts (`Verdicts`): the flow packs of the certified pairings, the reposition packs,
  the stays of the kept atoms, the non-connection pairs of the pruned edges, the
  admissibility of the dropped starts, the handoffs of the left transitions, the progress
  certificates of the reposition nodes.

Per window the cover's response is `coverX_gresp` (the general theorem's induction) with the
window's anchor; the windows assemble through `hstepMode_GR`, `HMode_regionG`,
`hstep_modeKeyed` and `theorem3_modeKeyed`, exactly as the per-benchmark keyed instances did.
-/
import RelCertifier.Proofs.Encoding.Emitted.Choice
import RelCertifier.Proofs.Encoding.Emitted.Region
import RelCertifier.Proofs.Encoding.ClockedKeyed

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLRel DLCalTiming Parse Run Set Oracle Progress Choice

variable {n : ℕ}

section Defs

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
  (prog : ProgressEmitE) (ce : ChoiceEmitE)

def JointAll : Prop :=
  ∀ l < nL p, ∀ q < nR p, (flagsOf p cov l q).jointOK = true → JointVerd p n cX cov l q
def DynAll : Prop :=
  ∀ l < nL p, ∀ q < nR p, ∀ pre : Bool,
    (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true →
    DynVerd p n cX cov l q pre
def AdmAll : Prop :=
  ∀ l < nL p, ∀ q < nR p, q ∉ admissibleOf p cov l →
    AdmVerd (vars p) n (rowOf p l) (mLof p l) (mRof p q)
def HandoffAll : Prop := ∀ m' < nL p, ∀ t ∈ (nextL p).getD m' [], HandoffVerd p n (m', t)

/-- Every verdict a benchmark's instance rests on. -/
structure Verdicts : Prop where
  stay : StayAll p n cX
  nonconn : NonConnAll p n cX cov
  joint : JointAll p n cX cov
  dyn : DynAll p n cX cov
  adm : AdmAll p n cov
  handoff : HandoffAll p n
  prog : ProgAll p n cX prog
  coverage : CoverageAll p n cX ce

/-- The checker's fuel for a window (`coverFuel`'s shape over the mode count). -/
def fuelOf (l : ℕ) : ℕ := B p cov l * (nR p + 1) + 1

/-- Every admissible start of every window is covered, by the extended checker on the
semantic right automaton. -/
noncomputable def coversOK : Bool :=
  (List.range (nL p)).all (fun l => (admissibleOf p cov l).all (fun q =>
    decideCoveredX (grOf p n (prunedOf cov)) (chOfC p cov ce l) (fuelOf p cov l)
      ⟨q, B p cov l, SrcSetting.preJ⟩))

/-- The regions of the chosen sets: after a joint segment, after a right-only segment, at a
hop (the anchor's region facts). -/
noncomputable def RJof (l q : ℕ) : Formula (Var n) :=
  if q < nR p then regionF p n cX l q false else Formula.tt
noncomputable def RRof (l q : ℕ) (σ : SrcSetting) : Formula (Var n) :=
  if q < nR p then regionF p n cX l q (preOf σ) else Formula.tt
noncomputable def RSof (l q : ℕ) (σ : SrcSetting) : Formula (Var n) :=
  if q < nR p then Formula.and (regionF p n cX l q (preOf σ)) (guardR p n q) else Formula.tt

/-- The stretch of a pairing, the window's own out of range. -/
noncomputable def lamOf (l q : ℕ) : ℝ :=
  if q < nR p then lam p cov l q else (((coverOf p cov l).lamQ : ℚ) : ℝ)

/-- The kept atoms of a right mode with the region Assumption 1 is relative to. -/
noncomputable def cutsR (reg : Formula (Var n)) (q : ℕ) : Formula (Var n) :=
  Formula.and (cuts p n cX q) reg

/-- The region of a right mode: its guard, its kept atoms, the Assumption 1 region. -/
noncomputable def gregion (reg : Formula (Var n)) (q : ℕ) : Formula (Var n) :=
  regionG (guardR p n) (cutsR p n cX reg) q

end Defs

section Proofs

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  {ce : ChoiceEmitE} (hs : structOK p n cov cX = true)

omit hs in
theorem cutF_fv_sub {atoms : List (CutAtomP n)} {S : Set (Var n)}
    (h : ∀ a ∈ atoms, a.1.fv ⊆ S) : (cutF atoms).fv ⊆ S := by
  unfold cutF
  suffices hgen : ∀ (acc : Formula (Var n)), acc.fv ⊆ S →
      (atoms.foldl (fun d a => Formula.and d a.1) acc).fv ⊆ S from
    hgen Formula.tt (by simp [Formula.fv])
  induction atoms with
  | nil => intro acc hacc; simpa using hacc
  | cons x xs ih =>
      intro acc hacc
      rw [List.foldl_cons]
      refine ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _ ?_
      intro v hv
      rcases hv with hv | hv
      · exact hacc hv
      · exact h x List.mem_cons_self hv

omit hs in
theorem cutPairsX_fvF_R {vars : List String} {atoms : List CutAtomX}
    (hwf : atomsWF vars n Side.R "L_" atoms = true) :
    ∀ a ∈ cutPairsX vars n Side.R atoms, a.1.fv ⊆ range Rv := by
  intro a ha v hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨op, a', b', hat, hop, hfa, hfb⟩ := atomOK_shape (atomsWF_mem hwf hx)
  simp only [hat, hostAtomF] at hv
  rcases hlow : lowerF vars n Side.R (PForm.cmp op a' b') with _ | f
  · rw [hlow] at hv; simp [Formula.fv] at hv
  · rw [hlow] at hv
    simp only [Option.map_some, Option.getD_some] at hv
    exact side_eq_R_mem (Run.lowerF_fv_side (resolvesTo_R vars)
      (by simp [PForm.namesFree, hfa, hfb]) hlow v hv)

include hs

theorem hiffR_any (q : ℕ) : AtomsIff (cR p n cX q) :=
  atomsIff_of_WF (atomsWF_R_any (hcuts hs) q)

theorem cuts_fv (q : ℕ) : (cuts p n cX q).fv ⊆ range Rv :=
  cutF_fv_sub (cutPairsX_fvF_R (atomsWF_R_any (hcuts hs) q))

theorem cutsR_fv {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv) (q : ℕ) :
    (cutsR p n cX reg q).fv ⊆ range Rv := by
  intro v hv
  rcases hv with hv | hv
  · exact cuts_fv hs q hv
  · exact hregR hv

theorem gregion_fv {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv) (q : ℕ) :
    (gregion p n cX reg q).fv ⊆ range Rv :=
  regionG_fv_sub (guardR_fv (hnames hs) q) (cutsR_fv hs hregR q)

/-! ### The anchor out of range -/

omit hs in
theorem barriers_dm {q : ℕ} (hq : ¬ q < nR p) : barriers p n cov q = [] := by
  simp [barriers, prunedTgts, mRof_dm hq, dm]

theorem AG_fv_any {l : ℕ} (hl : l < nL p) (q : ℕ) :
    (AG p n cX cov l q).fv ⊆ range Lv ∪ range Rv := by
  by_cases hq : q < nR p
  · exact AG_fv hs hl hq
  intro v hv
  rcases hv with hv | hv | hv
  · by_contra hc
    refine notMem_FM_fv (fun g' hg' hx => hc ?_) hv
    have hcg := cons_g_gs p n l (rowsOK_at (hrows hs) hl)
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hostComps_fv _ _ _ (hcg ▸ List.mem_cons_self) hx
    rcases List.mem_append.mp hg' with hg' | hg'
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact hostComps_fv _ _ _ (List.mem_of_mem_tail hg') hx
      · simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
        rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
        · exact Or.inl (cutPairsX_fv_L (atomsWF_L (hcuts hs) hl) a ha hx)
        · exact Or.inr (cutPairsX_fv_R (atomsWF_R_any (hcuts hs) q) a ha hx)
    · rw [barriers_dm hq] at hg'; simp at hg'
  · exact Or.inl (domL_fv (hnames hs) hv)
  · exact Or.inr (domR_fv (hnames hs) hv)

theorem AGr_fv_any {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv) {l : ℕ} (hl : l < nL p)
    (q : ℕ) : (AGr p n cX cov reg l q).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  rcases hv with hv | hv
  · exact AG_fv_any hs hl q hv
  · exact Or.inr (hregR hv)

theorem AG_post_any {l : ℕ} (hl : l < nL p) (q : ℕ) (y : State (Var n))
    (h : Formula.sat (AG p n cX cov l q) y) :
    Formula.sat (Formula.and (Formula.and (FRow p n l) (env p n)) (cuts p n cX q)) y := by
  obtain ⟨hFA, -⟩ := (sat_FM_append _ _ _ y).mp h.1
  obtain ⟨hF, hat⟩ := (sat_FM_append _ _ _ y).mp hFA
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL hs hl) (hiffR_any hs q) y).mp hat
  exact ⟨⟨hF, h.2⟩, (sat_cutF _ _).mpr hR⟩

/-! ### The certificates of a window -/

theorem lamOf_nonneg {l : ℕ} (hl : l < nL p) (q : ℕ) : 0 ≤ lamOf p cov l q := by
  unfold lamOf
  split_ifs with hq
  · exact lam_nonneg hs hl hq
  · exact (timeOK_at (htime hs) hl).2.2.1.le

theorem δ_pos {l : ℕ} (hl : l < nL p) : 0 < δ p cov l :=
  div_pos (timeOK_at (htime hs) hl).1 (timeOK_at (htime hs) hl).2.2.1

theorem lamOf_span {l : ℕ} (hl : l < nL p) (q : ℕ) : lamOf p cov l q * δ p cov l ≤ epsR p := by
  obtain ⟨heR, -, hlamQ, -, hq'⟩ := timeOK_at (htime hs) hl
  unfold lamOf δ
  split_ifs with hq
  · have hle := (hq' q hq).2
    rw [mul_div_assoc', div_le_iff₀ hlamQ, mul_comm (epsR p)]
    exact mul_le_mul_of_nonneg_right hle heR.le
  · rw [mul_div_cancel₀ _ hlamQ.ne']

omit hs in
theorem lamOf_eq {l q : ℕ} (hq : q < nR p) : lamOf p cov l q = lam p cov l q := by
  simp [lamOf, hq]

theorem budget_span {l : ℕ} (hl : l < nL p) : epsL p ≤ (B p cov l : ℝ) * δ p cov l := by
  obtain ⟨heR, -, hlamQ, hbud, -⟩ := timeOK_at (htime hs) hl
  unfold δ
  rw [mul_div_assoc', le_div_iff₀ hlamQ]
  exact hbud

/-- A chosen set's coverage premise, from its entry's verdict. -/
theorem cov_of_entry (hv : Verdicts p n cX cov prog ce) (hpo : progOK p n cov prog = true)
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
  refine guard_of_named hs hmL hq' hidxL hidxR (hv.coverage e hmem) y ?_ (fun hh => hg (hk ▸ hh))
  rw [hpre']
  exact regionSat_of_regionF hs hl _ y (hreg hq)

/-- **The certificates of window `l`**, as `CoverHyps`. -/
theorem coverHyps_of (hv : Verdicts p n cX cov prog ce) (hpo : progOK p n cov prog = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p)) (d : Fin n) {l : ℕ}
    (hl : l < nL p) :
    CoverHyps (grOf p n (prunedOf cov)) (chOfC p cov ce l) (fR p n) (domR p n) (fL p n l) (domL p n)
      (guardL p n l) (guardR p n) ((Side.Aux, d) : Var n) (epsR p) (δ p cov l) (lamOf p cov l)
      (AGr p n cX cov reg l)
      (RJof p n cX l) (RRof p n cX l) (RSof p n cX l) where
  hδ := δ_pos hs hl
  hlam := lamOf_nonneg hs hl
  hspan := lamOf_span hs hl
  hAfv := AGr_fv_any hs hregR hl
  hAdom := fun q y h => h.1.2.2
  hbox := fun q m hm hj σ ω hA hω => by
    obtain ⟨hq, -⟩ := grOf_modeAt_inv hm
    rw [lamOf_eq hq] at hω
    exact ⟨AG_box hs hv.nonconn hv.stay hl hq (by simpa [chOfC] using hj)
      (hv.joint l hl q hq (by simpa [chOfC] using hj)) σ ω hA.1 hω,
      reg_kept_joint hinv hregR (fR_fv (hnames hs) q) (domR_fv (hnames hs)) hm (grOf_sys hm)
        (grOf_dom hm) _ (lam_nonneg hs hl hq) hω hA.2⟩
  hhand := fun q e he y hA hleg => by
    obtain ⟨hq, -, -, -⟩ := edgesFrom_grOf he
    exact ⟨AG_hand hs hv.nonconn hl hq e he y hA.1 hleg, hA.2⟩
  hprune := fun q m hm e he hp σ ω hA hω => by
    obtain ⟨hq, -⟩ := grOf_modeAt_inv hm
    rw [lamOf_eq hq] at hω
    exact AG_prune hs hv.nonconn hv.stay hl hq e he hp σ ω hA.1 hω
  hrepoProg := fun q m hm pre hflag =>
    hrepoProg_of hs hv.nonconn hv.stay hv.prog hpo hregR hinv hwf hv.dyn ((Side.Aux, d) : Var n)
      (aux_notin_range_Lv d) (aux_notin_range_Rv d) hl q m hm pre
      (by cases pre <;> simpa [chOfC, chOf] using hflag)
  hRJ := fun q y hA => by
    unfold RJof; split_ifs with hq
    · exact AG_regionF hs hl hq false y hA.1 (by simp)
    · trivial
  hcovJ := fun q S hS y hy => by
    refine cov_of_entry hs hv hpo hl hS y (fun hq => ?_) (by simp)
    unfold RJof at hy; rw [if_pos hq] at hy; simpa using hy
  hRR := fun q σ y hA hgL => by
    unfold RRof; split_ifs with hq
    · exact AG_regionF hs hl hq (preOf σ) y hA.1 (fun hp => hgL (by cases σ <;> simp_all [preOf]))
    · trivial
  hcovR := fun q σ S hS y hy => by
    refine cov_of_entry hs hv hpo hl hS y (fun hq => ?_) (by simp)
    unfold RRof at hy; rw [if_pos hq] at hy; simpa using hy
  hRS := fun q σ y hA hg hgL => by
    unfold RSof; split_ifs with hq
    · exact ⟨AG_regionF hs hl hq (preOf σ) y hA.1 (fun hp => hgL (by cases σ <;> simp_all [preOf])), hg⟩
    · trivial
  hcovS := fun q σ S hS y hy => by
    refine cov_of_entry hs hv hpo hl hS y (fun hq => ?_) (fun _ => ?_)
    · unfold RSof at hy; rw [if_pos hq] at hy; simpa using hy.1
    · by_cases hq : q < nR p
      · unfold RSof at hy; rw [if_pos hq] at hy; exact hy.2
      · obtain ⟨e, he, -⟩ := List.mem_map.mp hS
        exact absurd (mem_entriesAt he).1 hq

/-- **Every admissible start is covered** (decided) and every other start is inadmissible
(its verdict). -/
theorem hcov_of (hv : Verdicts p n cX cov prog ce) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} {l : ℕ}
    (hl : l < nL p) (q : ℕ) (hq : q < (grOf p n (prunedOf cov)).modes.length)
    (hadm : AdmissibleStart (guardL p n l) (FRow p n l) (env p n) (guardR p n q) (cutsR p n cX reg q)) :
    CoveredX (grOf p n (prunedOf cov)) (chOfC p cov ce l) ⟨q, B p cov l, SrcSetting.preJ⟩ := by
  rw [grOf_len] at hq
  by_cases hmem : q ∈ admissibleOf p cov l
  · simp only [coversOK, List.all_eq_true, List.mem_range] at hcovers
    exact decideCoveredX_sound _ _ _ _ (hcovers l hl q hmem)
  · exfalso
    obtain ⟨σ, hgL, hσ, hg, -⟩ := hadm
    refine adm_sound (hv.adm l hl q hq hmem) σ hgL hg ?_
    have := (sat_FM_iff _ _ σ).mp hσ.1
    rwa [cons_g_gs p n l (rowsOK_at (hrows hs) hl)] at this

/-! ### The window responses -/

/-- The response of window `l` from every admissible start of every right mode. -/
theorem Hwindow (hv : Verdicts p n cX cov prog ce) (hpo : progOK p n cov prog = true)
    (hcovers : coversOK p n cov ce = true) {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p)) (b d : Fin n) (dt : ℝ)
    (hdt : dt ≤ epsL p) {l : ℕ} (hl : l < nL p) :
    ∀ (q : ℕ), q < (grOf p n (prunedOf cov)).modes.length → ∀ σ,
      Formula.sat (Formula.and (FRow p n l) (env p n)) σ →
      Formula.sat (guardR p n q) σ → Formula.sat (cutsR p n cX reg q) σ →
      GRespC (grOf p n (prunedOf cov)) ((Side.Aux, d) : Var n) (epsR p) q
        (windowOf p n ((Side.Aux, b) : Var n) dt l)
        (fun qf => Formula.and (Formula.and (FRow p n l) (env p n)) (cutsR p n cX reg qf)) σ := by
  intro q hq σ hσ hg hc
  have H := coverHyps_of hs hv hpo hregR hinv hwf d hl
  have hq' : q < nR p := by rwa [grOf_len] at hq
  refine coverX_gresp (grOf p n (prunedOf cov)) (chOfC p cov ce l) (fR p n) (domR p n) (fL p n l)
    (domL p n) (guardL p n l) b (guardR p n) ((Side.Aux, d) : Var n) (aux_notin_range_Lv d)
    (aux_notin_range_Rv d) (grOf_guardsRight (hnames hs)) grOf_guards
    (guardR_fv (hnames hs)) (fL_fv (hnames hs) l) (domL_fv (hnames hs)) (domR_fv (hnames hs))
    (guardL_fv (hnames hs) l) (fun q _ => fR_fv (hnames hs) q) (fun _ _ hm => grOf_sys hm)
    (fun _ _ hm => grOf_dom hm) (fun _ _ hm => grOf_weight hm)
    (epsR p) (δ p cov l) H.hδ (lamOf p cov l) H.hlam H.hspan (AGr p n cX cov reg l) H.hAfv H.hAdom
    H.hbox H.hhand reg hregR (fun _ _ h => h.2) hwf H.hprune H.hrepoProg _ H.hRJ H.hcovJ _ H.hRR
    H.hcovR _ H.hRS H.hcovS dt
    (B p cov l) (hdt.trans (budget_span hs hl)) q σ hg
    (fun hgate => hcov_of hs hv hcovers hl q hq ⟨σ, hgate, hσ, hg, hc⟩)
    (fun hgate => ⟨AG_start hs hv.nonconn hl hq' σ hgate hσ hg hc.1, hc.2⟩) _ ?_
  intro ν _ q' μ hμL hgq' hAq'
  have hpostm : Formula.sat (Formula.and (Formula.and (FRow p n l) (env p n))
      (cutsR p n cX reg q')) (mergeLR σ ν μ) :=
    ⟨(AG_post_any hs hl q' _ hAq'.1).1, (AG_post_any hs hl q' _ hAq'.1).2, hAq'.2⟩
  have hfv : (Formula.and (Formula.and (FRow p n l) (env p n)) (cutsR p n cX reg q')).fv ⊆
      range Lv ∪ range Rv := by
    intro v hv'
    rcases hv' with (hv' | hv' | hv') | hv'
    · by_contra hcon
      have hcg := cons_g_gs p n l (rowsOK_at (hrows hs) hl)
      refine notMem_FM_fv (fun g' hg' hx => hcon ?_) hv'
      rw [hcg] at hg'
      exact hostComps_fv _ _ _ hg' hx
    · exact Or.inl (domL_fv (hnames hs) hv')
    · exact Or.inr (domR_fv (hnames hs) hv')
    · exact Or.inr (cutsR_fv hs hregR q' hv')
  refine (sat_of_agree hfv (y := μ) (fun i => ?_) (fun i => ?_)).mp hpostm
  · rw [mergeLR_L, hμL i]
  · rw [mergeLR_R]

/-! ### The mode-keyed Theorem 3 -/

theorem grOf_Rv {pr : String → String → Bool} :
    ∀ q m, (grOf p n pr).modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm y hy
  rw [grOf_sys hm, grOf_dom hm] at hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fR p n q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fR p n q) (Term.const 1) (fR_fv (hnames hs) q)
      (by simp [Term.fv]) hy
  · exact domR_fv (hnames hs) hy

omit hs in
theorem comps_fv_any (l : ℕ) : ∀ g' ∈ g p n l :: gs p n l, g'.fv ⊆ range Lv ∪ range Rv := by
  intro g' hg'
  unfold g gs at hg'
  rcases hcomps : comps p n l with _ | ⟨c, cs⟩
  · rw [hcomps] at hg'
    simp only [List.headD_nil, List.tail_nil, List.mem_singleton] at hg'
    subst hg'; simp [Term.fv]
  · rw [hcomps] at hg'
    simp only [List.headD_cons, List.tail_cons] at hg'
    exact hostComps_fv _ _ _ (hcomps ▸ hg')

omit hs in
theorem FRow_fv_any (l : ℕ) : (FRow p n l).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hc
  exact notMem_FM_fv (fun g' hg' hx => hc (comps_fv_any (p := p) (n := n) l g' hg' hx)) hv

theorem evolveR_eq : Handoff.evolveR p = (mRof p 0).evolve := by
  have h0 : 0 < nR p := (structOK_iff.mp hs).2.2.2.2.2.2.2.2.2.1
  unfold Handoff.evolveR mRof
  unfold nR at h0
  rcases hm : p.R.modes with _ | ⟨a, as⟩
  · rw [hm] at h0; simp at h0
  · simp

omit hs in
/-- The claim of a benchmark with per-mode rows: Theorem 3 over the left automaton of the file
(`u_L`-keyed rows) and the CLOCKED guarded right automaton (each right cycle flows for at most
`ε_R`; mode variable `(Aux, a)`, left clock `(Aux, b)`, left mode variable `(Aux, c)`, right
clock `(Aux, d)`), with the envelope and the right region. -/
def keyedClaim (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
    (reg : Formula (Var n)) (a b c d : Fin n) (dt : ℝ) : Prop :=
  RFormula.rvalid (theorem3Form
    (leftAutomatonBody (leftAutOf p n ((Side.Aux, b) : Var n) dt) ((Side.Aux, c) : Var n))
    (rightAutomatonBodyC (grOf p n (prunedOf cov)) ((Side.Aux, a) : Var n) ((Side.Aux, d) : Var n)
      (epsR p))
    (psiK ((Side.Aux, c) : Var n) (ϕRow p n) (leftAutOf p n ((Side.Aux, b) : Var n) dt).numModes
      (domL p n) (domR p n)
      (mvRegionR ((Side.Aux, a) : Var n) (gregion p n cX reg) (grOf p n (prunedOf cov)).modes.length)))

/-- **Theorem 3 of a benchmark, mode-keyed, from its records.** -/
theorem theorem3_keyed_of_records (hv : Verdicts p n cX cov prog ce)
    (hpo : progOK p n cov prog = true) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (a b c d : Fin n) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hdc : d ≠ c) (dt : ℝ) (hdt : dt ≤ epsL p) :
    keyedClaim p n cX cov reg a b c d dt := by
  unfold keyedClaim
  set A := leftAutOf p n ((Side.Aux, b) : Var n) dt with hA
  set Gr := grOf p n (prunedOf cov) with hGr
  set mv : Var n := ((Side.Aux, a) : Var n) with hmv
  set uL : Var n := ((Side.Aux, c) : Var n) with huL
  set tg : Var n := ((Side.Aux, b) : Var n) with htg
  set tr : Var n := ((Side.Aux, d) : Var n) with htr
  have hmvtr : mv ≠ tr := by simp [hmv, htr, Prod.ext_iff, hda.symm]
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
  refine theorem3_modeKeyed_gen A uL (rightAutomatonBodyC Gr mv tr (epsR p)) (FRow p n) (ϕRow p n)
    (domL p n) (domR p n)
    (mvRegion mv (gregion p n cX reg) Gr.modes.length) (mvRegionR mv (gregion p n cX reg) Gr.modes.length)
    (encode_ϕRow p n) (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_GC A Gr a b c d hba hca hdb.symm hdc.symm (epsR p) hwin hgrd hnext hgR hRv
  · refine hstep_modeKeyed A uL (rightAutomatonBodyC Gr mv tr (epsR p)) (FRow p n) (env p n)
      (mvRegion mv (gregion p n cX reg) Gr.modes.length)
      (fun m h => aux_notin_range_Lv c (by
        rcases FRow_fv_any (p := p) (n := n) m h with h' | h'
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
    · exact notMem_bv_rightAutomatonBodyC Gr mv tr (epsR p) uL
        (by simp [huL, hmv, Prod.ext_iff, hca]) (by simp [huL, htr, Prod.ext_iff, hdc.symm])
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
      refine hstepMode_GRC Gr mv tr (epsR p) (FRow p n t) (env p n) (gregion p n cX reg) _
        (fun h => aux_notin_range_Lv a (by
          rcases FRow_fv_any (p := p) (n := n) t h with h' | h'
          · exact h'
          · exact absurd h' (aux_notin_range_Rv a)))
        hmvenv hmvreg hmvtr hfresh (guardsFresh_of_right Gr a hgR) hlt hframe
        (HMode_regionGC Gr mv tr (epsR p) (guardR p n) (cutsR p n cX reg) grOf_guards (FRow p n t)
          (env p n) _
          (fun q _ σ' ν hrun => frames_right (b := b)
            (by have := hwin t (by rw [hnum]; exact ht); rwa [hA, leftAutOf_window _ _ ht] at this)
            (guardR_fv (hnames hs) q) hrun)
          (fun q hq σ' _ hσ' hg hc =>
            Hwindow hs hv hpo hcovers hregR hinv hwf b d dt hdt ht q hq σ' hσ' hg hc)) σ hσ
    · -- the handoffs
      intro m' hm' t ht ω hF henv hg
      rw [hnum] at hm'
      rw [leftAutOf_succ] at ht
      have htlt := nextL_lt m' hm' t ht
      have hrow := (structOK_iff.mp hs).2.2.2.2.2.2.1
      have hres' := handoff_sound (hv.handoff m' hm' t ht) (rowsByName_at hrow hm')
        (rowsByName_at hrow htlt) ω
      rw [hA, leftAutOf_guard _ _ htlt] at hg
      have hcg := cons_g_gs p n m' (rowsOK_at (hrows hs) hm')
      have hct := cons_g_gs p n t (rowsOK_at (hrows hs) htlt)
      have hcomps : ∀ c' ∈ hostComps (vars p) n (rowOf p t), Term.eval c' ω ≤ 0 := by
        refine hres' ?_ ?_ hg ?_
        · have := (sat_FM_iff _ _ ω).mp hF
          rwa [hcg] at this
        · show Formula.sat (hostEvolve (vars p) n Side.L (mLof p m')) ω
          rw [hostEvolve_L (hu hs) hm']; exact henv.1
        · rw [evolveR_eq hs]
          exact henv.2
      refine (sat_FM_iff _ _ ω).mpr ?_
      rw [hct]
      exact hcomps
  · exact hddF_modeKeyed_GC A Gr a b c d hba hca hdb.symm hdc.symm (epsR p) (ϕRow p n) (domL p n)
      (domR p n)
      (mvRegionR mv (gregion p n cX reg) Gr.modes.length) hwin hgrd hnext hgR hRv
      (fun m _ => canonInvM_varsL (g p n m) (gs p n m) (comps_fv_any (p := p) (n := n) m))
      (fun m _ => canonInvM_varsR (g p n m) (gs p n m)) (domL_fv (hnames hs))
      (domR_fv (hnames hs)) rfl
      (fun v hv => mvRegion_fv_sub mv (gregion p n cX reg) Gr.modes.length
        (fun q _ => gregion_fv hs hregR q) hv)

end Proofs

end Emitted
end RelCertifier
