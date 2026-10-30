/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge at strict rows: data, anchor, handoffs, progress (extension `strict-atoms`)

The window's row read through its strictness mask (`maskOf`, the computable
`Oracle.invStrictFlags` aligned with the row's components): `FRowS`/`ϕRowS` (strict
components `< 0`), the strict anchor `AGS` (the flagged row, the closure atoms and barriers,
the envelope), and the facts the cover consumes:

* CONCLUSION sites, proved strict: `AGS_box` (the flagged joint pack `JointVerdS`: strict
  components by routes A/B), `AGS_boxD` (the EXISTING reposition pack: route A preserves
  `< 0`), `AGS_start`, `AGS_hand`, `AGS_post`;
* ASSUMPTION sites, reused through the weakening `AGS → AG`: `AGS_prune`, `AGS_pruneD`,
  `AGS_regionF`, hygiene (`AGS_fv`, the free variables are those of `AG`);
* `HandoffVerdS`/`handoff_soundS`: the strict handoff query (both rows at their masks);
* `hrepoProg_ofS`: the reposition-progress premise for the strict anchor.

With an all-false mask every definition collapses to the existing one (`FRowS_allFalse`,
`ϕRowS_allFalse`, `AGS_allFalse`, `jointVerdS_of_allFalse`). New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.Emitted.Progress
import RelCertifier.Proofs.Encoding.StrictCouple
import RelCertifier.Proofs.Encoding.ModeHandoffStrict

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLRel DLCalTiming Parse Run Set Oracle Progress Bridge

variable {n : ℕ}

section DataS

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)


/-- The row at its mask (strict components `< 0`), and its relational form. -/
noncomputable def FRowS (l : ℕ) : Formula (Var n) := FMS (g p n l) (gs p n l) (maskOf p n l)
noncomputable def ϕRowS (l : ℕ) : RFormula (Var n) := canonInvMS (g p n l) (gs p n l) (maskOf p n l)

theorem encode_ϕRowS (l : ℕ) : encode (Equiv.refl (Var n)) (ϕRowS p n l) = FRowS p n l :=
  encode_canonInvMS _ _ _

theorem maskOf_len (l : ℕ) : (maskOf p n l).length ≤ (gs p n l).length + 1 := by
  unfold maskOf gs
  rw [hostFlags_length, List.length_tail]
  unfold comps
  omega

/-- **The strict anchor** of window `l` at right mode `q`: the flagged row, the kept atoms of
both modes and the barriers (closures), the envelope. -/
noncomputable def AGS (l q : ℕ) : Formula (Var n) :=
  Formula.and (FMS (g p n l) (gs p n l ++ atomTerms (cL p n cX l) (cR p n cX q) ++
    barriers p n cov q) (maskOf p n l)) (env p n)

noncomputable def AGrS (reg : Formula (Var n)) (l q : ℕ) : Formula (Var n) :=
  Formula.and (AGS p n cX cov l q) reg

/-- The flagged joint pack of a certified pairing (strict components: routes A/B). -/
def JointVerdS (l q : ℕ) : Prop :=
  modalVerdXS p cX n (rowIdx p l) (strataOf p cov l q).order (lam p cov l q) l q

/-- The strict handoff verdict of a declared left transition. -/
def HandoffVerdS (tr : ℕ × ℕ) : Prop :=
  ∃ q, Handoff.queryOfS p n tr = some q ∧ z3solve q.toHost = Verdict.unsat

variable {p n cX cov}

theorem FRowS_weaken {l : ℕ} {y : State (Var n)} (h : Formula.sat (FRowS p n l) y) :
    Formula.sat (FRow p n l) y := FMS_weaken h

theorem AGS_weaken {l q : ℕ} {y : State (Var n)} (h : Formula.sat (AGS p n cX cov l q) y) :
    Formula.sat (AG p n cX cov l q) y := ⟨FMS_weaken h.1, h.2⟩

theorem AGS_fv_eq (l q : ℕ) : (AGS p n cX cov l q).fv = (AG p n cX cov l q).fv := by
  simp only [AGS, AG, Formula.fv, FMS_fv]

theorem FRowS_fv_eq (l : ℕ) : (FRowS p n l).fv = (FRow p n l).fv := FMS_fv _ _ _

/-! ### Collapse -/

theorem FRowS_allFalse {l : ℕ} (h : ∀ b ∈ maskOf p n l, b = false) :
    FRowS p n l = FRow p n l := FMS_allFalse _ _ h

theorem ϕRowS_allFalse {l : ℕ} (h : ∀ b ∈ maskOf p n l, b = false) :
    ϕRowS p n l = ϕRow p n l := canonInvMS_allFalse _ _ h

theorem AGS_allFalse {l q : ℕ} (h : ∀ b ∈ maskOf p n l, b = false) :
    AGS p n cX cov l q = AG p n cX cov l q := by
  unfold AGS AG; rw [FMS_allFalse _ _ h]

theorem jointVerdS_of_allFalse {l q : ℕ} (h : ∀ b ∈ maskOf p n l, b = false)
    (hv : JointVerd p n cX cov l q) : JointVerdS p n cX cov l q :=
  (modalVerdXS_allFalse p cX n (rowIdx p l) _ _ l q h).mpr hv

end DataS

/-! ## The strict handoff -/

theorem hostFlags_of_lower {vars : List String} {f : PForm} {fs : List Bool}
    (h : invStrictFlags vars n f = some fs) : hostFlags vars n f = fs := by
  simp [hostFlags, h]

/-- **The strict handoff**: the source row at its mask, the source evolve, the target guard
and the right evolve give the target row at its mask. -/
theorem handoff_soundS {p : PProblem} {tr : ℕ × ℕ} (hv : HandoffVerdS p n tr)
    {rowS rowT : PForm}
    (hS : Handoff.invRowOf p (p.L.modes.getD tr.1 dm) = some rowS)
    (hT : Handoff.invRowOf p (p.L.modes.getD tr.2 dm) = some rowT) :
    ∀ ω, (∀ c ∈ tagS (hostComps p.L.stateVars n rowS) (hostFlags p.L.stateVars n rowS),
        HoldsAt c.1 c.2 ω) →
      Formula.sat (hostEvolve p.L.stateVars n Side.L (p.L.modes.getD tr.1 dm)) ω →
      Formula.sat (hostGuard p.L.stateVars n Side.L (p.L.modes.getD tr.2 dm)) ω →
      Formula.sat (((lowerF p.L.stateVars n Side.R (Handoff.evolveR p)).map IForm.toHost).getD
        Formula.tt) ω →
      ∀ c ∈ tagS (hostComps p.L.stateVars n rowT) (hostFlags p.L.stateVars n rowT),
        HoldsAt c.1 c.2 ω := by
  obtain ⟨q, hq, hz⟩ := hv
  unfold Handoff.queryOfS at hq
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hq
  obtain ⟨rS, hrS, rT, hrT, hq⟩ := hq
  have hdm : (⟨"", [], .tt, .tt, []⟩ : PMode) = dm := rfl
  rw [hdm] at hrS hrT hq
  rw [hS] at hrS; obtain rfl := Option.some.inj hrS
  rw [hT] at hrT; obtain rfl := Option.some.inj hrT
  obtain ⟨cs, fs, eL, gT, eR, ct, ft, hcs, hfs, heL, hgT, heR, hct, hft, rfl⟩ :=
    ihandoffQueryS_eq hq
  intro ω hrow hev hg heR'
  rw [hostComps_of_lower hcs, hostFlags_of_lower hfs] at hrow
  rw [hostComps_of_lower hct, hostFlags_of_lower hft]
  rw [hostEvolve_of_lower heL] at hev
  rw [hostGuard_of_lower hgT] at hg
  rw [heR] at heR'
  simp only [Option.map_some, Option.getD_some] at heR'
  exact handoff_of_unsatS cs ct fs ft eL gT eR hz ω hrow hev hg heR'

/-- The existing verdict is the strict one when neither row has a strict atom. -/
theorem handoffVerdS_of_allFalse {p : PProblem} {tr : ℕ × ℕ}
    (hfs : ∀ rowS, Handoff.invRowOf p (p.L.modes.getD tr.1 dm) = some rowS →
      ∀ fs, invStrictFlags p.L.stateVars n rowS = some fs → ∀ b ∈ fs, b = false)
    (hft : ∀ rowT, Handoff.invRowOf p (p.L.modes.getD tr.2 dm) = some rowT →
      ∀ fs, invStrictFlags p.L.stateVars n rowT = some fs → ∀ b ∈ fs, b = false)
    (hv : HandoffVerd p n tr) : HandoffVerdS p n tr := by
  obtain ⟨q, hq, hz⟩ := hv
  refine ⟨q, ?_, hz⟩
  unfold Handoff.queryOfS
  unfold Handoff.queryOf at hq
  have hdm : (⟨"", [], .tt, .tt, []⟩ : PMode) = dm := rfl
  simp only [hdm] at hq ⊢
  rcases hS : Handoff.invRowOf p (p.L.modes.getD tr.1 dm) with _ | rS
  · rw [hS] at hq; simp at hq
  rcases hT : Handoff.invRowOf p (p.L.modes.getD tr.2 dm) with _ | rT
  · rw [hS, hT] at hq; simp at hq
  rw [hS, hT] at hq
  simp only [Option.bind_eq_bind, Option.bind_some] at hq ⊢
  rw [Handoff.ihandoffQueryS_eq_of_allFalse _ _ _ _ _ _ _ (hfs rS hS) (hft rT hT)]
  exact hq

/-! ## The strict anchor -/

section AnchorS

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE}
  (hs : structOK p n cov cX = true)

include hs

theorem AGS_fv {l q : ℕ} (hl : l < nL p) (hq : q < nR p) :
    (AGS p n cX cov l q).fv ⊆ range Lv ∪ range Rv := by
  rw [AGS_fv_eq]; exact AG_fv hs hl hq

omit hs in
theorem AGS_dom {l q : ℕ} (y : State (Var n)) (h : Formula.sat (AGS p n cX cov l q) y) :
    Formula.sat (domR p n) y := h.2.2

omit hs in
theorem maskOf_len_app {l : ℕ} (ts : List (Term (Var n))) :
    (maskOf p n l).length ≤ (gs p n l ++ ts).length + 1 :=
  le_trans (maskOf_len p n l) (by simp)

theorem AGS_post {l q : ℕ} (hl : l < nL p) (hq : q < nR p) (y : State (Var n))
    (h : Formula.sat (AGS p n cX cov l q) y) :
    Formula.sat (Formula.and (Formula.and (FRowS p n l) (env p n)) (cuts p n cX q)) y := by
  obtain ⟨hFA, -⟩ := (sat_FMS_append _ _ _ _ (maskOf_len_app _) y).mp h.1
  obtain ⟨hF, hat⟩ := (sat_FMS_append _ _ _ _ (maskOf_len p n l) y).mp hFA
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL hs hl) (hiffR hs hq) y).mp hat
  exact ⟨⟨hF, h.2⟩, (sat_cutF _ _).mpr hR⟩

theorem AGS_start (hnc : NonConnAll p n cX cov) {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    (σ : State (Var n)) (hgL : Formula.sat (guardL p n l) σ)
    (hσ : Formula.sat (Formula.and (FRowS p n l) (env p n)) σ)
    (hg : Formula.sat (guardR p n q) σ) (hc : Formula.sat (cuts p n cX q) σ) :
    Formula.sat (AGS p n cX cov l q) σ := by
  refine ⟨(sat_FMS_append _ _ _ _ (maskOf_len_app _) σ).mpr
    ⟨(sat_FMS_append _ _ _ _ (maskOf_len p n l) σ).mpr ⟨hσ.1, ?_⟩, ?_⟩, hσ.2⟩
  · exact (atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mpr
      ⟨cutsL_of_guard hs hl σ hgL, (sat_cutF _ _).mp hc⟩
  · exact barriers_entry hs hnc hq σ hg hσ.2.2

theorem AGS_hand (hnc : NonConnAll p n cX cov) {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    {pr : String → String → Bool} (e : REdge (Var n)) (he : e ∈ (grOf p n pr).edgesFrom q)
    (y : State (Var n)) (hA : Formula.sat (AGS p n cX cov l q) y) (hleg : SwitchLegal e y) :
    Formula.sat (AGS p n cX cov l e.tgt) y := by
  have htlt : e.tgt < nR p := by
    have := grOf_lt (hres hs) (pruned := pr) q e he; rwa [grOf_len] at this
  have hg : Formula.sat (guardR p n e.tgt) y := by
    unfold SwitchLegal at hleg; rwa [grOf_guards q e he] at hleg
  obtain ⟨hFA, -⟩ := (sat_FMS_append _ _ _ _ (maskOf_len_app _) y).mp hA.1
  obtain ⟨hF, hat⟩ := (sat_FMS_append _ _ _ _ (maskOf_len p n l) y).mp hFA
  obtain ⟨hLc, -⟩ := (atomTerms_iff (hiffL hs hl) (hiffR hs hq) y).mp hat
  refine ⟨(sat_FMS_append _ _ _ _ (maskOf_len_app _) y).mpr
    ⟨(sat_FMS_append _ _ _ _ (maskOf_len p n l) y).mpr ⟨hF, ?_⟩, ?_⟩, hA.2⟩
  · exact (atomTerms_iff (hiffL hs hl) (hiffR hs htlt) y).mpr ⟨hLc, cutsR_of_guard hs htlt y hg⟩
  · exact barriers_entry hs hnc htlt y hg hA.2.2

/-- The flagged components of the row in a strata order are those of `g :: gs`. -/
theorem orderTag_mem_equiv {l : ℕ} (hl : l < nL p) {order : List ℕ}
    (hperm' : order.Perm (List.range (compsLen p n l))) :
    (∀ c ∈ orderTag (comps p n l) (maskOf p n l) order, c ∈ tagS (g p n l :: gs p n l) (maskOf p n l)) ∧
    (∀ c ∈ tagS (g p n l :: gs p n l) (maskOf p n l), c ∈ orderTag (comps p n l) (maskOf p n l) order) := by
  rw [cons_g_gs p n l (rowsOK_at (hrows hs) hl)]
  rw [← comps_length] at hperm'
  exact ⟨fun c hc => (mem_orderTag_iff _ _ _ hperm' c).mp hc,
    fun c hc => (mem_orderTag_iff _ _ _ hperm' c).mpr hc⟩

theorem jointVerdS_core {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    (hv : JointVerdS p n cX cov l q) :
    VerdXCoreS (orderTag (comps p n l) (maskOf p n l) (strataOf p cov l q).order) (fL p n l)
      (fR p n q) (lam p cov l q) (domCutX (env p n) (cL p n cX l) (cR p n cX q)) := by
  have h : VerdXCoreS (orderTag (comps p n l) (maskOf p n l) (strataOf p cov l q).order)
      (fL p n l) (fR p n q) (lam p cov l q)
      (domCutX (Formula.and (hostEvolve (vars p) n Side.L (mLof p l))
        (hostEvolve (vars p) n Side.R (mRof p q))) (cL p n cX l) (cR p n cX q)) := hv
  rwa [hostEvolve_L (hu hs) hl, hostEvolve_R (hu hs) hq] at h

/-- **A joint segment at the pairing's stretch keeps the strict anchor.** -/
theorem AGS_box (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (hj : (flagsOf p cov l q).jointOK = true) (hv : JointVerdS p n cX cov l q) :
    ∀ σ ω, Formula.sat (AGS p n cX cov l q) σ →
      Program.sem (Program.ode (jointSys (fL p n l) (fR p n q) (Term.const (lam p cov l q)))
        (env p n)) σ ω → Formula.sat (AGS p n cX cov l q) ω := by
  intro σ ω hσ hω
  obtain ⟨hFA, hbar⟩ := (sat_FMS_append _ _ _ _ (maskOf_len_app _) σ).mp hσ.1
  obtain ⟨hsub1, hsub2⟩ := orderTag_mem_equiv hs hl (permOK_joint (hperm hs) hl hq hj)
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp (FMS_weaken hFA)
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  refine ⟨(sat_FMS_append _ _ _ _ (maskOf_len_app _) ω).mpr ⟨?_, ?_⟩, sem_ode_ends_in_domain hω⟩
  · exact couple_box_cutXS (g p n l) (gs p n l) (maskOf p n l) _ (cL p n cX l) (cR p n cX q)
      (fL p n l) (fR p n q) (lam p cov l q) (domL p n) (domR p n) (maskOf_len p n l) hsub1 hsub2
      (hiffL hs hl) (hiffR hs hq) (stayL_env hs hl hst _ _)
      (stayR_dom hs hq hst _ _ (lam_nonneg hs hl hq) _ (fun z hz => hz.2))
      (jointVerdS_core hs hl hq hv) σ ω hFA hω
  · exact barriers_keep hs hnc hst hq (fL p n l) _ (lam_nonneg hs hl hq) σ ω hcRσ hbar hω

/-- **A frozen-left segment keeps the strict anchor** (the existing reposition pack). -/
theorem AGS_boxD (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (pre : Bool)
    (hd : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true)
    (hv : DynVerd p n cX cov l q pre) :
    ∀ σ ω, Formula.sat (AGS p n cX cov l q) σ → (pre = true → Formula.sat (guardL p n l) σ) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR p n q) (Term.const 1))
        (Formula.and (domL p n) (domR p n))) σ ω → Formula.sat (AGS p n cX cov l q) ω := by
  intro σ ω hσ hgσ hω
  obtain ⟨hFA, hbar⟩ := (sat_FMS_append _ _ _ _ (maskOf_len_app _) σ).mp hσ.1
  obtain ⟨hsub1, hsub2⟩ := orderTag_mem_equiv hs hl (permOK_dyn (hperm hs) hl hq pre hd)
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp (FMS_weaken hFA)
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  have hverd := dynVerd_core hs hl hq pre hv
  unfold compsAt at hverd
  rw [← orderTag_map_snd (comps p n l) (maskOf p n l)] at hverd
  refine ⟨(sat_FMS_append _ _ _ _ (maskOf_len_app _) ω).mpr ⟨?_, ?_⟩, sem_ode_ends_in_domain hω⟩
  · refine couple_box_dynS pre (g p n l) (gs p n l) (maskOf p n l) _ (cL p n cX l) (cR p n cX q)
      (fR p n q) (domL p n) (domR p n) (guardL p n l) (maskOf_len p n l) hsub1 hsub2
      (hiffL hs hl) (hiffR hs hq)
      (cutPairsX_fv_L (atomsWF_L (hcuts hs) hl)) (guardL_fv (hnames hs) l) ?_
      hverd trivial σ ω hFA hgσ hω
    refine stayR_dom hs hq hst (fun _ => Term.const 0) 1 zero_le_one _ ?_
    intro z hz
    unfold dynBase at hz
    cases pre with
    | true => exact hz.1.2
    | false => exact hz.2
  · exact barriers_keep hs hnc hst hq (fun _ => Term.const 0) 1 zero_le_one σ ω hcRσ hbar hω


omit hs in
/-- The flags of the ordered tagged row are the row's mask at the order's indices. -/
theorem tagS_getD_fst (cs : List (Term (Var n))) (m : List Bool) (i : ℕ) :
    ((tagS cs m).getD i (false, Term.const 0)).1 = true → m.getD i false = true := by
  induction cs generalizing m i with
  | nil => simp
  | cons c cs ih =>
      cases i with
      | zero => cases m <;> simp
      | succ i =>
          intro h
          have := ih m.tail i (by simpa using h)
          cases m <;> simp_all

/-- **A frozen-left right-only run that stays in the pack's region before its last instant
keeps the strict anchor** (`AG_boxR` at a strict row). Whole domain: `AGS_boxD`. Pre-landing
region: on every proper prefix the run is in the half-open region, where the pack keeps the
tagged rows and atoms (`couple_box_dynS`); every `≤ 0` term is `≤ 0` at the end by continuity;
a strict component's pack is route A over the CLOSED region (`covers`), and the run, up to and
including its end, lies in that closed region narrowed by the domain, the atoms and the earlier
strata (all `≤ 0` along it), so route A keeps it `< 0` at the end (`flow_cert_sound_lt`). -/
theorem AGS_boxR (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (pre : Bool)
    (hd : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true)
    {rg : DynRegion n} (hrg : rg.fvR)
    (hcov : rg.covers ((orderTag (comps p n l) (maskOf p n l)
      (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)).map
        Prod.fst))
    (hv : DynVerd p n cX cov l q pre rg) :
    ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat (AGS p n cX cov l q) y →
      (pre = true → Formula.sat (guardL p n l) y) →
      ∀ T Φ, DLCalTiming.ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) ρ T Φ →
      (∀ t ∈ Ico (0 : ℝ) T, rg.pred (Φ t)) →
      Formula.sat (AGS p n cX cov l q) (mergeLR y y (Φ T)) := by
  intro y ρ hyρ hAy hgLy T Φ H hB
  have hAfv := AGS_fv hs hl hq
  set σ := mergeLR y y ρ with hσdef
  have hσ : Formula.sat (AGS p n cX cov l q) σ :=
    (sat_of_agree hAfv (y := y) (fun i => mergeLR_L y y ρ i)
      (fun i => by rw [mergeLR_R, hyρ i])).mpr hAy
  have hgσ : pre = true → Formula.sat (guardL p n l) σ := fun hp =>
    (sat_merge_L (guardL_fv (hnames hs) l) y y ρ).mpr (hgLy hp)
  have hdomLy : Formula.sat (domL p n) y := hAy.2.1
  have hfR := fR_fv (n := n) (hnames hs) q
  have hdomL := domL_fv (n := n) (hnames hs)
  have hdomR := domR_fv (n := n) (hnames hs)
  have hrunW := right_sol_merge_joint hfR hdomL hdomR H y y hdomLy
  rcases H.hr.lt_or_eq with hT | hT0
  swap
  · subst hT0; rw [H.hΦ0]; exact hσ
  cases rg with
  | whole =>
      exact AGS_boxD hs hnc hst hl hq pre hd hv _ _ hσ hgσ hrunW
  | pre Bh Bc mask hmono hclosed =>
  have hBfv : Bh.fv ⊆ range Rv := hrg
  obtain ⟨hFA, hbar⟩ := (sat_FMS_append _ _ _ _ (maskOf_len_app _) σ).mp hσ.1
  obtain ⟨hsub1, hsub2⟩ := orderTag_mem_equiv hs hl (permOK_dyn (hperm hs) hl hq pre hd)
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp (FMS_weaken hFA)
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  have hverd := dynVerd_core hs hl hq pre hv
  unfold compsAt at hverd
  rw [← orderTag_map_snd (comps p n l) (maskOf p n l)] at hverd
  set ts := orderTag (comps p n l) (maskOf p n l)
    (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder) with hts
  have hbox := couple_box_dynS pre (g p n l) (gs p n l) (maskOf p n l) ts (cL p n cX l)
    (cR p n cX q) (fR p n q) (domL p n) (domR p n) (guardL p n l) (maskOf_len p n l) hsub1 hsub2
    (hiffL hs hl) (hiffR hs hq) (cutPairsX_fv_L (atomsWF_L (hcuts hs) hl))
    (guardL_fv (hnames hs) l)
    (stayR_dom hs hq hst (fun _ => Term.const 0) 1 zero_le_one _ (fun z hz => by
      unfold dynBase at hz
      cases pre with
      | true => exact hz.1.2.1
      | false => exact hz.2.1)) hverd hcov
  -- every proper prefix: the tagged rows and the atoms
  have hpref : ∀ s ∈ Ico (0 : ℝ) T,
      Formula.sat (FMS (g p n l) (gs p n l ++ atomTerms (cL p n cX l) (cR p n cX q))
        (maskOf p n l)) (mergeLR y y (Φ s)) := by
    intro s hs'
    have Hs := ODESol_restrict H hs'.1 hs'.2.le
    have HsB : DLCalTiming.ODESol (rightBlock (fR p n q) (Term.const 1))
        (Formula.and (domR p n) Bh) ρ s Φ :=
      ⟨Hs.hr, Hs.hΦ0, Hs.hder, Hs.hmask, fun t ht =>
        ⟨Hs.hdom t ht, hB t ⟨ht.1, ht.2.trans_lt hs'.2⟩⟩⟩
    have hBR : (Formula.and (domR p n) Bh).fv ⊆ range Rv := by
      intro v hv'; rcases hv' with hv' | hv'
      · exact hdomR hv'
      · exact hBfv hv'
    exact hbox σ _ hFA hgσ (right_sol_merge_joint hfR hdomL hBR HsB y y hdomLy)
  have hcont : ∀ t : Term (Var n), ContinuousOn (fun s => Term.eval t (mergeLR y y (Φ s)))
      (Icc 0 T) := fun t =>
    (term_contDiff t).continuous.comp_continuousOn (merge_continuousOn H y)
  have hholds_le : ∀ (b : Bool) (t : Term (Var n)) (x : State (Var n)), HoldsAt b t x →
      Term.eval t x ≤ 0 := by
    intro b t x h; cases b
    · exact h
    · exact (show Term.eval t x < 0 from h).le
  -- every row component and every atom is `≤ 0` along the whole run
  have hrow : ∀ t ∈ Icc (0 : ℝ) T, ∀ c ∈ tagS (g p n l :: gs p n l) (maskOf p n l),
      Term.eval c.2 (mergeLR y y (Φ t)) ≤ 0 := by
    intro t ht c hc
    have hpre_t : ∀ s ∈ Ico (0 : ℝ) T, Term.eval c.2 (mergeLR y y (Φ s)) ≤ 0 := fun s hs' =>
      hholds_le _ _ _ ((sat_FMS_iff _ _ _ _).mp
        ((sat_FMS_append _ _ _ _ (maskOf_len p n l) _).mp (hpref s hs')).1 c hc)
    rcases ht.2.lt_or_eq with htT | rfl
    · exact hpre_t t ⟨ht.1, htT⟩
    · exact le_zero_of_Ico hT (hcont c.2) hpre_t
  have hatoms : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ atomTerms (cL p n cX l) (cR p n cX q),
      Term.eval a (mergeLR y y (Φ t)) ≤ 0 := by
    intro t ht a ha
    have hpre_t : ∀ s ∈ Ico (0 : ℝ) T, Term.eval a (mergeLR y y (Φ s)) ≤ 0 := fun s hs' =>
      ((sat_FMS_append _ _ _ _ (maskOf_len p n l) _).mp (hpref s hs')).2 a ha
    rcases ht.2.lt_or_eq with htT | rfl
    · exact hpre_t t ⟨ht.1, htT⟩
    · exact le_zero_of_Ico hT (hcont a) hpre_t
  -- the closed region along the whole run
  have hBc : ∀ t ∈ Icc (0 : ℝ) T, Formula.sat Bc (mergeLR y y (Φ t)) := by
    intro t ht
    rcases ht.2.lt_or_eq with htT | rfl
    · exact hmono _ ((sat_merge_R hBfv y y _).mpr (hB t ⟨ht.1, htT⟩))
    · exact hclosed (fun s => mergeLR y y (Φ s)) t hT (merge_continuousOn H y)
        (fun s hs' => (sat_merge_R hBfv y y _).mpr (hB s hs'))
  -- the strict row components, at the end
  have hstrict : ∀ c ∈ tagS (g p n l :: gs p n l) (maskOf p n l), c.1 = true →
      Term.eval c.2 (mergeLR y y (Φ T)) < 0 := by
    intro c hc hc1
    obtain ⟨i, hi, hci⟩ := List.getElem_of_mem (hsub2 c hc)
    have hi' : i < (ts.map Prod.snd).length := by simpa using hi
    have hm : mask.getD i false = true := hcov i (by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp [hci, hc1])
    have h := hverd i hi'
    simp only [hm, if_true] at h
    have hget : (ts.map Prod.snd)[i] = c.2 := by simp [hci]
    rw [hget] at h
    set Dom := dynDomHost pre (Formula.and (domCutX (env p n) (cL p n cX l) (cR p n cX q)) Bc)
      (guardL p n l) ((ts.map Prod.snd).take i) with hDom
    have hdomt : ∀ t ∈ Icc (0 : ℝ) T, Formula.sat Dom (mergeLR y y (Φ t)) := by
      intro t ht
      rw [hDom, sat_dynDomHost]
      have hat := (atomTerms_iff (hiffL hs hl) (hiffR hs hq) _).mp (hatoms t ht)
      have henv : Formula.sat (env p n) (mergeLR y y (Φ t)) :=
        ⟨(sat_merge_L hdomL y y _).mpr hdomLy, (sat_merge_R hdomR y y _).mpr (H.hdom t ht)⟩
      have hbase : Formula.sat (Formula.and (domCutX (env p n) (cL p n cX l) (cR p n cX q)) Bc)
          (mergeLR y y (Φ t)) := ⟨(sat_domCutX _ _ _ _).mpr ⟨henv, hat.1, hat.2⟩, hBc t ht⟩
      refine ⟨?_, (sat_bigLe_iff _ _).mpr (fun g' hg' => ?_)⟩
      · unfold dynBase
        cases pre with
        | false => exact hbase
        | true => exact ⟨hbase, (sat_merge_L (guardL_fv (hnames hs) l) y y _).mpr (hgLy rfl)⟩
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hg')
        exact hrow t ht c' (hsub1 c' hc')
    obtain ⟨hr, h0', hder, hmask, -⟩ := right_sol_merge hfR hdomR H y y
    have HD : DLCalTiming.ODESol (rightBlock (fR p n q) (Term.const 1)) (Formula.and Dom Formula.tt)
        σ T (fun t => mergeLR y y (Φ t)) :=
      ⟨hr, h0', hder, hmask, fun t ht => ⟨hdomt t ht, trivial⟩⟩
    have hrun : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR p n q)
        (Term.const 1)) Dom) σ (mergeLR y y (Φ T)) :=
      sem_ode_dom_mono (D := Formula.and Dom Formula.tt) (D' := Dom) (fun x hx => hx.1) ((sem_rightBlock_frozen_iff hfR (by simp [Term.fv])).mpr
        (DLCalTiming.sem_ode_restrict HD H.hr le_rfl))
    have hinit : Term.eval c.2 σ < 0 := by
      have := (sat_FMS_iff _ _ _ _).mp ((sat_FMS_append _ _ _ _ (maskOf_len p n l) σ).mp hFA).1 c hc
      rw [hc1] at this; exact this
    exact flow_cert_sound_lt ⟨c.2, fun _ => Term.const 0, fR p n q, Term.const 1, Dom⟩
      (z3_unsat_sound h) hinit _ hrun
  refine ⟨(sat_FMS_append _ _ _ _ (maskOf_len_app _) _).mpr ⟨?_, ?_⟩,
    sem_ode_ends_in_domain hrunW⟩
  · refine (sat_FMS_append _ _ _ _ (maskOf_len p n l) _).mpr ⟨?_, hatoms T ⟨hT.le, le_rfl⟩⟩
    refine (sat_FMS_iff _ _ _ _).mpr (fun c hc => ?_)
    rcases hc1 : c.1 with _ | _
    · show Term.eval c.2 _ ≤ 0
      exact hrow T ⟨hT.le, le_rfl⟩ c hc
    · show Term.eval c.2 _ < 0
      exact hstrict c hc hc1
  · exact barriers_keep hs hnc hst hq (fun _ => Term.const 0) 1 zero_le_one σ _ hcRσ hbar hrunW

theorem AGS_prune (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (e : REdge (Var n)) (he : e ∈ (grOf p n (prunedOf cov)).edgesFrom q)
    (hp : e.pruned = true) :
    ∀ σ ω, Formula.sat (AGS p n cX cov l q) σ →
      Program.sem (Program.ode (jointSys (fL p n l) (fR p n q) (Term.const (lam p cov l q)))
        (env p n)) σ ω → ¬ Formula.sat e.guard ω :=
  fun σ ω hσ hω => AG_prune hs hnc hst hl hq e he hp σ ω (AGS_weaken hσ) hω

theorem AGS_pruneD (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (e : REdge (Var n)) (he : e ∈ (grOf p n (prunedOf cov)).edgesFrom q)
    (hp : e.pruned = true) :
    ∀ σ ω, Formula.sat (AGS p n cX cov l q) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR p n q) (Term.const 1))
        (Formula.and (domL p n) (domR p n))) σ ω → ¬ Formula.sat e.guard ω :=
  fun σ ω hσ hω => AG_pruneD hs hnc hst hl hq e he hp σ ω (AGS_weaken hσ) hω

theorem AGS_regionF {l q : ℕ} (hl : l < nL p) (hq : q < nR p) (pre : Bool) (y : State (Var n))
    (hA : Formula.sat (AGS p n cX cov l q) y) (hgL : pre = true → Formula.sat (guardL p n l) y) :
    Formula.sat (regionF p n cX l q pre) y :=
  AG_regionF hs hl hq pre y (AGS_weaken hA) hgL

end AnchorS

/-! ## Reposition progress for the strict anchor -/

section ProgressS

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  (hs : structOK p n cov cX = true)

include hs

omit hs in
/-- The region of a node's pack covers its strict components (`dynMask` is the row's mask in the
node's strata order). -/
theorem dynRegion_covers (l q : ℕ) (pre : Bool) :
    (dynRegion p n cov prog l q pre).covers ((orderTag (comps p n l) (maskOf p n l)
      (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)).map
        Prod.fst) := by
  unfold dynRegion
  rcases nodeStage p n prog l q pre with _ | ⟨v, st⟩
  · trivial
  · intro i hi
    show (dynMask p n cov l q pre).getD i false = true
    unfold dynMask
    unfold orderTag at hi
    rw [List.map_map] at hi
    rcases ho : (if pre then (strataOf p cov l q).dynPreOrder
        else (strataOf p cov l q).dynPostOrder)[i]? with _ | k
    · simp [List.getD_eq_getElem?_getD, ho] at hi
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, ho, Option.map_some,
        Option.getD_some, Function.comp_apply] at hi ⊢
      have := tagS_getD_fst (comps p n l) (maskOf p n l) k
        (by rw [List.getD_eq_getElem?_getD]; exact hi)
      rwa [List.getD_eq_getElem?_getD] at this

/-- **The reposition-progress premise of every reposition node of window `l`, at a strict row**, from the node's
progress certificate and its right-only pack on the node's region (`dynRegion`: the whole domain
without the key, the pre-landing region with it). The landing cycle stops at the first entry into
the certificate's closed target (`Progress.lean`'s `*_reg` closers with `Bf` the region). -/
theorem hrepoProg_ofS (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX)
    (hprog : ProgAll p n cX prog) (hpo : progOK p n cov prog = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (hdyn : ∀ l < nL p, ∀ q < nR p, ∀ pre : Bool,
      (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true →
      DynVerd p n cX cov l q pre (dynRegion p n cov prog l q pre))
    (tr : Var n) (htrL : tr ∉ range Lv) (htrR : tr ∉ range Rv)
    {l : ℕ} (hl : l < nL p) :
    ∀ q m, (grOf p n (prunedOf cov)).modeAt q = some m → ∀ pre : Bool,
      (if pre then (chOf p cov l).repoPre q else (chOf p cov l).repoPost q) = true →
      RepoProgress (grOf p n (prunedOf cov)) tr (epsR p) (AGrS p n cX cov reg l) (guardL p n l)
        (guardR p n q) q pre := by
  intro q m hm pre hflag
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm
  have hflag' : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true := by
    cases pre <;> simpa [chOf] using hflag
  obtain ⟨hidxL, hidxR, hcert⟩ := progOK_at hpo hl hq
  obtain ⟨c, hcf, hok⟩ := hcert pre hflag'
  obtain ⟨hcmem, hcL, hcR, hcpre⟩ := certFor_mem hcf
  have hv := hprog c hcmem
  have hdv := hdyn l hl q hq pre hflag'
  -- Assumption 1 at `q`
  have hwfq := hwf q (by rw [grOf_len]; exact hq) (modeOf p n q) hm
  have hex : ∀ x, Formula.sat (guardR p n q) x → Formula.sat (domR p n) x → Formula.sat reg x →
      ∃ Φ, ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) x (epsR p) Φ :=
    fun x hg hd hr => (hwfq x hg hd hr).1
  have hcomp : ∀ x, Formula.sat (guardR p n q) x → Formula.sat (domR p n) x → Formula.sat reg x →
      ∀ t Φ, t ≤ epsR p →
      ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) x t Φ →
      ∃ e ∈ (grOf p n (prunedOf cov)).edgesFrom q, Formula.sat (guardR p n e.tgt) (Φ t) :=
    fun x hg hd hr t Φ ht H => (hwfq x hg hd hr).2 t Φ ht H
  have hAfv' : (AGrS p n cX cov reg l q).fv ⊆ range Lv ∪ range Rv := by
    intro v hv
    rcases hv with hv | hv
    · exact AGS_fv hs hl hq hv
    · exact Or.inr (hregR hv)
  -- the anchor with the region, kept along a right-only run that stays in the node's region
  -- before its last instant
  have hboxB : (dynRegion p n cov prog l q pre).fvR →
      ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat (AGrS p n cX cov reg l q) y →
      (pre = true → Formula.sat (guardL p n l) y) →
      ∀ T Φ, ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) ρ T Φ →
      (∀ t ∈ Ico (0 : ℝ) T, (dynRegion p n cov prog l q pre).pred (Φ t)) →
      Formula.sat (AGrS p n cX cov reg l q) (mergeLR y y (Φ T)) := by
    intro hrg y ρ hyρ hA hgLy T Φ H hB
    refine ⟨AGS_boxR hs hnc hst hl hq pre hflag' hrg (dynRegion_covers l q pre) hdv y ρ hyρ hA.1 hgLy T Φ H hB, ?_⟩
    have hrunW := right_sol_merge_joint (fR_fv (hnames hs) q) (domL_fv (hnames hs))
      (domR_fv (hnames hs)) H y y hA.1.2.1
    have hregσ : Formula.sat reg (mergeLR y y ρ) :=
      (sat_merge_R hregR y y ρ).mpr ((Formula.coincidence reg (fun v hv => by
        obtain ⟨i, rfl⟩ := hregR hv; exact hyρ i)).mp hA.2)
    exact reg_kept_joint hinv hregR (fR_fv (hnames hs) q) (domR_fv (hnames hs)) hm rfl rfl 1
      zero_le_one hrunW hregσ
  -- the region from the certificate's last stage (`st`, coordinate `v`)
  have hregion : ∀ (st : ProgressStageE) (v : Var n), c.stages.getLast? = some st →
      resolveVar (vars p) n Side.R st.var = some v → v = Rv v.2 →
      (dynRegion p n cov prog l q pre).fvR ∧
      ∀ x, Formula.sat (before v st).toHost x → (dynRegion p n cov prog l q pre).pred x := by
    intro st v hlast hv' hvR
    rw [dynRegion_cases hcf hlast hv']
    split_ifs
    · refine ⟨?_, fun x hx => hx⟩
      show (before v st).toHost.fv ⊆ range Rv
      intro x hx
      unfold before at hx
      split_ifs at hx <;>
        simp [IForm.toHost, ITerm.toHost, Formula.fv, Term.fv] at hx <;>
        (rw [hx, hvR]; exact ⟨v.2, rfl⟩)
    · exact ⟨trivial, fun _ _ => trivial⟩
  have hε : 0 < epsR p := (timeOK_at (htime hs) hl).1
  have hR : ∀ y, Formula.sat (AGrS p n cX cov reg l q) y → (pre = true → Formula.sat (guardL p n l) y) →
      Formula.sat (regionF p n cX l q pre) y := fun y hA hg => AGS_regionF hs hl hq pre y hA.1 hg
  have hRsat : ∀ y, Formula.sat (regionF p n cX l q pre) y →
      RegionSat (vars p) n cX (mLof p l) (mRof p q) (rowOf p l) pre y :=
    fun y hy => regionSat_of_regionF hs hl pre y hy
  have hpruneD := fun e he hp σ ω (hA : Formula.sat (AGrS p n cX cov reg l q) σ) hω =>
    AGS_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω
  rcases certOK_shape hok with ⟨st, hstg⟩ | ⟨sth, st, hstg, huph, hup⟩
  · -- one stage, in either direction
    obtain ⟨hrpos, -, hfree⟩ := certOK_stage hok (st := st) (by rw [hstg]; simp)
    have hlast : c.stages.getLast? = some st := by rw [hstg]; rfl
    cases hup : st.up
    · -- downward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one_down hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      refine repoProgress_one_down_reg (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGrS p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε tr htrL htrR reg hregR (fun y h => h.2) hex hcomp
        (dynRegion p n cov prog l q pre).pred
        (hboxB (hregion st v hlast hv' hvR).1)
        hpruneD (regionF p n cX l q pre) hR v.2 (st.theta : ℝ) ?_ ?_ (st.rate : ℝ) hrpos ?_ ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro x hx
        exact (hregion st v hlast hv' hvR).2 x ((sat_before_down v st hup x).mpr (by rw [hvR]; exact hx))
      · intro y hy hg hθ
        exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
      · intro y hy hlt
        exact hrate y (hRsat y hy) (by rw [hvR]; exact hlt)
    · -- upward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      refine repoProgress_one_reg (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGrS p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε tr htrL htrR reg hregR (fun y h => h.2) hex hcomp
        (dynRegion p n cov prog l q pre).pred
        (hboxB (hregion st v hlast hv' hvR).1)
        hpruneD (regionF p n cX l q pre) hR v.2 (st.theta : ℝ) ?_ ?_ ?_ (st.rate : ℝ) hrpos ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro x hx
        exact (hregion st v hlast hv' hvR).2 x ((sat_before_up v st hup x).mpr (by rw [hvR]; exact hx))
      · intro y hy hg hθ
        exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
      · intro y hy hlt
        exact hrate y (hRsat y hy) (by rw [hvR]; exact hlt)
  · -- two stages, both upward
    obtain ⟨hrhpos, -, hfreeh⟩ := certOK_stage hok (st := sth) (by rw [hstg]; simp)
    obtain ⟨hrpos, -, hfree⟩ := certOK_stage hok (st := st) (by rw [hstg]; simp)
    have hlast : c.stages.getLast? = some st := by rw [hstg]; rfl
    obtain ⟨w, v, hw', hv', hrate_h, hkeep_h, hrate, hline, hstart⟩ :=
      progressVerd_two hv sth st hstg huph hup
    rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate_h hkeep_h hrate hline hstart
    have hvR := resolve_Rv (p := p) hfree hv'
    have hwR := resolve_Rv (p := p) hfreeh hw'
    refine repoProgress_two_reg (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
      (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
      (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
      (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGrS p n cX cov reg l) hAfv'
      (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε tr htrL htrR reg hregR (fun y h => h.2) hex hcomp
      (dynRegion p n cov prog l q pre).pred
      (hboxB (hregion st v hlast hv' hvR).1)
      hpruneD (regionF p n cX l q pre) hR v.2 (st.theta : ℝ) ?_ ?_ ?_ (st.rate : ℝ) hrpos w.2
      (sth.theta : ℝ) (sth.rate : ℝ) hrhpos ?_ ?_ ?_
    · intro y hy hθ
      exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
    · intro x hx
      exact (hregion st v hlast hv' hvR).2 x ((sat_before_up v st hup x).mpr (by rw [hvR]; exact hx))
    · intro y hy hg hθ
      exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
    · intro y hy hlt
      exact hrate_h y (hRsat y hy) (by rw [hwR]; exact hlt)
    · intro y hy hle
      exact hkeep_h y (hRsat y hy) (by rw [hwR]; exact hle)
    · intro y hy hθh hlt
      exact hrate y (hRsat y hy) (by rw [hwR]; exact hθh) (by rw [hvR]; exact hlt)


end ProgressS

end Emitted
end RelCertifier
