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

/-! ## The mask of a row -/

/-- The lowered strictness mask of a row (`hostComps`' companion). -/
def hostFlags (vars : List String) (n : ℕ) (f : PForm) : List Bool :=
  (invStrictFlags vars n f).getD []

theorem hostFlags_length (vars : List String) (n : ℕ) (f : PForm) :
    (hostFlags vars n f).length = (hostComps vars n f).length := by
  have h := invStrictFlags_map_length vars n f
  unfold hostFlags hostComps
  rcases hc : invComponents vars n f with _ | cs <;>
    rcases hf : invStrictFlags vars n f with _ | fs <;> simp_all

section DataS

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)

/-- The strictness mask of window `l`'s row, aligned with `comps` (`g :: gs`). -/
def maskOf (l : ℕ) : List Bool := hostFlags (vars p) n (rowOf p l)

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
      (stayR_dom hs hq hst _ _ (lam_pos hs hl hq) _ (fun z hz => hz.2))
      (jointVerdS_core hs hl hq hv) σ ω hFA hω
  · exact barriers_keep hs hnc hst hq (fL p n l) _ (lam_pos hs hl hq) σ ω hcRσ hbar hω

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
      hverd σ ω hFA hgσ hω
    refine stayR_dom hs hq hst (fun _ => Term.const 0) 1 one_pos _ ?_
    intro z hz
    unfold dynBase at hz
    cases pre with
    | true => exact hz.1.2
    | false => exact hz.2
  · exact barriers_keep hs hnc hst hq (fun _ => Term.const 0) 1 one_pos σ ω hcRσ hbar hω

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

/-- **The reposition-progress premise at a strict row** (`hrepoProg_of` with the strict
anchor; the reposition packs and progress certificates are the existing ones). -/
theorem hrepoProg_ofS (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX)
    (hprog : ProgAll p n cX prog) (hpo : progOK p n cov prog = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (hdyn : ∀ l < nL p, ∀ q < nR p, ∀ pre : Bool,
      (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true →
      DynVerd p n cX cov l q pre)
    {l : ℕ} (hl : l < nL p) :
    ∀ q m, (grOf p n (prunedOf cov)).modeAt q = some m → ∀ pre : Bool,
      (if pre then (chOf p cov l).repoPre q else (chOf p cov l).repoPost q) = true →
      RepoProgress (grOf p n (prunedOf cov)) (AGrS p n cX cov reg l) (guardL p n l) (guardR p n q)
        q pre := by
  intro q m hm pre hflag
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm
  have hflag' : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true := by
    cases pre <;> simpa [chOf] using hflag
  obtain ⟨hidxL, hidxR, hcert⟩ := progOK_at hpo hl hq
  obtain ⟨c, hcf, hok⟩ := hcert pre hflag'
  obtain ⟨hcmem, hcL, hcR, hcpre⟩ := certFor_mem hcf
  have hv := hprog c hcmem
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
  -- the anchor with the region, kept along the frozen flow
  have hAfv' : (AGrS p n cX cov reg l q).fv ⊆ range Lv ∪ range Rv := by
    intro v hv
    rcases hv with hv | hv
    · exact AGS_fv hs hl hq hv
    · exact Or.inr (hregR hv)
  have hboxD' : ∀ σ ω, Formula.sat (AGrS p n cX cov reg l q) σ →
      (pre = true → Formula.sat (guardL p n l) σ) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR p n q) (Term.const 1))
        (Formula.and (domL p n) (domR p n))) σ ω → Formula.sat (AGrS p n cX cov reg l q) ω :=
    fun σ ω hA hg hω => ⟨AGS_boxD hs hnc hst hl hq pre hflag' (hdyn l hl q hq pre hflag') σ ω hA.1 hg hω,
      reg_kept_joint hinv hregR (fR_fv (hnames hs) q) (domR_fv (hnames hs)) hm rfl rfl 1 one_pos hω hA.2⟩
  have hε : 0 < epsR p := (timeOK_at (htime hs) hl).1
  -- the region
  have hR : ∀ y, Formula.sat (AGrS p n cX cov reg l q) y → (pre = true → Formula.sat (guardL p n l) y) →
      Formula.sat (regionF p n cX l q pre) y := fun y hA hg => AGS_regionF hs hl hq pre y hA.1 hg
  have hRsat : ∀ y, Formula.sat (regionF p n cX l q pre) y →
      RegionSat (vars p) n cX (mLof p l) (mRof p q) (rowOf p l) pre y :=
    fun y hy => regionSat_of_regionF hs hl pre y hy
  rcases certOK_shape hok with ⟨st, hstg⟩ | ⟨sth, st, hstg, huph, hup⟩
  · -- one stage, in either direction
    obtain ⟨hrpos, -, hfree⟩ := certOK_stage hok (st := st) (by rw [hstg]; simp)
    cases hup : st.up
    · -- downward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one_down hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      refine repoProgress_one_down (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGrS p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε reg hregR (fun y h => h.2) hex hcomp hboxD'
        (fun e he hp σ ω hA hω => AGS_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω) (regionF p n cX l q pre) hR
        v.2 (st.theta : ℝ) ?_ (st.rate : ℝ) hrpos ?_ ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro y hy hg hθ
        exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
      · intro y hy hlt
        exact hrate y (hRsat y hy) (by rw [hvR]; exact hlt)
    · -- upward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      refine repoProgress_one (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGrS p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε reg hregR (fun y h => h.2) hex hcomp hboxD'
        (fun e he hp σ ω hA hω => AGS_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω) (regionF p n cX l q pre) hR
        v.2 (st.theta : ℝ) ?_ ?_ (st.rate : ℝ) hrpos ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro y hy hg hθ
        exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
      · intro y hy hlt
        exact hrate y (hRsat y hy) (by rw [hvR]; exact hlt)
  · -- two stages, both upward
    obtain ⟨hrhpos, -, hfreeh⟩ := certOK_stage hok (st := sth) (by rw [hstg]; simp)
    obtain ⟨hrpos, -, hfree⟩ := certOK_stage hok (st := st) (by rw [hstg]; simp)
    obtain ⟨w, v, hw', hv', hrate_h, hkeep_h, hrate, hline, hstart⟩ :=
      progressVerd_two hv sth st hstg huph hup
    rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate_h hkeep_h hrate hline hstart
    have hvR := resolve_Rv (p := p) hfree hv'
    have hwR := resolve_Rv (p := p) hfreeh hw'
    refine repoProgress_two (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
      (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
      (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
      (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGrS p n cX cov reg l) hAfv'
      (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε reg hregR (fun y h => h.2) hex hcomp hboxD'
      (fun e he hp σ ω hA hω => AGS_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω) (regionF p n cX l q pre) hR
      v.2 (st.theta : ℝ) ?_ ?_ (st.rate : ℝ) hrpos w.2 (sth.theta : ℝ) (sth.rate : ℝ) hrhpos
      ?_ ?_ ?_
    · intro y hy hθ
      exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
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
