/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge for PRE-LANDING right-only nodes (opt-in `prelanding = true`)

Under the opt-in key (`docs/PRELANDING.md`) the tool certifies a right-only (reposition) node
by the pre-landing pack (`OracleAPI.checkDynRepoPL`): the right-only flow certificate over the
reposition domain narrowed by the half-open region BEFORE the node's progress certificate's
last threshold (`x < θ` upward, `x > θ` downward), any of the routes A, B, C per component.
The node is emitted in its own record (`Preland.PrelandEmitE`), never as the cover's
`dynPre`/`dynPost` flag.

* `withPL cov pl`: the cover with the pre-landing nodes merged into the flags (and their strata
  orders), for the cover GRAPH only (the tool's `effRows`); `plOK`: the key is set and the
  emitted whole-domain flags are all off (every reposition node of the file is pre-landing).
* `DynVerdPL`: the pre-landing pack of a node at the region of its certificate's last stage.
* `AG_boxPLH`: the anchor is kept along a right-only run that is in the region BEFORE its last
  instant (the half-open extension): on every proper prefix the run is in the region, so the
  pack keeps the rows and atoms there (`couple_box_dynPL`); the row and atom terms are
  continuous along the run, so they are `≤ 0` at the end too; the barriers and the envelope are
  whole-domain facts.
* `hrepoProg_ofPL`: `RepoProgress` of every node from its certificate and its pack, through the
  first-hit closers (`ProgressPL.lean`).
* `theorem3_window_of_records_pl`: Theorem 3 of a one-row benchmark from its records, the
  window form (`theorem3_window_of_records` with the pre-landing nodes), stated over the
  EMITTED cover (the claim reads the cover's pruned edges only, which the merge keeps).
* `bridgeGroupsPL`, `verdictsPL_of_groups`: every query, as groups, and a green run as the
  verdicts.

The non-strict chain only (the anchor's rows are `≤ 0` terms, closed under the limit); a strict
row's chain (`StrictKeyed`) keeps the whole-domain pack.

This file is additive: the existing chain and its 51 instances are unchanged (the pieces of
`Keyed.lean` / `Window.lean` / `Run.lean` that read the `Verdicts` structure are restated here
for `VerdictsPL`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.ProgressPL
import RelCertifier.Proofs.Flow.PicardBridge
import RelCertifier.VerdictsV2.ModalDynPL
import RelCertifier.Trusted.PrelandEmit

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLRel DLCalTiming Parse Run Set Oracle Progress Choice Preland Bridge

variable {n : ℕ}

/-! ## The merged cover and the data gate -/

/-- The cover with the pre-landing nodes merged into its flag rows (and their strata orders):
the rows the cover graph is built on (`OracleAPI.coverMode`'s `effRows`). -/
def withPL (cov : CoverEmitE) (pl : PrelandEmitE) : CoverEmitE :=
  { cov with covers := cov.covers.map (fun lc =>
      { lc with
        flags := lc.flags.map (fun f =>
          { f with dynPre := f.dynPre || (pl.find lc.mL f.name true).isSome,
                   dynPost := f.dynPost || (pl.find lc.mL f.name false).isSome }),
        strata := lc.strata.map (fun s =>
          { s with dynPreOrder := ((pl.find lc.mL s.mR true).map (·.order)).getD s.dynPreOrder,
                   dynPostOrder := ((pl.find lc.mL s.mR false).map (·.order)).getD
                     s.dynPostOrder }) }) }

/-- **The kernel-side data gate**: a pre-landing record is admitted only for a problem with the
opt-in key, and then every reposition node of the emitted cover is a pre-landing one (its
whole-domain flags are all off). -/
def plOK (p : PProblem) (cov : CoverEmitE) (pl : PrelandEmitE) : Bool :=
  (pl.nodes.isEmpty || p.prelanding) &&
  (!p.prelanding || cov.covers.all (fun lc => lc.flags.all (fun f => !f.dynPre && !f.dynPost)))

theorem prunedOf_withPL (cov : CoverEmitE) (pl : PrelandEmitE) :
    prunedOf (withPL cov pl) = prunedOf cov := rfl

/-! ## The pre-landing verdict of a node -/

section Defs

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
  (prog : ProgressEmitE) (ce : ChoiceEmitE)

/-- The pre-landing pack of node `(l, q, pre)`: at the region before its certificate's last
stage, in the node's strata order. -/
def DynVerdPL (l q : ℕ) (pre : Bool) : Prop :=
  ∀ c, certFor p prog l q pre = some c → ∀ st, c.stages.getLast? = some st →
    ∀ v, resolveVar (vars p) n Side.R st.var = some v →
      modalVerdDynPLX p cX n (rowIdx p l)
        (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)
        pre l q (before v st).toHost

def DynAllPL : Prop :=
  ∀ l < nL p, ∀ q < nR p, ∀ pre : Bool,
    (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true →
    DynVerdPL p n cX cov prog l q pre

/-- Every verdict a pre-landing benchmark's instance rests on (`Verdicts` with the pre-landing
packs in place of the whole-domain ones). -/
structure VerdictsPL : Prop where
  stay : StayAll p n cX
  nonconn : NonConnAll p n cX cov
  joint : JointAll p n cX cov
  dyn : DynAllPL p n cX cov prog
  adm : AdmAll p n cov
  handoff : HandoffAll p n
  prog : ProgAll p n cX prog
  coverage : CoverageAll p n cX ce

end Defs

/-! ## The half-open extension -/

/-- A continuous function `≤ 0` on `[0, T)` is `≤ 0` at `T`. -/
theorem le_zero_of_Ico {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : ContinuousOn f (Icc 0 T))
    (h : ∀ s ∈ Ico (0 : ℝ) T, f s ≤ 0) : f T ≤ 0 := by
  have hcl : T ∈ closure (Ico (0 : ℝ) T) := by
    rw [closure_Ico hT.ne]; exact ⟨hT.le, le_rfl⟩
  have hfw : ContinuousWithinAt f (Ico 0 T) T :=
    (hf T ⟨hT.le, le_rfl⟩).mono Ico_subset_Icc_self
  exact ContinuousWithinAt.closure_le hcl hfw continuousWithinAt_const h

/-- The merged state of a right-only run is continuous in time. -/
theorem merge_continuousOn {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (y : State (Var n)) :
    ContinuousOn (fun s => mergeLR y y (Φ s)) (Icc 0 T) := by
  refine continuousOn_pi.mpr (fun v => ?_)
  obtain ⟨sd, i⟩ := v
  cases sd with
  | L => simpa [mergeLR] using continuousOn_const
  | R =>
      have h := H.coord_continuousOn i
      simpa [mergeLR, Rv] using h
  | Aux => simpa [mergeLR] using continuousOn_const

section Proofs

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  {ce : ChoiceEmitE} (hs : structOK p n cov cX = true)

include hs

/-- **A frozen-left run that stays in a right region before its last instant keeps the
anchor**, from the node's pre-landing pack at that region. -/
theorem AG_boxPLH (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (pre : Bool)
    (hd : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true)
    (Bh : Formula (Var n)) (hBfv : Bh.fv ⊆ range Rv)
    (hv : modalVerdDynPLX p cX n (rowIdx p l)
      (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)
      pre l q Bh) :
    ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat (AG p n cX cov l q) y →
      (pre = true → Formula.sat (guardL p n l) y) →
      ∀ T Φ, ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) ρ T Φ →
      (∀ t ∈ Ico (0 : ℝ) T, Formula.sat Bh (Φ t)) →
      Formula.sat (AG p n cX cov l q) (mergeLR y y (Φ T)) := by
  intro y ρ hyρ hAy hgLy T Φ H hB
  have hAfv := AG_fv hs hl hq
  set σ := mergeLR y y ρ with hσdef
  have hσ : Formula.sat (AG p n cX cov l q) σ :=
    (sat_of_agree hAfv (y := y) (fun i => mergeLR_L y y ρ i)
      (fun i => by rw [mergeLR_R, hyρ i])).mpr hAy
  have hgσ : pre = true → Formula.sat (guardL p n l) σ := fun hp =>
    (sat_merge_L (guardL_fv (hnames hs) l) y y ρ).mpr (hgLy hp)
  have hdomLy : Formula.sat (domL p n) y := hAy.2.1
  have hfR := fR_fv (n := n) (hnames hs) q
  have hdomL := domL_fv (n := n) (hnames hs)
  have hdomR := domR_fv (n := n) (hnames hs)
  -- the whole run, on the envelope
  have hrunW := right_sol_merge_joint hfR hdomL hdomR H y y hdomLy
  obtain ⟨hFA, hbar⟩ := (sat_FM_append _ _ _ σ).mp hσ.1
  obtain ⟨hsub1, hsub2⟩ := comps_mem_equiv hs hl (permOK_dyn (hperm hs) hl hq pre hd)
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp hFA
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  -- the rows and atoms on every proper prefix (the prefix is in the region)
  have hverd : VerdDynCorePL pre (compsAt p n l
      (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder))
      (fR p n q) (domCutX (env p n) (cL p n cX l) (cR p n cX q)) (guardL p n l) Bh := by
    have h : VerdDynCorePL pre (compsAt p n l
        (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder))
        (fR p n q) (domCutX (Formula.and (hostEvolve (vars p) n Side.L (mLof p l))
          (hostEvolve (vars p) n Side.R (mRof p q))) (cL p n cX l) (cR p n cX q))
        (guardL p n l) Bh := hv
    rwa [hostEvolve_L (hu hs) hl, hostEvolve_R (hu hs) hq] at h
  have hbox := couple_box_dynPL pre (g p n l) (gs p n l) _ (cL p n cX l) (cR p n cX q)
      (fR p n q) (domL p n) (domR p n) (guardL p n l) Bh hsub1 hsub2 (hiffL hs hl) (hiffR hs hq)
      (cutPairsX_fv_L (atomsWF_L (hcuts hs) hl)) (guardL_fv (hnames hs) l)
      (stayR_dom hs hq hst (fun _ => Term.const 0) 1 zero_le_one _ (fun z hz => by
        unfold dynBase at hz
        cases pre with
        | true => exact hz.1.2.1
        | false => exact hz.2.1)) hverd
  have hpref : ∀ s ∈ Ico (0 : ℝ) T,
      Formula.sat (FM (g p n l) (gs p n l ++ atomTerms (cL p n cX l) (cR p n cX q)))
        (mergeLR y y (Φ s)) := by
    intro s hs'
    have Hs := ODESol_restrict H hs'.1 hs'.2.le
    have HsB : ODESol (rightBlock (fR p n q) (Term.const 1)) (Formula.and (domR p n) Bh) ρ s Φ :=
      ⟨Hs.hr, Hs.hΦ0, Hs.hder, Hs.hmask, fun t ht =>
        ⟨Hs.hdom t ht, hB t ⟨ht.1, ht.2.trans_lt hs'.2⟩⟩⟩
    have hBR : (Formula.and (domR p n) Bh).fv ⊆ range Rv := by
      intro v hv'; rcases hv' with hv' | hv'
      · exact hdomR hv'
      · exact hBfv hv'
    have hrun := right_sol_merge_joint hfR hdomL hBR HsB y y hdomLy
    exact hbox σ _ hFA hgσ hrun
  -- the limit at the end
  have hend : Formula.sat (FM (g p n l) (gs p n l ++ atomTerms (cL p n cX l) (cR p n cX q)))
      (mergeLR y y (Φ T)) := by
    rcases H.hr.lt_or_eq with hT | hT0
    · refine (sat_FM_iff _ _ _).mpr (fun t ht => ?_)
      have hc : ContinuousOn (fun s => Term.eval t (mergeLR y y (Φ s))) (Icc 0 T) :=
        (term_contDiff t).continuous.comp_continuousOn (merge_continuousOn H y)
      exact le_zero_of_Ico hT hc (fun s hs' => (sat_FM_iff _ _ _).mp (hpref s hs') t ht)
    · rw [← hT0, H.hΦ0]; exact hFA
  refine ⟨(sat_FM_append _ _ _ _).mpr ⟨hend, ?_⟩, sem_ode_ends_in_domain hrunW⟩
  exact barriers_keep hs hnc hst hq (fun _ => Term.const 0) 1 zero_le_one σ _ hcRσ hbar hrunW

/-- **The reposition-progress premise of every pre-landing node of window `l`.** -/
theorem hrepoProg_ofPL (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX)
    (hprog : ProgAll p n cX prog) (hpo : progOK p n cov prog = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (hdyn : DynAllPL p n cX cov prog)
    (tr : Var n) (htrL : tr ∉ range Lv) (htrR : tr ∉ range Rv)
    {l : ℕ} (hl : l < nL p) :
    ∀ q m, (grOf p n (prunedOf cov)).modeAt q = some m → ∀ pre : Bool,
      (if pre then (chOf p cov l).repoPre q else (chOf p cov l).repoPost q) = true →
      RepoProgress (grOf p n (prunedOf cov)) tr (epsR p) (AGr p n cX cov reg l) (guardL p n l)
        (guardR p n q) q pre := by
  intro q m hm pre hflag
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm
  have hflag' : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true := by
    cases pre <;> simpa [chOf] using hflag
  obtain ⟨hidxL, hidxR, hcert⟩ := progOK_at hpo hl hq
  obtain ⟨c, hcf, hok⟩ := hcert pre hflag'
  obtain ⟨hcmem, hcL, hcR, hcpre⟩ := certFor_mem hcf
  have hv := hprog c hcmem
  have hdv := hdyn l hl q hq pre hflag' c hcf
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
  have hAfv' : (AGr p n cX cov reg l q).fv ⊆ range Lv ∪ range Rv := by
    intro v hv
    rcases hv with hv | hv
    · exact AG_fv hs hl hq hv
    · exact Or.inr (hregR hv)
  -- the anchor with the region, kept along a frozen run before its last instant in `Bh`
  have hboxB : ∀ (Bh : Formula (Var n)), Bh.fv ⊆ range Rv →
      modalVerdDynPLX p cX n (rowIdx p l)
        (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)
        pre l q Bh →
      ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat (AGr p n cX cov reg l q) y →
      (pre = true → Formula.sat (guardL p n l) y) →
      ∀ T Φ, ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) ρ T Φ →
      (∀ t ∈ Ico (0 : ℝ) T, Formula.sat Bh (Φ t)) →
      Formula.sat (AGr p n cX cov reg l q) (mergeLR y y (Φ T)) := by
    intro Bh hBfv hvB y ρ hyρ hA hgLy T Φ H hB
    refine ⟨AG_boxPLH hs hnc hst hl hq pre hflag' Bh hBfv hvB y ρ hyρ hA.1 hgLy T Φ H hB, ?_⟩
    have hrunW := right_sol_merge_joint (fR_fv (hnames hs) q) (domL_fv (hnames hs))
      (domR_fv (hnames hs)) H y y hA.1.2.1
    have hregσ : Formula.sat reg (mergeLR y y ρ) :=
      (sat_merge_R hregR y y ρ).mpr ((Formula.coincidence reg (fun v hv => by
        obtain ⟨i, rfl⟩ := hregR hv; exact hyρ i)).mp hA.2)
    exact reg_kept_joint hinv hregR (fR_fv (hnames hs) q) (domR_fv (hnames hs)) hm rfl rfl 1
      zero_le_one hrunW hregσ
  have hε : 0 < epsR p := (timeOK_at (htime hs) hl).1
  have hR : ∀ y, Formula.sat (AGr p n cX cov reg l q) y → (pre = true → Formula.sat (guardL p n l) y) →
      Formula.sat (regionF p n cX l q pre) y := fun y hA hg => AG_regionF hs hl hq pre y hA.1 hg
  have hRsat : ∀ y, Formula.sat (regionF p n cX l q pre) y →
      RegionSat (vars p) n cX (mLof p l) (mRof p q) (rowOf p l) pre y :=
    fun y hy => regionSat_of_regionF hs hl pre y hy
  have hpruneD := fun e he hp σ ω (hA : Formula.sat (AGr p n cX cov reg l q) σ) hω =>
    AG_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω
  rcases certOK_shape hok with ⟨st, hstg⟩ | ⟨sth, st, hstg, huph, hup⟩
  · -- one stage, in either direction
    obtain ⟨hrpos, -, hfree⟩ := certOK_stage hok (st := st) (by rw [hstg]; simp)
    have hlast : c.stages.getLast? = some st := by rw [hstg]; rfl
    cases hup : st.up
    · -- downward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one_down hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      have hBfv : (before v st).toHost.fv ⊆ range Rv := by
        intro x hx
        simp [before, hup, IForm.toHost, ITerm.toHost, Formula.fv, Term.fv] at hx
        rw [hx, hvR]; exact ⟨v.2, rfl⟩
      refine repoProgress_one_downB (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGr p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε tr htrL htrR reg hregR (fun y h => h.2) hex hcomp
        (fun x => Formula.sat (before v st).toHost x)
        (hboxB _ hBfv (hdv st hlast v hv'))
        hpruneD (regionF p n cX l q pre) hR v.2 (st.theta : ℝ) ?_ ?_ (st.rate : ℝ) hrpos ?_ ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro x hx
        rw [sat_before_down v st hup, hvR]; exact hx
      · intro y hy hg hθ
        exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
      · intro y hy hlt
        exact hrate y (hRsat y hy) (by rw [hvR]; exact hlt)
    · -- upward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      have hBfv : (before v st).toHost.fv ⊆ range Rv := by
        intro x hx
        simp [before, hup, IForm.toHost, ITerm.toHost, Formula.fv, Term.fv] at hx
        rw [hx, hvR]; exact ⟨v.2, rfl⟩
      refine repoProgress_oneB (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGr p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε tr htrL htrR reg hregR (fun y h => h.2) hex hcomp
        (fun x => Formula.sat (before v st).toHost x)
        (hboxB _ hBfv (hdv st hlast v hv'))
        hpruneD (regionF p n cX l q pre) hR v.2 (st.theta : ℝ) ?_ ?_ ?_ (st.rate : ℝ) hrpos ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro x hx
        rw [sat_before_up v st hup, hvR]; exact hx
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
    have hBfv : (before v st).toHost.fv ⊆ range Rv := by
      intro x hx
      simp [before, hup, IForm.toHost, ITerm.toHost, Formula.fv, Term.fv] at hx
      rw [hx, hvR]; exact ⟨v.2, rfl⟩
    refine repoProgress_twoB (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
      (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
      (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
      (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGr p n cX cov reg l) hAfv'
      (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε tr htrL htrR reg hregR (fun y h => h.2) hex hcomp
      (fun x => Formula.sat (before v st).toHost x)
      (hboxB _ hBfv (hdv st hlast v hv'))
      hpruneD (regionF p n cX l q pre) hR v.2 (st.theta : ℝ) ?_ ?_ ?_ (st.rate : ℝ) hrpos w.2
      (sth.theta : ℝ) (sth.rate : ℝ) hrhpos ?_ ?_ ?_
    · intro y hy hθ
      exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
    · intro x hx
      rw [sat_before_up v st hup, hvR]; exact hx
    · intro y hy hg hθ
      exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
    · intro y hy hlt
      exact hrate_h y (hRsat y hy) (by rw [hwR]; exact hlt)
    · intro y hy hle
      exact hkeep_h y (hRsat y hy) (by rw [hwR]; exact hle)
    · intro y hy hθh hlt
      exact hrate y (hRsat y hy) (by rw [hwR]; exact hθh) (by rw [hvR]; exact hlt)

/-! ### The window theorem, with the pre-landing verdicts -/

/-- A chosen set's coverage premise, from its entry's verdict (`cov_of_entry`). -/
theorem cov_of_entryPL (hv : VerdictsPL p n cX cov prog ce) (hpo : progOK p n cov prog = true)
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

/-- **The certificates of window `l`**, as `CoverHyps` (`coverHyps_of` with the pre-landing
progress premise). -/
theorem coverHyps_ofPL (hv : VerdictsPL p n cX cov prog ce) (hpo : progOK p n cov prog = true)
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
    hrepoProg_ofPL hs hv.nonconn hv.stay hv.prog hpo hregR hinv hwf hv.dyn ((Side.Aux, d) : Var n)
      (aux_notin_range_Lv d) (aux_notin_range_Rv d) hl q m hm pre
      (by cases pre <;> simpa [chOfC, chOf] using hflag)
  hRJ := fun q y hA => by
    unfold RJof; split_ifs with hq
    · exact AG_regionF hs hl hq false y hA.1 (by simp)
    · trivial
  hcovJ := fun q S hS y hy => by
    refine cov_of_entryPL hs hv hpo hl hS y (fun hq => ?_) (by simp)
    unfold RJof at hy; rw [if_pos hq] at hy; simpa using hy
  hRR := fun q σ y hA hgL => by
    unfold RRof; split_ifs with hq
    · exact AG_regionF hs hl hq (preOf σ) y hA.1 (fun hp => hgL (by cases σ <;> simp_all [preOf]))
    · trivial
  hcovR := fun q σ S hS y hy => by
    refine cov_of_entryPL hs hv hpo hl hS y (fun hq => ?_) (by simp)
    unfold RRof at hy; rw [if_pos hq] at hy; simpa using hy
  hRS := fun q σ y hA hg hgL => by
    unfold RSof; split_ifs with hq
    · exact ⟨AG_regionF hs hl hq (preOf σ) y hA.1 (fun hp => hgL (by cases σ <;> simp_all [preOf])), hg⟩
    · trivial
  hcovS := fun q σ S hS y hy => by
    refine cov_of_entryPL hs hv hpo hl hS y (fun hq => ?_) (fun _ => ?_)
    · unfold RSof at hy; rw [if_pos hq] at hy; simpa using hy.1
    · by_cases hq : q < nR p
      · unfold RSof at hy; rw [if_pos hq] at hy; exact hy.2
      · obtain ⟨e, he, -⟩ := List.mem_map.mp hS
        exact absurd (mem_entriesAt he).1 hq

/-- Every admissible start is covered (decided) and every other start is inadmissible
(`hcov_of`). -/
theorem hcov_ofPL (hv : VerdictsPL p n cX cov prog ce) (hcovers : coversOK p n cov ce = true)
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

omit hs in
/-- **Theorem 3 of a one-row benchmark with pre-landing right-only nodes, from its records**
(window form). The claim is over the EMITTED cover `cov` (it reads its pruned edges only); the
structure, the progress shapes, the covers and the verdicts are those of the merged cover
`withPL cov pl`, and the data gate `plOK` admits the record only under the opt-in key. -/
theorem theorem3_window_of_records_pl {pl : PrelandEmitE}
    (_hpl : plOK p cov pl = true) (hs : structOK p n (withPL cov pl) cX = true)
    (hv : VerdictsPL p n cX (withPL cov pl) prog ce)
    (hpo : progOK p n (withPL cov pl) prog = true) (hcovers : coversOK p n (withPL cov pl) ce = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (hsame : rowsSame p = true) (a b d : Fin n) (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (dt : ℝ)
    (hdt : dt ≤ epsL p) :
    windowClaim p n cX cov reg a b d dt := by
  show windowClaim p n cX (withPL cov pl) reg a b d dt
  set covM := withPL cov pl
  unfold windowClaim
  refine theorem3_of_coverX (grOf p n (prunedOf covM)) a b d hab hda.symm hdb.symm dt (g p n 0)
    (gs p n 0)
    (comps_fv_any (p := p) (n := n) 0) (domL p n) (domR p n) (domL_fv (hnames hs))
    (domR_fv (hnames hs)) (guardR p n) (cutsR p n cX reg) grOf_guards (grOf_guardsRight (hnames hs))
    (guardR_fv (hnames hs)) (cutsR_fv hs hregR) (fR p n) (fun q _ => fR_fv (hnames hs) q)
    (fun _ _ hm => grOf_sys hm) (fun _ _ hm => grOf_dom hm) (fun _ _ hm => grOf_weight hm)
    (grOf_lt (n := n) (hres hs)) (nL p) (guardL p n) (fL p n) (fun l _ => guardL_fv (hnames hs) l)
    (fun l _ => fL_fv (hnames hs) l) (epsR p) reg hregR hwf (chOfC p covM ce) (B p covM) (δ p covM)
    (lamOf p covM) (AGr p n cX covM reg) (fun _ _ _ _ h => h.2) (RJof p n cX) (RRof p n cX) (RSof p n cX)
    (fun l hl => coverHyps_ofPL hs hv hpo hregR hinv hwf d hl) (fun l hl => hdt.trans (budget_span hs hl))
    ?_ ?_ ?_
  · intro l hl q hq hadm
    refine hcov_ofPL hs hv hcovers (reg := reg) hl q hq ?_
    obtain ⟨σ, h1, h2, h3, h4⟩ := hadm
    refine ⟨σ, h1, ⟨?_, h2.2⟩, h3, h4⟩
    show Formula.sat (FRow p n l) σ
    rw [FRow_same hsame]; exact h2.1
  · intro l hl q σ hgL hσ hg hc
    refine ⟨AG_start_any hs hv.nonconn hl q σ hgL ⟨?_, hσ.2⟩ hg hc.1, hc.2⟩
    show Formula.sat (FRow p n l) σ
    rw [FRow_same hsame]; exact hσ.1
  · intro l hl q' y hA
    have := AG_post_any hs hl q' y hA.1
    refine ⟨⟨?_, this.1.2⟩, this.2, hA.2⟩
    have hF : Formula.sat (FRow p n l) y := this.1.1
    rw [FRow_same hsame] at hF; exact hF

end Proofs

/-! ## The queries of a pre-landing benchmark, as groups -/

section Builders

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
  (prog : ProgressEmitE) (ce : ChoiceEmitE)

/-- The pre-landing pack of a flagged node: per component one group of the three routes, at
the region before its certificate's last stage. -/
def dynGroupsPL (l q : ℕ) (pre : Bool) : Option (List (List (IForm n))) :=
  if (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) then
    match certFor p prog l q pre with
    | none => none
    | some c =>
      match c.stages.getLast? with
      | none => none
      | some st =>
        match resolveVar (vars p) n Side.R st.var with
        | none => none
        | some v =>
          modalVerdDynPLXQueries p cX n (rowIdx p l)
            (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)
            pre l q (before v st)
  else some []

/-- **Every query of a pre-landing benchmark**, in groups (`bridgeGroups` with `dynGroupsPL`). -/
def bridgeGroupsPL : Option (List (List (IForm n))) := do
  let sL ← (List.range (nL p)).mapM (fun l =>
    stayGroups p n Side.L (mLof p l) (cutAtomsOfX cX.L (mLof p l).name))
  let sR ← (List.range (nR p)).mapM (fun q =>
    stayGroups p n Side.R (mRof p q) (cutAtomsOfX cX.R (mRof p q).name))
  let nc ← (List.range (nR p)).mapM (nonConnGroups p n cX cov)
  let jt ← (List.range (nL p)).mapM (fun l => (List.range (nR p)).mapM (jointGroups p n cX cov l))
  let dy ← (List.range (nL p)).mapM (fun l => (List.range (nR p)).mapM (fun q =>
    [true, false].mapM (dynGroupsPL p n cX cov prog l q)))
  let ad ← (List.range (nL p)).mapM (admGroups p n cov)
  let ho ← (List.range (nL p)).mapM (handoffGroups p n)
  let pr ← prog.certs.mapM (progGroups p n cX)
  let cv ← ce.entries.mapM (coverageGroups p n cX)
  pure (sL.flatten ++ sR.flatten ++ nc.flatten ++ jt.flatten.flatten ++
    dy.flatten.flatten.flatten ++ ad.flatten ++ ho.flatten ++ pr.flatten ++ cv.flatten)

end Builders

section Link

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  {ce : ChoiceEmitE}

theorem dynVerdPL_of_groups {l q : ℕ} {pre : Bool} {gs : List (List (IForm n))}
    (h : dynGroupsPL p n cX cov prog l q pre = some gs) (hok : GroupsOK gs)
    (hd : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true) :
    DynVerdPL p n cX cov prog l q pre := by
  intro c hc st hst v hv
  unfold dynGroupsPL at h
  rw [if_pos hd, hc] at h
  simp only [hst, hv] at h
  exact modalVerdDynPLX_of_queries h (fun i hi => hok _ (List.getElem_mem hi))

/-- **A green run is the `VerdictsPL` structure.** -/
theorem verdictsPL_of_groups {gs : List (List (IForm n))}
    (h : bridgeGroupsPL p n cX cov prog ce = some gs) (hok : GroupsOK gs) :
    VerdictsPL p n cX cov prog ce := by
  unfold bridgeGroupsPL at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at h
  obtain ⟨sL, hsL, sR, hsR, nc, hnc, jt, hjt, dy, hdy, ad, had, ho, hho, pr, hpr, cv, hcv, rfl⟩ := h
  obtain ⟨h1, h9⟩ := groupsOK_append hok
  obtain ⟨h1, h8⟩ := groupsOK_append h1
  obtain ⟨h1, h7⟩ := groupsOK_append h1
  obtain ⟨h1, h6⟩ := groupsOK_append h1
  obtain ⟨h1, h5⟩ := groupsOK_append h1
  obtain ⟨h1, h4⟩ := groupsOK_append h1
  obtain ⟨h1, h3⟩ := groupsOK_append h1
  obtain ⟨h1, h2⟩ := groupsOK_append h1
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨g, hg, hgl⟩ := mapM_range hsL l hl
    exact stayVerd_of_groups hgl (groupsOK_flatten h1 _ hg)
  · intro q hq
    obtain ⟨g, hg, hgq⟩ := mapM_range hsR q hq
    exact stayVerd_of_groups hgq (groupsOK_flatten h2 _ hg)
  · intro q hq
    obtain ⟨g, hg, hgq⟩ := mapM_range hnc q hq
    exact nonConnVerd_of_groups hgq (groupsOK_flatten h3 _ hg)
  · intro l hl q hq hj
    obtain ⟨gl, hgl, hl'⟩ := mapM_range hjt l hl
    obtain ⟨g, hg, hq'⟩ := mapM_range hl' q hq
    exact jointVerd_of_groups hq' (groupsOK_flatten h4 _ (List.mem_flatten.mpr ⟨gl, hgl, hg⟩)) hj
  · intro l hl q hq pre hd
    obtain ⟨gl, hgl, hl'⟩ := mapM_range hdy l hl
    obtain ⟨gq, hgq, hq'⟩ := mapM_range hl' q hq
    obtain ⟨g, hg, hpre⟩ := mapM_option_forall hq' pre (by cases pre <;> simp)
    exact dynVerdPL_of_groups hpre
      (groupsOK_flatten h5 _ (List.mem_flatten.mpr ⟨gq, List.mem_flatten.mpr ⟨gl, hgl, hgq⟩, hg⟩)) hd
  · intro l hl q hq hmem
    obtain ⟨g, hg, hgl⟩ := mapM_range had l hl
    exact admVerd_of_groups hgl (groupsOK_flatten h6 _ hg) q hq hmem
  · intro m' hm' t ht
    obtain ⟨g, hg, hgm⟩ := mapM_range hho m' hm'
    exact handoffVerd_of_groups hgm (groupsOK_flatten h7 _ hg) t ht
  · intro c hc
    obtain ⟨g, hg, hgc⟩ := mapM_option_forall hpr c hc
    exact progVerd_of_groups hgc (groupsOK_flatten h8 _ hg)
  · intro e he
    obtain ⟨g, hg, hge⟩ := mapM_option_forall hcv e he
    exact coverageVerd_of_groups hge (groupsOK_flatten h9 _ hg)

end Link

end Emitted
end RelCertifier
