/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rung2b_6dof` over the GUARDED right automaton — Theorem 3 by the ladder climb

`RoverRung2b6dofModal.rung2b_6dof_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT` with the bookkeeping `mvValid`. This file states it over the
GUARDED chain (every edge tests the lowered guard of the band it enters, `GrG_guards`) at the
mode-consistent region (the right in the guard of its current band; no cut is kept), with the
response of `Proofs/Encoding/LadderClimb.lean`: after the left window the reference climbs the
chain (explicit runs, each switch at the next band's floor, legal) and holds `FLAT` until
the declared combined-coordinate row holds. Z3-free.
-/
import RelCertifier.Instances.RoverRung2b6dofModal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverRung2b6dofGuarded

open DL DLCalTiming DLRel Parse Set RoverRung2b6dofModal GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := hostGuard vsB2 6 Side.R (mRB2 tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [modeB2 0, modeB2 1, modeB2 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range refinement_ladder_rover_rung2b_6dof_IR.R.modes.length).flatMap (fun q =>
      (mRB2 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2b_6dof_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range refinement_ladder_rover_rung2b_6dof_IR.R.modes.length).flatMap (fun q =>
      (mRB2 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2b_6dof_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsB2 6 Side.R (mRB2 e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeB2 q) := by
  interval_cases q <;> rfl

theorem GrG_len : GrG.modes.length = 3 := rfl

theorem hltG : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.tgt < GrG.modes.length := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrG, edgeG]

theorem hRvG : ∀ q m, GrG.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hq : q < 3 := by
    by_contra h
    have hn : GrG.modeAt q = none := List.getElem?_eq_none (by simp [GrG]; omega)
    rw [hn] at hm; exact absurd hm (by simp)
  have hm' : m = modeB2 q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvB2 q (modeB2 q) (GrB2_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvB2 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsB2 6 Side.R (mRB2 q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsB2 _ dummyB2 rfl (by
    simp [refinement_ladder_rover_rung2b_6dof_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 6)) : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 6)) : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 6)) : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x ↔
    (7/5 ≤ x (Rv 1)) := by
  simp [hostGuard, mRB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region (the guard; no kept cut) -/

noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vsB2 6 Side.R (mRB2 q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvB2 ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cB2_eq (q : ℕ) : cB2 q = ladC q := rfl

noncomputable def aR : Fin 6 → ℝ := ![0, 0, 0, 0, 0, 0]
noncomputable def bR : Fin 6 → ℝ := fun _ => 0

theorem aR_nonneg : ∀ k, 0 ≤ aR k := by
  intro k; fin_cases k <;> simp [aR]

noncomputable def LR : LadderRun GrG domRB2 :=
  LadderRun.ofLinear GrG domRB2 modeB2 fRB2 aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRB20_eval q hq, cB2_eq])
    (fun q hq x => fRB21_eval q hq x)
    (fun q hq i h0 h1 x => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB22_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB23_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB24_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB25_eval q hq]; simp [aR, bR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRB2 ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 4) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 4) hD.2.2.2.2.2.2.2.1 ht).2
      have hc := ladC_bounds q
      have hk : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) (bR k) ≤ phiLin aR bR q ρ k t ∧
            phiLin aR bR q ρ k t ≤ max (ρ (Rv k)) (bR k) :=
        fun k h0 h1 => phiLin_other_between aR bR q ρ k h0 h1 (aR_nonneg k) ht
      rw [sat_domRB2]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num [bR])) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.1 (by norm_num [bR])) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num [bR])),
        le_trans hD.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.1 (by norm_num [bR])) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2 (by norm_num [bR]))⟩)
    (fun ρ hρ => by have hD := (sat_domRB2 ρ).mp hρ; exact hD.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x
      rw [sat_guardR2]; exact hs)

/-! ## The guarded response to a left window: the combined coordinate `w = s + v/3`

Along every right band `w` grows at exactly the band's set point (`ṡ + v̇/3 = v + (c − v)`),
and the declared row is `w_L ≤ w_R + 0.2`. -/

noncomputable def wR (x : State (Var 6)) : ℝ := x (Rv 1) + x (Rv 0) / 3

theorem run_w (q : ℕ) (ρ : State (Var 6)) (t : ℝ) :
    wR (LR.run q ρ t) = wR ρ + ladC q * t := by
  show wR (trajR ρ (phiLin aR bR q ρ) t) = wR ρ + ladC q * t
  simp only [wR, trajR_R, phiLin, one_ne_zero, if_false, if_true]
  ring

/-- **The climb by the combined coordinate**: from band `q` (in its odometer band), climb to
`FLAT` and hold it until `w_R ≥ W`; every switch at the next band's floor (legal). -/
theorem climbW (q : ℕ) (hq : q < 3) (ρ : State (Var 6)) (hdom : Formula.sat domRB2 ρ)
    (hg : (q = 0 → ρ (Rv 1) < 3/5) ∧ (q = 1 → 3/5 ≤ ρ (Rv 1) ∧ ρ (Rv 1) < 7/5) ∧
      (q = 2 → 7/5 ≤ ρ (Rv 1))) (W : ℝ) {post : ℕ → Formula (Var 6)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domRB2 μ → 7/5 ≤ μ (Rv 1) →
      W ≤ wR μ → Formula.sat (post 2) μ) :
    RResp GrG q post ρ := by
  -- the FLAT hold, from any FLAT state
  have hflat : ∀ κ, Formula.sat domRB2 κ → 7/5 ≤ κ (Rv 1) → (∀ i, κ (Lv i) = ρ (Lv i)) →
      RResp GrG 2 post κ := by
    intro κ hκ hs hκL
    set τ : ℝ := max 0 ((W - wR κ) * (20/13)) with hτ
    have hτ0 : 0 ≤ τ := le_max_left _ _
    have hrun := LR.sem 2 (by norm_num) κ hκ τ hτ0
    set μ := LR.run 2 κ τ with hμ
    have hμs : 7/5 ≤ μ (Rv 1) := le_trans hs (LR.s_low 2 (by norm_num) κ hκ τ hτ0).2
    have hw : W ≤ wR μ := by
      rw [hμ, run_w]
      have : (W - wR κ) * (20/13) ≤ τ := le_max_right _ _
      have hc : ladC 2 = 13/20 := by norm_num [ladC]
      rw [hc]; nlinarith
    have hleg : SwitchLegal (edgeG 2 2) μ := by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) μ
      rw [sat_guardR2]; exact hμs
    exact rresp_step (post := post) (LR.modeAt 2 (by norm_num))
      (edgeG_mem 2 2 (by simp [GrG])) hrun hleg (rresp_stop (hpost μ (fun i => (LR.left 2 κ τ i).trans (hκL i))
      (LR.end_dom 2 (by norm_num) κ hκ τ hτ0) hμs hw))
  have hmoder : ∀ κ, Formula.sat domRB2 κ → κ (Rv 1) < 7/5 → (∀ i, κ (Lv i) = ρ (Lv i)) →
      RResp GrG 1 post κ := by
    intro κ hκ hs hκL
    obtain ⟨τ, hτ, hτs⟩ := LR.reach 1 (by norm_num) κ hκ (7/5) (le_of_lt hs)
    have hrun := LR.sem 1 (by norm_num) κ hκ τ hτ
    have hleg : SwitchLegal (edgeG 1 2) (LR.run 1 κ τ) := by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) (LR.run 1 κ τ)
      rw [sat_guardR2]; exact le_of_eq hτs.symm
    exact rresp_step (post := post) (LR.modeAt 1 (by norm_num))
      (edgeG_mem 1 2 (by simp [GrG])) hrun hleg (hflat _ (LR.end_dom 1 (by norm_num) κ hκ τ hτ) (le_of_eq hτs.symm)
      (fun i => (LR.left 1 κ τ i).trans (hκL i)))
  interval_cases q
  · obtain ⟨τ, hτ, hτs⟩ := LR.reach 0 (by norm_num) ρ hdom (3/5) (le_of_lt (hg.1 rfl))
    have hrun := LR.sem 0 (by norm_num) ρ hdom τ hτ
    have hleg : SwitchLegal (edgeG 0 1) (LR.run 0 ρ τ) := by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 1)) (LR.run 0 ρ τ)
      rw [sat_guardR1]; exact ⟨le_of_eq hτs.symm, by rw [hτs]; norm_num⟩
    exact rresp_step (post := post) (LR.modeAt 0 (by norm_num))
      (edgeG_mem 0 1 (by simp [GrG])) hrun hleg (hmoder _ (LR.end_dom 0 (by norm_num) ρ hdom τ hτ) (by rw [hτs]; norm_num)
      (fun i => LR.left 0 ρ τ i))
  · exact hmoder ρ hdom (hg.2.1 rfl).2 (fun _ => rfl)
  · exact hflat ρ hdom (hg.2.2 rfl) (fun _ => rfl)

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 6)}
    (h : Program.sem (windowSeg (leftBlock (fLB2 l)) domLB2 tgB2 dt 2) σ ν) (i : Fin 6) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLB2 l) domLB2 1 dt 2 (hfLB2 l hl) hdomLB2
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem sat_FB2 (x : State (Var 6)) : Formula.sat (FM gB2 gsB2) x ↔
    (x (Lv 1) - x (Rv 1) - 1/5) + 1/3 * (x (Lv 0) - x (Rv 0)) ≤ 0 := by
  rw [sat_FM_iff]
  simp only [gsB2, List.mem_cons, List.not_mem_nil, or_false, forall_eq, eval_gB2]

/-- **The guarded response** of left window `l` from right band `q` (in its guard): climb to
`FLAT` and hold until `w_R ≥ w_L − 0.2`. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3) {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (FM gB2 gsB2) envB2) σ)
    (hguard : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 q)) σ) :
    GResp GrG q (windowSeg (leftBlock (fLB2 l)) domLB2 tgB2 dt 2)
      (fun _ => Formula.and (Formula.and (FM gB2 gsB2) envB2) Formula.tt) σ := by
  refine gresp_of_rresp (fun ν hwin => ?_)
  have hR := window_right l hl dt hwin
  have hdomLν : Formula.sat domLB2 ν :=
    windowSeg_end_domL (leftBlock (fLB2 l)) domLB2 tgB2 dt 2 (by norm_num) hwin
  have hdomRν : Formula.sat domRB2 ν := by
    refine (Formula.coincidence domRB2 (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRB2 hx
    exact (hR i).symm
  have hgν : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 q)) ν :=
    frames_right (vars_windowSegL_sub (fLB2 l) domLB2 1 dt 2 (hfLB2 l hl) hdomLB2)
      (hguardR_all q) hwin hguard
  refine climbW q hq ν hdomRν ⟨?_, ?_, ?_⟩ (ν (Lv 1) + ν (Lv 0) / 3 - 1/5) ?_
  · rintro rfl; rw [sat_guardR0] at hgν; exact hgν.2
  · rintro rfl; rw [sat_guardR1] at hgν; exact hgν
  · rintro rfl; rw [sat_guardR2] at hgν; exact hgν
  · intro μ hμL hμd _ hw
    refine ⟨⟨(sat_FB2 μ).mpr ?_, ?_, hμd⟩, trivial⟩
    · rw [hμL 0, hμL 1]; unfold wR at hw; linarith
    · refine (Formula.coincidence domLB2 (fun x hx => ?_)).mpr hdomLν
      obtain ⟨i, rfl⟩ := hdomLB2 hx
      exact hμL i

/-! ## Theorem 3 over the guarded automaton -/

/-- **`rung2b_6dof`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The left: the file's three windows (`bigChoice`, two clocked pieces of
at most `dt` each); the right: the chain `STEEP → MODER → FLAT` of the file with every edge
testing the entered band's guard (`GrG_guards`). Loop invariant: the declared rows
`(s_L − s_R − 0.2) + (v_L − v_R)/3 ≤ 0`, both envelopes, the right in the guard of its current band
(`mvRegionR` at `gregion`). Response: climb to `FLAT` and hold until `s_R + v_R/3 ≥ s_L + v_L/3 − 0.2` (`climbW`). Z3-free; every window length `dt`. -/
theorem rung2b_6dof_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsB2 dt))
      (rightAutomatonBody GrG mvB2)
      (RFormula.and (RFormula.and (canonInvM gB2 gsB2) (envLR domLB2 domRB2))
        (mvRegionR mvB2 gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvB2 (FM gB2 gsB2) domLB2 domRB2 gregion
    (leftProgsB2 dt) (canonInvM gB2 gsB2) (encode_canonInvM gB2 gsB2) ?_ ?_ ?_
  · exact hdis_multi_G GrG 0 1 dt leftDataB2 (by decide) hgRG hRvG hLB2
  · refine hstep_assembled_GR GrG mvB2 (FM gB2 gsB2) envB2 gregion (leftProgsB2 dt)
      hmvFB2 hmvenvB2 hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesB2 dt) ?_
    refine Hmulti_regionG GrG mvB2 _ (fun _ => Formula.tt) GrG_guards (FM gB2 gsB2) envB2
      (leftProgsB2 dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsB2, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_windowSegL_sub d.1 d.2.1 1 dt d.2.2 (hLB2 d hd).1 (hLB2 d hd).2)
        (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsB2, leftDataB2, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt q hq hσ hg
      · exact respondG 1 (by norm_num) dt q hq hσ hg
      · exact respondG 2 (by norm_num) dt q hq hσ hg
  · exact hddF_multiR_plain_G GrG 0 1 dt leftDataB2 gregion (canonInvM gB2 gsB2) domLB2 domRB2
      (by decide) hgRG hRvG hLB2 (fun q _ => gregion_fv q)
      (canonInvM_varsL gB2 gsB2 (by
        intro g' hg'
        simp only [gB2, gsB2, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gB2 gsB2) hdomLB2 hdomRB2

end RoverRung2b6dofGuarded
end RelCertifier
