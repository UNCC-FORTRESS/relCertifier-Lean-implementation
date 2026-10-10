/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung1` over the GUARDED right automaton — Theorem 3 by the ladder climb

`RoverDofTerrainRung1Modal.rover_dof_terrain_rung1_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT` with the bookkeeping `mvValid`. This file states it over the
GUARDED chain (every edge tests the lowered guard of the band it enters, `GrG_guards`) at the
mode-consistent region (the right in the guard of its current band; no cut is kept), with the
response of `Proofs/Encoding/LadderClimb.lean`: after the left window the reference climbs the
chain (explicit runs, each switch at the next band's floor, legal) and holds `FLAT` until
`v_L ≤ v_R` and `s_L ≤ s_R + 0.2`. Z3-free.
-/
import RelCertifier.Instances.RoverDofTerrainRung1Modal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverDofTerrainRung1Guarded

open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung1Modal GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsE 3 Side.R (mRE tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeE 0, modeE 1, modeE 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range rover_dof_terrain_rung1_IR.R.modes.length).flatMap (fun q =>
      (mRE q).next.map (fun nm =>
        (q, rover_dof_terrain_rung1_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range rover_dof_terrain_rung1_IR.R.modes.length).flatMap (fun q =>
      (mRE q).next.map (fun nm =>
        (q, rover_dof_terrain_rung1_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsE 3 Side.R (mRE e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeE q) := by
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
  have hqm : q < 3 ∧ m = modeE q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])
  obtain ⟨hq3, rfl⟩ := hqm
  exact hRvE q (modeE q) (GrE_modeAt q hq3)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvE ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsE 3 Side.R (mRE q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsE _ dummyE rfl (by
    simp [rover_dof_terrain_rung1_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRE, rover_dof_terrain_rung1_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRE, rover_dof_terrain_rung1_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRE, rover_dof_terrain_rung1_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region (the guard; no kept cut) -/

noncomputable def gregion (q : ℕ) : Formula (Var 3) :=
  regionG (fun q => hostGuard vsE 3 Side.R (mRE q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvE ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The ladder run (explicit; `ψ_R` frozen) -/

theorem cstE_eq (q : ℕ) : cstE q = ladC q := rfl

noncomputable def aR : Fin 3 → ℝ := fun _ => 0
noncomputable def bR : Fin 3 → ℝ := fun _ => 0

noncomputable def LR : LadderRun GrG domRE :=
  LadderRun.ofLinear GrG domRE modeE fRE aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRE0_eval q hq, cstE_eq])
    (fun q hq x => fRE1_eval q hq x)
    (fun q hq i h0 h1 x => by
      have hi : i = 2 := by fin_cases i <;> simp_all
      subst hi
      rw [fRE2_eval q hq]; simp [aR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRE ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 1) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 1) hD.2.2.2.1 ht).2
      have hp := phiLin_other aR bR q ρ (n := 1) 2 (by decide) (by decide) t
      have hc := ladC_bounds q
      rw [sat_domRE, trajR_R, trajR_R, trajR_R]
      simp only [aR, bR, zero_mul, neg_zero, Real.exp_zero, mul_one, zero_add, sub_zero] at hp
      rw [hp]
      refine ⟨hD.1, hD.2.1, by linarith [hD.2.2.1], ?_, ?_⟩
      · exact le_trans (le_min hD.2.2.2.1 (by linarith)) hv.1
      · exact le_trans hv.2 (max_le hD.2.2.2.2 (by linarith)))
    (fun ρ hρ => ((sat_domRE ρ).mp hρ).2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

/-! ## The guarded response to a left window -/

theorem fLE0_eval (l : ℕ) (hl : l < 3) (x : State (Var 3)) :
    Term.eval (fLE l 0) x = 3 * (cstE l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLE, hostDyn, mLE, rover_dof_terrain_rung1_IR, vsE, Run.dynOf,
      Run.lowerE, gp_3, gp_0_30, gp_0_50, gp_0_65, gp_1, gp_0_5, gp_m1, gp_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Lv, cstE]

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 3)}
    (h : Program.sem (windowSeg (leftBlock (fLE l)) domLE tgE dt 1) σ ν) (i : Fin 3) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLE l) domLE 1 dt 1 (hfLE l hl) hdomLE
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem sat_FE (x : State (Var 3)) : Formula.sat (FM gE gsE) x ↔
    (x (Lv 0) - x (Rv 0) ≤ 0 ∧ x (Lv 1) - (x (Rv 1) + 1/5) ≤ 0) := by
  rw [sat_FM_iff]
  simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    gAt0_eval, gAt1_eval]

/-- **The guarded response** of left window `l` from right band `q` (in its guard): the
ladder climb, then hold `FLAT` until both rows hold. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM gE gsE) envE) σ)
    (hguard : Formula.sat (hostGuard vsE 3 Side.R (mRE q)) σ) :
    GResp GrG q (windowSeg (leftBlock (fLE l)) domLE tgE dt 1)
      (fun _ => Formula.and (Formula.and (FM gE gsE) envE) Formula.tt) σ := by
  refine gresp_of_rresp (fun ν hwin => ?_)
  have hR := window_right l hl dt hwin
  have hvL := windowSeg_coord_le_or_lt (fLE l) domLE tgE dt 0 3 (cstE l) (by norm_num)
    (by simp [Lv, Prod.ext_iff]) (fun s _ => fLE0_eval l hl s) 1 hwin
  have hrow := (sat_FE σ).mp hσ.1
  have hdomLν : Formula.sat domLE ν :=
    windowSeg_end_domL (leftBlock (fLE l)) domLE tgE dt 1 (by norm_num) hwin
  have hdomRν : Formula.sat domRE ν := by
    refine (Formula.coincidence domRE (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRE hx
    exact (hR i).symm
  have hgν : Formula.sat (hostGuard vsE 3 Side.R (mRE q)) ν :=
    frames_right (vars_windowSegL_sub (fLE l) domLE 1 dt 1 (hfLE l hl) hdomLE)
      (hguardR_all q) hwin hguard
  have hcl := ladC_bounds l
  have hV : ν (Lv 0) < 13/20 ∨ ν (Lv 0) ≤ ν (Rv 0) := by
    rcases hvL with h | h
    · right; rw [hR 0]; linarith [hrow.1]
    · left; rw [cstE_eq] at h; linarith [hcl.2]
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domRE μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ν (Rv 0) ≤ μ (Rv 0) → ν (Lv 0) ≤ μ (Rv 0) →
      ν (Lv 1) - 1/5 ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM gE gsE) envE) Formula.tt) μ := by
    intro μ hμL hμd _ _ _ hv hs
    refine ⟨⟨(sat_FE μ).mpr ⟨by rw [hμL 0]; linarith, by rw [hμL 1]; linarith⟩, ?_, hμd⟩,
      trivial⟩
    refine (Formula.coincidence domLE (fun x hx => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLE hx
    exact hμL i
  refine LR.climb q hq ν hdomRν ⟨?_, ?_, ?_⟩ _ _ hV hfin
  · rintro rfl; rw [sat_guardR0] at hgν; exact ⟨hgν.2.1, hgν.2.2⟩
  · rintro rfl; rw [sat_guardR1] at hgν; exact hgν
  · rintro rfl; rw [sat_guardR2] at hgν; exact hgν

/-! ## Theorem 3 over the guarded automaton -/

/-- **`rover_dof_terrain_rung1`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The left: the file's three windows (`bigChoice`, one clocked piece of
at most `dt` each); the right: the chain `STEEP → MODER → FLAT` of the file with every edge
testing the entered band's guard (`GrG_guards`). Loop invariant: the declared rows
`v_L ≤ v_R ∧ s_L ≤ s_R + 0.2`, both envelopes, the right in the guard of its current band
(`mvRegionR` at `gregion`). Response: the ladder climb. Z3-free; every window length `dt`. -/
theorem rover_dof_terrain_rung1_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsE dt))
      (rightAutomatonBody GrG mvE)
      (RFormula.and (RFormula.and (canonInvM gE gsE) (envLR domLE domRE))
        (mvRegionR mvE gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvE (FM gE gsE) domLE domRE gregion
    (leftProgsE dt) (canonInvM gE gsE) (encode_canonInvM gE gsE) ?_ ?_ ?_
  · exact hdis_multi_G GrG 0 1 dt leftDataE (by decide) hgRG hRvG hLE
  · refine hstep_assembled_GR GrG mvE (FM gE gsE) envE gregion (leftProgsE dt)
      hmvFE hmvenvE hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesE dt) ?_
    refine Hmulti_regionG GrG mvE _ (fun _ => Formula.tt) GrG_guards (FM gE gsE) envE
      (leftProgsE dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsE, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_windowSegL_sub d.1 d.2.1 1 dt d.2.2 (hLE d hd).1 (hLE d hd).2)
        (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsE, leftDataE, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt q hq hσ hg
      · exact respondG 1 (by norm_num) dt q hq hσ hg
      · exact respondG 2 (by norm_num) dt q hq hσ hg
  · exact hddF_multiR_plain_G GrG 0 1 dt leftDataE gregion (canonInvM gE gsE) domLE domRE
      (by decide) hgRG hRvG hLE (fun q _ => gregion_fv q)
      (canonInvM_varsL gE gsE (by
        intro g' hg'
        simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gE gsE) hdomLE hdomRE

end RoverDofTerrainRung1Guarded
end RelCertifier
