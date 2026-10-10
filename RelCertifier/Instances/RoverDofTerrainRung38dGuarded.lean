/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung3_8d` over the GUARDED right automaton — Theorem 3 by the ladder climb

`RoverDofTerrainRung38dModal.rover_dof_terrain_rung3_8d_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT` with the bookkeeping `mvValid`. This file states it over the
GUARDED chain (every edge tests the lowered guard of the band it enters, `GrG_guards`) at the
mode-consistent region (the right in the guard of its current band; no cut is kept), with the
response of `Proofs/Encoding/LadderClimb.lean`: after the left window the reference climbs the
chain (explicit runs, each switch at the next band's floor, legal) and holds `FLAT` until
`v_L ≤ v_R` and `s_L ≤ s_R + 0.2`. Z3-free.
-/
import RelCertifier.Instances.RoverDofTerrainRung38dModal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverDofTerrainRung38dGuarded

open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung38dModal GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := hostGuard vsU 8 Side.R (mRU tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 8) :=
  { modes := [modeU 0, modeU 1, modeU 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range rover_dof_terrain_rung3_8d_IR.R.modes.length).flatMap (fun q =>
      (mRU q).next.map (fun nm =>
        (q, rover_dof_terrain_rung3_8d_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range rover_dof_terrain_rung3_8d_IR.R.modes.length).flatMap (fun q =>
      (mRU q).next.map (fun nm =>
        (q, rover_dof_terrain_rung3_8d_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsU 8 Side.R (mRU e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeU q) := by
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
  have hqm : q < 3 ∧ m = modeU q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])
  obtain ⟨hq3, rfl⟩ := hqm
  exact hRvU q (modeU q) (GrU_modeAt q hq3)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvU ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsU 8 Side.R (mRU q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsU _ dummyU rfl (by
    simp [rover_dof_terrain_rung3_8d_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region (the guard; no kept cut) -/

noncomputable def gregion (q : ℕ) : Formula (Var 8) :=
  regionG (fun q => hostGuard vsU 8 Side.R (mRU q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvU ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cstU_eq (q : ℕ) : cstU q = ladC q := rfl

noncomputable def aR : Fin 8 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 1]
noncomputable def bR : Fin 8 → ℝ := fun _ => 0

theorem aR_nonneg : ∀ k, 0 ≤ aR k := by
  intro k; fin_cases k <;> simp [aR]

noncomputable def LR : LadderRun GrG domRU :=
  LadderRun.ofLinear GrG domRU modeU fRU aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRU0_eval q hq, cstU_eq])
    (fun q hq x => fRU1_eval q hq x)
    (fun q hq i h0 h1 x => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU2_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU3_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU4_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU5_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU6_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU7_eval q hq]; simp [aR, bR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRU ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 6) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 6) hD.2.2.2.2.2.2.2.2.2.2.2.1 ht).2
      have hc := ladC_bounds q
      have hk : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) (bR k) ≤ phiLin aR bR q ρ k t ∧
            phiLin aR bR q ρ k t ≤ max (ρ (Rv k)) (bR k) :=
        fun k h0 h1 => phiLin_other_between aR bR q ρ k h0 h1 (aR_nonneg k) ht
      rw [sat_domRU]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num [bR])) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.1 (by norm_num [bR])) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num [bR])) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans hD.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num [bR]))⟩)
    (fun ρ hρ => by have hD := (sat_domRU ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

/-! ## The guarded response to a left window -/

theorem fLU0_eval (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLU l 0) x = 3 * (cstU l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLU, hostDyn, mLU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_1, gp_0_15, gp_0_2, gp_0_25, gp_0_3, gp_0_30, gp_0_35, gp_0_4, gp_0_5, gp_0_50, gp_0_6, gp_0_65, gp_0_7, gp_0_75, gp_0_8, gp_0_9, gp_1, gp_1_0, gp_1_1, gp_1_2, gp_1_4, gp_1_5, gp_1_6, gp_2, gp_2_0, gp_3, gp_4, gp_5, gp_10, gp_m0_5, gp_m0_25, gp_m1, gp_m1_0, gp_m2, gp_m0_3, gp_m0_6, gp_0_125, gp_1_125, gp_0_156, gp_0_33, gp_899_95, gp_m1_5, gp_1_52, gp_m1_52, gp_m3_04, gp_3_04, gp_m0_8, gp_0_05, gp_0_45, gp_0_55, gp_0_06,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Lv, cstU]

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 8)}
    (h : Program.sem (windowSeg (leftBlock (fLU l)) domLU tgU dt 1) σ ν) (i : Fin 8) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLU l) domLU 1 dt 1 (hfLU l hl) hdomLU
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem sat_FE (x : State (Var 8)) : Formula.sat (FM gU gsU) x ↔
    (x (Lv 0) - x (Rv 0) ≤ 0 ∧ x (Lv 1) - (x (Rv 1) + 1/5) ≤ 0) := by
  rw [sat_FM_iff]
  simp only [gU, gsU, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    gAt0_eval, gAt1_eval]

/-- **The guarded response** of left window `l` from right band `q` (in its guard): the
ladder climb, then hold `FLAT` until both rows hold. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3) {σ : State (Var 8)}
    (hσ : Formula.sat (Formula.and (FM gU gsU) envU) σ)
    (hguard : Formula.sat (hostGuard vsU 8 Side.R (mRU q)) σ) :
    GResp GrG q (windowSeg (leftBlock (fLU l)) domLU tgU dt 1)
      (fun _ => Formula.and (Formula.and (FM gU gsU) envU) Formula.tt) σ := by
  refine gresp_of_rresp (fun ν hwin => ?_)
  have hR := window_right l hl dt hwin
  have hvL := windowSeg_coord_le_or_lt (fLU l) domLU tgU dt 0 3 (cstU l) (by norm_num)
    (by simp [Lv, Prod.ext_iff]) (fun s _ => fLU0_eval l hl s) 1 hwin
  have hrow := (sat_FE σ).mp hσ.1
  have hdomLν : Formula.sat domLU ν :=
    windowSeg_end_domL (leftBlock (fLU l)) domLU tgU dt 1 (by norm_num) hwin
  have hdomRν : Formula.sat domRU ν := by
    refine (Formula.coincidence domRU (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRU hx
    exact (hR i).symm
  have hgν : Formula.sat (hostGuard vsU 8 Side.R (mRU q)) ν :=
    frames_right (vars_windowSegL_sub (fLU l) domLU 1 dt 1 (hfLU l hl) hdomLU)
      (hguardR_all q) hwin hguard
  have hcl := ladC_bounds l
  have hV : ν (Lv 0) < 13/20 ∨ ν (Lv 0) ≤ ν (Rv 0) := by
    rcases hvL with h | h
    · right; rw [hR 0]; linarith [hrow.1]
    · left; rw [cstU_eq] at h; linarith [hcl.2]
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domRU μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ν (Rv 0) ≤ μ (Rv 0) → ν (Lv 0) ≤ μ (Rv 0) →
      ν (Lv 1) - 1/5 ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM gU gsU) envU) Formula.tt) μ := by
    intro μ hμL hμd _ _ _ hv hs
    refine ⟨⟨(sat_FE μ).mpr ⟨by rw [hμL 0]; linarith, by rw [hμL 1]; linarith⟩, ?_, hμd⟩,
      trivial⟩
    refine (Formula.coincidence domLU (fun x hx => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLU hx
    exact hμL i
  refine LR.climb q hq ν hdomRν ⟨?_, ?_, ?_⟩ _ _ hV hfin
  · rintro rfl; rw [sat_guardR0] at hgν; exact ⟨hgν.2.1, hgν.2.2⟩
  · rintro rfl; rw [sat_guardR1] at hgν; exact hgν
  · rintro rfl; rw [sat_guardR2] at hgν; exact hgν

/-! ## Theorem 3 over the guarded automaton -/

/-- **`rover_dof_terrain_rung3_8d`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The left: the file's three windows (`bigChoice`, one clocked piece of
at most `dt` each); the right: the chain `STEEP → MODER → FLAT` of the file with every edge
testing the entered band's guard (`GrG_guards`). Loop invariant: the declared rows
`v_L ≤ v_R ∧ s_L ≤ s_R + 0.2`, both envelopes, the right in the guard of its current band
(`mvRegionR` at `gregion`). Response: the ladder climb. Z3-free; every window length `dt`. -/
theorem rover_dof_terrain_rung3_8d_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsU dt))
      (rightAutomatonBody GrG mvU)
      (RFormula.and (RFormula.and (canonInvM gU gsU) (envLR domLU domRU))
        (mvRegionR mvU gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvU (FM gU gsU) domLU domRU gregion
    (leftProgsU dt) (canonInvM gU gsU) (encode_canonInvM gU gsU) ?_ ?_ ?_
  · exact hdis_multi_G GrG 0 1 dt leftDataU (by decide) hgRG hRvG hLU
  · refine hstep_assembled_GR GrG mvU (FM gU gsU) envU gregion (leftProgsU dt)
      hmvFU hmvenvU hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesU dt) ?_
    refine Hmulti_regionG GrG mvU _ (fun _ => Formula.tt) GrG_guards (FM gU gsU) envU
      (leftProgsU dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsU, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_windowSegL_sub d.1 d.2.1 1 dt d.2.2 (hLU d hd).1 (hLU d hd).2)
        (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsU, leftDataU, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt q hq hσ hg
      · exact respondG 1 (by norm_num) dt q hq hσ hg
      · exact respondG 2 (by norm_num) dt q hq hσ hg
  · exact hddF_multiR_plain_G GrG 0 1 dt leftDataU gregion (canonInvM gU gsU) domLU domRU
      (by decide) hgRG hRvG hLU (fun q _ => gregion_fv q)
      (canonInvM_varsL gU gsU (by
        intro g' hg'
        simp only [gU, gsU, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gU gsU) hdomLU hdomRU

end RoverDofTerrainRung38dGuarded
end RelCertifier
