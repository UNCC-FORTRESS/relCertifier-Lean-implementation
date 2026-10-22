/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` (suite_v2) over the GUARDED right automaton

`V2Story3RolloverRungB.story3_rollover_ladder_rung_b_modeKeyed` states Theorem 3 over the
`⊤`-guarded right chain (the response stays in the start band for the whole window). Over the
GUARDED chain (every edge tests the lowered guard of the band it enters, `GrG_guards`) and at
the mode-consistent region (the right in the guard of its current band and above its kept
odometer floor, `gregion`), the cut-only statement was false (a `STEEP` reference at
`s_R = 5` has no step); with the guard conjunct it holds.

The declared rows tie the reference's attitude to the deployed's clock (energy rows in
`ψ_L − ψ_R`, `θ_L − θ_R`), so the response keeps time with the left window: the reference
runs for exactly the window's duration, switching up the chain inside the window when its
odometer reaches the next band's floor (`syncClimb`). On every stretch the anchor of the
pair (left mode, current band) is preserved by the certified coupling of that pair
(`couple_box_cutX`, the unchanged verdict packs `Verd l q`, all nine pairs at λ = 1); at a
switch point the entered band's kept atom is its odometer floor, which the reference sits on.
-/
import RelCertifier.InstancesV2.Modal.Story3RolloverRungB
import RelCertifier.InstancesV2.WellFormed.Story3RolloverRungB
import RelCertifier.Proofs.Encoding.LadderSync
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace V2Story3RolloverRungBGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle Story3RolloverRungBModal
  V2Story3RolloverRungB GPins

/-! ## The guarded right graph -/

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range story3_rollover_ladder_rung_b_IR.R.modes.length).flatMap (fun q =>
      (mRV q).next.map (fun nm =>
        (q, story3_rollover_ladder_rung_b_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range story3_rollover_ladder_rung_b_IR.R.modes.length).flatMap (fun q =>
      (mRV q).next.map (fun nm =>
        (q, story3_rollover_ladder_rung_b_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsV 12 Side.R (mRV e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

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
  have hm' : m = modeV q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvV q (modeV q) (GrV_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsV 12 Side.R (mRV q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsV _ dummyV rfl (by
    simp [story3_rollover_ladder_rung_b_IR, story3_rollover_ladder_rung_b_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

/-! ## The anchors and their box invariance (the certified couplings) -/

noncomputable def anc (l q : ℕ) : Formula (Var 12) := FM (g l) (gs l ++ atomTerms (cL l) (cR q))

theorem anc_box (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : Verd l q) :
    ∀ σ ω, Formula.sat (anc l q) σ →
      Program.sem (Program.ode (jointSys (fL l) (fRV q) (Term.const 1))
        (Formula.and domL domRV)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX (g l) (gs l) (comps l) (cL l) (cR q) (fL l) (fRV q) 1 domL domRV
    (fun c hc => by rw [comps_eq] at hc; exact hc)
    (fun c hc => by rw [comps_eq]; exact hc)
    (hiffL l hl) (hiffR q) (stayL l q hl) (stayR l q) (verd_core l q hl hq hv)

theorem sat_cR (q : ℕ) (hq : q < 3) (y : State (Var 12)) :
    CutSat (cR q) y ↔ sK q ≤ y (Rv 1) := by
  constructor
  · intro h
    have := (hiffR q _ (by rw [cR_eq q hq]; exact List.mem_cons_self) y).mp
      (h _ (by rw [cR_eq q hq]; exact List.mem_cons_self))
    simp [thrGe, Term.eval, AOp.interp] at this; linarith
  · intro h a ha
    rw [cR_eq q hq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    refine (hiffR q _ (by rw [cR_eq q hq]; exact List.mem_cons_self) y).mpr ?_
    simp [thrGe, Term.eval, AOp.interp]; linarith

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (y : State (Var 12)) :
    Formula.sat (anc l q) y ↔
      Formula.sat (FRow l) y ∧ CutSat (cL l) y ∧ sK q ≤ y (Rv 1) := by
  unfold anc FRow
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q), sat_cR q hq]

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 2) (y : State (Var 12))
    (hy : Formula.sat (anc l q) y) (hs : y (Rv 1) = (if q = 0 then 3/5 else 7/5)) :
    Formula.sat (anc l (q+1)) y := by
  obtain ⟨h1, h2, -⟩ := (anc_iff l q hl (by omega) y).mp hy
  refine (anc_iff l (q+1) hl (by omega) y).mpr ⟨h1, h2, ?_⟩
  interval_cases q <;> simp at hs <;> simp [sK, hs]

theorem anc_fv (l q : ℕ) (hl : l < 3) : (anc l q).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  unfold anc at hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => hn (anchor_fv l q hl c (by simpa using hc) hvc)) hv

/-! ## The synchronized guarded response -/

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 12)}
    (h : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν) (i : Fin 12) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem band_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 12))
    (h : Formula.sat (hostGuard vsV 12 Side.R (mRV q)) x) : ladBand q x := by
  interval_cases q
  · rw [sat_guardR0] at h
    exact ⟨fun _ => h, fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR1] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun _ => h, fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR2] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num), fun _ => h⟩

/-- **The guarded response** of left window `l` from right band `q` (in its guard and above
its odometer floor): the reference keeps time with the left window and climbs the chain
inside it (`syncClimb`); the anchor of the band it ends in holds at the window's end. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3)
    (hvs : ∀ q' < 3, Verd l q') {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FRow l) env) σ)
    (hgR : Formula.sat (hostGuard vsV 12 Side.R (mRV q)) σ)
    (hreg : Formula.sat (region q) σ) :
    GResp GrG q (gwindowSeg (hostGuard vsV 12 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FRow l) env) (region qf)) σ := by
  refine gresp_of_rresp (fun ν hν => ?_)
  obtain ⟨hgl, hwin⟩ := gwindowSeg_runs hν
  have hR := window_right l hl dt hwin
  have hdomLν : Formula.sat domL ν :=
    windowSeg_end_domL (leftBlock (fL l)) domL tg dt 1 (by norm_num) hwin
  -- the single clocked piece, as a solution
  simp only [windowSeg, List.replicate_succ, List.replicate_zero, bigSeq] at hwin
  obtain ⟨ν1, hseg, hrest⟩ := hwin
  rw [sem_test] at hrest
  obtain ⟨hνeq, -⟩ := hrest
  have hode := clockedSeg_runs hseg
  obtain ⟨r, ΦL, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hode
  have hL : ODESol (clk tg (leftBlock (fL l))) domL (Function.update σ tg 0) r ΦL :=
    ⟨hr, hΦ0, hder, hmask, hdom⟩
  have hΦrν : ∀ i, ΦL r (Lv i) = ν (Lv i) := by
    intro i; rw [hΦr, hνeq]
  have hdomRν : Formula.sat domRV ν := by
    refine (Formula.coincidence domRV (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRV hx
    exact (hR i).symm
  have htgL : ∀ i, tg ≠ Lv i := fun i => by simp [Lv, Prod.ext_iff]
  have htgR : ∀ i, tg ≠ Rv i := fun i => by simp [Rv, Prod.ext_iff]
  -- the anchor at the window's start
  have hA0 : Formula.sat (anc l q) (mergeLR σ (ΦL 0) ν) := by
    have hσA : Formula.sat (anc l q) σ := by
      refine (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgl, ?_⟩
      exact (sat_cR q hq σ).mp ((sat_region q σ).mp hreg)
    refine (sat_of_agree (anc_fv l q hl) (y := σ) (fun i => ?_) (fun i => ?_)).mpr hσA
    · rw [mergeLR_L, hΦ0, Function.update_of_ne (by simp [Lv, Prod.ext_iff])]
    · rw [mergeLR_R, hR i]
  refine syncClimb LR fRV (fun _ _ => rfl) (fL l) domL tg htgL htgR (hfL l hl)
    (fun q' hq' => hfRV q' hq') hdomL hdomRV hL σ (anc l)
    (fun q' hq' => anc_box l q' hl hq' (hvs q' hq'))
    (fun q' hq' y hy hs => anc_hand l q' hl hq' y hy hs)
    (edgeG 0 0) (edgeG 0 1) (edgeG 1 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 0 1 (by simp [GrG]))
    (edgeG_mem 1 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl rfl rfl
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 0)) y
      rw [sat_guardR0]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 1)) y
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 1)) y
      rw [sat_guardR1]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) y
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun y hs => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) y
      rw [sat_guardR2]; exact hs)
    ν _ ?_ q hq 0 le_rfl hr ν (fun _ => rfl) hdomRν
    (band_of_guard q hq ν (frames_right (vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL)
      (hguardR_all q) (by
        simp only [windowSeg, List.replicate_succ, List.replicate_zero, bigSeq]
        exact ⟨ν1, hseg, by rw [sem_test]; exact ⟨hνeq, trivial⟩⟩) hgR)) hA0
  intro qf hqf μ hμL hμd _ hA
  have hAμ : Formula.sat (anc l qf) μ := by
    refine (sat_of_agree (anc_fv l qf hl) (y := mergeLR σ (ΦL r) μ) (fun i => ?_)
      (fun i => ?_)).mpr hA
    · rw [mergeLR_L, hΦrν i, hμL i]
    · rw [mergeLR_R]
  obtain ⟨hrow, -, hs⟩ := (anc_iff l qf hl hqf μ).mp hAμ
  refine ⟨⟨hrow, ?_, hμd⟩, (sat_region qf μ).mpr ((sat_cR qf hqf μ).mpr hs)⟩
  refine (Formula.coincidence domL (fun x hx => ?_)).mpr hdomLν
  obtain ⟨i, rfl⟩ := hdomL hx
  exact hμL i

/-! ## The mode-consistent region and Theorem 3 -/

noncomputable def gregion (q : ℕ) : Formula (Var 12) :=
  regionG (fun q => hostGuard vsV 12 Side.R (mRV q)) region q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q)

theorem hmvregG : ∀ q, mv ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

theorem hulRG : uL ∉ (rightAutomatonBody GrG mv).bv :=
  notMem_bv_rightAutomatonBody_G GrG mv uL (by decide) (aux_notin_range_Rv 2) hgRG hRvG

theorem hulBkG : uL ∉ (mvRegion mv gregion GrG.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv gregion GrG.modes.length (fun q _ => gregion_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hstepMG (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv gregion GrG.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 12)) ((A dt).window t)
      (Program.star (rightAutomatonBody GrG mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv gregion GrG.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  obtain ⟨hv0, hv1, hv2⟩ : Verd t 0 ∧ Verd t 1 ∧ Verd t 2 := by
    match t, ht with
    | 0, _ => exact ⟨h00, h01, h02⟩
    | 1, _ => exact ⟨h10, h11, h12⟩
    | 2, _ => exact ⟨h20, h21, h22⟩
  have hvs : ∀ q' < 3, Verd t q' := by
    intro q' hq'
    match q', hq' with
    | 0, _ => exact hv0
    | 1, _ => exact hv1
    | 2, _ => exact hv2
  refine hstepMode_GR GrG mv (FRow t) env gregion _ (aux_notin_FRow 0 t) hmvenv hmvregG
    hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (framesGw t dt 0 (by decide)) ?_
  refine HMode_regionG GrG mv _ region GrG_guards (FRow t) env _ ?_ ?_
  · intro q _ σ ν hrun
    exact frames_right (vars_gwindowSegL_sub _ (fL t) domL 1 dt 1 (hguardL t ht) (hfL t ht)
      hdomL) (hguardR_all q) hrun
  · intro q hq σ _ hσ hg hreg
    rw [GrG_len] at hq
    exact respondG t ht dt q hq hvs hσ hg hreg

/-- **`story3_rollover_ladder_rung_b` (suite_v2), Theorem 3 over the GUARDED right automaton,
at the mode-consistent region.** The statement of `story3_rollover_ladder_rung_b_modeKeyed`
(the declared rows keyed by `u_L`, the file's left automaton, both envelopes) with every right
edge testing the entered band's guard (`GrG_guards`) and the loop invariant's right region the
current band's guard and kept odometer floor (`mvRegionR` at `gregion`). Response: the
synchronized climb (`syncClimb`), switching inside the window at the band floors, every switch
legal. Residuals: the nine packs `Verd l q` (unchanged). -/
theorem story3_rollover_ladder_rung_b_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody GrG mv)
      (psiK uL ϕRow (A dt).numModes domL domRV
        (mvRegionR mv gregion GrG.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL GrG mv FRow ϕRow domL domRV
    (mvRegion mv gregion GrG.modes.length) (mvRegionR mv gregion GrG.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (A dt) GrG 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) hgRG hRvG
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody GrG mv) FRow env
      (mvRegion mv gregion GrG.modes.length) (aux_notin_FRow 2) hulenv hulBkG (hulG dt)
      (hframesUl dt) hulRG (hnext dt)
      (hstepMG dt h00 h01 h02 h10 h11 h12 h20 h21 h22) (handoff dt)
  · exact hddF_modeKeyed_G (A dt) GrG 0 1 2 (by decide) (by decide) ϕRow domL domRV
      (mvRegionR mv gregion GrG.modes.length) (hwin dt) (hgrd dt) (hnext dt) hgRG hRvG
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomRV rfl
      (fun v hv => mvRegion_fv_sub mv gregion GrG.modes.length (fun q _ => gregion_fv q) hv)

end V2Story3RolloverRungBGuarded
end RelCertifier
