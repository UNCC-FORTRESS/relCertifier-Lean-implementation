/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_refine` (suite_v2) over the GUARDED right automaton — Theorem 3 by a climb

`V2RoverPatrolRefine.rover_patrol_refine_modeKeyed` states Theorem 3 over the `⊤`-guarded
right graph. This file states it over the GUARDED graph `GrG` (every declared edge tests the
lowered guard of the zone it enters, `GrG_guards`) at the mode-consistent region (the right
zone's guard and its kept cut atoms, `gregion`).

Both rows bound the deployed from above by the reference (`a_L + 5 v_L ≤ 5 v_R + 0.35`,
`s_L ≤ s_R + m`), and the reference's zone loops only raise `v_R` and `s_R`. So, as for
`rover_patrol_zones`, the right climbs the route after the left window and runs in `FAST`
until both rows hold. The deployed's `w = a + 5 v` is bounded at the window's end by a
linear-form chain: `q = a + 2.5 (v − c)` decays (`q' = −2.5 q`, the critically damped lag's
eigen-form), and `y = a + 5 (v − c)` obeys `y' = −2.5 (y − q)`, so `{q ≤ Q, y ≤ M}` with
`0 ≤ Q ≤ M` is a box invariant of the left flow (two differential invariants, the second
stratified on the first). Entered from the left guard (`|a| ≤ 0.5`, `v ≤ cap`), the chain caps
`w_L ≤ max(w_L(start), 7.25)` at the window's end; `FAST` reaches `5 v_R + 0.35 ≥ 7.25`.
Z3-free.
-/
import RelCertifier.InstancesV2.Modal.RoverPatrolRefine
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Flow.DISuperlevel

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolRefineGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolRefine

/-! ## The guarded right graph -/

noncomputable def edgeG (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_len : GrG.modes.length = 4 := rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 4) : GrG.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrG_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : GrG.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.guard = hostGuard vs 3 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem edgeList_tgt (p : ℕ × ℕ) (hp : p ∈ edgeList) : p.2 < 4 := by
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem hltG : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.tgt < GrG.modes.length := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact edgeList_tgt p hp

theorem hRvG : ∀ q m, GrG.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨hq, rfl⟩ := GrG_modeAt_inv hm
  exact hRv q (modeW q) (Gr_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vs 3 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [rover_patrol_refine_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeG s t ∈ GrG.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 1)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 9/10) := by
  simp [hostGuard, mR, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0, hp50_0,
    hp0_3, hp0_6, hp0_9, hp1_1, hp1_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR3 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 3)) x ↔
    (50 ≤ x (Rv 1) ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/2) := by
  simp [hostGuard, mR, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0, hp50_0,
    hp0_3, hp0_6, hp0_9, hp1_1, hp1_5, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- The zone guards: `lo ≤ s < hi` (no ceiling in `FAST`), `0.3 ≤ v ≤ cap`. -/
theorem sat_guardR (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) x ↔
      (loL q ≤ x (Rv 1) ∧ (q < 3 → x (Rv 1) < (if q = 0 then 20 else 50)) ∧
        3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ capL q) := by
  interval_cases q <;>
    simp [hostGuard, mR, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0,
      hp50_0, hp0_3, hp0_6, hp0_9, hp1_1, hp1_5, vs, Run.resolveVar, List.findIdx?_cons,
      IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc, loL,
      loQ, capL, capQ]

/-! ## The mode-consistent region -/

noncomputable def gregion (q : ℕ) : Formula (Var 3) :=
  regionG (fun q => hostGuard vs 3 Side.R (mR q)) region q

theorem gregion_fv (q : ℕ) (hq : q < 4) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

theorem hmvregG : ∀ q, mv ∉ (gregion q).fv := by
  intro q
  exact notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) (hmvreg q)

/-! ## The climb -/

theorem capL3 : capL 3 = 3/2 := by norm_num [capL, capQ]

theorem exp_neg_two_le : Real.exp (-2) ≤ 1/4 := by
  have h1 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : (4:ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
  have hpos : 0 < Real.exp 2 := Real.exp_pos 2
  rw [Real.exp_neg]
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

theorem exp_neg_four_le : Real.exp (-4) ≤ 1/16 := by
  have h := exp_neg_two_le
  have h2 : Real.exp (-4) = Real.exp (-2) * Real.exp (-2) := by rw [← Real.exp_add]; norm_num
  rw [h2]
  have hp := Real.exp_pos (-2)
  nlinarith

/-- **The `FAST` run**: long enough that `v_R ≥ max(v_R, 1.425)` and `s_R ≥ S`, then the
self-loop (legal). -/
theorem climbFast (ρ : State (Var 3)) (hdom : Formula.sat domR ρ)
    (hg : 50 ≤ ρ (Rv 1) ∧ 3/10 ≤ ρ (Rv 0) ∧ ρ (Rv 0) ≤ 3/2) (S : ℝ)
    {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ρ (Rv 0) ≤ μ (Rv 0) →
      57/40 ≤ μ (Rv 0) → S ≤ μ (Rv 1) → Formula.sat (post 3) μ) :
    RResp GrG 3 post ρ := by
  obtain ⟨hs50, hv3, hv15⟩ := hg
  set τ : ℝ := 4 + max 0 (S - ρ (Rv 1)) * (10/3) with hτ
  have hτ4 : 4 ≤ τ := by
    have : 0 ≤ max 0 (S - ρ (Rv 1)) * (10/3) := mul_nonneg (le_max_left _ _) (by norm_num)
    linarith
  have hτ0 : 0 ≤ τ := by linarith
  have hrun := mode_run 3 (by norm_num) ρ τ hτ0 hdom
  set μ := solR (capL 3) 1 ρ τ with hμ
  have hex0 := ex_pos 1 τ
  have hex1 : ex 1 τ ≤ 1/16 := by
    have : ex 1 τ ≤ Real.exp (-4) := by
      unfold ex; exact Real.exp_le_exp.mpr (by linarith)
    linarith [exp_neg_four_le]
  have hge := ex_ge 1 τ
  have hμv : μ (Rv 0) = 3/2 + (ρ (Rv 0) - 3/2) * ex 1 τ := by rw [hμ, solR_0, capL3]
  have hμs : μ (Rv 1) = ρ (Rv 1) + 1 * (3/2) * τ + (ρ (Rv 0) - 3/2) * (1 - ex 1 τ) := by
    rw [hμ, solR_1, capL3]
  have hμL : ∀ i, μ (Lv i) = ρ (Lv i) := fun i =>
    solR_other _ 1 ρ τ (by simp [Lv, Rv, Prod.ext_iff]) (by simp [Lv, Rv, Prod.ext_iff])
  have hv_ge : ρ (Rv 0) ≤ μ (Rv 0) := by rw [hμv]; nlinarith
  have hv_le : μ (Rv 0) ≤ 3/2 := by rw [hμv]; nlinarith
  have hv_hi : 57/40 ≤ μ (Rv 0) := by rw [hμv]; nlinarith
  have hs_low : ρ (Rv 1) + 3/10 * τ ≤ μ (Rv 1) := by
    rw [hμs]
    have h1 : 0 ≤ (3/2 - ρ (Rv 0)) * (τ - 1 + ex 1 τ) := by
      apply mul_nonneg (by linarith); linarith
    nlinarith
  have hs_S : S ≤ μ (Rv 1) := by
    have hm : S - ρ (Rv 1) ≤ max 0 (S - ρ (Rv 1)) := le_max_right _ _
    have : 3/10 * τ = 6/5 + max 0 (S - ρ (Rv 1)) := by rw [hτ]; ring
    linarith
  have hs50' : 50 ≤ μ (Rv 1) := by
    have : 0 ≤ 3/10 * τ := by positivity
    linarith
  have hdomμ : Formula.sat domR μ := solR_stays 3 (by norm_num) 1 zero_le_one ρ hdom hτ0
  refine rresp_step (GrG_modeAt 3 (by norm_num)) (edgeG_mem 3 3 (by simp [edgeList])) hrun ?_
    (rresp_stop ?_)
  · show Formula.sat (hostGuard vs 3 Side.R (mR 3)) μ
    rw [sat_guardR3]
    exact ⟨hs50', by linarith, hv_le⟩
  · exact hpost μ hμL hdomμ hs50' (by linarith) hv_le hv_ge hv_hi hs_S

/-- **The climb from `MEDIUM_*`** (`q = 1, 2`): run to `s = 50`, switch into `FAST`. -/
theorem climbMed (q : ℕ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ρ : State (Var 3))
    (hdom : Formula.sat domR ρ) (hs : ρ (Rv 1) < 50) (hv3 : 3/10 ≤ ρ (Rv 0))
    (hvc : ρ (Rv 0) ≤ capL q) (S : ℝ) {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ρ (Rv 0) ≤ μ (Rv 0) →
      57/40 ≤ μ (Rv 0) → S ≤ μ (Rv 1) → Formula.sat (post 3) μ) :
    RResp GrG q post ρ := by
  have hq4 : q < 4 := by omega
  have hcq : capL q ≤ 11/10 := by
    interval_cases q <;> norm_num [capL, capQ]
  obtain ⟨κ, hrun, hκs, hκv1, hκv2, hκo⟩ := mode_reach q hq4 50 ρ hdom hv3 hvc
  have hκs' : κ (Rv 1) = 50 := by rw [hκs]; exact max_eq_right (le_of_lt hs)
  have hκL : ∀ i, κ (Lv i) = ρ (Lv i) := fun i =>
    hκo (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩
  have hκdom : Formula.sat domR κ := sem_ode_ends_in_domain hrun
  have hedge : (q, 3) ∈ edgeList := by interval_cases q <;> simp [edgeList]
  refine rresp_step (GrG_modeAt q (by omega)) (edgeG_mem q 3 hedge) hrun ?_ ?_
  · show Formula.sat (hostGuard vs 3 Side.R (mR 3)) κ
    rw [sat_guardR3]
    exact ⟨le_of_eq hκs'.symm, by linarith, by linarith⟩
  · refine climbFast κ hκdom ⟨le_of_eq hκs'.symm, by linarith, by linarith⟩ S ?_
    intro μ hμL hμd h1 h2 h3 h4 h5 h6
    exact hpost μ (fun i => (hμL i).trans (hκL i)) hμd h1 h2 h3 (le_trans hκv1 h4) h5 h6

/-- **The climb from `SLOW`**: run to `s = 20`, switch into `MEDIUM_ECO`, then `climbMed`. -/
theorem climbSlow (ρ : State (Var 3)) (hdom : Formula.sat domR ρ) (hs : ρ (Rv 1) < 20)
    (hv3 : 3/10 ≤ ρ (Rv 0)) (hvc : ρ (Rv 0) ≤ 3/5) (S : ℝ) {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ρ (Rv 0) ≤ μ (Rv 0) →
      57/40 ≤ μ (Rv 0) → S ≤ μ (Rv 1) → Formula.sat (post 3) μ) :
    RResp GrG 0 post ρ := by
  have hc0 : capL 0 = 3/5 := by norm_num [capL, capQ]
  have hc1 : capL 1 = 9/10 := by norm_num [capL, capQ]
  obtain ⟨κ, hrun, hκs, hκv1, hκv2, hκo⟩ := mode_reach 0 (by norm_num) 20 ρ hdom hv3
    (by rw [hc0]; exact hvc)
  have hκs' : κ (Rv 1) = 20 := by rw [hκs]; exact max_eq_right (le_of_lt hs)
  have hκL : ∀ i, κ (Lv i) = ρ (Lv i) := fun i =>
    hκo (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩
  have hκdom : Formula.sat domR κ := sem_ode_ends_in_domain hrun
  rw [hc0] at hκv2
  refine rresp_step (GrG_modeAt 0 (by norm_num)) (edgeG_mem 0 1 (by simp [edgeList])) hrun ?_ ?_
  · show Formula.sat (hostGuard vs 3 Side.R (mR 1)) κ
    rw [sat_guardR1]
    exact ⟨le_of_eq hκs'.symm, by linarith, by linarith, by linarith⟩
  · refine climbMed 1 le_rfl (by norm_num) κ hκdom (by linarith) (by linarith)
      (by rw [hc1]; linarith) S ?_
    intro μ hμL hμd h1 h2 h3 h4 h5 h6
    exact hpost μ (fun i => (hμL i).trans (hκL i)) hμd h1 h2 h3 (le_trans hκv1 h4) h5 h6

/-! ## The deployed's `w = a + 5 v` across a window: the linear-form chain -/

theorem cLv_eq (l : ℕ) (hl : l < 4) : cLv l = 4/5 * capL l := by
  interval_cases l <;> norm_num [cLv, cLQ, capL, capQ]

/-- The left guard's caps: `a ≤ 0.5`, `v ≤ cap`. -/
theorem guardL_caps (l : ℕ) (hl : l < 4) (x : State (Var 3))
    (h : Formula.sat (hostGuard vs 3 Side.L (mL l)) x) :
    x (Lv 2) ≤ 1/2 ∧ x (Lv 0) ≤ capL l := by
  interval_cases l <;>
    simp [hostGuard, mL, rover_patrol_refine_IRv2, Run.lowerF, Run.lowerE, hp0_0, hp20_0,
      hp50_0, hp0_3, hp0_6, hp0_9, hp1_1, hp1_5, hp0_5, hpm0_5, vs, Run.resolveVar,
      List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv,
      capL, capQ] at h ⊢ <;>
    exact ⟨by linarith [h], by linarith [h]⟩

theorem leftBlock_wf (f : Fin 3 → Term (Var 3)) : (leftBlock f).WellFormed := by
  have hLinj : Function.Injective (Lv (n := 3)) := by
    intro a b h; simpa [Lv, Prod.ext_iff] using h
  unfold ODESystem.WellFormed leftBlock
  simp only [List.map_map, Function.comp_def]
  exact (List.nodup_finRange 3).map hLinj

theorem htg_leftBlock (f : Fin 3 → Term (Var 3)) : tg ∉ (leftBlock f).bound := by
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub f _ h
  exact aux_ne_Lv 1 i hi

theorem lie_clk_left (f : Fin 3 → Term (Var 3)) (t : Term (Var 3)) (ht : tg ∉ t.fv)
    (x : State (Var 3)) :
    Lie (DLCalTiming.clk tg (leftBlock f)) (fun ω => Term.eval t ω) x
      = Term.eval (lie1L t f) x := by
  rw [eval_lie1L]
  unfold Lie DLCalTiming.clk leftBlock
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_map,
    Function.comp_def]
  rw [tderiv_fderiv t tg x, tderiv_not_free ht x, Fin.sum_univ_def]
  simp only [Term.eval, zero_mul, add_zero]
  congr 1
  refine List.map_congr_left ?_
  intro i _
  rw [tderiv_fderiv]

theorem wf_clk (l : ℕ) : (DLCalTiming.clk tg (leftBlock (fL l))).WellFormed :=
  clk_wellFormed tg _ (leftBlock_wf _) (htg_leftBlock _)

theorem tg_lin (r c K : ℝ) : tg ∉ (linLe (Lv (0 : Fin 3)) (Lv 2) r c K).fv := by
  simp [linLe, linQ, Term.fv, Lv, Prod.ext_iff]

/-- `y ≤ M` along the left flow, given `q ≤ M` (`y' = −2.5 (y − q)`). -/
theorem super_y (l : ℕ) (hl : l < 4) (M : ℝ) (D : Formula (Var 3))
    (hgiven : ∀ z, Formula.sat D z →
      Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) (5/2) (cLv l) M) z ≤ 0) :
    ∀ z, Formula.sat D z → 0 ≤ Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) 5 (cLv l) M) z →
      Term.eval (lie1L (linLe (Lv (0 : Fin 3)) (Lv 2) 5 (cLv l) M) (fL l)) z ≤ 0 := by
  intro z hz hge
  have hlie : Term.eval (lie1L (linLe (Lv (0 : Fin 3)) (Lv 2) 5 (cLv l) M) (fL l)) z
      = Term.eval (lie1L (linQ (Lv (0 : Fin 3)) (Lv 2) 5 (cLv l)) (fL l)) z := by
    rw [eval_lie1L, eval_lie1L]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [linLe, tderiv, Term.eval, AOp.interp]
  rw [hlie, eval_lie1L_linQ 0 2, fL2_eval l hl, fL0_eval l hl]
  have hq := hgiven z hz
  simp only [linLe, eval_linQ, Term.eval, AOp.interp] at hq hge
  nlinarith

/-- **The window's end bound on `w`**: from a start inside the left guard (`|a| ≤ 0.5`,
`v ≤ cap`), the single clocked piece ends with `a + 5 v ≤ max(start, 7.25)`. -/
theorem window_w (l : ℕ) (hl : l < 4) (dt : ℝ) {σ ν : State (Var 3)}
    (hsem : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν)
    (hq0 : σ (Lv 2) + 5/2 * (σ (Lv 0) - cLv l) ≤ 5/4) :
    ν (Lv 2) + 5 * ν (Lv 0) ≤ max (σ (Lv 2) + 5 * σ (Lv 0)) (29/4) := by
  simp only [windowSeg, List.replicate_succ, List.replicate_zero, bigSeq] at hsem
  obtain ⟨mid, hseg, hrest⟩ := hsem
  rw [sem_test] at hrest
  obtain ⟨rfl, -⟩ := hrest
  have hode := clockedSeg_runs hseg
  set σ' := Function.update σ tg 0 with hσ'
  have hL : ∀ i, σ' (Lv i) = σ (Lv i) := fun i => Function.update_of_ne (by simp [Lv, Prod.ext_iff]) _ _
  set c := cLv l with hcdef
  set Q : ℝ := max (σ (Lv 2) + 5/2 * (σ (Lv 0) - c)) 0 with hQ
  set M : ℝ := max (σ (Lv 2) + 5 * (σ (Lv 0) - c)) Q with hM
  have hQ0 : 0 ≤ Q := le_max_right _ _
  have hQM : Q ≤ M := le_max_right _ _
  -- q ≤ Q along the flow
  have hboxq : ∀ ν0, Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) (5/2) c Q) ν0 ≤ 0 →
      BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (fun ω => Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) (5/2) c Q) ω) ν0 := by
    intro ν0 hν0
    refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable _) ?_ hν0
    intro x hx hge
    rw [lie_clk_left _ _ (tg_lin _ _ _)]
    exact super_linear_le_L (jx := 0) (jy := 2) (a := 25/4) (b := 5) (c := c) (r := 5/2) (K := Q)
      (by norm_num) (by norm_num) hQ0 (fL l) domL (fun z _ => fL0_eval l hl z)
      (fun z _ => by rw [fL2_eval l hl]) x hx hge
  -- y ≤ M along the flow, stratified on q ≤ Q
  have hboxy : ∀ ν0, Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) (5/2) c Q) ν0 ≤ 0 →
      Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) 5 c M) ν0 ≤ 0 →
      BoxLe (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (fun ω => Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) 5 c M) ω) ν0 := by
    refine stay_given (Fq := Formula.cmp CompOp.le (linLe (Lv (0 : Fin 3)) (Lv 2) (5/2) c Q)
      (Term.const 0)) (gq := linLe (Lv (0 : Fin 3)) (Lv 2) (5/2) c Q)
      (fun z => by simp [Formula.sat, CompOp.interp, Term.eval]) hboxq ?_
    intro ν0 hν0
    refine DI_nonstrict_superlevel (wf_clk l) (term_differentiable _) ?_ hν0
    intro x hx hge
    rw [lie_clk_left _ _ (tg_lin _ _ _)]
    refine super_y l hl M _ (fun z hz => ?_) x hx hge
    have h2 := hz.2
    simp only [Formula.sat, CompOp.interp, Term.eval] at h2
    simp only [linLe, eval_linQ, Term.eval, AOp.interp] at h2 ⊢
    linarith
  have hq0' : Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) (5/2) c Q) σ' ≤ 0 := by
    simp only [linLe, eval_linQ, Term.eval, AOp.interp, hL]
    linarith [le_max_left (σ (Lv 2) + 5/2 * (σ (Lv 0) - c)) 0]
  have hy0' : Term.eval (linLe (Lv (0 : Fin 3)) (Lv 2) 5 c M) σ' ≤ 0 := by
    simp only [linLe, eval_linQ, Term.eval, AOp.interp, hL]
    linarith [le_max_left (σ (Lv 2) + 5 * (σ (Lv 0) - c)) Q]
  have hend := hboxy σ' hq0' hy0' mid hode
  simp only [linLe, eval_linQ, Term.eval, AOp.interp] at hend
  -- `w = y + 5c ≤ M + 5c`
  have hcap : c ≤ 6/5 := by
    rw [hcdef, cLv_eq l hl]; have h3 := (cap_bounds l hl).2; linarith
  rcases le_total (σ (Lv 2) + 5 * (σ (Lv 0) - c)) Q with h1 | h1
  · rw [hM, max_eq_right h1] at hend
    rcases le_total (σ (Lv 2) + 5/2 * (σ (Lv 0) - c)) 0 with h2 | h2
    · rw [hQ, max_eq_right h2] at hend
      have : 5 * c ≤ 6 := by linarith
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [hQ, max_eq_left h2] at hend
      exact le_trans (by linarith) (le_max_right _ _)
  · rw [hM, max_eq_left h1] at hend
    exact le_trans (by linarith) (le_max_left _ _)

/-! ## The guarded response to a left window -/

theorem window_right (l : ℕ) (hl : l < 4) (dt : ℝ) {σ ν : State (Var 3)}
    (h : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν) (i : Fin 3) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **The guarded catch-up response** of left zone `l`'s window from right zone `q` (in its
guard and its kept atoms): climb the route and run in `FAST` until both rows hold. -/
theorem respondG (l : ℕ) (hl : l < 4) (dt : ℝ) (q : ℕ) (hq : q < 4) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hguard : Formula.sat (hostGuard vs 3 Side.R (mR q)) σ)
    (hreg : Formula.sat (region q) σ) :
    GResp GrG q (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM (g l) (gs l)) env) (region qf)) σ := by
  refine gresp_of_rresp (fun ν hν => ?_)
  obtain ⟨hgl, hwin⟩ := gwindowSeg_runs hν
  have hR := window_right l hl dt hwin
  have hrow := (sat_FRow l hl σ).mp hσ.1
  -- the left guard at the window's start: `|a| ≤ 0.5`, `v ≤ cap`
  have hq0 : σ (Lv 2) + 5/2 * (σ (Lv 0) - cLv l) ≤ 5/4 := by
    obtain ⟨ha, hv⟩ := guardL_caps l hl σ hgl
    rw [cLv_eq l hl]
    have h3 := (cap_bounds l hl).2
    nlinarith
  have hw := window_w l hl dt hwin hq0
  have hdomLν : Formula.sat domL ν :=
    windowSeg_end_domL (leftBlock (fL l)) domL tg dt 1 (by norm_num) hwin
  have hdomRν : Formula.sat domR ν := by
    rw [sat_domR, hR 0, hR 1, hR 2]; exact (sat_domR σ).mp hσ.2.2
  have hx := (cutSatR_val q hq σ).mp ((sat_region_lt q hq σ).mp hreg)
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ν (Rv 0) ≤ μ (Rv 0) →
      57/40 ≤ μ (Rv 0) → ν (Lv 1) ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region 3)) μ := by
    intro μ hμL hμd h50 h3 h15 hv h12 hs
    have hm := (show 0 ≤ mL' l by interval_cases l <;> norm_num [mL', mQ])
    refine ⟨⟨(sat_FRow l hl μ).mpr ⟨?_, ?_⟩, ?_, hμd⟩, ?_⟩
    · rw [hμL 0, hμL 2]
      rw [hR 0] at hv
      rcases le_total (σ (Lv 2) + 5 * σ (Lv 0)) (29/4) with h | h
      · rw [max_eq_right h] at hw; linarith
      · rw [max_eq_left h] at hw; linarith [hrow.1]
    · rw [hμL 1]; linarith
    · rw [sat_domL, hμL 0, hμL 1, hμL 2]; exact (sat_domL ν).mp hdomLν
    · rw [sat_region_lt 3 (by norm_num), cutSatR_val 3 (by norm_num)]
      exact ⟨by norm_num [loL, loQ]; linarith, h3, by rw [capL3]; exact h15⟩
  have hgν : Formula.sat (hostGuard vs 3 Side.R (mR q)) ν :=
    frames_right (vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL) (hguardR_all q) hwin
      hguard
  rw [sat_guardR q hq] at hgν
  interval_cases q
  · exact climbSlow ν hdomRν (hgν.2.1 (by norm_num)) hgν.2.2.1
      (by have := hgν.2.2.2; norm_num [capL, capQ] at this; linarith) (ν (Lv 1)) hfin
  · exact climbMed 1 le_rfl (by norm_num) ν hdomRν (hgν.2.1 (by norm_num)) hgν.2.2.1
      hgν.2.2.2 (ν (Lv 1)) hfin
  · exact climbMed 2 (by norm_num) le_rfl ν hdomRν (hgν.2.1 (by norm_num)) hgν.2.2.1
      hgν.2.2.2 (ν (Lv 1)) hfin
  · exact climbFast ν hdomRν ⟨by have := hgν.1; norm_num [loL, loQ] at this; linarith,
      hgν.2.2.1, by have := hgν.2.2.2; rw [capL3] at this; exact this⟩ (ν (Lv 1)) hfin

/-! ## The per-mode steps and Theorem 3 -/

theorem hulRG : uL ∉ (rightAutomatonBody GrG mv).bv :=
  notMem_bv_rightAutomatonBody_G GrG mv uL (by decide) (aux_notin_range_Rv 2) hgRG hRvG

theorem hulBkG : uL ∉ (mvRegion mv gregion GrG.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv gregion GrG.modes.length (fun q hq => gregion_fv q hq) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hstepMG (dt : ℝ) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv gregion GrG.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((A dt).window t)
      (Program.star (rightAutomatonBody GrG mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv gregion GrG.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  refine hstepMode_GR GrG mv (FRow t) env gregion _ (aux_notin_FRow 0 t) hmvenv hmvregG
    hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (framesGw t dt 0 (by decide)) ?_
  refine HMode_regionG GrG mv _ region GrG_guards (FRow t) env _ ?_ ?_
  · intro q _ σ ν hrun
    exact frames_right (vars_gwindowSegL_sub _ (fL t) domL 1 dt 1 (hguardL t ht) (hfL t ht)
      hdomL) (hguardR_all q) hrun
  · intro q hq σ _ hσ hg hreg
    rw [GrG_len] at hq
    exact respondG t ht dt q hq hσ hg hreg

/-- **`rover_patrol_refine` (suite_v2), Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The statement of `rover_patrol_refine_modeKeyed` with every right
edge testing the entered zone's guard (`GrG_guards`) and the loop invariant's right region the
current zone's guard and kept cut atoms (`mvRegionR` at `gregion`). Response: the climb, with
the deployed's `a + 5 v` capped by the linear-form chain. Z3-free; every window length. -/
theorem rover_patrol_refine_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody GrG mv)
      (psiK uL ϕRow (A dt).numModes domL domR
        (mvRegionR mv gregion GrG.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL GrG mv FRow ϕRow domL domR
    (mvRegion mv gregion GrG.modes.length) (mvRegionR mv gregion GrG.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (A dt) GrG 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) hgRG hRvG
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody GrG mv) FRow env
      (mvRegion mv gregion GrG.modes.length) (aux_notin_FRow 2) hulenv hulBkG (hulG dt)
      (hframesUl dt) hulRG (hnext dt) (hstepMG dt) (handoff dt)
  · exact hddF_modeKeyed_G (A dt) GrG 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv gregion GrG.modes.length) (hwin dt) (hgrd dt) (hnext dt) hgRG hRvG
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv gregion GrG.modes.length (fun q hq => gregion_fv q hq) hv)

end V2RoverPatrolRefineGuarded
end RelCertifier
