/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones` (suite_v2) over the GUARDED right automaton — Theorem 3 by a climb

`V2RoverPatrolZones.rover_patrol_zones_modeKeyed` states Theorem 3 over the `⊤`-guarded
right graph. This file states it over the GUARDED graph `GrG` (every declared edge tests the
lowered guard of the mode it enters, `GrG_guards`) at the mode-consistent region: the right
mode's guard and its kept cut atoms (`gregion`, `STALL` excluded).

The response is built from the model after the left window. Both rows bound the deployed from
above by the reference (`v_L ≤ v_R`, `s_L ≤ s_R + m`), and the reference's zone loops only
raise `v_R` (towards the zone command, which only grows along the route) and `s_R`. So the
right climbs the route: from its zone it runs to the next zone's floor and switches there
(`SLOW → MEDIUM_ECO` at `s = 20`, `MEDIUM_* → FAST` at `s = 50`, legal by the explicit end
state), then runs in `FAST` long enough that `v_R ≥ 1.2` (the deployed's highest set point; a
window never raises `v_L` above `max(v_L, 1.2)`, `windowSeg_coord_le_max`) and `s_R ≥ s_L`, and
takes the self-loop `FAST → FAST` (legal: `s ≥ 50`, `0.3 ≤ v ≤ 1.5`). No verdict pack is
needed: the theorem is Z3-free.
-/
import RelCertifier.InstancesV2.Modal.RoverPatrolZones
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolZonesGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolZones

/-! ## The guarded right graph -/

/-- The declared edge `s → t` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The file's right automaton (the modes and `next` lists of `Gr`, `edgeList_eq_IR`), every
edge guarded. -/
noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_len : GrG.modes.length = 5 := rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 5) : GrG.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrG_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : GrG.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of the
mode it enters. -/
theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.guard = hostGuard vs 3 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem edgeList_tgt (p : ℕ × ℕ) (hp : p ∈ edgeList) : p.2 < 5 := by
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

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
  hostGuard_fv_R_getD vs _ dm rfl (by simp [rover_patrol_zones_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeG s t ∈ GrG.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 20 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/5) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 1)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 9/10) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 2)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 11/10) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR3 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 3)) x ↔
    (50 ≤ x (Rv 1) ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/2) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard and its kept cut atoms
(`region`; `STALL`, the pruned sink, excluded). -/
noncomputable def gregion (q : ℕ) : Formula (Var 3) :=
  regionG (fun q => hostGuard vs 3 Side.R (mR q)) region q

theorem gregion_fv (q : ℕ) (hq : q < 5) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

theorem hmvregG : ∀ q, mv ∉ (gregion q).fv := by
  intro q
  refine notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) (hmvreg q)

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

/-- **The `FAST` run.** From a `FAST` state in its guard and the envelope, run long enough that
`v_R ≥ max(v_R, 1.2)` and `s_R ≥ S`, then take the self-loop (legal). -/
theorem climbFast (ρ : State (Var 3)) (hdom : Formula.sat domR ρ)
    (hg : 50 ≤ ρ (Rv 1) ∧ 3/10 ≤ ρ (Rv 0) ∧ ρ (Rv 0) ≤ 3/2) (S : ℝ)
    {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ρ (Rv 0) ≤ μ (Rv 0) →
      6/5 ≤ μ (Rv 0) → S ≤ μ (Rv 1) → Formula.sat (post 3) μ) :
    RResp GrG 3 post ρ := by
  obtain ⟨hs50, hv3, hv15⟩ := hg
  set τ : ℝ := 2 + max 0 (S - ρ (Rv 1)) * (10/3) with hτ
  have hτ2 : 2 ≤ τ := by
    have : 0 ≤ max 0 (S - ρ (Rv 1)) * (10/3) := mul_nonneg (le_max_left _ _) (by norm_num)
    linarith
  have hτ0 : 0 ≤ τ := by linarith
  have hrun := mode_run 3 (by norm_num) ρ τ hτ0 hdom
  set μ := solR (capL 3) ρ τ with hμ
  have hex0 := ex_pos τ
  have hex1 : ex τ ≤ 1/4 := by
    have : ex τ ≤ Real.exp (-2) := by
      unfold ex; exact Real.exp_le_exp.mpr (by linarith)
    linarith [exp_neg_two_le]
  have hge := ex_ge τ
  have hμv : μ (Rv 0) = 3/2 + (ρ (Rv 0) - 3/2) * ex τ := by rw [hμ, solR_0, capL3]
  have hμs : μ (Rv 1) = ρ (Rv 1) + 3/2 * τ + (ρ (Rv 0) - 3/2) * (1 - ex τ) := by
    rw [hμ, solR_1, capL3]
  have hμL : ∀ i, μ (Lv i) = ρ (Lv i) := fun i =>
    solR_other _ ρ τ (by simp [Lv, Rv, Prod.ext_iff]) (by simp [Lv, Rv, Prod.ext_iff])
  have hv_ge : ρ (Rv 0) ≤ μ (Rv 0) := by rw [hμv]; nlinarith
  have hv_le : μ (Rv 0) ≤ 3/2 := by rw [hμv]; nlinarith
  have hv_12 : 6/5 ≤ μ (Rv 0) := by rw [hμv]; nlinarith
  -- `s(τ) ≥ s₀ + v₀ τ ≥ s₀ + 0.3 τ`
  have hs_low : ρ (Rv 1) + 3/10 * τ ≤ μ (Rv 1) := by
    rw [hμs]
    have h1 : 0 ≤ (3/2 - ρ (Rv 0)) * (τ - 1 + ex τ) := by
      apply mul_nonneg (by linarith); linarith
    nlinarith
  have hs_S : S ≤ μ (Rv 1) := by
    have hm : S - ρ (Rv 1) ≤ max 0 (S - ρ (Rv 1)) := le_max_right _ _
    have : 3/10 * τ = 3/5 + max 0 (S - ρ (Rv 1)) := by rw [hτ]; ring
    linarith
  have hs50' : 50 ≤ μ (Rv 1) := by
    have : 0 ≤ 3/10 * τ := by positivity
    linarith
  have hdomμ : Formula.sat domR μ := solR_stays 3 (by norm_num) ρ hdom hτ0
  refine rresp_step (GrG_modeAt 3 (by norm_num)) (edgeG_mem 3 3 (by simp [edgeList])) hrun ?_
    (rresp_stop ?_)
  · show Formula.sat (hostGuard vs 3 Side.R (mR 3)) μ
    rw [sat_guardR3]
    exact ⟨hs50', by linarith, hv_le⟩
  · exact hpost μ hμL hdomμ hs50' (by linarith) hv_le hv_ge hv_12 hs_S

/-- **The climb from `MEDIUM_ECO`/`MEDIUM_BRISK`** (`q = 1, 2`, guard `20 ≤ s < 50`): run the
zone to `s = 50`, switch into `FAST` (legal), then `climbFast`. -/
theorem climbMed (q : ℕ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ρ : State (Var 3))
    (hdom : Formula.sat domR ρ) (hs : ρ (Rv 1) < 50) (hv3 : 3/10 ≤ ρ (Rv 0))
    (hvc : ρ (Rv 0) ≤ capL q) (S : ℝ) {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ρ (Rv 0) ≤ μ (Rv 0) →
      6/5 ≤ μ (Rv 0) → S ≤ μ (Rv 1) → Formula.sat (post 3) μ) :
    RResp GrG q post ρ := by
  have hq4 : q < 4 := by omega
  have hc := cap_bounds q hq4
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

/-- **The climb from `SLOW`** (guard `s < 20`): run `SLOW` to `s = 20`, switch into
`MEDIUM_ECO` (legal), then `climbMed`. -/
theorem climbSlow (ρ : State (Var 3)) (hdom : Formula.sat domR ρ) (hs : ρ (Rv 1) < 20)
    (hv3 : 3/10 ≤ ρ (Rv 0)) (hvc : ρ (Rv 0) ≤ 3/5) (S : ℝ) {post : ℕ → Formula (Var 3)}
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ρ (Rv 0) ≤ μ (Rv 0) →
      6/5 ≤ μ (Rv 0) → S ≤ μ (Rv 1) → Formula.sat (post 3) μ) :
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

/-! ## The guarded response to a left window -/

theorem upd_tg_ne_Lv0 : tg ≠ Lv 0 := by simp [Lv, Prod.ext_iff]

/-- A left window keeps the deployed's speed below `max(v_L, 1.2)`. -/
theorem window_vL (l : ℕ) (hl : l < 4) (dt : ℝ) {σ ν : State (Var 3)}
    (h : Program.sem (windowSeg (leftBlock (fL l)) domL tg dt 1) σ ν) :
    ν (Lv 0) ≤ max (σ (Lv 0)) (6/5) := by
  have h1 := windowSeg_coord_le_max (fL l) domL tg dt 0 (5/4) (cLv l) (by norm_num)
    upd_tg_ne_Lv0 (fun s _ => fL0_eval l hl s) 1 h
  have hc : cLv l ≤ 6/5 := by interval_cases l <;> norm_num [cLv, cLQ]
  exact le_trans h1 (max_le_max le_rfl hc)

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
  obtain ⟨-, hwin⟩ := gwindowSeg_runs hν
  have hR := window_right l hl dt hwin
  have hvL := window_vL l hl dt hwin
  have hrow := (sat_FRow l hl σ).mp hσ.1
  have hdomLν : Formula.sat domL ν :=
    windowSeg_end_domL (leftBlock (fL l)) domL tg dt 1 (by norm_num) hwin
  have hdomRν : Formula.sat domR ν := by
    rw [sat_domR, hR 0, hR 1]; exact (sat_domR σ).mp hσ.2.2
  have hx := (cutSatR_val q hq σ).mp ((sat_region_lt q hq σ).mp hreg)
  -- the final-state obligation, shared by every start zone
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domR μ →
      50 ≤ μ (Rv 1) → 3/10 ≤ μ (Rv 0) → μ (Rv 0) ≤ 3/2 → ν (Rv 0) ≤ μ (Rv 0) →
      6/5 ≤ μ (Rv 0) → ν (Lv 1) ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region 3)) μ := by
    intro μ hμL hμd h50 h3 h15 hv h12 hs
    have hm := (show 0 ≤ mL' l by interval_cases l <;> norm_num [mL', mQ])
    refine ⟨⟨(sat_FRow l hl μ).mpr ⟨?_, ?_⟩, ?_, hμd⟩, ?_⟩
    · rw [hμL 0]
      have : ν (Lv 0) ≤ max (σ (Rv 0)) (6/5) :=
        le_trans hvL (max_le_max (by linarith [hrow.1]) le_rfl)
      rw [← hR 0] at this
      rcases le_total (ν (Rv 0)) (6/5) with h | h
      · rw [max_eq_right h] at this; linarith
      · rw [max_eq_left h] at this; linarith
    · rw [hμL 1]; linarith
    · rw [sat_domL, hμL 0, hμL 1]; exact (sat_domL ν).mp hdomLν
    · rw [sat_region_lt 3 (by norm_num), cutSatR_val 3 (by norm_num)]
      exact ⟨by norm_num [loL, loQ]; linarith, h3, by rw [capL3]; exact h15⟩
  have hgν : Formula.sat (hostGuard vs 3 Side.R (mR q)) ν :=
    frames_right (vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL) (hguardR_all q) hwin
      hguard
  rw [← hR 0, ← hR 1] at hx
  interval_cases q
  · rw [sat_guardR0] at hgν
    exact climbSlow ν hdomRν hgν.2.1 hgν.2.2.1 hgν.2.2.2 (ν (Lv 1)) hfin
  · rw [sat_guardR1] at hgν
    exact climbMed 1 le_rfl (by norm_num) ν hdomRν hgν.2.1 hgν.2.2.1 hx.2.2 (ν (Lv 1)) hfin
  · rw [sat_guardR2] at hgν
    exact climbMed 2 (by norm_num) le_rfl ν hdomRν hgν.2.1 hgν.2.2.1 hx.2.2 (ν (Lv 1)) hfin
  · rw [sat_guardR3] at hgν
    exact climbFast ν hdomRν hgν (ν (Lv 1)) hfin

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
    by_cases h4 : q < 4
    · exact respondG t ht dt q h4 hσ hg hreg
    · exact absurd hreg (not_sat_region_sink q h4 σ)

/-- **`rover_patrol_zones` (suite_v2), Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The statement of `rover_patrol_zones_modeKeyed` (the declared rows
keyed by `u_L`, the file's left automaton, the envelope) with every right edge testing the
entered mode's guard (`GrG_guards`) and the loop invariant's right region the current mode's
guard and kept cut atoms (`mvRegionR` at `gregion`; `STALL` excluded). Response: the climb
(`respondG`), every switch legal. Z3-free; for every window length `dt`. -/
theorem rover_patrol_zones_guarded (dt : ℝ) :
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

end V2RoverPatrolZonesGuarded
end RelCertifier
