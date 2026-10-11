/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story2_lateral_rung_a_8dof` over the GUARDED automata — Theorem 3 by replaying the cover

`Story2LateralAModal` states Theorem 3 over the `⊤`-guarded right chain with PLAIN left windows. This file
states it with the paper's left program (every left window entered inside its lowered guard,
first as the choice of the guard-gated windows, `story2_lateral_rung_a_choice`, then as the guard-gated left
automaton, `story2_lateral_rung_a_leftAut`, by the generic bridge) against the GUARDED right chain at the
mode-consistent region, and proves it by REPLAYING THE EMITTED COVER
(`InstancesV2/BenchCovers/story2_lateral_rung_a_8dof.lean`, λ = 1, budget 1): the left guard, the right's
current guard and `s_L ≤ s_R` give `l ≤ q` (every lower start is inadmissible, as the cover
records), and the right keeps time with the window in the joint nodes (the bands at or above
the window's), switching up at each floor it reaches, every stretch preserved by the joint
pack `Verd l q` (the emitted cover's queries, strata `[0, 1, 3, 4, 5, 6, 2]`). Every switch is legal against the
entered band's guard; the explicit band runs (`LR`) supply only the existence of the right's
runs.
-/
import RelCertifier.Instances.Story2LateralAModal
import RelCertifier.Proofs.Encoding.LadderSync
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.InstancesV2.Cuts.story2_lateral_rung_a_8dof

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace Story2LateralAGuarded

open DL DLCalTiming DLRel Parse Set Story2LateralAModal GPins RelCertifier.Oracle

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := hostGuard vsY 8 Side.R (mRY tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 8) :=
  { modes := [modeY 0, modeY 1, modeY 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range story2_lateral_rung_a_8dof_IR.R.modes.length).flatMap (fun q =>
      (mRY q).next.map (fun nm =>
        (q, story2_lateral_rung_a_8dof_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range story2_lateral_rung_a_8dof_IR.R.modes.length).flatMap (fun q =>
      (mRY q).next.map (fun nm =>
        (q, story2_lateral_rung_a_8dof_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsY 8 Side.R (mRY e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeY q) := by
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
  have hm' : m = modeY q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvY q (modeY q) (GrY_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvY ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsY 8 Side.R (mRY q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsY _ dummyY rfl (by
    simp [story2_lateral_rung_a_8dof_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The guards, evaluated -/

noncomputable def guardY (l : ℕ) : Formula (Var 8) := hostGuard vsY 8 Side.L (mLY l)


theorem sat_guardR0 (x : State (Var 8)) : Formula.sat (hostGuard vsY 8 Side.R (mRY 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRY, story2_lateral_rung_a_8dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsY,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 8)) : Formula.sat (hostGuard vsY 8 Side.R (mRY 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRY, story2_lateral_rung_a_8dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsY,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 8)) : Formula.sat (hostGuard vsY 8 Side.R (mRY 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mRY, story2_lateral_rung_a_8dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsY,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- The left guards place the deployed's odometer in its band. -/
theorem guardL_band (l : ℕ) (hl : l < 3) (x : State (Var 8))
    (h : Formula.sat (guardY l) x) :
    (l = 0 → x (Lv 1) < 3/5) ∧ (l = 1 → 3/5 ≤ x (Lv 1) ∧ x (Lv 1) < 7/5) ∧
      (l = 2 → 7/5 ≤ x (Lv 1)) := by
  interval_cases l <;>
    simp [guardY, hostGuard, mLY, story2_lateral_rung_a_8dof_IR, Run.lowerF, Run.lowerE,
      gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsY, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Lv, and_assoc] at h ⊢ <;> (try linarith) <;> tauto

theorem gAtS_eval (x : State (Var 8)) : Term.eval (gAt 2) x = x (Lv 1) - x (Rv 1) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invYPF, story2_lateral_rung_a_8dof_IR, Run.invToG,
    Run.lowerE, vsY, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

/-- **The bands are ordered**: the deployed in band `l` (its window's guard), the reference
in band `q` (its current mode's guard), and `s_L ≤ s_R` give `l ≤ q`. -/
theorem band_le (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 8))
    (hL : Formula.sat (guardY l) x) (hR : Formula.sat (hostGuard vsY 8 Side.R (mRY q)) x)
    (hs : x (Lv 1) ≤ x (Rv 1)) : l ≤ q := by
  have hb := guardL_band l hl x hL
  interval_cases q
  · rw [sat_guardR0] at hR
    interval_cases l
    · exact le_rfl
    · have := (hb.2.1 rfl).1; linarith
    · have := hb.2.2 rfl; linarith
  · rw [sat_guardR1] at hR
    interval_cases l
    · omega
    · exact le_rfl
    · have := hb.2.2 rfl; linarith
  · omega

theorem band_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 8))
    (h : Formula.sat (hostGuard vsY 8 Side.R (mRY q)) x) : ladBand q x := by
  interval_cases q
  · rw [sat_guardR0] at h
    exact ⟨fun _ => h, fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR1] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun _ => h, fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR2] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num), fun _ => h⟩

/-! ## The reference's band runs (explicit; the attitude-weighted odometer) -/

/-- The reference's laws for every coordinate other than `v` and `s`: decay `e^{−t}` or frozen. -/
noncomputable def dR : Fin 8 → ℝ := ![0, 0, 1, 1, 1, 1, 0, 1]

noncomputable def φo (ρ : State (Var 8)) (i : Fin 8) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ²`. -/
noncomputable def kapT (ρ : State (Var 8)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 3 t * φo ρ 3 t)

theorem dR_nonneg (k : Fin 8) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 8)) (hρ : Formula.sat domRY ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 3 t ∧ φo ρ 3 t ≤ 3/20) := by
  have hD := (sat_domRY ρ).mp hρ
  obtain ⟨_, _, h2l, h2h, _, h3l, h3h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b3 := decay_between (ρ (Rv 3)) (dR 3) t (dR_nonneg 3) ht
  unfold φo
  exact ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
    le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b3.1,
    le_trans b3.2 (max_le h3h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 8)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 8)) (hρ : Formula.sat domRY ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h3l, h3h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem cstY_eq (q : ℕ) : cstY q = ladC q := rfl

noncomputable def LR : LadderRun GrG domRY :=
  LadderRun.ofKappa GrG domRY modeY fRY φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRY0_eval q hq, cstY_eq])
    (fun ρ i h0 h1 => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRY2_eval q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRY3_eval q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRY4_eval q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRY5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRY6_eval q hq]
        have hf : φo ρ 6 = fun u => ρ (Rv 6) * Real.exp (-(dR 6 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRY7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRY1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 3 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRY ρ).mp hρ
      obtain ⟨h6l, h6h, h2l, h2h, h1l, h3l, h3h, h0l, h0h, h7l, h7h, h4l, h4h, h5l, h5h⟩ := hD
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) h0l ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domRY]
      simp only [trajR_R]
      exact ⟨le_trans (le_min h6l (by norm_num)) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le h6h (by norm_num)),
        le_trans (le_min h2l (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le h2h (by norm_num)),
        le_trans h1l hs,
        le_trans (le_min h3l (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le h3h (by norm_num)),
        le_trans (le_min h0l (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le h0h (by linarith [hc.2])),
        le_trans (le_min h7l (by norm_num)) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le h7h (by norm_num)),
        le_trans (le_min h4l (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le h4h (by norm_num)),
        le_trans (le_min h5l (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le h5h (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRY ρ).mp hρ; exact hD.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs _ => by
      show Formula.sat (hostGuard vsY 8 Side.R (mRY 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsY 8 Side.R (mRY 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsY 8 Side.R (mRY 2)) x
      rw [sat_guardR2]; exact hs)

/-! ## The guarded window family -/

noncomputable def leftDataG : List (Formula (Var 8) × (Fin 8 → Term (Var 8))
    × Formula (Var 8) × ℕ) :=
  [(guardY 0, fLY 0, domLY, 1), (guardY 1, fLY 1, domLY, 1), (guardY 2, fLY 2, domLY, 1)]

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 8)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tgY dt d.2.2.2)

theorem hguardL (l : ℕ) (hl : l < 3) : (guardY l).fv ⊆ range Lv :=
  hostGuard_fv_L vsY (mLY l) (by interval_cases l <;> decide)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataG, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfLY 0 (by norm_num), hdomLY⟩
  · exact ⟨hguardL 1 (by norm_num), hfLY 1 (by norm_num), hdomLY⟩
  · exact ⟨hguardL 2 (by norm_num), hfLY 2 (by norm_num), hdomLY⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mvY := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tgY dt d.2.2.2 mvY (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aV (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
def vStr (q : ℕ) : String := if q = 0 then "0.3" else if q = 1 then "0.5" else "0.65"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 8) :=
  cutPairsX vsY 8 Side.L (cutAtomsOfX story2_lateral_rung_a_8dof_cutsV2X.L (mLY l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 8) :=
  cutPairsX vsY 8 Side.R (cutAtomsOfX story2_lateral_rung_a_8dof_cutsV2X.R (mRY q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsY 8 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsY,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsY 8 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsY,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vsY 8 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))] := by
  rw [← gL_s l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsY 8 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))] := by
  rw [← gR_s q hq]; interval_cases q <;> rfl

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) := by
  rw [cL_eq l hl]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  rw [← gL_s l hl]; exact hostAtom_iff (Or.inr rfl) ν
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) := by
  rw [cR_eq q hq]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  rw [← gR_s q hq]; exact hostAtom_iff (Or.inr rfl) ν

/-! ## O1: guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vsY 8 Side.L (mLY l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard story2_lateral_rung_a_8dof_cutsV2X_wf (mLY l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, story2_lateral_rung_a_8dof_cutsV2X, mLY,
        story2_lateral_rung_a_8dof_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, story2_lateral_rung_a_8dof_cutsV2X, mLY,
        story2_lateral_rung_a_8dof_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsY,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mLY, story2_lateral_rung_a_8dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsY,
        Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vsY 8 Side.R (mRY q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard story2_lateral_rung_a_8dof_cutsV2X_wf (mRY q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, story2_lateral_rung_a_8dof_cutsV2X, mRY,
        story2_lateral_rung_a_8dof_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, story2_lateral_rung_a_8dof_cutsV2X, mRY,
        story2_lateral_rung_a_8dof_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsY, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRY, story2_lateral_rung_a_8dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsY,
        Run.resolveVar, List.findIdx?_cons]

/-! ## The fields and envelopes the atoms' staying needs -/

theorem fLY_eval0 (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLY l 0) x = 3 * (ladC l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLY, hostDyn, mLY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv, ladC]

theorem fLY_eval1 (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLY l 1) x =
      x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 3) * x (Lv 3))) := by
  interval_cases l <;>
    simp [fLY, hostDyn, mLY, story2_lateral_rung_a_8dof_IR, vsY, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv]

theorem domL_bnd (z : State (Var 8)) (hz : Formula.sat domLY z) :
    0 ≤ z (Lv 0) ∧ -(1:ℝ)/2 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 1/2 ∧ -(1:ℝ)/2 ≤ z (Lv 3) ∧
      z (Lv 3) ≤ 1/2 := by
  simp only [domLY, hostEvolve, mLY, story2_lateral_rung_a_8dof_IR, vsY] at hz
  simp [Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv] at hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 8)) (hz : Formula.sat domLY z) :
    0 ≤ Term.eval (fLY l 1) z := by
  rw [fLY_eval1 l hl]
  obtain ⟨h0, h1, h2, h3, h4⟩ := domL_bnd z hz
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Lv 2) * z (Lv 2))) - 3/10 * (z (Lv 3) * z (Lv 3)) := by nlinarith
  exact mul_nonneg h0 this

theorem sdotR_nonneg (q : ℕ) (hq : q < 3) (z : State (Var 8)) (hz : Formula.sat domRY z) :
    0 ≤ Term.eval (fRY q 1) z := by
  rw [fRY1_eval q hq]
  have hD := (sat_domRY z).mp hz
  casesm* _ ∧ _
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Rv 2) * z (Rv 2))) - 3/10 * (z (Rv 3) * z (Rv 3)) := by nlinarith
  exact mul_nonneg (by assumption) this

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

theorem stayL (l q : ℕ) (hl : l < 3) (c : ℝ) :
    AtomsStayC (cL l) (jointSys (fLY l) (fRY q) (Term.const c)) (Formula.and domLY domRY) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domLY domRY) (fun x h => h)
    (fun z hz _ => sdotL_nonneg l hl z hz.1) hinit

theorem stayR_gen (q : ℕ) (hq : q < 3) (fL : Fin 8 → Term (Var 8)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 8)) (hD : ∀ z, Formula.sat D z → Formula.sat domRY z) :
    AtomsStayC (cR q) (jointSys fL (fRY q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
    (fun z hz _ => sdotR_nonneg q hq z (hD z hz)) hinit

/-! ## The invariant's components, as the tool lowers them: the statement's own rows -/

theorem comps_eq : hostComps vsY 8
    (story2_lateral_rung_a_8dof_IRv2.invariants.getD 0 ("", PForm.tt)).2 =
      [gAt 0, gAt 1, gAt 2, gAt 3, gAt 4, gAt 5, gAt 6] := by
  have hrow : (story2_lateral_rung_a_8dof_IRv2.invariants.getD 0 ("", PForm.tt)).2
      = invYPF := rfl
  have hlist : pAtoms invYPF = [(atomsOf invYPF).getD 0 .tt, (atomsOf invYPF).getD 1 .tt, (atomsOf invYPF).getD 2 .tt, (atomsOf invYPF).getD 3 .tt, (atomsOf invYPF).getD 4 .tt, (atomsOf invYPF).getD 5 .tt, (atomsOf invYPF).getD 6 .tt] := by decide
  rw [hrow, hostComps_atoms vsY invYPF ?_, hlist]
  · rfl
  · rw [hlist]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hdrops : ("L_v".drop 2).copy = "v" ∧ ("R_v".drop 2).copy = "v" ∧
        ("L_s".drop 2).copy = "s" ∧ ("R_s".drop 2).copy = "s" ∧
        ("L_psi".drop 2).copy = "psi" ∧ ("R_psi".drop 2).copy = "psi" ∧
        ("L_theta_p".drop 2).copy = "theta_p" ∧ ("R_theta_p".drop 2).copy = "theta_p" ∧
        ("L_y".drop 2).copy = "y" ∧ ("R_y".drop 2).copy = "y" ∧
        ("L_y2".drop 2).copy = "y2" ∧ ("R_y2".drop 2).copy = "y2" := by decide
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨⟨_, _, _, rfl⟩, by
        simp [atomsOf, invYPF, story2_lateral_rung_a_8dof_IR, Run.invToG, Run.lowerE,
          vsY, gp_0_3, Run.resolveVar, Parse.dr, hdrops, List.findIdx?_cons]⟩

theorem comps_fv : ∀ c ∈ gY :: gsY, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [gY, gsY, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 1, strata `[0, 1, 3, 4, 5, 6, 2]`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX story2_lateral_rung_a_8dof_IRv2 story2_lateral_rung_a_8dof_cutsV2X 8 0
    [0, 1, 3, 4, 5, 6, 2] 1 l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsY 8 Side.L (mLY l) = domLY := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vsY 8 Side.R (mRY q) = domRY := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (gY :: gsY) (fLY l) (fRY q) 1
      (domCutX (Formula.and domLY domRY) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdXCore (([0, 1, 3, 4, 5, 6, 2] : List ℕ).map (fun i => (hostComps vsY 8
      (story2_lateral_rung_a_8dof_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i
        (Term.const 0)))
    (fLY l) (fRY q) 1 (domCutX (Formula.and (hostEvolve vsY 8 Side.L (mLY l))
      (hostEvolve vsY 8 Side.R (mRY q))) (cL l) (cR q)) at h'
  rw [hc] at h'
  simpa [gY, gsY] using h'

/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mRY q = dummyY :=
    List.getD_eq_default _ _ (by simp [story2_lateral_rung_a_8dof_IR]; omega)
  simp only [cR, this]
  rfl

noncomputable def anc (l q : ℕ) : Formula (Var 8) := FM gY (gsY ++ atomTerms (cL l) (cR q))

theorem cL_fv (l : ℕ) (hl : l < 3) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv := by
  intro a ha
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  intro x hx; simp [thrGe, Term.fv] at hx; subst hx; simp

theorem cR_fv (q : ℕ) : ∀ a ∈ cR q, a.2.fv ⊆ range Rv := by
  intro a ha
  by_cases hq : q < 3
  · rw [cR_eq q hq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    intro x hx; simp [thrGe, Term.fv] at hx; subst hx; simp
  · rw [cR_nil q (by omega)] at ha; simp at ha

theorem anc_fv (l q : ℕ) (hl : l < 3) : (anc l q).fv ⊆ range Lv ∪ range Rv := by
  intro x hx
  by_contra hS
  refine notMem_FM_fv (fun g' hg' hxg => hS ?_) hx
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact comps_fv _ List.mem_cons_self hxg
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact comps_fv _ (List.mem_cons_of_mem _ hg') hxg
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
  rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl (cL_fv l hl a ha hxg)
  · exact Or.inr (cR_fv q a ha hxg)

theorem anc_box (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : Verd l q) :
    ∀ σ ω, Formula.sat (anc l q) σ →
      Program.sem (Program.ode (jointSys (fLY l) (fRY q) (Term.const 1))
        (Formula.and domLY domRY)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX gY gsY (gY :: gsY) (cL l) (cR q) (fLY l) (fRY q) 1 domLY domRY
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl _)
    (stayR_gen q hq (fLY l) 1 (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vsY 8 Side.R (mRY e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 8)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM gY gsY) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

/-! ## The ladder's switching choreography (odometer bands, no speed cap) -/

abbrev Cap (_q : ℕ) (_x : State (Var 8)) : Prop := True

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 8))
    (hg : Formula.sat (hostGuard vsY 8 Side.R (mRY q)) x) (hd : Formula.sat domRY x) :
    ladPre Cap domRY q x := ⟨hq, band_of_guard q hq x hg, trivial, hd⟩

theorem ladPre_R (q : ℕ) (x y : State (Var 8)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : ladPre Cap domRY q x) : ladPre Cap domRY q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, -, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, trivial, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · refine (Formula.coincidence domRY (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRY hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 8), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vsY 8 Side.R (mRY 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2⟩
theorem leg11 : ∀ x : State (Var 8), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vsY 8 Side.R (mRY 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2⟩
theorem leg01 : ∀ x : State (Var 8), x (Rv 1) = 3/5 → Cap 0 x → SwitchLegal LR.e01 x := by
  intro x hs _
  show Formula.sat (hostGuard vsY 8 Side.R (mRY 1)) x
  rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩
theorem leg12 : ∀ x : State (Var 8), x (Rv 1) = 7/5 → Cap 1 x → SwitchLegal LR.e12 x := by
  intro x hs _
  show Formula.sat (hostGuard vsY 8 Side.R (mRY 2)) x
  rw [sat_guardR2]; exact le_of_eq hs.symm
theorem leg22 : ∀ x : State (Var 8), 7/5 ≤ x (Rv 1) → Cap 2 x → SwitchLegal LR.e22 x := by
  intro x hs _
  show Formula.sat (hostGuard vsY 8 Side.R (mRY 2)) x
  rw [sat_guardR2]; exact hs

/-- The cover's joint nodes of window `l`: the bands at or above the window's (every start
below is inadmissible: the left guard, the right guard and `s_L ≤ s_R` order the bands); no
reposition node is used. -/
def J (l q : ℕ) : Prop := l ≤ q ∧ q < 3
def D (_l _q : ℕ) : Prop := False

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 8) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domRY q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domRY) E :=
  ladder_hmove LR Cap (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (edgeG 0 0)
    (edgeG 1 1) (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    leg01 leg11 leg12 leg22 (J l) (fun q hJ hq2 => ⟨by have := hJ.1; omega, by omega⟩) E hE

theorem hexitR (l : ℕ) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domRY) (ladPre Cap domRY) :=
  fun _ hD => hD.elim

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (q : ℕ) (hq : q < 3) {σ : State (Var 8)}
    (hσ : Formula.sat (Formula.and (FM gY gsY) envY) σ)
    (hg : Formula.sat (hostGuard vsY 8 Side.R (mRY q)) σ) :
    GResp GrG q (gwindowSeg (guardY l) (leftBlock (fLY l)) domLY tgY dt (0 + 1))
      (fun _ => Formula.and (Formula.and (FM gY gsY) envY) Formula.tt) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · exact h.elim
  refine replay_gresp GrG LR.m fRY domRY (fLY l) domLY (guardY l) aY
    hgRG (hfLY l hl) hdomLY hdomRY (hguardL l hl) 1 one_pos (J l) (D l)
    (fun q h => hfRY q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h.2)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.2 (hJv q h))
    (fun q h => (h : False).elim)
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domRY) (ladPre Cap domRY) (ladPre Cap domRY) ladPre_R ladPre_R
    (hmoveR l _ (fun _ _ _ h => h)) (fun _ _ => hmoveR l _ (fun _ _ hJ h => ⟨hJ, h⟩))
    (hexitR l) dt 0 q σ ?_ hσ.2.1 _ ?_
  · intro hgL
    have hpre := pre_of_guard q hq σ hg hσ.2.2
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    have hsrow : σ (Lv 1) ≤ σ (Rv 1) := by
      have h := (sat_FM_iff gY gsY σ).mp hσ.1 (gAt 2) (by simp [gY, gsY])
      rw [gAtS_eval] at h; linarith
    exact Or.inl ⟨⟨band_le l q hl hq σ hgL hg hsrow, hq⟩, hpre⟩
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLY ν :=
      windowSeg_end_domL (leftBlock (fLY l)) domLY tgY dt (0 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FM gY gsY) μ := by
      refine (sat_of_agree (fun x hx => ?_) (fun i => ?_) (fun i => ?_)).mp hA'
      · by_contra hS
        exact notMem_FM_fv (fun g' hg' hxg => hS (comps_fv g' hg' hxg)) hx
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hpre.2.2.2⟩, trivial⟩
    refine (Formula.coincidence domLY (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLY hv
    exact hμL i

/-! ## Theorem 3 -/

noncomputable def gregion (q : ℕ) : Formula (Var 8) :=
  regionG (fun q => hostGuard vsY 8 Side.R (mRY q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvY ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-- **`story2_lateral_rung_a_8dof`, Theorem 3 over the guarded right automaton, the
left windows guard-gated, by replaying the emitted cover** (the choice form; see
`rover_ladder_rung2_3to6_leftAut` for the left automaton). The right answers window `l` from
band `q` (always `q ≥ l`: the left guard, the right guard and `s_L ≤ s_R` order the bands, the
cover's admissibility) by keeping time with the window at the cover's λ = 1 in the joint
nodes, switching up at each floor it reaches, every stretch preserved by its joint pack
`Verd l q` (the emitted cover's queries, strata `[0, 1, 3, 4, 5, 6, 2]`). -/
theorem story2_lateral_rung_a_choice (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mvY)
      (RFormula.and (RFormula.and (canonInvM gY gsY) (envLR domLY domRY))
        (mvRegionR mvY gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvY (FM gY gsY) domLY domRY gregion
    (leftProgsG dt) (canonInvM gY gsY) (encode_canonInvM gY gsY) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgsG, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLG d hd).1
        (hLG d hd).2.1 (hLG d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub GrG _ hgRG hRvG hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · refine hstep_assembled_GR GrG mvY (FM gY gsY) envY gregion (leftProgsG dt)
      hmvFY hmvenvY hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesG dt) ?_
    refine Hmulti_regionG GrG mvY _ (fun _ => Formula.tt) GrG_guards (FM gY gsY) envY
      (leftProgsG dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsG, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLG d hd).1
        (hLG d hd).2.1 (hLG d hd).2.2) (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsG, leftDataG, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · refine respondR 0 (by norm_num) dt (fun q h => ?_) q hq hσ hg
        obtain ⟨-, h3⟩ := h
        interval_cases q
        · exact h00
        · exact h01
        · exact h02
      · refine respondR 1 (by norm_num) dt (fun q h => ?_) q hq hσ hg
        obtain ⟨h1, h3⟩ := h
        interval_cases q
        · exact h11
        · exact h12
      · refine respondR 2 (by norm_num) dt (fun q h => ?_) q hq hσ hg
        obtain ⟨h1, h3⟩ := h
        interval_cases q
        exact h22
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM gY gsY) domLY domRY
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL gY gsY comps_fv)
      (canonInvM_varsR gY gsY) hdomLY hdomRY

/-! ## The paper's left program: the guard-gated left automaton -/

/-- The file's left `next` lists, resolved to indices (`STEEP → [MODER, STEEP]`,
`MODER → [FLAT, MODER]`, `FLAT → [FLAT]`). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLY l).next.filterMap
    (Handoff.leftModeIndex story2_lateral_rung_a_8dof_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

noncomputable def AL (dt : ℝ) : LeftAut 8 := LeftAut.ofG leftDataG tgY dt nextLA

abbrev uLA : Var 8 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsY 8 Side.L (mLY l)) := rfl

/-- **`story2_lateral_rung_a_8dof`, Theorem 3 with the paper's left program** (the
guard-gated left automaton against the guarded right automaton; the rows for every left mode;
the right in its current band's guard). -/
theorem story2_lateral_rung_a_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvY)
      (psiK uLA (fun _ => canonInvM gY gsY) (AL dt).numModes domLY domRY
        (mvRegionR mvY gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLY domRY gregion _
    (story2_lateral_rung_a_choice dt h00 h01 h02 h11 h12 h22)
    (fun q _ => gregion_fv q)
    (canonInvM_varsL gY gsY (by
      intro g' hg'
      simp only [gY, gsY, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _))
    (canonInvM_varsR gY gsY) hdomLY hdomRY
    (LeftAut.ofG_vars leftDataG 1 dt nextLA hLG).1 (LeftAut.ofG_vars leftDataG 1 dt nextLA hLG).2
    (LeftAut.ofG_hnext leftDataG tgY dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftDataG tgY dt nextLA)

end Story2LateralAGuarded
end RelCertifier
