/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2_3to6` over the GUARDED automata — Theorem 3 by replaying the cover

`RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal` states Theorem 3 over the `⊤`-guarded right chain with PLAIN left windows. This file
states it with the paper's left program (every left window entered inside its lowered guard,
first as the choice of the guard-gated windows, `rover_ladder_rung2_3to6_choice`, then as the guard-gated left
automaton, `rover_ladder_rung2_3to6_leftAut`, by the generic bridge) against the GUARDED right chain at the
mode-consistent region, and proves it by REPLAYING THE EMITTED COVER
(`InstancesV2/BenchCovers/refinement_ladder_rover_rung2_3to6.lean`, λ = 1, budget 1): the left guard, the right's
current guard and `s_L ≤ s_R` give `l ≤ q` (every lower start is inadmissible, as the cover
records), and the right keeps time with the window in the joint nodes (the bands at or above
the window's), switching up at each floor it reaches, every stretch preserved by the joint
pack `Verd l q` (the emitted cover's queries, strata `[0, 2, 3, 1]`). Every switch is legal against the
entered band's guard; the explicit band runs (`LR`) supply only the existence of the right's
runs.
-/
import RelCertifier.Instances.RoverLadderRung2Modal
import RelCertifier.Proofs.Encoding.LadderSync
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung2_3to6

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverLadderRung2Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung2Modal GPins RelCertifier.Oracle

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := hostGuard vs6 6 Side.R (mR6 tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [mode6 0, mode6 1, mode6 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range refinement_ladder_rover_rung2_3to6_IR.R.modes.length).flatMap (fun q =>
      (mR6 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2_3to6_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range refinement_ladder_rover_rung2_3to6_IR.R.modes.length).flatMap (fun q =>
      (mR6 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2_3to6_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vs6 6 Side.R (mR6 e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (mode6 q) := by
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
  have hm' : m = mode6 q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRv6 q (mode6 q) (Gr6_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mv6 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vs6 6 Side.R (mR6 q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs6 _ dummy6 rfl (by
    simp [refinement_ladder_rover_rung2_3to6_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The guards, evaluated -/

theorem sat_guardR0 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2_3to6_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2_3to6_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2_3to6_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-- The left guards place the deployed's odometer in its band. -/
theorem guardL_band (l : ℕ) (hl : l < 3) (x : State (Var 6))
    (h : Formula.sat (guard6 l) x) :
    (l = 0 → x (Lv 1) < 3/5) ∧ (l = 1 → 3/5 ≤ x (Lv 1) ∧ x (Lv 1) < 7/5) ∧
      (l = 2 → 7/5 ≤ x (Lv 1)) := by
  interval_cases l <;>
    simp [guard6, hostGuard, mL6, refinement_ladder_rover_rung2_3to6_IR, Run.lowerF, Run.lowerE,
      gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Lv, and_assoc] at h ⊢ <;> (try linarith) <;> tauto

theorem gAt1_eval (x : State (Var 6)) : Term.eval (gAt 1) x = x (Lv 1) - x (Rv 1) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, inv6PF, refinement_ladder_rover_rung2_3to6_IR, Run.invToG,
    Run.lowerE, vs6, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

/-- **The bands are ordered**: the deployed in band `l` (its window's guard), the reference
in band `q` (its current mode's guard), and `s_L ≤ s_R` give `l ≤ q`. -/
theorem band_le (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 6))
    (hL : Formula.sat (guard6 l) x) (hR : Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) x)
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

theorem band_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 6))
    (h : Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) x) : ladBand q x := by
  interval_cases q
  · rw [sat_guardR0] at h
    exact ⟨fun _ => h, fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR1] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun _ => h, fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR2] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num), fun _ => h⟩

/-! ## The reference's band runs (explicit; the heading-weighted odometer) -/

/-- The attitude laws: `ψ, θ` decay `e^{−t}`, `z, φ` are frozen. -/
noncomputable def dR : Fin 6 → ℝ := ![0, 0, 1, 1, 0, 0]

noncomputable def φo (ρ : State (Var 6)) (i : Fin 6) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2`. -/
noncomputable def kapT (ρ : State (Var 6)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t)

theorem dR_nonneg (k : Fin 6) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 6)) (hρ : Formula.sat domR6 ρ) {t : ℝ} (ht : 0 ≤ t) :
    -(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20 := by
  have hD := (sat_domR6 ρ).mp hρ
  obtain ⟨_, _, h2l, h2h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  unfold φo
  exact ⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
    le_trans b2.2 (max_le h2h (by norm_num))⟩

theorem kapT_cont (ρ : State (Var 6)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 6)) (hρ : Formula.sat domR6 ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨h2l, h2h⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem cst6_eq (q : ℕ) : cst6 q = ladC q := rfl

noncomputable def LR : LadderRun GrG domR6 :=
  LadderRun.ofKappa GrG domR6 mode6 fR6 φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fR6_eval0 q hq, cst6_eq])
    (fun ρ i h0 h1 => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval2 q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval3 q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval4 q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fR6_eval5 q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fR6_eval1 q hq, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domR6 ρ).mp hρ
      obtain ⟨h5l, h5h, h2l, h2h, h1l, h3l, h3h, h0l, h0h, h4l, h4h⟩ := hD
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) h0l ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domR6]
      simp only [trajR_R]
      exact ⟨le_trans (le_min h5l (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le h5h (by norm_num)),
        le_trans (le_min h2l (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le h2h (by norm_num)),
        le_trans h1l hs,
        le_trans (le_min h3l (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le h3h (by norm_num)),
        le_trans (le_min h0l (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le h0h (by linarith [hc.2])),
        le_trans (le_min h4l (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le h4h (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domR6 ρ).mp hρ; exact hD.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs _ => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs _ => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs _ => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x
      rw [sat_guardR2]; exact hs)

/-! ## The guarded window family -/

noncomputable def leftDataG : List (Formula (Var 6) × (Fin 6 → Term (Var 6))
    × Formula (Var 6) × ℕ) :=
  [(guard6 0, fL6 0, domL6, 1), (guard6 1, fL6 1, domL6, 1), (guard6 2, fL6 2, domL6, 1)]

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 6)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg6 dt d.2.2.2)

theorem hguardL (l : ℕ) (hl : l < 3) : (guard6 l).fv ⊆ range Lv :=
  hostGuard_fv_L vs6 (mL6 l) (by interval_cases l <;> decide)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataG, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfL6 0 (by norm_num), hdomL6⟩
  · exact ⟨hguardL 1 (by norm_num), hfL6 1 (by norm_num), hdomL6⟩
  · exact ⟨hguardL 2 (by norm_num), hfL6 2 (by norm_num), hdomL6⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mv6 := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg6 dt d.2.2.2 mv6 (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aV (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
def vStr (q : ℕ) : String := if q = 0 then "0.3" else if q = 1 then "0.5" else "0.65"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs6 6 Side.L (cutAtomsOfX refinement_ladder_rover_rung2_3to6_cutsV2X.L (mL6 l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 6) :=
  cutPairsX vs6 6 Side.R (cutAtomsOfX refinement_ladder_rover_rung2_3to6_cutsV2X.R (mR6 q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vs6 6 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vs6,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gL_v (l : ℕ) (hl : l < 3) : hostAtomG vs6 6 Side.L (aV (vStr l)) = thrLe (Lv 0) (ladC l) := by
  interval_cases l <;>
  simp [aV, vStr, ladC, hostAtomG, cutAtomG, Run.lowerE, gp_0_3, gp_0_5, gp_0_65, vs6,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vs6 6 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vs6,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vs6 6 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l)),
      (hostAtomF vs6 6 Side.L (aV (vStr l)), thrLe (Lv 0) (ladC l))] := by
  rw [← gL_s l hl, ← gL_v l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vs6 6 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))] := by
  rw [← gR_s q hq]; interval_cases q <;> rfl

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) := by
  rw [cL_eq l hl]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [← gL_s l hl]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gL_v l hl]; exact hostAtom_iff (Or.inl rfl) ν
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) := by
  rw [cR_eq q hq]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  rw [← gR_s q hq]; exact hostAtom_iff (Or.inr rfl) ν

/-! ## O1: guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vs6 6 Side.L (mL6 l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard refinement_ladder_rover_rung2_3to6_cutsV2X_wf (mL6 l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2_3to6_cutsV2X, mL6,
        refinement_ladder_rover_rung2_3to6_IR] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2_3to6_cutsV2X, mL6,
        refinement_ladder_rover_rung2_3to6_IR] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vs6,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL6, refinement_ladder_rover_rung2_3to6_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
        Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard refinement_ladder_rover_rung2_3to6_cutsV2X_wf (mR6 q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2_3to6_cutsV2X, mR6,
        refinement_ladder_rover_rung2_3to6_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2_3to6_cutsV2X, mR6,
        refinement_ladder_rover_rung2_3to6_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vs6, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases q <;>
      simp [mR6, refinement_ladder_rover_rung2_3to6_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
        Run.resolveVar, List.findIdx?_cons]

/-! ## The fields and envelopes the atoms' staying needs -/

theorem fL6_eval0 (l : ℕ) (hl : l < 3) (x : State (Var 6)) :
    Term.eval (fL6 l 0) x = 3 * (ladC l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fL6, hostDyn, mL6, refinement_ladder_rover_rung2_3to6_IR, vs6, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv, ladC]

theorem fL6_eval1 (l : ℕ) (hl : l < 3) (x : State (Var 6)) :
    Term.eval (fL6 l 1) x =
      x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 3) * x (Lv 3))) := by
  interval_cases l <;>
    simp [fL6, hostDyn, mL6, refinement_ladder_rover_rung2_3to6_IR, vs6, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv]

theorem domL_bnd (z : State (Var 6)) (hz : Formula.sat domL6 z) :
    0 ≤ z (Lv 0) ∧ -(1:ℝ)/2 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 1/2 ∧ -(1:ℝ)/2 ≤ z (Lv 3) ∧
      z (Lv 3) ≤ 1/2 := by
  simp only [domL6, hostEvolve, mL6, refinement_ladder_rover_rung2_3to6_IR, vs6] at hz
  simp [Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv] at hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 6)) (hz : Formula.sat domL6 z) :
    0 ≤ Term.eval (fL6 l 1) z := by
  rw [fL6_eval1 l hl]
  obtain ⟨h0, h1, h2, h3, h4⟩ := domL_bnd z hz
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Lv 2) * z (Lv 2))) - 3/10 * (z (Lv 3) * z (Lv 3)) := by nlinarith
  exact mul_nonneg h0 this

theorem sdotR_nonneg (q : ℕ) (hq : q < 3) (z : State (Var 6)) (hz : Formula.sat domR6 z) :
    0 ≤ Term.eval (fR6 q 1) z := by
  rw [fR6_eval1 q hq]
  have hD := (sat_domR6 z).mp hz
  casesm* _ ∧ _
  have : (0:ℝ) ≤ 1 - 1/2 * (z (Rv 2) * z (Rv 2)) := by nlinarith
  exact mul_nonneg (by assumption) this

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

theorem stayL (l q : ℕ) (hl : l < 3) (c : ℝ) :
    AtomsStayC (cL l) (jointSys (fL6 l) (fR6 q) (Term.const c)) (Formula.and domL6 domR6) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domL6 domR6) (fun x h => h)
      (fun z hz _ => sdotL_nonneg l hl z hz.1) hinit
  · exact boxle_thrLe_L 0 (ladC l) _ _ _ _ (Formula.and domL6 domR6) (fun x h => h)
      (fun z hz hK => by rw [fL6_eval0 l hl]; linarith) hinit

theorem stayR_gen (q : ℕ) (hq : q < 3) (fL : Fin 6 → Term (Var 6)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 6)) (hD : ∀ z, Formula.sat D z → Formula.sat domR6 z) :
    AtomsStayC (cR q) (jointSys fL (fR6 q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
    (fun z hz _ => sdotR_nonneg q hq z (hD z hz)) hinit

/-! ## The invariant's components, as the tool lowers them: the statement's own rows -/

theorem comps_eq : hostComps vs6 6
    (refinement_ladder_rover_rung2_3to6_IRv2.invariants.getD 0 ("", PForm.tt)).2 =
      [gAt 0, gAt 1, gAt 2, gAt 3] := by
  have hrow : (refinement_ladder_rover_rung2_3to6_IRv2.invariants.getD 0 ("", PForm.tt)).2
      = inv6PF := rfl
  have hlist : pAtoms inv6PF = [(atomsOf inv6PF).getD 0 .tt, (atomsOf inv6PF).getD 1 .tt,
      (atomsOf inv6PF).getD 2 .tt, (atomsOf inv6PF).getD 3 .tt] := by decide
  rw [hrow, hostComps_atoms vs6 inv6PF ?_, hlist]
  · rfl
  · rw [hlist]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hdrops : ("L_v".drop 2).copy = "v" ∧ ("R_v".drop 2).copy = "v" ∧
        ("L_s".drop 2).copy = "s" ∧ ("R_s".drop 2).copy = "s" ∧
        ("L_psi".drop 2).copy = "psi" ∧ ("R_psi".drop 2).copy = "psi" := by decide
    rcases ha with rfl | rfl | rfl | rfl <;>
      exact ⟨⟨_, _, _, rfl⟩, by
        simp [atomsOf, inv6PF, refinement_ladder_rover_rung2_3to6_IR, Run.invToG, Run.lowerE,
          vs6, Run.resolveVar, Parse.dr, hdrops, List.findIdx?_cons]⟩

theorem comps_fv : ∀ c ∈ g6 :: gs6, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact hgAt _

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 1, strata `[0, 2, 3, 1]`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX refinement_ladder_rover_rung2_3to6_IRv2 refinement_ladder_rover_rung2_3to6_cutsV2X 6 0
    [0, 2, 3, 1] 1 l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vs6 6 Side.L (mL6 l) = domL6 := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vs6 6 Side.R (mR6 q) = domR6 := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (g6 :: gs6) (fL6 l) (fR6 q) 1
      (domCutX (Formula.and domL6 domR6) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdXCore (([0, 2, 3, 1] : List ℕ).map (fun i => (hostComps vs6 6
      (refinement_ladder_rover_rung2_3to6_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i
        (Term.const 0)))
    (fL6 l) (fR6 q) 1 (domCutX (Formula.and (hostEvolve vs6 6 Side.L (mL6 l))
      (hostEvolve vs6 6 Side.R (mR6 q))) (cL l) (cR q)) at h'
  rw [hc] at h'
  simpa [g6, gs6] using h'

/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mR6 q = dummy6 :=
    List.getD_eq_default _ _ (by simp [refinement_ladder_rover_rung2_3to6_IR]; omega)
  simp only [cR, this]
  rfl

noncomputable def anc (l q : ℕ) : Formula (Var 6) := FM g6 (gs6 ++ atomTerms (cL l) (cR q))

theorem cL_fv (l : ℕ) (hl : l < 3) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv := by
  intro a ha
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
  · intro x hx; simp [thrGe, thrLe, Term.fv] at hx; subst hx; simp

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
      Program.sem (Program.ode (jointSys (fL6 l) (fR6 q) (Term.const 1))
        (Formula.and domL6 domR6)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX g6 gs6 (g6 :: gs6) (cL l) (cR q) (fL6 l) (fR6 q) 1 domL6 domR6
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl _)
    (stayR_gen q hq (fL6 l) 1 (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vs6 6 Side.R (mR6 e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 6)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM g6 gs6) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

/-! ## The ladder's switching choreography (odometer bands, no speed cap) -/

abbrev Cap (_q : ℕ) (_x : State (Var 6)) : Prop := True

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 6))
    (hg : Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) x) (hd : Formula.sat domR6 x) :
    ladPre Cap domR6 q x := ⟨hq, band_of_guard q hq x hg, trivial, hd⟩

theorem ladPre_R (q : ℕ) (x y : State (Var 6)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : ladPre Cap domR6 q x) : ladPre Cap domR6 q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, -, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, trivial, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · refine (Formula.coincidence domR6 (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomR6 hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 6), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vs6 6 Side.R (mR6 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2⟩
theorem leg11 : ∀ x : State (Var 6), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2⟩
theorem leg01 : ∀ x : State (Var 6), x (Rv 1) = 3/5 → Cap 0 x → SwitchLegal LR.e01 x := by
  intro x hs _
  show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) x
  rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩
theorem leg12 : ∀ x : State (Var 6), x (Rv 1) = 7/5 → Cap 1 x → SwitchLegal LR.e12 x := by
  intro x hs _
  show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x
  rw [sat_guardR2]; exact le_of_eq hs.symm
theorem leg22 : ∀ x : State (Var 6), 7/5 ≤ x (Rv 1) → Cap 2 x → SwitchLegal LR.e22 x := by
  intro x hs _
  show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x
  rw [sat_guardR2]; exact hs

/-- The cover's joint nodes of window `l`: the bands at or above the window's (every start
below is inadmissible: the left guard, the right guard and `s_L ≤ s_R` order the bands); no
reposition node is used. -/
def J (l q : ℕ) : Prop := l ≤ q ∧ q < 3
def D (_l _q : ℕ) : Prop := False

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 6) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domR6 q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domR6) E :=
  ladder_hmove LR Cap (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (edgeG 0 0)
    (edgeG 1 1) (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    leg01 leg11 leg12 leg22 (J l) (fun q hJ hq2 => ⟨by have := hJ.1; omega, by omega⟩) E hE

theorem hexitR (l : ℕ) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domR6) (ladPre Cap domR6) :=
  fun _ hD => hD.elim

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (q : ℕ) (hq : q < 3) {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (FM g6 gs6) env6) σ)
    (hg : Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) σ) :
    GResp GrG q (gwindowSeg (guard6 l) (leftBlock (fL6 l)) domL6 tg6 dt (0 + 1))
      (fun _ => Formula.and (Formula.and (FM g6 gs6) env6) Formula.tt) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · exact h.elim
  refine replay_gresp GrG LR.m fR6 domR6 (fL6 l) domL6 (guard6 l) a6
    hgRG (hfL6 l hl) hdomL6 hdomR6 (hguardL l hl) 1 one_pos (J l) (D l)
    (fun q h => hfR6 q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h.2)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.2 (hJv q h))
    (fun q h => (h : False).elim)
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domR6) (ladPre Cap domR6) (ladPre Cap domR6) ladPre_R ladPre_R
    (hmoveR l _ (fun _ _ _ h => h)) (fun _ _ => hmoveR l _ (fun _ _ hJ h => ⟨hJ, h⟩))
    (hexitR l) dt 0 q σ ?_ hσ.2.1 _ ?_
  · intro hgL
    have hpre := pre_of_guard q hq σ hg hσ.2.2
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    have hsrow : σ (Lv 1) ≤ σ (Rv 1) := by
      have h := (sat_FM_iff g6 gs6 σ).mp hσ.1 (gAt 1) (by simp [g6, gs6])
      rw [gAt1_eval] at h; linarith
    exact Or.inl ⟨⟨band_le l q hl hq σ hgL hg hsrow, hq⟩, hpre⟩
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domL6 ν :=
      windowSeg_end_domL (leftBlock (fL6 l)) domL6 tg6 dt (0 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FM g6 gs6) μ := by
      refine (sat_of_agree (fun x hx => ?_) (fun i => ?_) (fun i => ?_)).mp hA'
      · by_contra hS
        exact notMem_FM_fv (fun g' hg' hxg => hS (comps_fv g' hg' hxg)) hx
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hpre.2.2.2⟩, trivial⟩
    refine (Formula.coincidence domL6 (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomL6 hv
    exact hμL i

/-! ## Theorem 3 -/

noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vs6 6 Side.R (mR6 q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mv6 ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-- **`refinement_ladder_rover_rung2_3to6`, Theorem 3 over the guarded right automaton, the
left windows guard-gated, by replaying the emitted cover** (the choice form; see
`rover_ladder_rung2_3to6_leftAut` for the left automaton). The right answers window `l` from
band `q` (always `q ≥ l`: the left guard, the right guard and `s_L ≤ s_R` order the bands, the
cover's admissibility) by keeping time with the window at the cover's λ = 1 in the joint
nodes, switching up at each floor it reaches, every stretch preserved by its joint pack
`Verd l q` (the emitted cover's queries, strata `[0, 2, 3, 1]`). -/
theorem rover_ladder_rung2_3to6_choice (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mv6)
      (RFormula.and (RFormula.and (canonInvM g6 gs6) (envLR domL6 domR6))
        (mvRegionR mv6 gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mv6 (FM g6 gs6) domL6 domR6 gregion
    (leftProgsG dt) (canonInvM g6 gs6) (encode_canonInvM g6 gs6) ?_ ?_ ?_
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
  · refine hstep_assembled_GR GrG mv6 (FM g6 gs6) env6 gregion (leftProgsG dt)
      hmvF6 hmvenv6 hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesG dt) ?_
    refine Hmulti_regionG GrG mv6 _ (fun _ => Formula.tt) GrG_guards (FM g6 gs6) env6
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
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM g6 gs6) domL6 domR6
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL g6 gs6 comps_fv)
      (canonInvM_varsR g6 gs6) hdomL6 hdomR6

/-! ## The paper's left program: the guard-gated left automaton -/

/-- The file's left `next` lists, resolved to indices (`STEEP → [MODER, STEEP]`,
`MODER → [FLAT, MODER]`, `FLAT → [FLAT]`). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mL6 l).next.filterMap
    (Handoff.leftModeIndex refinement_ladder_rover_rung2_3to6_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

noncomputable def AL (dt : ℝ) : LeftAut 6 := LeftAut.ofG leftDataG tg6 dt nextLA

abbrev uLA : Var 6 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vs6 6 Side.L (mL6 l)) := rfl

/-- **`refinement_ladder_rover_rung2_3to6`, Theorem 3 with the paper's left program** (the
guard-gated left automaton against the guarded right automaton; the rows for every left mode;
the right in its current band's guard). -/
theorem rover_ladder_rung2_3to6_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mv6)
      (psiK uLA (fun _ => canonInvM g6 gs6) (AL dt).numModes domL6 domR6
        (mvRegionR mv6 gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL6 domR6 gregion _
    (rover_ladder_rung2_3to6_choice dt h00 h01 h02 h11 h12 h22)
    (fun q _ => gregion_fv q)
    (canonInvM_varsL g6 gs6 (by
      intro g' hg'
      simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl | rfl | rfl <;> exact hgAt _))
    (canonInvM_varsR g6 gs6) hdomL6 hdomR6
    (LeftAut.ofG_vars leftDataG 1 dt nextLA hLG).1 (LeftAut.ofG_vars leftDataG 1 dt nextLA hLG).2
    (LeftAut.ofG_hnext leftDataG tg6 dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftDataG tg6 dt nextLA)

end RoverLadderRung2Guarded
end RelCertifier
