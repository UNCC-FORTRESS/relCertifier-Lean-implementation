/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2_3to6` over the GUARDED automata — the synchronized climb

`RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal` states Theorem 3 over the `⊤`-guarded
right chain with PLAIN left windows (no left guard test). Over the guarded right automaton
that form is false (`docs/GUARDED-SWITCHING.md` §4.5: a `FLAT` window from `s_L = 0.1`).
This file states it with the paper's left program: every left window is entered inside its
lowered guard (`STEEP`: `0 ≤ s < 0.6 ∧ v ≤ 0.3`, `MODER`: `0.6 ≤ s < 1.4 ∧ v ≤ 0.5`,
`FLAT`: `s ≥ 1.4 ∧ v ≤ 0.65`), first as the choice of the guard-gated windows
(`rover_ladder_rung2_3to6_choice`), then as the guard-gated left automaton
(`rover_ladder_rung2_3to6_leftAut`, by the generic bridge).

Response. The row `ψ_L = ψ_R` (both `ψ' = −ψ`) ties the reference to the deployed's clock, so
the reference answers a window by running for exactly its duration, climbing the chain inside
it when its odometer reaches the next band's floor (`syncClimb`). The left guard and the
right's mode-consistent region order the bands: `s_L` is in band `l`, `s_R` in band `q`, and
`s_L ≤ s_R`, so `l ≤ q`; the reference only climbs, so every stretch is a pair `(l, q')` with
`l ≤ q'`, exactly the forward and same-band pairs the certificate covers. On each stretch the
rows are preserved by that pair's certified coupling (the unchanged packs `Verd36 l q'`, all
at λ = 1). The pairs `l > q'` (the flattened left's mismatched terrain pair) never occur.
-/
import RelCertifier.Instances.RoverLadderRung2Modal
import RelCertifier.Proofs.Encoding.LadderSync
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverLadderRung2Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung2Modal GPins

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

/-! ## The rows are box invariants of the certified forward and same-band joint flows -/

theorem FM6_fv : (FM g6 gs6).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => by
    simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact hn (hgAt _ hvc)) hv

theorem row_box (l q : ℕ) (hv : Verd36 l q) :
    ∀ σ ω, Formula.sat (FM g6 gs6) σ →
      Program.sem (Program.ode (jointSys (fL6 l) (fR6 q) (Term.const 1))
        (Formula.and domL6 domR6)) σ ω → Formula.sat (FM g6 gs6) ω := by
  intro σ ω hσ hω
  have hAll := segPresAll_from_strata_verdicts' (fL6 l) (fR6 q) (Term.const 1)
    (Formula.and domL6 domR6) (g6 :: gs6) hv
  exact (sat_FM_iff g6 gs6 ω).mpr (hAll σ ((sat_FM_iff g6 gs6 σ).mp hσ) ω hω)

/-- The anchor of band `q'` for left window `l`: the rows when `l ≤ q'`, `⊥` otherwise (the
reference never visits a band below the window's). -/
noncomputable def anchor (l q' : ℕ) : Formula (Var 6) :=
  if l ≤ q' then FM g6 gs6 else Formula.neg Formula.tt

/-! ## The guarded window family and the synchronized response -/

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

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 6)}
    (h : Program.sem (windowSeg (leftBlock (fL6 l)) domL6 tg6 dt 1) σ ν) (i : Fin 6) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fL6 l) domL6 1 dt 1 (hfL6 l hl) hdomL6
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **The guarded response** of the guard-gated window `l` from right band `q` (in its guard):
the synchronized climb; the rows hold at the window's end. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3)
    (hv : ∀ q' < 3, l ≤ q' → Verd36 l q') {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (FM g6 gs6) env6) σ)
    (hgR : Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) σ) :
    GResp GrG q (gwindowSeg (guard6 l) (leftBlock (fL6 l)) domL6 tg6 dt 1)
      (fun _ => Formula.and (Formula.and (FM g6 gs6) env6) Formula.tt) σ := by
  refine gresp_of_rresp (fun ν hν => ?_)
  obtain ⟨hgL, hwin⟩ := gwindowSeg_runs hν
  have hsrow : σ (Lv 1) ≤ σ (Rv 1) := by
    have h := (sat_FM_iff g6 gs6 σ).mp hσ.1 (gAt 1) (by simp [g6, gs6])
    rw [gAt1_eval] at h; linarith
  have hlq : l ≤ q := band_le l q hl hq σ hgL hgR hsrow
  have hR := window_right l hl dt hwin
  have hdomLν : Formula.sat domL6 ν :=
    windowSeg_end_domL (leftBlock (fL6 l)) domL6 tg6 dt 1 (by norm_num) hwin
  have hgν : Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) ν :=
    frames_right (vars_windowSegL_sub (fL6 l) domL6 1 dt 1 (hfL6 l hl) hdomL6)
      (hguardR_all q) hwin hgR
  have hwin' := hwin
  simp only [windowSeg, List.replicate_succ, List.replicate_zero, bigSeq] at hwin'
  obtain ⟨ν1, hseg, hrest⟩ := hwin'
  rw [sem_test] at hrest
  obtain ⟨hνeq, -⟩ := hrest
  have hode := clockedSeg_runs hseg
  obtain ⟨r, ΦL, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hode
  have hL : ODESol (clk tg6 (leftBlock (fL6 l))) domL6 (Function.update σ tg6 0) r ΦL :=
    ⟨hr, hΦ0, hder, hmask, hdom⟩
  have hΦrν : ∀ i, ΦL r (Lv i) = ν (Lv i) := by
    intro i; rw [hΦr, hνeq]
  have hdomRν : Formula.sat domR6 ν := by
    refine (Formula.coincidence domR6 (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomR6 hx
    exact (hR i).symm
  have hA0 : Formula.sat (anchor l q) (mergeLR σ (ΦL 0) ν) := by
    rw [anchor, if_pos hlq]
    refine (sat_of_agree FM6_fv (y := σ) (fun i => ?_) (fun i => ?_)).mpr hσ.1
    · rw [mergeLR_L, hΦ0, Function.update_of_ne (by simp [Lv, Prod.ext_iff])]
    · rw [mergeLR_R, hR i]
  refine syncClimb LR fR6 (fun _ _ => rfl) (fL6 l) domL6 tg6 (fun i => by simp [Lv, Prod.ext_iff])
    (fun i => by simp [Rv, Prod.ext_iff]) (hfL6 l hl)
    (fun q' hq' => hfR6 q' hq') hdomL6 hdomR6 hL σ (anchor l)
    (fun q' hq' σ' ω hσ' hω => by
      by_cases hlq' : l ≤ q'
      · rw [anchor, if_pos hlq'] at hσ' ⊢
        exact row_box l q' (hv q' hq' hlq') σ' ω hσ' hω
      · rw [anchor, if_neg hlq'] at hσ'
        exact absurd hσ' (by simp [Formula.sat]))
    (fun q' _ y hy _ => by
      by_cases hlq' : l ≤ q'
      · rw [anchor, if_pos hlq'] at hy
        rw [anchor, if_pos (by omega)]; exact hy
      · rw [anchor, if_neg hlq'] at hy
        exact absurd hy (by simp [Formula.sat]))
    (edgeG 0 0) (edgeG 0 1) (edgeG 1 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 0 1 (by simp [GrG]))
    (edgeG_mem 1 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl rfl rfl
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 0)) y
      rw [sat_guardR0]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) y
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) y
      rw [sat_guardR1]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) y
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun y hs => by
      show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) y
      rw [sat_guardR2]; exact hs)
    ν _ ?_ q hq 0 le_rfl hr ν (fun _ => rfl) hdomRν (band_of_guard q hq ν hgν) hA0
  intro qf _ μ hμL hμd _ hA
  have hAF : Formula.sat (FM g6 gs6) (mergeLR σ (ΦL r) μ) := by
    by_cases hlq' : l ≤ qf
    · rw [anchor, if_pos hlq'] at hA; exact hA
    · rw [anchor, if_neg hlq'] at hA; exact absurd hA (by simp [Formula.sat])
  have hAμ : Formula.sat (FM g6 gs6) μ := by
    refine (sat_of_agree FM6_fv (y := mergeLR σ (ΦL r) μ) (fun i => ?_)
      (fun i => ?_)).mpr hAF
    · rw [mergeLR_L, hΦrν i, hμL i]
    · rw [mergeLR_R]
  refine ⟨⟨hAμ, ?_, hμd⟩, trivial⟩
  refine (Formula.coincidence domL6 (fun x hx => ?_)).mpr hdomLν
  obtain ⟨i, rfl⟩ := hdomL6 hx
  exact hμL i

/-! ## Theorem 3 -/

noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vs6 6 Side.R (mR6 q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mv6 ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-- **`refinement_ladder_rover_rung2_3to6`, Theorem 3 over the guarded right automaton, the
left windows guard-gated** (the choice form; see `rover_ladder_rung2_3to6_leftAut` for the
left automaton). Loop invariant: the declared rows (`v_L ≤ v_R`, `s_L ≤ s_R`, `ψ_L = ψ_R`),
both envelopes, the right in its current band's guard. Residuals: the six packs of the
certified forward and same-band pairs (`Verd36 l q`, `l ≤ q`), unchanged. -/
theorem rover_ladder_rung2_3to6_choice (dt : ℝ)
    (hv00 : Verd36 0 0) (hv01 : Verd36 0 1) (hv02 : Verd36 0 2)
    (hv11 : Verd36 1 1) (hv12 : Verd36 1 2) (hv22 : Verd36 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mv6)
      (RFormula.and (RFormula.and (canonInvM g6 gs6) (envLR domL6 domR6))
        (mvRegionR mv6 gregion GrG.modes.length))) := by
  have hv : ∀ l < 3, ∀ q' < 3, l ≤ q' → Verd36 l q' := by
    intro l hl q' hq' hlq
    match l, q', hl, hq', hlq with
    | 0, 0, _, _, _ => exact hv00
    | 0, 1, _, _, _ => exact hv01
    | 0, 2, _, _, _ => exact hv02
    | 1, 1, _, _, _ => exact hv11
    | 1, 2, _, _, _ => exact hv12
    | 2, 2, _, _, _ => exact hv22
    | 1, 0, _, _, h => exact absurd h (by norm_num)
    | 2, 0, _, _, h => exact absurd h (by norm_num)
    | 2, 1, _, _, h => exact absurd h (by norm_num)
    | l + 3, _, h, _, _ => exact absurd h (by omega)
    | _, q' + 3, _, h, _ => exact absurd h (by omega)
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
      · exact respondG 0 (by norm_num) dt q hq (hv 0 (by norm_num)) hσ hg
      · exact respondG 1 (by norm_num) dt q hq (hv 1 (by norm_num)) hσ hg
      · exact respondG 2 (by norm_num) dt q hq (hv 2 (by norm_num)) hσ hg
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM g6 gs6) domL6 domR6
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL g6 gs6 (by
        intro g' hg'
        simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl <;> exact hgAt _))
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
    (hv00 : Verd36 0 0) (hv01 : Verd36 0 1) (hv02 : Verd36 0 2)
    (hv11 : Verd36 1 1) (hv12 : Verd36 1 2) (hv22 : Verd36 2 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mv6)
      (psiK uLA (fun _ => canonInvM g6 gs6) (AL dt).numModes domL6 domR6
        (mvRegionR mv6 gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL6 domR6 gregion _
    (rover_ladder_rung2_3to6_choice dt hv00 hv01 hv02 hv11 hv12 hv22)
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
