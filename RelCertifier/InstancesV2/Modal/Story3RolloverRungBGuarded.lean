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

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsV 12 Side.R (mRV tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeV 0, modeV 1, modeV 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

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

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeV q) := by
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
  have hm' : m = modeV q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvV q (modeV q) (GrV_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsV 12 Side.R (mRV q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsV _ dummyV rfl (by
    simp [story3_rollover_ladder_rung_b_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated (odometer bands only) -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsV 12 Side.R (mRV 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRV, story3_rollover_ladder_rung_b_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsV,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsV 12 Side.R (mRV 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRV, story3_rollover_ladder_rung_b_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsV,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mRV, story3_rollover_ladder_rung_b_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsV,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The reference's band runs (explicit; the attitude-weighted odometer) -/

/-- The attitude/heave laws: `ψ, θ, φ` decay `e^{−t}`, the yaw-rate pair `(e, r)` is the
critically damped `e = (e₀ + r₀ t) e^{−2t}`, `r = r₀ e^{−2t}`, the rest are frozen. -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0]

noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  if i = 6 then (ρ (Rv 6) + ρ (Rv 7) * t) * Real.exp (-(2 * t))
  else ρ (Rv i) * Real.exp (-(dR i * t))

noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem dR_nonneg (k : Fin 12) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_6 (ρ : State (Var 12)) (t : ℝ) :
    φo ρ 6 t = (ρ (Rv 6) + ρ (Rv 7) * t) * Real.exp (-(2 * t)) := by simp [φo]
theorem φo_dec (ρ : State (Var 12)) (i : Fin 12) (h6 : i ≠ 6) (t : ℝ) :
    φo ρ i t = ρ (Rv i) * Real.exp (-(dR i * t)) := by simp [φo, h6]

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRV ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) := by
  have hD := (sat_domRV ρ).mp hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h2l, h2h, _, _, _, h4l, h4h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b4 := decay_between (ρ (Rv 4)) (dR 4) t (dR_nonneg 4) ht
  rw [φo_dec ρ 2 (by decide), φo_dec ρ 4 (by decide)]
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b4.1, le_trans b4.2 (max_le h4h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT; simp only [φo_dec ρ 2 (by decide), φo_dec ρ 4 (by decide)]; fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRV ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem cstV_eq (q : ℕ) : cstV q = ladC q := rfl

noncomputable def LR : LadderRun GrG domRV :=
  LadderRun.ofKappa GrG domRV modeV fRV φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRV0_eval q hq, cstV_eq])
    (fun ρ i h0 h1 => by
      by_cases h6 : i = 6
      · subst h6; simp [φo]
      · rw [φo_dec ρ i h6]; simp)
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV2_eval q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := by
          funext u; exact φo_dec ρ 2 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide), φo_dec ρ 2 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV3_eval q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := by
          funext u; exact φo_dec ρ 3 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide), φo_dec ρ 3 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV4_eval q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := by
          funext u; exact φo_dec ρ 4 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide), φo_dec ρ 4 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := by
          funext u; exact φo_dec ρ 5 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide), φo_dec ρ 5 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV6_eval q hq, trajR_R, trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide),
          phiK_other _ _ q ρ 7 (by decide) (by decide), φo_dec ρ 7 (by decide), φo_6]
        have hf : φo ρ 6 = fun u => (ρ (Rv 6) + ρ (Rv 7) * u) * Real.exp (-(2 * u)) := by
          funext u; exact φo_6 ρ u
        rw [hf]
        convert hasDerivAt_coupledK (ρ (Rv 6)) (ρ (Rv 7)) 2 t using 1
        simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := by
          funext u; exact φo_dec ρ 7 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide), φo_dec ρ 7 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV8_eval q hq]
        have hf : φo ρ 8 = fun u => ρ (Rv 8) * Real.exp (-(dR 8 * u)) := by
          funext u; exact φo_dec ρ 8 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 8 (by decide) (by decide), φo_dec ρ 8 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV9_eval q hq]
        have hf : φo ρ 9 = fun u => ρ (Rv 9) * Real.exp (-(dR 9 * u)) := by
          funext u; exact φo_dec ρ 9 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 9 (by decide) (by decide), φo_dec ρ 9 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV10_eval q hq]
        have hf : φo ρ 10 = fun u => ρ (Rv 10) * Real.exp (-(dR 10 * u)) := by
          funext u; exact φo_dec ρ 10 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 10 (by decide) (by decide), φo_dec ρ 10 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRV11_eval q hq]
        have hf : φo ρ 11 = fun u => ρ (Rv 11) * Real.exp (-(dR 11 * u)) := by
          funext u; exact φo_dec ρ 11 (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 11 (by decide) (by decide), φo_dec ρ 11 (by decide)]
             convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRV1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRV ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 → k ≠ 6 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 h6 => by
          rw [phiK_other φo kapT q ρ k h0 h1, φo_dec ρ k h6]
          exact decay_between _ _ t (dR_nonneg k) ht
      have he : -(38/25:ℝ) ≤ phiK φo kapT q ρ 6 t ∧ phiK φo kapT q ρ 6 t ≤ 38/25 := by
        rw [phiK_other φo kapT q ρ 6 (by decide) (by decide), φo_6]
        obtain ⟨h6l, h6h, _, _, _, _, _, _, _, _, _, _, h7l, h7h, _⟩ := hD
        exact coupled_boundK _ _ 2 (38/25) t (by norm_num) ⟨by linarith, h6h⟩
          ⟨by linarith, by linarith⟩ ht
      rw [sat_domRV]
      simp only [trajR_R]
      exact ⟨by linarith [he.1],
        he.2,
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 9 (by decide) (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 8 (by decide) (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 11 (by decide) (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 10 (by decide) (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRV ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs _ => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsV 12 Side.R (mRV 2)) x
      rw [sat_guardR2]; exact hs)

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
