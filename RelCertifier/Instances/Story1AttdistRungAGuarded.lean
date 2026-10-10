/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_a_6to8` over the GUARDED right automaton — the synchronized climb

`Story1AttdistRungAHandoff.story1_attdist_rung_a_modeKeyed` states Theorem 3 at the declared
mode-dependent rows over the `⊤`-guarded right chain with the bookkeeping `mvValid`. This file
states it over the GUARDED chain (every edge tests the lowered guard of the band it enters,
`GrG_guards`) at the mode-consistent region (the right in the guard of its current band; no
cut is kept). The rows' attitude-energy conjuncts tie the reference to the deployed's clock,
so the response keeps time with the left window and climbs the chain inside it when its
odometer reaches the next band's floor (`syncClimb`); on every stretch the rows are preserved
by the certified coupling of the pair (left window, current band) — the unchanged packs
`VerdS`/`VerdD`, all at λ = 1, every pair present.
-/
import RelCertifier.Instances.Story1AttdistRungAHandoff
import RelCertifier.Proofs.Encoding.LadderSync
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace Story1AttdistRungAGuarded

open DL DLCalTiming DLRel Parse Set Story1AttdistRungAModal Story1AttdistRungAHandoff GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := hostGuard vsD 8 Side.R (mRD tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 8) :=
  { modes := [modeD 0, modeD 1, modeD 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range story1_attdist_rung_a_6to8_IR.R.modes.length).flatMap (fun q =>
      (mRD q).next.map (fun nm =>
        (q, story1_attdist_rung_a_6to8_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range story1_attdist_rung_a_6to8_IR.R.modes.length).flatMap (fun q =>
      (mRD q).next.map (fun nm =>
        (q, story1_attdist_rung_a_6to8_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsD 8 Side.R (mRD e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeD q) := by
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
  have hm' : m = modeD q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvD q (modeD q) (GrD_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvD ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsD 8 Side.R (mRD q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsD _ dummyD rfl (by
    simp [story1_attdist_rung_a_6to8_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated (odometer bands only) -/

theorem sat_guardR0 (x : State (Var 8)) : Formula.sat (hostGuard vsD 8 Side.R (mRD 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRD, story1_attdist_rung_a_6to8_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsD,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 8)) : Formula.sat (hostGuard vsD 8 Side.R (mRD 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRD, story1_attdist_rung_a_6to8_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsD,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 8)) : Formula.sat (hostGuard vsD 8 Side.R (mRD 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mRD, story1_attdist_rung_a_6to8_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsD,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]


/-! ## The reference's band runs (explicit; the attitude-weighted odometer) -/

/-- The attitude/heave laws: `ψ, θ, z, φ` decay `e^{−t}`, the rates are frozen. -/
noncomputable def dR : Fin 8 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 1]

noncomputable def φo (ρ : State (Var 8)) (i : Fin 8) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

noncomputable def kapT (ρ : State (Var 8)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem dR_nonneg (k : Fin 8) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 8)) (hρ : Formula.sat domRD ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) := by
  have hD := (sat_domRD ρ).mp hρ
  obtain ⟨_, _, _, _, _, _, h2l, h2h, _, h4l, h4h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b4 := decay_between (ρ (Rv 4)) (dR 4) t (dR_nonneg 4) ht
  unfold φo
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b4.1, le_trans b4.2 (max_le h4h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 8)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 8)) (hρ : Formula.sat domRD ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem cstD_eq (q : ℕ) : cstD q = ladC q := rfl

noncomputable def LR : LadderRun GrG domRD :=
  LadderRun.ofKappa GrG domRD modeD fRD φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRD0_eval q hq, cstD_eq])
    (fun ρ i h0 h1 => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRD2_eval q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRD3_eval q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRD4_eval q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRD5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRD6_eval q hq]
        have hf : φo ρ 6 = fun u => ρ (Rv 6) * Real.exp (-(dR 6 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRD7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRD1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRD ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domRD]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRD ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs _ => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs _ => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 2)) x
      rw [sat_guardR2]; exact hs)

/-! ## The rows are box invariants of the certified joint flows -/

theorem FRow_fv (l : ℕ) : (FRow l).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => by
    obtain ⟨i, rfl⟩ := mem_rowGs hc
    exact hn (hgRowAt l i hvc)) hv

/-- The rows of left window `l` stay along every run of the joint system of `(l, q)`. -/
theorem row_box (l q : ℕ) (hl : l < 3)
    (hS : l = 0 → VerdS q) (hD : 0 < l → VerdD l q) :
    ∀ σ ω, Formula.sat (FRow l) σ →
      Program.sem (Program.ode (jointSys (fLD l) (fRD q) (Term.const 1))
        (Formula.and domLD domRD)) σ ω → Formula.sat (FRow l) ω := by
  intro σ ω hσ hω
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · rw [FRow_zero] at hσ ⊢
    have hAll := segPresAll_from_strata_verdicts' (fLD 0) (fRD q) (Term.const 1)
      (Formula.and domLD domRD) (gS :: gsS) (hS rfl)
    exact (sat_FM_iff gS gsS ω).mpr (hAll σ ((sat_FM_iff gS gsS σ).mp hσ) ω hω)
  · have hrow : FRow l = FM gD gsD := by
      interval_cases l
      · exact FRow_one
      · exact FRow_two
    rw [hrow] at hσ ⊢
    have hAll := segPresAll_from_strata_verdicts' (fLD l) (fRD q) (Term.const 1)
      (Formula.and domLD domRD) (gD :: gsD) (hD hpos)
    exact (sat_FM_iff gD gsD ω).mpr (hAll σ ((sat_FM_iff gD gsD σ).mp hσ) ω hω)

/-! ## The synchronized guarded response -/

theorem band_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 8))
    (h : Formula.sat (hostGuard vsD 8 Side.R (mRD q)) x) : ladBand q x := by
  interval_cases q
  · rw [sat_guardR0] at h
    exact ⟨fun _ => h, fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR1] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun _ => h, fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR2] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num), fun _ => h⟩

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 8)}
    (h : Program.sem (windowSeg (leftBlock (fLD l)) domLD tgD dt 1) σ ν) (i : Fin 8) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLD l) domLD 1 dt 1 (hfLD l hl) hdomLD
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **The guarded response** of left window `l` from right band `q` (in its guard): the
synchronized climb; the rows hold at the window's end. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3)
    (hS : ∀ q' < 3, l = 0 → VerdS q') (hD : ∀ q' < 3, 0 < l → VerdD l q') {σ : State (Var 8)}
    (hσ : Formula.sat (Formula.and (FRow l) envD) σ)
    (hgR : Formula.sat (hostGuard vsD 8 Side.R (mRD q)) σ) :
    GResp GrG q (windowSeg (leftBlock (fLD l)) domLD tgD dt 1)
      (fun _ => Formula.and (Formula.and (FRow l) envD) Formula.tt) σ := by
  refine gresp_of_rresp (fun ν hwin => ?_)
  have hR := window_right l hl dt hwin
  have hdomLν : Formula.sat domLD ν :=
    windowSeg_end_domL (leftBlock (fLD l)) domLD tgD dt 1 (by norm_num) hwin
  have hgν : Formula.sat (hostGuard vsD 8 Side.R (mRD q)) ν :=
    frames_right (vars_windowSegL_sub (fLD l) domLD 1 dt 1 (hfLD l hl) hdomLD)
      (hguardR_all q) hwin hgR
  have hwin' := hwin
  simp only [windowSeg, List.replicate_succ, List.replicate_zero, bigSeq] at hwin'
  obtain ⟨ν1, hseg, hrest⟩ := hwin'
  rw [sem_test] at hrest
  obtain ⟨hνeq, -⟩ := hrest
  have hode := clockedSeg_runs hseg
  obtain ⟨r, ΦL, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hode
  have hL : ODESol (clk tgD (leftBlock (fLD l))) domLD (Function.update σ tgD 0) r ΦL :=
    ⟨hr, hΦ0, hder, hmask, hdom⟩
  have hΦrν : ∀ i, ΦL r (Lv i) = ν (Lv i) := by
    intro i; rw [hΦr, hνeq]
  have hdomRν : Formula.sat domRD ν := by
    refine (Formula.coincidence domRD (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRD hx
    exact (hR i).symm
  have hA0 : Formula.sat (FRow l) (mergeLR σ (ΦL 0) ν) := by
    refine (sat_of_agree (FRow_fv l) (y := σ) (fun i => ?_) (fun i => ?_)).mpr hσ.1
    · rw [mergeLR_L, hΦ0, Function.update_of_ne (by simp [Lv, Prod.ext_iff])]
    · rw [mergeLR_R, hR i]
  refine syncClimb LR fRD (fun _ _ => rfl) (fLD l) domLD tgD (fun i => by simp [Lv, Prod.ext_iff])
    (fun i => by simp [Rv, Prod.ext_iff]) (hfLD l hl)
    (fun q' hq' => hfRD q' hq') hdomLD hdomRD hL σ (fun _ => FRow l)
    (fun q' hq' => row_box l q' hl (hS q' hq') (hD q' hq'))
    (fun q' hq' y hy hs => hy)
    (edgeG 0 0) (edgeG 0 1) (edgeG 1 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 0 1 (by simp [GrG]))
    (edgeG_mem 1 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl rfl rfl
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 0)) y
      rw [sat_guardR0]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 1)) y
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 1)) y
      rw [sat_guardR1]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 2)) y
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun y hs => by
      show Formula.sat (hostGuard vsD 8 Side.R (mRD 2)) y
      rw [sat_guardR2]; exact hs)
    ν _ ?_ q hq 0 le_rfl hr ν (fun _ => rfl) hdomRν (band_of_guard q hq ν hgν) hA0
  intro qf _ μ hμL hμd _ hA
  have hAμ : Formula.sat (FRow l) μ := by
    refine (sat_of_agree (FRow_fv l) (y := mergeLR σ (ΦL r) μ) (fun i => ?_)
      (fun i => ?_)).mpr hA
    · rw [mergeLR_L, hΦrν i, hμL i]
    · rw [mergeLR_R]
  refine ⟨⟨hAμ, ?_, hμd⟩, trivial⟩
  refine (Formula.coincidence domLD (fun x hx => ?_)).mpr hdomLν
  obtain ⟨i, rfl⟩ := hdomLD hx
  exact hμL i

/-! ## The mode-consistent region and Theorem 3 -/

noncomputable def gregion (q : ℕ) : Formula (Var 8) :=
  regionG (fun q => hostGuard vsD 8 Side.R (mRD q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvD ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

theorem hulRG : ulD ∉ (rightAutomatonBody GrG mvD).bv :=
  notMem_bv_rightAutomatonBody_G GrG mvD ulD (by decide) (aux_notin_range_Rv 2) hgRG hRvG

theorem hulBkG : ulD ∉ (mvRegion mvD gregion GrG.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mvD gregion GrG.modes.length (fun q _ => gregion_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hstepMG (dt : ℝ)
    (hvS0 : VerdS 0) (hvS1 : VerdS 1) (hvS2 : VerdS 2)
    (hv10 : VerdD 1 0) (hv11 : VerdD 1 1) (hv12 : VerdD 1 2)
    (hv20 : VerdD 2 0) (hv21 : VerdD 2 1) (hv22 : VerdD 2 2) :
    ∀ t < (AD dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envD)
      (mvRegion mvD gregion GrG.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 8)) ((AD dt).window t)
      (Program.star (rightAutomatonBody GrG mvD))
      (Formula.and (Formula.and (FRow t) envD)
        (mvRegion mvD gregion GrG.modes.length))) σ := by
  intro t ht
  rw [AD_numModes] at ht
  rw [AD_window dt t ht]
  have hS : ∀ q' < 3, t = 0 → VerdS q' := by
    intro q' hq' _
    match q', hq' with
    | 0, _ => exact hvS0
    | 1, _ => exact hvS1
    | 2, _ => exact hvS2
  have hD : ∀ q' < 3, 0 < t → VerdD t q' := by
    intro q' hq' ht0
    obtain ⟨h0, h1, h2⟩ : VerdD t 0 ∧ VerdD t 1 ∧ VerdD t 2 := by
      match t, ht, ht0 with
      | 1, _, _ => exact ⟨hv10, hv11, hv12⟩
      | 2, _, _ => exact ⟨hv20, hv21, hv22⟩
    match q', hq' with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
  have hframe : FramesMv (windowSeg (leftBlock (fLD t)) domLD tgD dt 1) mvD := by
    refine framesMv_window (leftBlock (fLD t)) domLD tgD dt 1 mvD (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLD t) _ h
    exact aux_ne_Lv 0 i hi
  refine hstepMode_GR GrG mvD (FRow t) envD gregion _ (aux_notin_FRow 0 t) hmvenvD hmvregG
    hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG hframe ?_
  refine HMode_regionG_ofF GrG mvD _ (fun _ => Formula.tt) GrG_guards (fun _ _ _ => trivial)
    (FRow t) envD _ ?_ ?_
  · intro q _ σ ν hrun
    exact frames_right (vars_windowSegL_sub (fLD t) domLD 1 dt 1 (hfLD t ht) hdomLD)
      (hguardR_all q) hrun
  · intro q hq σ _ hσ hg
    rw [GrG_len] at hq
    have h := respondG t ht dt q hq hS hD hσ hg
    exact gresp_mono (post := fun _ => Formula.and (Formula.and (FRow t) envD) Formula.tt)
      (post' := fun _ => Formula.and (FRow t) envD) (fun _ _ h => h.1) h

/-- **`story1_attdist_rung_a_6to8`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The statement of `story1_attdist_rung_a_modeKeyed` (the declared
rows keyed by `u_L`, the file's left automaton, both envelopes) with every right edge testing
the entered band's guard (`GrG_guards`) and the loop invariant's right region the current
band's guard (`mvRegionR` at `gregion`). Response: the synchronized climb. Residuals: the
nine packs `VerdS`/`VerdD` (unchanged). -/
theorem story1_attdist_rung_a_guarded (dt : ℝ)
    (hvS0 : VerdS 0) (hvS1 : VerdS 1) (hvS2 : VerdS 2)
    (hv10 : VerdD 1 0) (hv11 : VerdD 1 1) (hv12 : VerdD 1 2)
    (hv20 : VerdD 2 0) (hv21 : VerdD 2 1) (hv22 : VerdD 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AD dt) ulD)
      (rightAutomatonBody GrG mvD)
      (psiK ulD ϕRow (AD dt).numModes domLD domRD
        (mvRegionR mvD gregion GrG.modes.length))) := by
  refine theorem3_modeKeyed (AD dt) ulD GrG mvD FRow ϕRow domLD domRD
    (mvRegion mvD gregion GrG.modes.length) (mvRegionR mvD gregion GrG.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (AD dt) GrG 0 1 2 (by decide) (by decide) (hwinD dt) (hgrdD dt)
      (hnextD dt) hgRG hRvG
  · exact hstep_modeKeyed (AD dt) ulD (rightAutomatonBody GrG mvD) FRow envD
      (mvRegion mvD gregion GrG.modes.length) (aux_notin_FRow 2) hulenvD hulBkG (hulGD dt)
      (hframesUlD dt) hulRG (hnextD dt)
      (hstepMG dt hvS0 hvS1 hvS2 hv10 hv11 hv12 hv20 hv21 hv22) (handoffD dt)
  · exact hddF_modeKeyed_G (AD dt) GrG 0 1 2 (by decide) (by decide) ϕRow domLD domRD
      (mvRegionR mvD gregion GrG.modes.length) (hwinD dt) (hgrdD dt) (hnextD dt) hgRG hRvG
      (fun m _ => canonInvM_varsL (gRowAt m 0) (rowGs m) (fun g' hg' => by
        obtain ⟨i, rfl⟩ := mem_rowGs hg'
        exact hgRowAt m i))
      (fun m _ => canonInvM_varsR (gRowAt m 0) (rowGs m)) hdomLD hdomRD rfl
      (fun v hv => mvRegion_fv_sub mvD gregion GrG.modes.length (fun q _ => gregion_fv q) hv)

end Story1AttdistRungAGuarded
end RelCertifier
