/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_b_12dof` over the GUARDED right automaton — the synchronized climb

`Story1AttdistRungBHandoff.story1_attdist_rung_b_modeKeyed` states Theorem 3 at the declared
mode-dependent rows over the `⊤`-guarded right chain, each right band's checked-cut ceiling
`v_R ≤ c_m` as its region. This file states it over the GUARDED chain (every edge tests the
lowered guard of the band it enters, `GrG_guards`) at the mode-consistent region (the band's
guard and its ceiling, `gregion`). The rows' attitude-energy conjuncts tie the reference to
the deployed's clock: the response keeps time with the left window piece by piece and climbs
the chain inside it at the band floors (`syncWindow`). On a stretch in band `m ≥ r` (left
window `r`) the anchor (row `r` and the ceiling of `m`) is preserved by the certified coupling
`VerdR r m`. A band below the window's (`m < r`, only for the energy rows `r ≥ 1`) has no pack
of its own: there the energy rows ride the certified coupling of `(r, r)` along a VIRTUAL run
of band `r` (a proof device, not part of the response), whose attitude coordinates coincide
with the actual run's (the bands differ only in `v`, `s`), and the ceiling of `m` stays along
band `m`'s own run.
-/
import RelCertifier.Instances.Story1AttdistRungBHandoff
import RelCertifier.Proofs.Encoding.LadderSync
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace Story1AttdistRungBGuarded

open DL DLCalTiming DLRel Parse Set Story1AttdistRungBModal Story1AttdistRungBHandoff GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsF 12 Side.R (mRF tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeF 0, modeF 1, modeF 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range story1_attdist_rung_b_12dof_IR.R.modes.length).flatMap (fun q =>
      (mRF q).next.map (fun nm =>
        (q, story1_attdist_rung_b_12dof_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range story1_attdist_rung_b_12dof_IR.R.modes.length).flatMap (fun q =>
      (mRF q).next.map (fun nm =>
        (q, story1_attdist_rung_b_12dof_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsF 12 Side.R (mRF e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeF q) := by
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
  have hm' : m = modeF q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvF q (modeF q) (GrF_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvF ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsF 12 Side.R (mRF q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsF _ dummyF rfl (by
    simp [story1_attdist_rung_b_12dof_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRF, story1_attdist_rung_b_12dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRF, story1_attdist_rung_b_12dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x ↔
    (7/5 ≤ x (Rv 1)) := by
  simp [hostGuard, mRF, story1_attdist_rung_b_12dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cstF_eq (q : ℕ) : cstF q = ladC q := rfl

/-- The attitude/heave laws: `ψ = (ψ₀ + ω_ψ₀ t) e^{−t}`, `θ` alike, the rates and the
`z/φ/y` coordinates decaying `e^{−t}`, the `ω_z/ω_φ/ω_y` rates frozen. -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]

noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  if i = 2 then (ρ (Rv 2) + ρ (Rv 3) * t) * Real.exp (-t)
  else if i = 4 then (ρ (Rv 4) + ρ (Rv 5) * t) * Real.exp (-t)
  else ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ²`. -/
noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem φo_2 (ρ : State (Var 12)) (t : ℝ) :
    φo ρ 2 t = (ρ (Rv 2) + ρ (Rv 3) * t) * Real.exp (-t) := by simp [φo]
theorem φo_4 (ρ : State (Var 12)) (t : ℝ) :
    φo ρ 4 t = (ρ (Rv 4) + ρ (Rv 5) * t) * Real.exp (-t) := by simp [φo]
theorem φo_dec (ρ : State (Var 12)) (i : Fin 12) (h2 : i ≠ 2) (h4 : i ≠ 4) (t : ℝ) :
    φo ρ i t = ρ (Rv i) * Real.exp (-(dR i * t)) := by simp [φo, h2, h4]

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRF ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(3/5:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/5) ∧ (-(3/5:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/5) := by
  have hD := (sat_domRF ρ).mp hρ
  obtain ⟨_, _, h3l, h3h, h5l, h5h, _, _, _, _, _, _, h2l, h2h, _, h4l, h4h, _⟩ := hD
  rw [φo_2, φo_4]
  exact ⟨coupled_bound _ _ (3/5) t ⟨by linarith, h2h⟩ ⟨by linarith, h3h⟩ ht,
    coupled_bound _ _ (3/5) t ⟨by linarith, h4h⟩ ⟨by linarith, h5h⟩ ht⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT; simp only [φo_2, φo_4]; fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRF ρ) {t : ℝ} (ht : 0 ≤ t) :
    7/10 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

noncomputable def LR : LadderRun GrG domRF :=
  LadderRun.ofKappa GrG domRF modeF fRF φo kapT (7/10) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRF0_eval q hq, cstF_eq])
    (fun ρ i h0 h1 => by
      by_cases h2 : i = 2
      · subst h2; simp [φo]
      by_cases h4 : i = 4
      · subst h4; simp [φo]
      · rw [φo_dec ρ i h2 h4]; simp)
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF2_eval q hq, trajR_R, trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide),
          phiK_other _ _ q ρ 3 (by decide) (by decide), φo_dec ρ 3 (by decide) (by decide), φo_2]
        have h := hasDerivAt_coupled (ρ (Rv 2)) (ρ (Rv 3)) t
        have hf : φo ρ 2 = fun u => (ρ (Rv 2) + ρ (Rv 3) * u) * Real.exp (-u) := by
          funext u; exact φo_2 ρ u
        rw [hf]; convert h using 1; simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF3_eval q hq, trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide),
          φo_dec ρ 3 (by decide) (by decide)]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := by
          funext u; exact φo_dec ρ 3 (by decide) (by decide) u
        rw [hf]; convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF4_eval q hq, trajR_R, trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide),
          phiK_other _ _ q ρ 5 (by decide) (by decide), φo_dec ρ 5 (by decide) (by decide), φo_4]
        have h := hasDerivAt_coupled (ρ (Rv 4)) (ρ (Rv 5)) t
        have hf : φo ρ 4 = fun u => (ρ (Rv 4) + ρ (Rv 5) * u) * Real.exp (-u) := by
          funext u; exact φo_4 ρ u
        rw [hf]; convert h using 1; simp [dR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := by
          funext u; exact φo_dec ρ 5 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide), φo_dec ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF6_eval q hq]
        have hf : φo ρ 6 = fun u => ρ (Rv 6) * Real.exp (-(dR 6 * u)) := by
          funext u; exact φo_dec ρ 6 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide), φo_dec ρ 6 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := by
          funext u; exact φo_dec ρ 7 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide), φo_dec ρ 7 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF8_eval q hq]
        have hf : φo ρ 8 = fun u => ρ (Rv 8) * Real.exp (-(dR 8 * u)) := by
          funext u; exact φo_dec ρ 8 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 8 (by decide) (by decide), φo_dec ρ 8 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF9_eval q hq]
        have hf : φo ρ 9 = fun u => ρ (Rv 9) * Real.exp (-(dR 9 * u)) := by
          funext u; exact φo_dec ρ 9 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 9 (by decide) (by decide), φo_dec ρ 9 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF10_eval q hq]
        have hf : φo ρ 10 = fun u => ρ (Rv 10) * Real.exp (-(dR 10 * u)) := by
          funext u; exact φo_dec ρ 10 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 10 (by decide) (by decide), φo_dec ρ 10 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRF11_eval q hq]
        have hf : φo ρ 11 = fun u => ρ (Rv 11) * Real.exp (-(dR 11 * u)) := by
          funext u; exact φo_dec ρ 11 (by decide) (by decide) u
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 11 (by decide) (by decide), φo_dec ρ 11 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR])
          | (convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRF1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRF ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hb2 : -(3/5:ℝ) ≤ phiK φo kapT q ρ 2 t ∧ phiK φo kapT q ρ 2 t ≤ 3/5 := by
        rw [phiK_other φo kapT q ρ 2 (by decide) (by decide)]; exact (φo_bounds ρ hρ ht).1
      have hb4 : -(3/5:ℝ) ≤ phiK φo kapT q ρ 4 t ∧ phiK φo kapT q ρ 4 t ≤ 3/5 := by
        rw [phiK_other φo kapT q ρ 4 (by decide) (by decide)]; exact (φo_bounds ρ hρ ht).2
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (7/10) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 4 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 h2 h4 => by
          rw [phiK_other φo kapT q ρ k h0 h1, φo_dec ρ k h2 h4]
          exact decay_between _ _ t (by fin_cases k <;> simp [dR]) ht
      rw [sat_domRF]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 9 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 11 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 8 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        by linarith [hb2.1],
        hb2.2,
        le_trans hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs,
        by linarith [hb4.1],
        hb4.2,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 10 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 6 (by decide) (by decide) (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide) (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRF ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
      rw [sat_guardR2]; exact hs)


theorem LR_run (q : ℕ) (ρ : State (Var 12)) (t : ℝ) :
    LR.run q ρ t = trajR ρ (phiK φo kapT q ρ) t := rfl

/-- Two bands' runs from the same state agree off `v` and `s`. -/
theorem LR_run_attitude (q q' : ℕ) (ρ : State (Var 12)) (t : ℝ) (i : Fin 12) (h0 : i ≠ 0)
    (h1 : i ≠ 1) : LR.run q ρ t (Rv i) = LR.run q' ρ t (Rv i) := by
  rw [LR_run, LR_run, trajR_R, trajR_R, phiK_other _ _ q ρ i h0 h1, phiK_other _ _ q' ρ i h0 h1]

/-! ## The anchors: row `r` and the ceiling of band `m` -/

noncomputable def anc (r m : ℕ) : Formula (Var 12) := FM (gR r) (gs9R r m)

theorem anc_fv (r m : ℕ) : (anc r m).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  unfold anc at hv
  by_contra hn
  refine notMem_FM_fv (fun c hc hvc => hn ?_) hv
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hgRowAt r 0 hvc
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨i, rfl⟩ := mem_gsR (List.mem_cons_of_mem _ hc)
      exact hgRowAt r i hvc
    · rw [List.mem_singleton] at hc
      subst hc
      simp only [ceilF, Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        or_false] at hvc
      subst hvc; exact Or.inr ⟨0, rfl⟩

theorem eval_ceilF (m : ℕ) (x : State (Var 12)) :
    Term.eval (ceilF m) x = x (Rv 0) - (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20) := by
  simp [ceilF, Term.eval, AOp.interp]

/-- The anchor, split: row `r` and `v_R ≤ c_m`. -/
theorem anc_iff (r m : ℕ) (x : State (Var 12)) :
    Formula.sat (anc r m) x ↔ Formula.sat (FRow r) x ∧ x (Rv 0) ≤ ladC m := by
  unfold anc FRow gs9R
  rw [sat_FM_iff, sat_FM_iff]
  constructor
  · intro h
    refine ⟨fun c hc => h c ?_, ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hc)
    · have := h (ceilF m) (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
      rw [eval_ceilF] at this
      unfold ladC; linarith
  · rintro ⟨h1, h2⟩ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h1 _ List.mem_cons_self
    · rcases List.mem_append.mp hc with hc | hc
      · exact h1 c (List.mem_cons_of_mem _ hc)
      · rw [List.mem_singleton] at hc
        subst hc
        rw [eval_ceilF]; unfold ladC at h2; linarith

/-- The certified pair `(r, m)` (`r ≤ m`): its anchor is a box invariant of the joint flow. -/
theorem anc_box (r m : ℕ) (hv : VerdR r m) :
    ∀ σ ω, Formula.sat (anc r m) σ →
      Program.sem (Program.ode (jointSys (fLF r) (fRF m) (Term.const 1))
        (Formula.and domLF domRF)) σ ω → Formula.sat (anc r m) ω := by
  intro σ ω hσ hω
  have hAll := segPresAll_from_strata_verdicts' (fLF r) (fRF m) (Term.const 1)
    (Formula.and domLF domRF) (ceilF m :: gR r :: gsR r) hv
  have hmem : ∀ c, c ∈ ceilF m :: gR r :: gsR r ↔ c ∈ gR r :: gs9R r m := by
    intro c
    simp only [gs9R, List.mem_cons, List.mem_append, List.mem_singleton]
    tauto
  have hσ' := (sat_FM_iff (gR r) (gs9R r m) σ).mp hσ
  refine (sat_FM_iff (gR r) (gs9R r m) ω).mpr (fun c hc => ?_)
  exact hAll σ (fun c' hc' => hσ' c' ((hmem c').mp hc')) ω hω c ((hmem c).mpr hc)

/-- The energy rows (`r ≥ 1`) read no `v_R`, `s_R`. -/
theorem FRow_attitude (r : ℕ) (hr : 1 ≤ r) (hr3 : r < 3) (x y : State (Var 12))
    (hL : ∀ i, x (Lv i) = y (Lv i)) (hR : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → x (Rv i) = y (Rv i)) :
    Formula.sat (FRow r) x ↔ Formula.sat (FRow r) y := by
  have hrow : FRow r = FRow 1 := by
    interval_cases r
    · rfl
    · exact FRow_two_eq_one
  rw [hrow]
  unfold FRow
  rw [sat_FM_iff, sat_FM_iff]
  have hdL : ("L_psi".drop 2).copy = "psi" := by decide
  have hdR : ("R_psi".drop 2).copy = "psi" := by decide
  have hdLo : ("L_omega_psi".drop 2).copy = "omega_psi" := by decide
  have hdRo : ("R_omega_psi".drop 2).copy = "omega_psi" := by decide
  have hdLt : ("L_theta_p".drop 2).copy = "theta_p" := by decide
  have hdRt : ("R_theta_p".drop 2).copy = "theta_p" := by decide
  have hdLw : ("L_omega_theta".drop 2).copy = "omega_theta" := by decide
  have hdRw : ("R_omega_theta".drop 2).copy = "omega_theta" := by decide
  have e2 := hR 2 (by decide) (by decide)
  have e3 := hR 3 (by decide) (by decide)
  have e4 := hR 4 (by decide) (by decide)
  have e5 := hR 5 (by decide) (by decide)
  simp only [Lv, Rv] at hL e2 e3 e4 e5
  simp [gR, gsR, gRowAt, atomsOf, invRowPF, story1_attdist_rung_b_12dof_IR, Run.invToG,
    Run.lowerE, vsF, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, Parse.dr, hdL, hdR, hdLo, hdRo, hdLt, hdRt,
    hdLw, hdRw, List.findIdx?_cons, ITerm.toHost, Term.eval, AOp.interp, hL, e2, e3, e4, e5]

/-! ## The stretch invariance of the anchors (certified, or along the virtual band) -/

theorem anc_stretch (r : ℕ) (hr : r < 3) (hvs : ∀ m < 3, r ≤ m → VerdR r m)
    {x : State (Var 12)} {rr : ℝ} {ΦL : ℝ → State (Var 12)}
    (hL : ODESol (clk tgF (leftBlock (fLF r))) domLF x rr ΦL) (ω₀ : State (Var 12)) :
    ∀ m < 3, ∀ a b, 0 ≤ a → a ≤ b → b ≤ rr → ∀ ρ, Formula.sat domRF ρ →
      Formula.sat (anc r m) (mergeLR ω₀ (ΦL a) ρ) →
      Formula.sat (anc r m) (mergeLR ω₀ (ΦL b) (LR.run m ρ (b - a))) := by
  intro m hm a b ha hab hb ρ hρ hA
  have htgL : ∀ i, tgF ≠ Lv i := fun i => by simp [Lv, Prod.ext_iff]
  have htgR : ∀ i, tgF ≠ Rv i := fun i => by simp [Rv, Prod.ext_iff]
  have hLs := odeSol_shift hL ha hab hb
  -- a stretch of band `m'` from `ρ`, as a joint run of the pair `(r, m')`
  have joint : ∀ m' < 3, Program.sem (Program.ode (jointSys (fLF r) (fRF m') (Term.const 1))
      (Formula.and domLF domRF)) (mergeLR ω₀ (ΦL a) ρ)
      (mergeLR ω₀ (ΦL b) (LR.run m' ρ (b - a))) := by
    intro m' hm'
    have hRs := LR.sol m' hm' ρ hρ (b - a) (by linarith)
    have hj := joint_of_sols tgF htgL htgR (hfLF r hr) (hfRF m' hm') hdomLF hdomRF hLs hRs ω₀
    have h0 : (fun t => ΦL (a + t)) 0 = ΦL a := by simp
    have h1 : (fun t => ΦL (a + t)) (b - a) = ΦL b := by simp
    have h2 : (fun t => LR.run m' ρ t) 0 = ρ := hRs.hΦ0
    simp only [h0, h1, h2] at hj
    exact hj
  by_cases hrm : r ≤ m
  · exact anc_box r m (hvs m hm hrm) _ _ hA (joint m hm)
  · -- the virtual band `r`
    have hmr : m < r := by omega
    obtain ⟨hrow, hceil⟩ := (anc_iff r m _).mp hA
    have hAr : Formula.sat (anc r r) (mergeLR ω₀ (ΦL a) ρ) := by
      refine (anc_iff r r _).mpr ⟨hrow, ?_⟩
      have := (ladC_mono_le m r (by omega))
      linarith
    have hEnd := (anc_iff r r _).mp (anc_box r r (hvs r hr le_rfl) _ _ hAr (joint r hr))
    refine (anc_iff r m _).mpr ⟨?_, ?_⟩
    · refine (FRow_attitude r (by omega) hr _ _ (fun i => ?_) (fun i h0 h1 => ?_)).mp hEnd.1
      · rw [mergeLR_L, mergeLR_L]
      · rw [mergeLR_R, mergeLR_R, LR_run_attitude r m ρ (b - a) i h0 h1]
    · rw [mergeLR_R] at hceil ⊢
      have := (LR.v_mono m hm ρ (by linarith) (t := b - a) (by linarith)).2
      exact this

/-! ## The synchronized guarded response -/

theorem band_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 12))
    (h : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) x) : ladBand q x := by
  interval_cases q
  · rw [sat_guardR0] at h
    exact ⟨fun _ => h, fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR1] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun _ => h, fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR2] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num), fun _ => h⟩

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 12)}
    (h : Program.sem (windowSeg (leftBlock (fLF l)) domLF tgF dt 2) σ ν) (i : Fin 12) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLF l) domLF 1 dt 2 (hfLF l hl) hdomLF
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem sat_regionF (m : ℕ) (x : State (Var 12)) :
    Formula.sat (regionF m) x ↔ x (Rv 0) ≤ ladC m := by
  simp only [regionF, Formula.sat, CompOp.interp, eval_ceilF, Term.eval]
  unfold ladC; constructor <;> intro h <;> linarith

/-- **The guarded response** of left window `l` from right band `q` (in its guard, under its
ceiling): the synchronized climb across the window's two pieces. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3)
    (hvs : ∀ m < 3, l ≤ m → VerdR l m) {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FRow l) envF) σ)
    (hgR : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) σ)
    (hreg : Formula.sat (regionF q) σ) :
    GResp GrG q (windowSeg (leftBlock (fLF l)) domLF tgF dt 2)
      (fun qf => Formula.and (Formula.and (FRow l) envF) (regionF qf)) σ := by
  refine gresp_of_rresp (fun ν hwin => ?_)
  have hR := window_right l hl dt hwin
  have hdomLν : Formula.sat domLF ν :=
    windowSeg_end_domL (leftBlock (fLF l)) domLF tgF dt 2 (by norm_num) hwin
  have hgν : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) ν :=
    frames_right (vars_windowSegL_sub (fLF l) domLF 1 dt 2 (hfLF l hl) hdomLF)
      (hguardR_all q) hwin hgR
  have hdomRν : Formula.sat domRF ν := by
    refine (Formula.coincidence domRF (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRF hx
    exact (hR i).symm
  have hA0 : Formula.sat (anc l q) (mergeLR σ σ ν) := by
    have hσA : Formula.sat (anc l q) σ :=
      (anc_iff l q σ).mpr ⟨hσ.1, (sat_regionF q σ).mp hreg⟩
    refine (sat_of_agree (anc_fv l q) (y := σ) (fun i => ?_) (fun i => ?_)).mpr hσA
    · rw [mergeLR_L]
    · rw [mergeLR_R, hR i]
  have h := syncWindow LR fRF (fun _ _ => rfl) (fLF l) domLF tgF
    (fun i => by simp [Lv, Prod.ext_iff]) (fun i => by simp [Rv, Prod.ext_iff]) (hfLF l hl)
    (fun q' hq' => hfRF q' hq') hdomLF hdomRF dt (anc l) (fun m => anc_fv l m)
    (fun x rr ΦL hL ω₀ => anc_stretch l hl hvs hL ω₀)
    (fun m hm y hy hs => by
      obtain ⟨h1, h2⟩ := (anc_iff l m y).mp hy
      refine (anc_iff l (m+1) y).mpr ⟨h1, ?_⟩
      have := ladC_mono_le m (m+1) (by omega)
      linarith)
    (edgeG 0 0) (edgeG 0 1) (edgeG 1 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 0 1 (by simp [GrG]))
    (edgeG_mem 1 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl rfl rfl
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 0)) y
      rw [sat_guardR0]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) y
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun y h0 h1 => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) y
      rw [sat_guardR1]; exact ⟨h0, h1⟩)
    (fun y hs => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) y
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun y hs => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) y
      rw [sat_guardR2]; exact hs)
    ν σ 2 σ ν hwin q hq ν (fun _ => rfl) hdomRν (band_of_guard q hq ν hgν) hA0
  refine rresp_of_rrespP (rrespP_mono ?_ h)
  rintro qf μ ⟨_, hμL, hμd, _, hA⟩
  have hAμ : Formula.sat (anc l qf) μ := by
    refine (sat_of_agree (anc_fv l qf) (y := mergeLR σ ν μ) (fun i => ?_) (fun i => ?_)).mpr hA
    · rw [mergeLR_L, hμL i]
    · rw [mergeLR_R]
  obtain ⟨hrow, hceil⟩ := (anc_iff l qf μ).mp hAμ
  refine ⟨⟨hrow, ?_, hμd⟩, (sat_regionF qf μ).mpr hceil⟩
  refine (Formula.coincidence domLF (fun x hx => ?_)).mpr hdomLν
  obtain ⟨i, rfl⟩ := hdomLF hx
  exact hμL i

/-! ## The mode-consistent region and Theorem 3 -/

noncomputable def gregion (q : ℕ) : Formula (Var 12) :=
  regionG (fun q => hostGuard vsF 12 Side.R (mRF q)) regionF q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (regionF_fv q)

theorem hmvregG : ∀ q, mvF ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

theorem hulRG : ulF ∉ (rightAutomatonBody GrG mvF).bv :=
  notMem_bv_rightAutomatonBody_G GrG mvF ulF (by decide) (aux_notin_range_Rv 2) hgRG hRvG

theorem hulBkG : ulF ∉ (mvRegion mvF gregion GrG.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mvF gregion GrG.modes.length (fun q _ => gregion_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hstepMG (dt : ℝ) (hv : ∀ r m, r < 3 → m < 3 → r ≤ m → VerdR r m) :
    ∀ t < (AF dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envF)
      (mvRegion mvF gregion GrG.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 12)) ((AF dt).window t)
      (Program.star (rightAutomatonBody GrG mvF))
      (Formula.and (Formula.and (FRow t) envF)
        (mvRegion mvF gregion GrG.modes.length))) σ := by
  intro t ht
  rw [AF_numModes] at ht
  rw [AF_window dt t ht]
  have hframe : FramesMv (windowSeg (leftBlock (fLF t)) domLF tgF dt 2) mvF := by
    refine framesMv_window (leftBlock (fLF t)) domLF tgF dt 2 mvF (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF t) _ h
    exact aux_ne_Lv 0 i hi
  refine hstepMode_GR GrG mvF (FRow t) envF gregion _ (aux_notin_FRow 0 t) hmvenvF hmvregG
    hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG hframe ?_
  refine HMode_regionG GrG mvF _ regionF GrG_guards (FRow t) envF _ ?_ ?_
  · intro q _ σ ν hrun
    exact frames_right (vars_windowSegL_sub (fLF t) domLF 1 dt 2 (hfLF t ht) hdomLF)
      (hguardR_all q) hrun
  · intro q hq σ _ hσ hg hreg
    rw [GrG_len] at hq
    exact respondG t ht dt q hq (fun m hm htm => hv t m ht hm htm) hσ hg hreg

/-- **`story1_attdist_rung_b_12dof`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The statement of `story1_attdist_rung_b_modeKeyed` (the declared
rows keyed by `u_L`, the file's left automaton with windows of two clocked pieces, both
envelopes) with every right edge testing the entered band's guard (`GrG_guards`) and the loop
invariant's right region the current band's guard and ceiling (`mvRegionR` at `gregion`).
Response: the synchronized climb (`syncWindow`). Residuals: the six packs `VerdR r m`
(`r ≤ m`, unchanged). -/
theorem story1_attdist_rung_b_guarded (dt : ℝ)
    (hv00 : VerdR 0 0) (hv01 : VerdR 0 1) (hv02 : VerdR 0 2)
    (hv11 : VerdR 1 1) (hv12 : VerdR 1 2) (hv22 : VerdR 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AF dt) ulF)
      (rightAutomatonBody GrG mvF)
      (psiK ulF ϕRow (AF dt).numModes domLF domRF
        (mvRegionR mvF gregion GrG.modes.length))) := by
  have hv : ∀ r m, r < 3 → m < 3 → r ≤ m → VerdR r m := by
    intro r m hr hm hrm
    match r, m, hr, hm, hrm with
    | 0, 0, _, _, _ => exact hv00
    | 0, 1, _, _, _ => exact hv01
    | 0, 2, _, _, _ => exact hv02
    | 1, 1, _, _, _ => exact hv11
    | 1, 2, _, _, _ => exact hv12
    | 2, 2, _, _, _ => exact hv22
  refine theorem3_modeKeyed (AF dt) ulF GrG mvF FRow ϕRow domLF domRF
    (mvRegion mvF gregion GrG.modes.length) (mvRegionR mvF gregion GrG.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (AF dt) GrG 0 1 2 (by decide) (by decide) (hwinF dt) (hgrdF dt)
      (hnextF dt) hgRG hRvG
  · exact hstep_modeKeyed (AF dt) ulF (rightAutomatonBody GrG mvF) FRow envF
      (mvRegion mvF gregion GrG.modes.length) (aux_notin_FRow 2) hulenvF hulBkG (hulGF dt)
      (hframesUlF dt) hulRG (hnextF dt) (hstepMG dt hv) (handoffF dt)
  · exact hddF_modeKeyed_G (AF dt) GrG 0 1 2 (by decide) (by decide) ϕRow domLF domRF
      (mvRegionR mvF gregion GrG.modes.length) (hwinF dt) (hgrdF dt) (hnextF dt) hgRG hRvG
      (fun m _ => canonInvM_varsL (gR m) (gsR m) (fun g' hg' => by
        obtain ⟨i, rfl⟩ := mem_gsR hg'
        exact hgRowAt m i))
      (fun m _ => canonInvM_varsR (gR m) (gsR m)) hdomLF hdomRF rfl
      (fun v hv => mvRegion_fv_sub mvF gregion GrG.modes.length (fun q _ => gregion_fv q) hv)

end Story1AttdistRungBGuarded
end RelCertifier
