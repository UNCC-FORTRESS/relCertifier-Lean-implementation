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
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.Proofs.Encoding.ReplayModeKeyed
import RelCertifier.InstancesV2.Cuts.story1_attdist_rung_b_12dof

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace Story1AttdistRungBGuarded

open DL DLCalTiming DLRel Parse Set Story1AttdistRungBModal Story1AttdistRungBHandoff GPins RelCertifier.Oracle

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

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

noncomputable def guardF (l : ℕ) : Formula (Var 12) := hostGuard vsF 12 Side.L (mLF l)

theorem hguardL (l : ℕ) (hl : l < 3) : (guardF l).fv ⊆ range Lv :=
  hostGuard_fv_L vsF (mLF l) (by interval_cases l <;> decide)

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 12) :=
  cutPairsX vsF 12 Side.L (cutAtomsOfX story1_attdist_rung_b_12dof_cutsV2X.L (mLF l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 12) :=
  cutPairsX vsF 12 Side.R (cutAtomsOfX story1_attdist_rung_b_12dof_cutsV2X.R (mRF q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsF 12 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsF,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsF 12 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsF,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vsF 12 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))] := by
  rw [← gL_s l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsF 12 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))] := by
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
    ∀ ν, Formula.sat (hostGuard vsF 12 Side.L (mLF l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard story1_attdist_rung_b_12dof_cutsV2X_wf (mLF l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, story1_attdist_rung_b_12dof_cutsV2X, mLF,
        story1_attdist_rung_b_12dof_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, story1_attdist_rung_b_12dof_cutsV2X, mLF,
        story1_attdist_rung_b_12dof_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsF,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mLF, story1_attdist_rung_b_12dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsF,
        Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vsF 12 Side.R (mRF q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard story1_attdist_rung_b_12dof_cutsV2X_wf (mRF q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, story1_attdist_rung_b_12dof_cutsV2X, mRF,
        story1_attdist_rung_b_12dof_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, story1_attdist_rung_b_12dof_cutsV2X, mRF,
        story1_attdist_rung_b_12dof_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsF, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRF, story1_attdist_rung_b_12dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vsF,
        Run.resolveVar, List.findIdx?_cons]

/-! ## The fields and envelopes the atoms' staying needs -/

theorem fLF_eval1 (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fLF l 1) x =
      x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 4) * x (Lv 4))) := by
  interval_cases l <;>
    simp [fLF, hostDyn, mLF, story1_attdist_rung_b_12dof_IR, vsF, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv]

theorem domL_bnd (z : State (Var 12)) (hz : Formula.sat domLF z) :
    0 ≤ z (Lv 0) ∧ -(3:ℝ)/5 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 3/5 ∧ -(3:ℝ)/5 ≤ z (Lv 4) ∧
      z (Lv 4) ≤ 3/5 := by
  simp only [domLF, hostEvolve, mLF, story1_attdist_rung_b_12dof_IR, vsF] at hz
  simp [Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv] at hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 12)) (hz : Formula.sat domLF z) :
    0 ≤ Term.eval (fLF l 1) z := by
  rw [fLF_eval1 l hl]
  obtain ⟨h0, h1, h2, h3, h4⟩ := domL_bnd z hz
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Lv 2) * z (Lv 2))) - 3/10 * (z (Lv 4) * z (Lv 4)) := by nlinarith
  exact mul_nonneg h0 this

theorem sdotR_nonneg (q : ℕ) (hq : q < 3) (z : State (Var 12)) (hz : Formula.sat domRF z) :
    0 ≤ Term.eval (fRF q 1) z := by
  rw [fRF1_eval q hq]
  have hD := (sat_domRF z).mp hz
  casesm* _ ∧ _
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Rv 2) * z (Rv 2))) - 3/10 * (z (Rv 4) * z (Rv 4)) := by nlinarith
  exact mul_nonneg (by assumption) this

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

theorem stayL (l q : ℕ) (hl : l < 3) (c : ℝ) :
    AtomsStayC (cL l) (jointSys (fLF l) (fRF q) (Term.const c)) (Formula.and domLF domRF) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domLF domRF) (fun x h => h)
    (fun z hz _ => sdotL_nonneg l hl z hz.1) hinit

theorem stayR_gen (q : ℕ) (hq : q < 3) (fL : Fin 12 → Term (Var 12)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 12)) (hD : ∀ z, Formula.sat D z → Formula.sat domRF z) :
    AtomsStayC (cR q) (jointSys fL (fRF q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
    (fun z hz _ => sdotR_nonneg q hq z (hD z hz)) hinit

/-! ## The invariant's components, as the tool lowers them: the statement's own rows -/

/-- The cover's strata order of window `l` (`STEEP`: `[0, 1, 2]`; `MODER`, `FLAT`: `[0, 1]`). -/
def ordOf (l : ℕ) : List ℕ := if l = 0 then [0, 1, 2] else [0, 1]

theorem pAtoms_row (l : ℕ) (hl : l < 3) :
    pAtoms (story1_attdist_rung_b_12dof_IRv2.invariants.getD l ("", PForm.tt)).2 =
      (ordOf l).map (fun i => (atomsOf (invRowPF l)).getD i .tt) := by
  interval_cases l <;> decide

theorem comps_eq (l : ℕ) (hl : l < 3) : hostComps vsF 12
    (story1_attdist_rung_b_12dof_IRv2.invariants.getD l ("", PForm.tt)).2 =
      (ordOf l).map (fun i => gRowAt l i) := by
  rw [hostComps_atoms vsF _ ?_, pAtoms_row l hl, List.map_map]
  · rfl
  · rw [pAtoms_row l hl]
    intro a ha
    have hdrops : ("L_v".drop 2).copy = "v" ∧ ("R_v".drop 2).copy = "v" ∧
        ("L_psi".drop 2).copy = "psi" ∧ ("R_psi".drop 2).copy = "psi" ∧
        ("L_omega_psi".drop 2).copy = "omega_psi" ∧
        ("L_theta_p".drop 2).copy = "theta_p" ∧ ("R_theta_p".drop 2).copy = "theta_p" ∧
        ("L_omega_theta".drop 2).copy = "omega_theta" ∧
        ("R_omega_psi".drop 2).copy = "omega_psi" ∧
        ("R_omega_theta".drop 2).copy = "omega_theta" := by decide
    interval_cases l <;>
    · simp only [ordOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false, if_true, show (1:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 0 by decide,
        if_false] at ha
      rcases ha with rfl | rfl | rfl <;>
        exact ⟨⟨_, _, _, rfl⟩, by
          simp [atomsOf, invRowPF, story1_attdist_rung_b_12dof_IR, Run.invToG, Run.lowerE,
            vsF, gp_2, gp_0_25, Run.resolveVar, Parse.dr, hdrops, List.findIdx?_cons]⟩

theorem rowList (l : ℕ) (hl : l < 3) :
    (ordOf l).map (fun i => gRowAt l i) = gR l :: gsR l := by
  interval_cases l <;> rfl

theorem comps_fv (l : ℕ) : ∀ c ∈ gR l :: gsR l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  obtain ⟨i, rfl⟩ := mem_gsR hc
  exact hgRowAt l i

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 1, the declared row of
`l`, strata `ordOf l`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX story1_attdist_rung_b_12dof_IRv2 story1_attdist_rung_b_12dof_cutsV2X 12 l
    (ordOf l) 1 l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsF 12 Side.L (mLF l) = domLF := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vsF 12 Side.R (mRF q) = domRF := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (gR l :: gsR l) (fLF l) (fRF q) 1
      (domCutX (Formula.and domLF domRF) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  change VerdXCore ((ordOf l).map (fun i => (hostComps vsF 12
      (story1_attdist_rung_b_12dof_IRv2.invariants.getD l ("", PForm.tt)).2).getD i
        (Term.const 0)))
    (fLF l) (fRF q) 1 (domCutX (Formula.and (hostEvolve vsF 12 Side.L (mLF l))
      (hostEvolve vsF 12 Side.R (mRF q))) (cL l) (cR q)) at h'
  rw [comps_eq l hl] at h'
  rw [← rowList l hl]
  interval_cases l <;> simpa [ordOf] using h'

/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mRF q = dummyF :=
    List.getD_eq_default _ _ (by simp [story1_attdist_rung_b_12dof_IR]; omega)
  simp only [cR, this]
  rfl

noncomputable def anc (l q : ℕ) : Formula (Var 12) :=
  FM (gR l) (gsR l ++ atomTerms (cL l) (cR q))

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
  · exact comps_fv l _ List.mem_cons_self hxg
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact comps_fv l _ (List.mem_cons_of_mem _ hg') hxg
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
  rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl (cL_fv l hl a ha hxg)
  · exact Or.inr (cR_fv q a ha hxg)

theorem anc_box (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : Verd l q) :
    ∀ σ ω, Formula.sat (anc l q) σ →
      Program.sem (Program.ode (jointSys (fLF l) (fRF q) (Term.const 1))
        (Formula.and domLF domRF)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX (gR l) (gsR l) (gR l :: gsR l) (cL l) (cR q) (fLF l) (fRF q)
    1 domLF domRF (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl _)
    (stayR_gen q hq (fLF l) 1 (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vsF 12 Side.R (mRF e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 12)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FRow l) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc FRow
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem FRow_fv (l : ℕ) : (FRow l).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => hn (comps_fv l c hc hvc)) hv

/-! ## The band ceilings (the region's checked cut) -/

theorem eval_ceilF (m : ℕ) (x : State (Var 12)) :
    Term.eval (ceilF m) x = x (Rv 0) - (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20) := by
  simp [ceilF, Term.eval, AOp.interp]

theorem sat_regionF (m : ℕ) (x : State (Var 12)) :
    Formula.sat (regionF m) x ↔ x (Rv 0) ≤ ladC m := by
  simp only [regionF, Formula.sat, CompOp.interp, eval_ceilF, Term.eval]
  unfold ladC; constructor <;> intro h <;> linarith


/-! ## The ladder's switching choreography (odometer bands, the band's ceiling carried) -/

abbrev Cap (q : ℕ) (x : State (Var 12)) : Prop := x (Rv 0) ≤ ladC q

theorem band_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 12))
    (h : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) x) : ladBand q x := by
  interval_cases q
  · rw [sat_guardR0] at h
    exact ⟨fun _ => h, fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR1] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun _ => h, fun h' => absurd h' (by norm_num)⟩
  · rw [sat_guardR2] at h
    exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' (by norm_num), fun _ => h⟩

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 12))
    (hg : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) x) (hreg : Formula.sat (regionF q) x)
    (hd : Formula.sat domRF x) :
    ladPre Cap domRF q x := ⟨hq, band_of_guard q hq x hg, (sat_regionF q x).mp hreg, hd⟩

theorem ladPre_R (q : ℕ) (x y : State (Var 12)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : ladPre Cap domRF q x) : ladPre Cap domRF q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, hc, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · show y (Rv 0) ≤ ladC q
    rw [← hxy 0]; exact hc
  · refine (Formula.coincidence domRF (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRF hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 12), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vsF 12 Side.R (mRF 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2⟩
theorem leg11 : ∀ x : State (Var 12), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2⟩
theorem leg01 : ∀ x : State (Var 12), x (Rv 1) = 3/5 → Cap 0 x → SwitchLegal LR.e01 x := by
  intro x hs _
  show Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x
  rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩
theorem leg12 : ∀ x : State (Var 12), x (Rv 1) = 7/5 → Cap 1 x → SwitchLegal LR.e12 x := by
  intro x hs _
  show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
  rw [sat_guardR2]; exact le_of_eq hs.symm
theorem leg22 : ∀ x : State (Var 12), 7/5 ≤ x (Rv 1) → Cap 2 x → SwitchLegal LR.e22 x := by
  intro x hs _
  show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
  rw [sat_guardR2]; exact hs

/-- The cover's joint nodes of window `l`: every band (all nine pairs are `jointOK`, every
start admissible); no reposition node. The ceiling of the current band is carried along. -/
def J (_l q : ℕ) : Prop := q < 3
def D (_l _q : ℕ) : Prop := False

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 12) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domRF q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domRF) E :=
  ladder_hmove LR Cap (ladCap_run LR) ladCap_up (edgeG 0 0)
    (edgeG 1 1) (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    leg01 leg11 leg12 leg22 (J l) (fun q _ hq2 => by show q + 1 < 3; omega) E hE

theorem hexitR (l : ℕ) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domRF) (ladPre Cap domRF) :=
  fun _ hD => hD.elim

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (q : ℕ) (hq : q < 3) {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FRow l) envF) σ)
    (hg : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) σ) (hreg : Formula.sat (regionF q) σ) :
    GResp GrG q (gwindowSeg (guardF l) (leftBlock (fLF l)) domLF tgF dt (1 + 1))
      (fun qf => Formula.and (Formula.and (FRow l) envF) (regionF qf)) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h
    · exact h.elim
  refine replay_gresp GrG LR.m fRF domRF (fLF l) domLF (guardF l) 1
    hgRG (hfLF l hl) hdomLF hdomRF (hguardL l hl) 1 one_pos (J l) (D l)
    (fun q h => hfRF q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h (hJv q h))
    (fun q h => (h : False).elim)
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domRF) (ladPre Cap domRF) (ladPre Cap domRF) ladPre_R ladPre_R
    (hmoveR l _ (fun _ _ _ h => h)) (fun _ _ => hmoveR l _ (fun _ _ hJ h => ⟨hJ, h⟩))
    (hexitR l) dt 1 q σ ?_ hσ.2.1 _ ?_
  · intro hgL
    have hpre := pre_of_guard q hq σ hg hreg hσ.2.2
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    exact ⟨Or.inl ⟨hq, hpre⟩, hA⟩
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLF ν :=
      windowSeg_end_domL (leftBlock (fLF l)) domLF tgF dt (1 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FRow l) μ := by
      refine (sat_of_agree (FRow_fv l) (fun i => ?_) (fun i => ?_)).mp hA'
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hpre.2.2.2⟩, (sat_regionF q' μ).mpr hpre.2.2.1⟩
    refine (Formula.coincidence domLF (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLF hv
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

/-- The per-left-mode step: the gated window's replay, carried to the plain window at the
entered mode's guard. -/
theorem hstepMG (dt : ℝ) (hJv : ∀ l < 3, ∀ q, J l q → Verd l q) :
    ∀ t < (AF dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envF)
      (mvRegion mvF gregion GrG.modes.length)) σ →
    Formula.sat ((AF dt).guard t) σ →
    Formula.sat (faModal (Equiv.refl (Var 12)) ((AF dt).window t)
      (Program.star (rightAutomatonBody GrG mvF))
      (Formula.and (Formula.and (FRow t) envF)
        (mvRegion mvF gregion GrG.modes.length))) σ := by
  intro t ht σ hσ hgL
  rw [AF_numModes] at ht
  rw [AF_guard dt t ht] at hgL
  rw [AF_window dt t ht]
  refine faModal_ungate (φ := guardF t) hgL ?_
  have hframe : FramesMv (gwindowSeg (guardF t) (leftBlock (fLF t)) domLF tgF dt 2) mvF := by
    refine framesMv_gwindow (guardF t) (fLF t) domLF tgF dt 2 mvF (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF t) _ h
    exact aux_ne_Lv 0 i hi
  refine hstepMode_GR GrG mvF (FRow t) envF gregion _ (aux_notin_FRow 0 t) hmvenvF hmvregG
    hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG hframe ?_ σ hσ
  refine HMode_regionG GrG mvF _ regionF GrG_guards (FRow t) envF _ ?_ ?_
  · intro q _ σ ν hrun
    exact frames_right (vars_gwindowSegL_sub (guardF t) (fLF t) domLF 1 dt 2 (hguardL t ht)
      (hfLF t ht) hdomLF) (hguardR_all q) hrun
  · intro q hq σ _ hσ hg hreg
    rw [GrG_len] at hq
    exact respondR t ht dt (hJv t ht) q hq hσ hg hreg

/-- **`story1_attdist_rung_b_12dof`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region, by replaying the emitted cover.** The statement of
`story1_attdist_rung_b_modeKeyed` (the declared rows keyed by `u_L`, the file's left
automaton, both envelopes) with every right edge testing the entered band's guard
(`GrG_guards`) and the loop invariant's right region the current band's guard (`mvRegionR` at
`gregion`: the band's guard and its ceiling). Response
(`InstancesV2/BenchCovers/story1_attdist_rung_b_12dof.lean`, λ = 1, budget 1, all nine pairs
`jointOK`, every start admissible): the right keeps time with the window (two clocked pieces)
entered inside its guard, switching up at each floor it reaches (the ceiling carried along
the band's own run and across the switch), every stretch
preserved by its joint pack `Verd l q` (the emitted cover's queries at the declared row of
`l`, strata `[0, 1, 2]` for `STEEP`, `[0, 1]` for `MODER`/`FLAT`). -/
theorem story1_attdist_rung_b_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AF dt) ulF)
      (rightAutomatonBody GrG mvF)
      (psiK ulF ϕRow (AF dt).numModes domLF domRF
        (mvRegionR mvF gregion GrG.modes.length))) := by
  have hJv : ∀ l < 3, ∀ q, J l q → Verd l q := by
    intro l hl q hq
    change q < 3 at hq
    match l, q, hl, hq with
    | 0, 0, _, _ => exact h00
    | 0, 1, _, _ => exact h01
    | 0, 2, _, _ => exact h02
    | 1, 0, _, _ => exact h10
    | 1, 1, _, _ => exact h11
    | 1, 2, _, _ => exact h12
    | 2, 0, _, _ => exact h20
    | 2, 1, _, _ => exact h21
    | 2, 2, _, _ => exact h22
  refine theorem3_modeKeyed (AF dt) ulF GrG mvF FRow ϕRow domLF domRF
    (mvRegion mvF gregion GrG.modes.length) (mvRegionR mvF gregion GrG.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (AF dt) GrG 0 1 2 (by decide) (by decide) (hwinF dt) (hgrdF dt)
      (hnextF dt) hgRG hRvG
  · exact hstep_modeKeyed_g (AF dt) ulF (rightAutomatonBody GrG mvF) FRow envF
      (mvRegion mvF gregion GrG.modes.length) (aux_notin_FRow 2) hulenvF hulBkG (hulGF dt)
      (hframesUlF dt) hulRG (hnextF dt) (hstepMG dt hJv) (handoffF dt)
  · exact hddF_modeKeyed_G (AF dt) GrG 0 1 2 (by decide) (by decide) ϕRow domLF domRF
      (mvRegionR mvF gregion GrG.modes.length) (hwinF dt) (hgrdF dt) (hnextF dt) hgRG hRvG
      (fun m _ => canonInvM_varsL (gR m) (gsR m) (fun g' hg' => by
        obtain ⟨i, rfl⟩ := mem_gsR hg'
        exact hgRowAt m i))
      (fun m _ => canonInvM_varsR (gR m) (gsR m)) hdomLF hdomRF rfl
      (fun v hv => mvRegion_fv_sub mvF gregion GrG.modes.length (fun q _ => gregion_fv q) hv)

end Story1AttdistRungBGuarded
end RelCertifier
