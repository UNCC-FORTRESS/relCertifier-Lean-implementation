/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2c_6dof` over the GUARDED right automaton — the mirror

`RoverRung2cModal.rover_rung2c_modal` states Theorem 3 at the lockstep invariant
(`v_L = v_R`, `s_L = s_R`, `ψ_L = ψ_R`, `θ_L = θ_R`) over the `⊤`-guarded right chain. Over the
GUARDED chain (every edge tests the lowered guard of the band it enters, `GrG_guards`) at the
mode-consistent region (the right in the guard of its current band and above its odometer
floor), the response is forced: the lockstep puts the right in the band of the left window
(the left's guard places `s_L = s_R` in it), the right mirrors the window in that band (the
certified coupling of the pair, `VerdR6 l`), and switches at the window's end into the band
its odometer has reached. A `STEEP` window that carries the odometer from below `0.6` past
`1.4` would leave the right with no legal switch (`STEEP`'s successors are `MODER` and
`STEEP`), and any switch inside the window would break the lockstep (the bands' `v` set points
differ): the guarded statement is FALSE for windows that long (`dt > 2.12`). It holds for every
window up to the model's control interval, `dt ≤ ε_L = 1`: the odometer grows by at most
`0.8 dt ≤ 0.8`, the width of `MODER`'s band, from strictly below `STEEP`'s ceiling `0.6`.
-/
import RelCertifier.Instances.RoverRung2cModal
import RelCertifier.Proofs.Encoding.LadderSync
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverRung2cGuarded

open DL DLCalTiming DLRel Parse Set RoverRung2cModal GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := hostGuard vs6 6 Side.R (mR6 tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [mode6 0, mode6 1, mode6 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range refinement_ladder_rover_rung2c_6dof_IR.R.modes.length).flatMap (fun q =>
      (mR6 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2c_6dof_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range refinement_ladder_rover_rung2c_6dof_IR.R.modes.length).flatMap (fun q =>
      (mR6 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2c_6dof_IR.R.modes.findIdx (·.name == nm))))
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
    simp [refinement_ladder_rover_rung2c_6dof_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated (odometer bands only) -/

theorem sat_guardR0 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2c_6dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2c_6dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 6)) : Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) x ↔
    7/5 ≤ x (Rv 1) := by
  simp [hostGuard, mR6, refinement_ladder_rover_rung2c_6dof_IR, Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4, vs6,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]


/-! ## The reference's band runs (explicit; the attitude-weighted odometer) -/

/-- `ψ, θ` decay `e^{−t}`, `z, φ` are frozen. -/
noncomputable def dR : Fin 6 → ℝ := ![0, 0, 1, 1, 0, 0]

noncomputable def φo (ρ : State (Var 6)) (i : Fin 6) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

noncomputable def kapT (ρ : State (Var 6)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 3 t * φo ρ 3 t)

theorem dR_nonneg (k : Fin 6) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 6)) (hρ : Formula.sat domR6 ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 3 t ∧ φo ρ 3 t ≤ 3/20) := by
  have hD := (sat_domR6 ρ).mp hρ
  obtain ⟨_, _, h2l, h2h, _, h3l, h3h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b3 := decay_between (ρ (Rv 3)) (dR 3) t (dR_nonneg 3) ht
  unfold φo
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b3.1, le_trans b3.2 (max_le h3h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 6)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 6)) (hρ : Formula.sat domR6 ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h3l, h3h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem kapT_le (ρ : State (Var 6)) (t : ℝ) : kapT ρ t ≤ 1 := by
  unfold kapT
  nlinarith [mul_self_nonneg (φo ρ 2 t), mul_self_nonneg (φo ρ 3 t)]

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
      rw [fR6_eval1 q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 3 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domR6 ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) hD.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domR6]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
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

theorem LR_run (q : ℕ) (ρ : State (Var 6)) (t : ℝ) :
    LR.run q ρ t = trajR ρ (phiK φo kapT q ρ) t := rfl

/-! ## The anchor (lockstep and the band's odometer floor) and its box invariance -/

noncomputable def anc (l : ℕ) : Formula (Var 6) := FM g6 (gs9 l)

theorem anc_box (l : ℕ) (hv : VerdR6 l) :
    ∀ σ ω, Formula.sat (anc l) σ →
      Program.sem (Program.ode (jointSys (fL6 l) (fR6 l) (Term.const 1))
        (Formula.and domL6 domR6)) σ ω → Formula.sat (anc l) ω := by
  intro σ ω hσ hω
  have hAll := segPresAll_from_strata_verdicts' (fL6 l) (fR6 l) (Term.const 1)
    (Formula.and domL6 domR6) (g6 :: gs9 l) hv
  exact (sat_FM_iff g6 (gs9 l) ω).mpr (hAll σ ((sat_FM_iff g6 (gs9 l) σ).mp hσ) ω hω)

theorem anc_fv (l : ℕ) : (anc l).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  unfold anc at hv
  by_contra hn
  refine notMem_FM_fv (fun c hc hvc => hn ?_) hv
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hgAt 0 hvc
  · rcases List.mem_append.mp hc with hc | hc
    · simp only [gs6, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _ hvc
    · rw [List.mem_singleton] at hc
      subst hc
      simp only [lowFace, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
        Set.mem_singleton_iff] at hvc
      subst hvc; exact Or.inr ⟨1, rfl⟩

theorem lock_s {x : State (Var 6)} (h : Formula.sat (FM g6 gs6) x) : x (Lv 1) = x (Rv 1) := by
  have h2 := (sat_FM_iff g6 gs6 x).mp h (gAt 2) (by simp [gs6])
  have h3 := (sat_FM_iff g6 gs6 x).mp h (gAt 3) (by simp [gs6])
  rw [gAt2_eval] at h2
  rw [gAt3_eval] at h3
  linarith

/-! ## The mirror response -/

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 6)}
    (h : Program.sem (windowSeg (leftBlock (fL6 l)) domL6 tg6 dt 1) σ ν) (i : Fin 6) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fL6 l) domL6 1 dt 1 (hfL6 l hl) hdomL6
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **The mirror response** of left window `l` from right band `q` (in its guard and above its
floor), for windows up to the control interval `ε_L = 1`: the right mirrors the window in band `l = q` and switches
at its end into the band its odometer has reached (`l` or `l + 1`). -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt1 : dt ≤ 1) (q : ℕ) (hq : q < 3)
    (hv : VerdR6 l) {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (FM g6 gs6) env6) σ)
    (hgR : Formula.sat (hostGuard vs6 6 Side.R (mR6 q)) σ)
    (hreg : Formula.sat (region6 q) σ) :
    GResp GrG q (gwindowSeg (guard6 l) (leftBlock (fL6 l)) domL6 tg6 dt 1)
      (fun qf => Formula.and (Formula.and (FM g6 gs6) env6) (region6 qf)) σ := by
  refine gresp_of_rresp (fun ν hν => ?_)
  obtain ⟨hgl, hwin⟩ := gwindowSeg_runs hν
  have hR := window_right l hl dt hwin
  have hdomLν : Formula.sat domL6 ν :=
    windowSeg_end_domL (leftBlock (fL6 l)) domL6 tg6 dt 1 (by norm_num) hwin
  have hwin' := hwin
  simp only [windowSeg, List.replicate_succ, List.replicate_zero, bigSeq] at hwin'
  obtain ⟨ν1, hseg, hrest⟩ := hwin'
  rw [sem_test] at hrest
  obtain ⟨hνeq, -⟩ := hrest
  obtain ⟨r, ΦL, hL, hΦr, hrdt⟩ := clockedSeg_sol hseg
  have hΦrν : ∀ i, ΦL r (Lv i) = ν (Lv i) := by intro i; rw [hΦr, hνeq]
  have hdomRν : Formula.sat domR6 ν := by
    refine (Formula.coincidence domR6 (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomR6 hx
    exact (hR i).symm
  -- the lockstep puts the right in the left window's band: `q = l`
  have hsl := lock_s hσ.1
  have hql : q = l := by
    have hgq := hgR
    interval_cases l <;> interval_cases q <;> first
      | rfl
      | (exfalso
         first
           | (rw [sat_guard6_0] at hgl) | (rw [sat_guard6_1] at hgl) | (rw [sat_guard6_2] at hgl)
         first
           | (rw [sat_guardR0] at hgq) | (rw [sat_guardR1] at hgq) | (rw [sat_guardR2] at hgq)
         first | linarith [hgl.1, hgl.2, hgq.1, hgq.2] | linarith [hgl.1, hgl.2, hgq])
  subst hql
  -- the mirror stretch: the pair's anchor from the window's start to its end
  have hA0 : Formula.sat (anc q) (mergeLR σ (ΦL 0) ν) := by
    have hσA : Formula.sat (anc q) σ := FM_add9 q hσ.1 ((sat_region6_iff q σ).mp hreg)
    refine (sat_of_agree (anc_fv q) (y := σ) (fun i => ?_) (fun i => ?_)).mpr hσA
    · rw [mergeLR_L, hL.hΦ0, Function.update_of_ne (by simp [Lv, Prod.ext_iff])]
    · rw [mergeLR_R, hR i]
  have hRs := LR.sol q hq ν hdomRν r hL.hr
  have hj := joint_of_sols tg6 (fun i => by simp [Lv, Prod.ext_iff]) (fun i => by simp [Rv, Prod.ext_iff])
    (hfL6 q hq) (hfR6 q hq) hdomL6 hdomR6 hL hRs σ
  have h2 : (fun t => LR.run q ν t) 0 = ν := hRs.hΦ0
  simp only [h2] at hj
  have hAr := anc_box q hv _ _ hA0 hj
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = LR.run q ν r := ⟨_, rfl⟩
  rw [← hμ] at hAr
  have hμL : ∀ i, μ (Lv i) = ν (Lv i) := by rw [hμ]; exact LR.left q ν r
  have hrows : Formula.sat (FM g6 gs6) μ := by
    refine FM_drop9 q ((sat_of_agree (anc_fv q) (y := mergeLR σ (ΦL r) μ) (fun i => ?_)
      (fun i => ?_)).mpr hAr)
    · rw [mergeLR_L, hΦrν i, hμL i]
    · rw [mergeLR_R]
  have hμdom : Formula.sat domR6 μ := by rw [hμ]; exact LR.end_dom q hq ν hdomRν r hL.hr
  -- the odometer at the end: from the band's floor, grown by at most `0.8 r`
  have hs_lo : ν (Rv 1) ≤ μ (Rv 1) := by rw [hμ]; exact (LR.s_low q hq ν hdomRν r hL.hr).2
  have hs_hi : μ (Rv 1) ≤ ν (Rv 1) + 4/5 * r := by
    rw [hμ, LR_run, trajR_R, phiK_s]
    have hD := (sat_domR6 ν).mp hdomRν
    have := integral_vk_high q ν (kapT ν) (kapT_cont ν) hD.2.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2.1
      hL.hr (fun u hu _ => ⟨by linarith [kapT_low ν hdomRν hu], kapT_le ν u⟩)
    linarith
  have hfin : ∀ qf, qf < 3 → b6 qf ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM g6 gs6) env6) (region6 qf)) μ := by
    intro qf _ hb
    refine ⟨⟨hrows, ?_, hμdom⟩, (sat_region6_iff qf μ).mpr hb⟩
    refine (Formula.coincidence domL6 (fun x hx => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomL6 hx
    exact hμL i
  have hrun : Program.sem (Program.ode (mode6 q).sys (mode6 q).dom) ν μ := by
    rw [hμ]; exact LR.sem q hq ν hdomRν r hL.hr
  have hνs : ν (Rv 1) = σ (Rv 1) := hR 1
  interval_cases q
  · rw [sat_guardR0] at hgR
    by_cases hlo : μ (Rv 1) < 3/5
    · exact rresp_step (GrG_modeAt 0 (by norm_num)) (edgeG_mem 0 0 (by simp [GrG])) hrun
        (by show Formula.sat (hostGuard vs6 6 Side.R (mR6 0)) μ
            rw [sat_guardR0]; exact ⟨by linarith [hgR.1], hlo⟩)
        (rresp_stop (hfin 0 (by norm_num) (by simp [b6]; linarith [hgR.1])))
    · exact rresp_step (GrG_modeAt 0 (by norm_num)) (edgeG_mem 0 1 (by simp [GrG])) hrun
        (by show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) μ
            rw [sat_guardR1]; exact ⟨not_lt.mp hlo, by nlinarith [hgR.2]⟩)
        (rresp_stop (hfin 1 (by norm_num) (by simp [b6]; linarith [not_lt.mp hlo])))
  · rw [sat_guardR1] at hgR
    by_cases hlo : μ (Rv 1) < 7/5
    · exact rresp_step (GrG_modeAt 1 (by norm_num)) (edgeG_mem 1 1 (by simp [GrG])) hrun
        (by show Formula.sat (hostGuard vs6 6 Side.R (mR6 1)) μ
            rw [sat_guardR1]; exact ⟨by linarith [hgR.1], hlo⟩)
        (rresp_stop (hfin 1 (by norm_num) (by simp [b6]; linarith [hgR.1])))
    · exact rresp_step (GrG_modeAt 1 (by norm_num)) (edgeG_mem 1 2 (by simp [GrG])) hrun
        (by show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) μ
            rw [sat_guardR2]; exact not_lt.mp hlo)
        (rresp_stop (hfin 2 (by norm_num) (by simp [b6]; linarith [not_lt.mp hlo])))
  · rw [sat_guardR2] at hgR
    exact rresp_step (GrG_modeAt 2 (by norm_num)) (edgeG_mem 2 2 (by simp [GrG])) hrun
      (by show Formula.sat (hostGuard vs6 6 Side.R (mR6 2)) μ
          rw [sat_guardR2]; linarith)
      (rresp_stop (hfin 2 (by norm_num) (by simp [b6]; linarith)))

/-! ## The mode-consistent region and Theorem 3 -/

noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vs6 6 Side.R (mR6 q)) region6 q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region6_fv q)

theorem hmvregG : ∀ q, mv6 ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-- **`refinement_ladder_rover_rung2c_6dof`, Theorem 3 over the GUARDED right automaton, at
the mode-consistent region, for every window up to the control interval (`dt ≤ ε_L = 1`).** The statement of
`rover_rung2c_modal` (the lockstep rows, both envelopes, the file's three guard-gated left
windows) with every right edge testing the entered band's guard (`GrG_guards`) and the loop
invariant's right region the current band's guard and odometer floor (`mvRegionR` at
`gregion`). Response: the mirror (`respondG`). Residuals: the three packs `VerdR6 l`
(unchanged). For `dt > 2.12` the statement is false (`docs/GUARDED-SWITCHING.md` §4.5, by
argument); the windows beyond the control interval are outside the model. -/
theorem rover_rung2c_guarded (dt : ℝ) (hdt : 0 ≤ dt) (hdt1 : dt ≤ 1)
    (hv0 : VerdR6 0) (hv1 : VerdR6 1) (hv2 : VerdR6 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs6 dt))
      (rightAutomatonBody GrG mv6)
      (RFormula.and (RFormula.and (canonInvM g6 gs6) (envLR domL6 domR6))
        (mvRegionR mv6 gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mv6 (FM g6 gs6) domL6 domR6 gregion
    (leftProgs6 dt) (canonInvM g6 gs6) (encode_canonInvM g6 gs6) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgs6, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL6 d hd).1
        (hL6 d hd).2.1 (hL6 d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub GrG _ hgRG hRvG hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · refine hstep_assembled_GR GrG mv6 (FM g6 gs6) env6 gregion (leftProgs6 dt)
      hmvF6 hmvenv6 hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframes6 dt) ?_
    refine Hmulti_regionG GrG mv6 _ region6 GrG_guards (FM g6 gs6) env6 (leftProgs6 dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgs6, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL6 d hd).1
        (hL6 d hd).2.1 (hL6 d hd).2.2) (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg hreg
      rw [GrG_len] at hq
      simp only [leftProgs6, leftData6, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt hdt1 q hq hv0 hσ hg hreg
      · exact respondG 1 (by norm_num) dt hdt1 q hq hv1 hσ hg hreg
      · exact respondG 2 (by norm_num) dt hdt1 q hq hv2 hσ hg hreg
  · exact hddF_multiR_G GrG 0 1 dt leftData6 gregion (canonInvM g6 gs6) domL6 domR6
      (by decide) hgRG hRvG hL6 (fun q _ => gregion_fv q)
      (canonInvM_varsL g6 gs6 (by
        intro g' hg'
        simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR g6 gs6) hdomL6 hdomR6

end RoverRung2cGuarded
end RelCertifier
