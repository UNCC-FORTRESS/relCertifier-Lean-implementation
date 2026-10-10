/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_rung4_8to12` over the GUARDED right automaton — Theorem 3 by the ladder climb

`Story3RolloverBaseModal.story3_rollover_base_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT` with the bookkeeping `mvValid`. This file states it over the
GUARDED chain (every edge tests the lowered guard of the band it enters, `GrG_guards`) at the
mode-consistent region (the right in the guard of its current band; no cut is kept), with the
response of `Proofs/Encoding/LadderClimb.lean`: after the left window the reference climbs the
chain (explicit runs, each switch at the next band's floor, legal) and holds `FLAT` until
`v_L ≤ v_R` and `s_L ≤ s_R + 0.2`. Z3-free.
-/
import RelCertifier.Instances.Story3RolloverBaseModal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace Story3RolloverBaseGuarded

open DL DLCalTiming DLRel Parse Set Story3RolloverBaseModal GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsB 12 Side.R (mRB tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeB 0, modeB 1, modeB 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range story3_rollover_base_12dof_IR.R.modes.length).flatMap (fun q =>
      (mRB q).next.map (fun nm =>
        (q, story3_rollover_base_12dof_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range story3_rollover_base_12dof_IR.R.modes.length).flatMap (fun q =>
      (mRB q).next.map (fun nm =>
        (q, story3_rollover_base_12dof_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsB 12 Side.R (mRB e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeB q) := by
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
  have hm' : m = modeB q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvB q (modeB q) (GrB_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvB ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsB 12 Side.R (mRB q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsB _ dummyB rfl (by
    simp [story3_rollover_base_12dof_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsB 12 Side.R (mRB 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRB, story3_rollover_base_12dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsB 12 Side.R (mRB 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRB, story3_rollover_base_12dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsB 12 Side.R (mRB 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRB, story3_rollover_base_12dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cstB_eq (q : ℕ) : cstB q = ladC q := rfl

/-- The attitude/heave laws: every coordinate other than `v` and `s` decays `e^{−t}` or is
frozen (the reference's `ψ, θ, e, φ` relax, their rates and `z, y` are constant). -/
noncomputable def dR : Fin 12 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0]

noncomputable def φo (ρ : State (Var 12)) (i : Fin 12) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ²`. -/
noncomputable def kapT (ρ : State (Var 12)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem dR_nonneg (k : Fin 12) : 0 ≤ dR k := by fin_cases k <;> simp [dR]

theorem φo_bounds (ρ : State (Var 12)) (hρ : Formula.sat domRB ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) := by
  have hD := (sat_domRB ρ).mp hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h2l, h2h, _, _, _, h4l, h4h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (dR_nonneg 2) ht
  have b4 := decay_between (ρ (Rv 4)) (dR 4) t (dR_nonneg 4) ht
  unfold φo
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b4.1, le_trans b4.2 (max_le h4h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 12)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 12)) (hρ : Formula.sat domRB ρ) {t : ℝ} (ht : 0 ≤ t) :
    4/5 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

noncomputable def LR : LadderRun GrG domRB :=
  LadderRun.ofKappa GrG domRB modeB fRB φo kapT (4/5) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRB0_eval q hq, cstB_eq])
    (fun ρ i h0 h1 => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB2_eval q hq]
        have hf : φo ρ 2 = fun u => ρ (Rv 2) * Real.exp (-(dR 2 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 2 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 2)) (dR 2) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB3_eval q hq]
        have hf : φo ρ 3 = fun u => ρ (Rv 3) * Real.exp (-(dR 3 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 3 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 3)) (dR 3) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB4_eval q hq]
        have hf : φo ρ 4 = fun u => ρ (Rv 4) * Real.exp (-(dR 4 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 4 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 4)) (dR 4) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB5_eval q hq]
        have hf : φo ρ 5 = fun u => ρ (Rv 5) * Real.exp (-(dR 5 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 5 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 5)) (dR 5) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB6_eval q hq]
        have hf : φo ρ 6 = fun u => ρ (Rv 6) * Real.exp (-(dR 6 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 6 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 6)) (dR 6) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB7_eval q hq]
        have hf : φo ρ 7 = fun u => ρ (Rv 7) * Real.exp (-(dR 7 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 7 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 7)) (dR 7) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB8_eval q hq]
        have hf : φo ρ 8 = fun u => ρ (Rv 8) * Real.exp (-(dR 8 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 8 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 8)) (dR 8) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB9_eval q hq]
        have hf : φo ρ 9 = fun u => ρ (Rv 9) * Real.exp (-(dR 9 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 9 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 9)) (dR 9) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB10_eval q hq]
        have hf : φo ρ 10 = fun u => ρ (Rv 10) * Real.exp (-(dR 10 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 10 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 10)) (dR 10) t using 1; simp [dR])
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB11_eval q hq]
        have hf : φo ρ 11 = fun u => ρ (Rv 11) * Real.exp (-(dR 11 * u)) := rfl
        rw [hf]
        first
          | (rw [trajR_R, phiK_other _ _ q ρ 11 (by decide) (by decide)]
             convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR, φo])
          | (convert hasDerivAt_decay (ρ (Rv 11)) (dR 11) t using 1; simp [dR]))
    (fun q hq ρ _ t _ => by
      rw [fRB1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRB ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (4/5) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (dR_nonneg k) ht
      rw [sat_domRB]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num)) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.1 (by norm_num)) (hk 9 (by decide) (by decide)).1,
        le_trans (hk 9 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 8 (by decide) (by decide)).1,
        le_trans (hk 8 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 11 (by decide) (by decide)).1,
        le_trans (hk 11 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num)) (hk 10 (by decide) (by decide)).1,
        le_trans (hk 10 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRB ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB 12 Side.R (mRB 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB 12 Side.R (mRB 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB 12 Side.R (mRB 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

/-! ## The guarded response to a left window -/

theorem fLB0_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fLB l 0) x = 3 * (cstB l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLB, hostDyn, mLB, story3_rollover_base_12dof_IR, vsB, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Lv, cstB]

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 12)}
    (h : Program.sem (windowSeg (leftBlock (fLB l)) domLB tgB dt 2) σ ν) (i : Fin 12) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLB l) domLB 1 dt 2 (hfLB l hl) hdomLB
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem gAt0_eval (x : State (Var 12)) : Term.eval (gAt 0) x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gAt, atomsOf, invBPF, story3_rollover_base_12dof_IR, Run.invToG,
    Run.lowerE, vsB, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt1_eval (x : State (Var 12)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invBPF, story3_rollover_base_12dof_IR, Run.invToG,
    Run.lowerE, vsB, gp_0_2, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

/-- The left-only conjuncts of the declared rows read only left coordinates. -/
theorem gAt2_left (x y : State (Var 12)) (h : ∀ i, x (Lv i) = y (Lv i)) :
    Term.eval (gAt 2) x = Term.eval (gAt 2) y := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdr : ("L_r".drop 2).copy = "r" := by decide
  have hde : ("L_e".drop 2).copy = "e" := by decide
  simp only [Lv] at h
  simp [gAt, atomsOf, invBPF, story3_rollover_base_12dof_IR, Run.invToG, Run.lowerE, vsB, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4,
    Run.resolveVar, Parse.dr, hdL, hdr, hde, List.findIdx?_cons, ITerm.toHost, Term.eval,
    AOp.interp, h]

theorem gAt3_left (x y : State (Var 12)) (h : ∀ i, x (Lv i) = y (Lv i)) :
    Term.eval (gAt 3) x = Term.eval (gAt 3) y := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdr : ("L_r".drop 2).copy = "r" := by decide
  have hde : ("L_e".drop 2).copy = "e" := by decide
  simp only [Lv] at h
  simp [gAt, atomsOf, invBPF, story3_rollover_base_12dof_IR, Run.invToG, Run.lowerE, vsB, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4,
    Run.resolveVar, Parse.dr, hdL, hdr, hde, List.findIdx?_cons, ITerm.toHost, Term.eval,
    AOp.interp, h]

theorem gAt4_left (x y : State (Var 12)) (h : ∀ i, x (Lv i) = y (Lv i)) :
    Term.eval (gAt 4) x = Term.eval (gAt 4) y := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdr : ("L_r".drop 2).copy = "r" := by decide
  have hde : ("L_e".drop 2).copy = "e" := by decide
  simp only [Lv] at h
  simp [gAt, atomsOf, invBPF, story3_rollover_base_12dof_IR, Run.invToG, Run.lowerE, vsB, gp_0, gp_0_0, gp_0_05, gp_0_06, gp_0_0625, gp_0_07, gp_0_0775, gp_0_08, gp_0_085, gp_0_1, gp_0_125, gp_0_15, gp_0_156, gp_0_2, gp_0_205, gp_0_25, gp_0_255, gp_0_3, gp_0_30, gp_0_33, gp_0_35, gp_0_355, gp_0_4, gp_0_45, gp_0_48, gp_0_5, gp_0_50, gp_0_55, gp_0_6, gp_0_65, gp_0_6775, gp_0_7, gp_0_72, gp_0_75, gp_0_8, gp_0_84, gp_0_855, gp_0_88, gp_0_9, gp_0_95, gp_1, gp_10, gp_1000_0, gp_100_0, gp_10_0, gp_12_0, gp_12_45, gp_12_5, gp_13_0, gp_15_0, gp_15_5, gp_16, gp_16_0, gp_17_0, gp_1_0, gp_1_001, gp_1_1, gp_1_125, gp_1_15, gp_1_2, gp_1_25, gp_1_3, gp_1_4, gp_1_5, gp_1_52, gp_1_6, gp_1_62, gp_1_68, gp_1_8, gp_2, gp_20_0, gp_21_0, gp_22_0, gp_23_0, gp_24_0, gp_25_0, gp_26_0, gp_27_0, gp_28_0, gp_29_0, gp_2_0, gp_2_1, gp_2_2, gp_2_25, gp_2_5, gp_2_6, gp_3, gp_30_0, gp_32_0, gp_33_0, gp_34_0, gp_35_0, gp_36_0, gp_3_0, gp_3_04, gp_3_2, gp_3_5, gp_3_6, gp_4, gp_40_0, gp_4_0, gp_4_4, gp_5, gp_50_0, gp_5_0, gp_5_5, gp_60_0, gp_6_0, gp_6_5, gp_7_45, gp_8, gp_80_0, gp_899_95, gp_8_0, gp_8_45, gp_90_0, gp_99_0, gp_9_0, gp_9_524, gp_m0_01, gp_m0_125, gp_m0_2, gp_m0_25, gp_m0_3, gp_m0_4, gp_m0_42, gp_m0_45, gp_m0_5, gp_m0_6, gp_m0_7, gp_m0_75, gp_m0_8, gp_m1, gp_m10_0, gp_m1_0, gp_m1_5, gp_m1_52, gp_m2, gp_m2_0, gp_m2_5, gp_m3_04, gp_m4,
    Run.resolveVar, Parse.dr, hdL, hdr, hde, List.findIdx?_cons, ITerm.toHost, Term.eval,
    AOp.interp, h]

theorem sat_FB (x : State (Var 12)) : Formula.sat (FM gB gsB) x ↔ (Term.eval (gAt 0) x ≤ 0 ∧ Term.eval (gAt 1) x ≤ 0 ∧ Term.eval (gAt 2) x ≤ 0 ∧ Term.eval (gAt 3) x ≤ 0 ∧ Term.eval (gAt 4) x ≤ 0) := by
  rw [sat_FM_iff]
  simp only [gB, gsB, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

theorem sat_regionB (m : ℕ) (x : State (Var 12)) : Formula.sat (regionB m) x ↔
    x (Rv 0) ≤ (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20) := by
  simp [regionB, ceilB, Formula.sat, CompOp.interp, Term.eval, AOp.interp]

/-- **The guarded response** of left window `l` from right band `q` (in its guard): the
ladder climb, then hold `FLAT` until the two relational rows hold. The left-only conjuncts of
the declared rows (they constrain the deployed alone) hold at the left window's end: any
response of the certified relaxation (`hold`, from `HmultiB`) ends there with the same left
coordinates. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3) {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FM gB gsB) envB) σ)
    (hguard : Formula.sat (hostGuard vsB 12 Side.R (mRB q)) σ)
    (hold : ∀ ν, Program.sem (gwindowSeg Formula.tt (leftBlock (fLB l)) domLB tgB dt 2) σ ν →
      ∃ μ, (∀ i, μ (Lv i) = ν (Lv i)) ∧ Formula.sat (FM gB gsB) μ) :
    GResp GrG q (gwindowSeg Formula.tt (leftBlock (fLB l)) domLB tgB dt 2)
      (fun qf => Formula.and (Formula.and (FM gB gsB) envB) (regionB qf)) σ := by
  refine gresp_of_rresp (fun ν hν => ?_)
  obtain ⟨μo, hμoL, hμoF⟩ := hold ν hν
  have hlo := (sat_FB μo).mp hμoF
  obtain ⟨-, hwin⟩ := gwindowSeg_runs hν
  have hR := window_right l hl dt hwin
  have hvL := windowSeg_coord_le_or_lt (fLB l) domLB tgB dt 0 3 (cstB l) (by norm_num)
    (by simp [Lv, Prod.ext_iff]) (fun s _ => fLB0_eval l hl s) 2 hwin
  have hrow := (sat_FB σ).mp hσ.1
  rw [gAt0_eval] at hrow
  have hdomLν : Formula.sat domLB ν :=
    windowSeg_end_domL (leftBlock (fLB l)) domLB tgB dt 2 (by norm_num) hwin
  have hdomRν : Formula.sat domRB ν := by
    refine (Formula.coincidence domRB (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRB hx
    exact (hR i).symm
  have hgν : Formula.sat (hostGuard vsB 12 Side.R (mRB q)) ν :=
    frames_right (vars_windowSegL_sub (fLB l) domLB 1 dt 2 (hfLB l hl) hdomLB)
      (hguardR_all q) hwin hguard
  have hcl := ladC_bounds l
  have hV : ν (Lv 0) < 13/20 ∨ ν (Lv 0) ≤ ν (Rv 0) := by
    rcases hvL with h | h
    · right; rw [hR 0]; linarith [hrow.1]
    · left; rw [cstB_eq] at h; linarith [hcl.2]
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domRB μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ν (Rv 0) ≤ μ (Rv 0) → ν (Lv 0) ≤ μ (Rv 0) →
      ν (Lv 1) - 1/5 ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM gB gsB) envB) (regionB 2)) μ := by
    intro μ hμL hμd _ hcap _ hv hs
    have hμL' : ∀ i, μ (Lv i) = μo (Lv i) := fun i => (hμL i).trans (hμoL i).symm
    refine ⟨⟨(sat_FB μ).mpr ?_, ?_, hμd⟩, ?_⟩
    · have hμL := hμL'
      refine ⟨by rw [gAt0_eval, hμL' 0, hμoL 0]; linarith,
        by rw [gAt1_eval, hμL' 1, hμoL 1]; linarith, ?_⟩
      exact ⟨by rw [gAt2_left μ μo hμL']; exact hlo.2.2.1, by rw [gAt3_left μ μo hμL']; exact hlo.2.2.2.1, by rw [gAt4_left μ μo hμL']; exact hlo.2.2.2.2⟩
    · refine (Formula.coincidence domLB (fun x hx => ?_)).mpr hdomLν
      obtain ⟨i, rfl⟩ := hdomLB hx
      exact hμL i
    · rw [sat_regionB]; simpa using hcap
  refine LR.climb q hq ν hdomRν ⟨?_, ?_, ?_⟩ _ _ hV hfin
  · rintro rfl; rw [sat_guardR0] at hgν; exact ⟨hgν.2.1, hgν.2.2⟩
  · rintro rfl; rw [sat_guardR1] at hgν; exact hgν
  · rintro rfl; rw [sat_guardR2] at hgν; exact hgν

/-! ## Theorem 3 over the guarded automaton -/

noncomputable def gregion (q : ℕ) : Formula (Var 12) :=
  regionG (fun q => hostGuard vsB 12 Side.R (mRB q)) regionB q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (regionB_fv q)

theorem hmvregG : ∀ q, mvB ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-- **`story3_rollover_base_12dof`, Theorem 3 over the GUARDED right automaton, at the mode-consistent
region.** The left: the file's three windows (two clocked pieces of at most `dt` each); the
right: the 12-DOF chain `STEEP → MODER → FLAT` of the file with every edge testing the entered
band's guard (`GrG_guards`). Loop invariant: the declared rows (`v_L ≤ v_R`,
`s_L ≤ s_R + 0.2` and the deployed-only conjuncts), both envelopes, the right in the guard of
its current band and under its cut ceiling (`mvRegionR` at `gregion`). Response: the ladder
climb with the attitude-weighted odometer; the deployed-only conjuncts are those the certified
relaxation's response keeps (the verdict packs `VerdB`, unchanged). -/
theorem story3_rollover_base_guarded (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdB 0 0) (hv01 : VerdB 0 1) (hv02 : VerdB 0 2)
    (hv11 : VerdB 1 1) (hv12 : VerdB 1 2) (hv22 : VerdB 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsB dt))
      (rightAutomatonBody GrG mvB)
      (RFormula.and (RFormula.and (canonInvM gB gsB) (envLR domLB domRB))
        (mvRegionR mvB gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvB (FM gB gsB) domLB domRB gregion
    (leftProgsB dt) (canonInvM gB gsB) (encode_canonInvM gB gsB) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgsB, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLB d hd).1
        (hLB d hd).2.1 (hLB d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub GrG _ hgRG hRvG hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · refine hstep_assembled_GR GrG mvB (FM gB gsB) envB gregion (leftProgsB dt)
      hmvFB hmvenvB hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesB dt) ?_
    refine Hmulti_regionG GrG mvB _ regionB GrG_guards (FM gB gsB) envB (leftProgsB dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsB, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLB d hd).1
        (hLB d hd).2.1 (hLB d hd).2.2) (hguardR_all q) hrun
    · intro P hP q hq σ hmv hσ hg hreg
      rw [GrG_len] at hq
      have hold : ∀ ν, Program.sem P σ ν → ∃ μ, (∀ i, μ (Lv i) = ν (Lv i)) ∧
          Formula.sat (FM gB gsB) μ := by
        intro ν hν
        obtain ⟨segs, halign, -, -, hfa⟩ := HmultiB dt hdt hv00 hv01 hv02 hv11 hv12 hv22 P hP q
          (by simpa [GrB] using hq) σ hmv hσ hreg
        rw [faModal_sat] at hfa
        obtain ⟨μ, hrun, hpost⟩ := hfa ν hν
        rw [Program.rename_refl] at hrun
        exact ⟨μ, bigSeq_odes_left GrB hRvB segs halign hrun, hpost.1.1⟩
      simp only [leftProgsB, leftDataB, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt q hq hσ hg hold
      · exact respondG 1 (by norm_num) dt q hq hσ hg hold
      · exact respondG 2 (by norm_num) dt q hq hσ hg hold
  · exact hddF_multiR_G GrG 0 1 dt leftDataB gregion (canonInvM gB gsB) domLB domRB
      (by decide) hgRG hRvG hLB (fun q _ => gregion_fv q)
      (canonInvM_varsL gB gsB (by
        intro g' hg'
        simp only [gB, gsB, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gB gsB) hdomLB hdomRB

end Story3RolloverBaseGuarded
end RelCertifier
