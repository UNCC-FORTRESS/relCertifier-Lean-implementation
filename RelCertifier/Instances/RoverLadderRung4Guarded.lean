/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_rung4_8to12` over the GUARDED right automaton — Theorem 3 by the ladder climb

`RoverLadderRung4Modal.rover_ladder_rung4_8to12_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT` with the bookkeeping `mvValid`. This file states it over the
GUARDED chain (every edge tests the lowered guard of the band it enters, `GrG_guards`) at the
mode-consistent region (the right in the guard of its current band; no cut is kept), with the
response of `Proofs/Encoding/LadderClimb.lean`: after the left window the reference climbs the
chain (explicit runs, each switch at the next band's floor, legal) and holds `FLAT` until
`v_L ≤ v_R` and `s_L ≤ s_R + 0.2`. Z3-free.
-/
import RelCertifier.Instances.RoverLadderRung4Modal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverLadderRung4Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung4Modal GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 12) :=
  { src := st, tgt := tgt, guard := hostGuard vsF 12 Side.R (mRF tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 12) :=
  { modes := [modeF 0, modeF 1, modeF 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range refinement_ladder_rover_rung4_8to12_IR.R.modes.length).flatMap (fun q =>
      (mRF q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung4_8to12_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range refinement_ladder_rover_rung4_8to12_IR.R.modes.length).flatMap (fun q =>
      (mRF q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung4_8to12_IR.R.modes.findIdx (·.name == nm))))
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
    simp [refinement_ladder_rover_rung4_8to12_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRF, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRF, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 12)) : Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRF, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsF, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
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
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsF 12 Side.R (mRF 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

/-! ## The guarded response to a left window -/

theorem fLF0_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fLF l 0) x = 3 * (cstF l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLF, hostDyn, mLF, refinement_ladder_rover_rung4_8to12_IR, vsF, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_1, gp_0_15, gp_0_2, gp_0_25, gp_0_3, gp_0_30, gp_0_35, gp_0_4, gp_0_5, gp_0_50, gp_0_6, gp_0_65, gp_0_7, gp_0_75, gp_0_8, gp_0_9, gp_1, gp_1_0, gp_1_1, gp_1_2, gp_1_4, gp_1_5, gp_1_6, gp_2, gp_2_0, gp_3, gp_4, gp_5, gp_10, gp_m0_5, gp_m0_25, gp_m1, gp_m1_0, gp_m2, gp_m0_3, gp_m0_6, gp_0_125, gp_1_125, gp_0_156, gp_0_33, gp_899_95, gp_m1_5, gp_1_52, gp_m1_52, gp_m3_04, gp_3_04, gp_m0_8, gp_0_05, gp_0_45, gp_0_55, gp_0_06,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Lv, cstF]

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 12)}
    (h : Program.sem (windowSeg (leftBlock (fLF l)) domLF tgF dt 2) σ ν) (i : Fin 12) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLF l) domLF 1 dt 2 (hfLF l hl) hdomLF
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

theorem gAt0_eval (x : State (Var 12)) : Term.eval (gAt 0) x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gAt, atomsOf, invFPF, refinement_ladder_rover_rung4_8to12_IR, Run.invToG,
    Run.lowerE, vsF, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt1_eval (x : State (Var 12)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invFPF, refinement_ladder_rover_rung4_8to12_IR, Run.invToG,
    Run.lowerE, vsF, gp_0_2, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem sat_FF (x : State (Var 12)) : Formula.sat (FM gF gsF) x ↔
    (x (Lv 0) - x (Rv 0) ≤ 0 ∧ x (Lv 1) - (x (Rv 1) + 1/5) ≤ 0) := by
  rw [sat_FM_iff]
  simp only [gF, gsF, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    gAt0_eval, gAt1_eval]

theorem sat_regionF (m : ℕ) (x : State (Var 12)) : Formula.sat (regionF m) x ↔
    x (Rv 0) ≤ (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20) := by
  simp [regionF, ceilF, Formula.sat, CompOp.interp, Term.eval, AOp.interp]

/-- **The guarded response** of left window `l` from right band `q` (in its guard): the
ladder climb, then hold `FLAT` until both rows hold; the final band is `FLAT`, whose ceiling
`v ≤ 0.65` the climb keeps. -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3) {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FM gF gsF) envF) σ)
    (hguard : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) σ) :
    GResp GrG q (gwindowSeg Formula.tt (leftBlock (fLF l)) domLF tgF dt 2)
      (fun qf => Formula.and (Formula.and (FM gF gsF) envF) (regionF qf)) σ := by
  refine gresp_of_rresp (fun ν hν => ?_)
  obtain ⟨-, hwin⟩ := gwindowSeg_runs hν
  have hR := window_right l hl dt hwin
  have hvL := windowSeg_coord_le_or_lt (fLF l) domLF tgF dt 0 3 (cstF l) (by norm_num)
    (by simp [Lv, Prod.ext_iff]) (fun s _ => fLF0_eval l hl s) 2 hwin
  have hrow := (sat_FF σ).mp hσ.1
  have hdomLν : Formula.sat domLF ν :=
    windowSeg_end_domL (leftBlock (fLF l)) domLF tgF dt 2 (by norm_num) hwin
  have hdomRν : Formula.sat domRF ν := by
    refine (Formula.coincidence domRF (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRF hx
    exact (hR i).symm
  have hgν : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) ν :=
    frames_right (vars_windowSegL_sub (fLF l) domLF 1 dt 2 (hfLF l hl) hdomLF)
      (hguardR_all q) hwin hguard
  have hcl := ladC_bounds l
  have hV : ν (Lv 0) < 13/20 ∨ ν (Lv 0) ≤ ν (Rv 0) := by
    rcases hvL with h | h
    · right; rw [hR 0]; linarith [hrow.1]
    · left; rw [cstF_eq] at h; linarith [hcl.2]
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domRF μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ν (Rv 0) ≤ μ (Rv 0) → ν (Lv 0) ≤ μ (Rv 0) →
      ν (Lv 1) - 1/5 ≤ μ (Rv 1) →
      Formula.sat (Formula.and (Formula.and (FM gF gsF) envF) (regionF 2)) μ := by
    intro μ hμL hμd _ hcap _ hv hs
    refine ⟨⟨(sat_FF μ).mpr ⟨by rw [hμL 0]; linarith, by rw [hμL 1]; linarith⟩, ?_, hμd⟩, ?_⟩
    · refine (Formula.coincidence domLF (fun x hx => ?_)).mpr hdomLν
      obtain ⟨i, rfl⟩ := hdomLF hx
      exact hμL i
    · rw [sat_regionF]; simpa using hcap
  refine LR.climb q hq ν hdomRν ⟨?_, ?_, ?_⟩ _ _ hV hfin
  · rintro rfl; rw [sat_guardR0] at hgν; exact ⟨hgν.2.1, hgν.2.2⟩
  · rintro rfl; rw [sat_guardR1] at hgν; exact hgν
  · rintro rfl; rw [sat_guardR2] at hgν; exact hgν

/-! ## Theorem 3 over the guarded automaton -/

noncomputable def gregion (q : ℕ) : Formula (Var 12) :=
  regionG (fun q => hostGuard vsF 12 Side.R (mRF q)) regionF q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (regionF_fv q)

theorem hmvregG : ∀ q, mvF ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-- **`refinement_ladder_rover_rung4_8to12`, Theorem 3 over the GUARDED right automaton, at
the mode-consistent region.** The left: the file's three windows (two clocked pieces of at most
`dt` each); the right: the 12-DOF chain `STEEP → MODER → FLAT` of the file with every edge
testing the entered band's guard (`GrG_guards`). Loop invariant: the declared rows
`v_L ≤ v_R ∧ s_L ≤ s_R + 0.2`, both envelopes, the right in the guard of its current band and
under its cut ceiling (`mvRegionR` at `gregion`). Response: the ladder climb with the
attitude-weighted odometer (`LadderRun.ofKappa`). Z3-free; every window length `dt`. -/
theorem rover_ladder_rung4_8to12_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsF dt))
      (rightAutomatonBody GrG mvF)
      (RFormula.and (RFormula.and (canonInvM gF gsF) (envLR domLF domRF))
        (mvRegionR mvF gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvF (FM gF gsF) domLF domRF gregion
    (leftProgsF dt) (canonInvM gF gsF) (encode_canonInvM gF gsF) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgsF, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLF d hd).1
        (hLF d hd).2.1 (hLF d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub GrG _ hgRG hRvG hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · refine hstep_assembled_GR GrG mvF (FM gF gsF) envF gregion (leftProgsF dt)
      hmvFF hmvenvF hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesF dt) ?_
    refine Hmulti_regionG GrG mvF _ regionF GrG_guards (FM gF gsF) envF (leftProgsF dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsF, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLF d hd).1
        (hLF d hd).2.1 (hLF d hd).2.2) (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsF, leftDataF, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt q hq hσ hg
      · exact respondG 1 (by norm_num) dt q hq hσ hg
      · exact respondG 2 (by norm_num) dt q hq hσ hg
  · exact hddF_multiR_G GrG 0 1 dt leftDataF gregion (canonInvM gF gsF) domLF domRF
      (by decide) hgRG hRvG hLF (fun q _ => gregion_fv q)
      (canonInvM_varsL gF gsF (by
        intro g' hg'
        simp only [gF, gsF, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gF gsF) hdomLF hdomRF

end RoverLadderRung4Guarded
end RelCertifier
