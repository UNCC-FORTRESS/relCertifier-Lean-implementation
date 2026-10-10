/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung4_8to12` over the GUARDED right automaton — Theorem 3 by
replaying the cover

`RoverLadderRung4Modal.rover_ladder_rung4_8to12_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT`. This file states it over the GUARDED chain (every edge tests the
lowered guard of the band it enters, `GrG_guards`) at the mode-consistent region (the right in
the guard of its current band and under its cut ceiling `v_R ≤ c_q`), against the gated left
windows (two clocked pieces; carried to the paper's left automaton in
`Instances/LeftAutLegacy.lean`), and proves it by REPLAYING THE EMITTED COVER
(`InstancesV2/BenchCovers/refinement_ladder_rover_rung4_8to12.lean`, λ = 17/10 for every
window): a band just below the window's (`dynPre`) repositions alone to the next floor,
preserved by the reposition pack `VerdD l q`; in the joint nodes (the bands at or above the
window's, `jointOK`) the right keeps time with the window at the cover's stretch `17/10`,
switching up at each floor it reaches, every stretch preserved by the joint pack `Verd l q`;
the `FLAT` window from `STEEP` is inadmissible. Every switch is legal against the entered
band's guard; the explicit band runs (`LR`, the attitude-weighted odometer) supply only the
existence of the right's runs. Hypotheses: six joint packs and two reposition packs
(`modalVerdX`, `modalVerdDynX`).
-/
import RelCertifier.Instances.RoverLadderRung4Modal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayBridge
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung4_8to12

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverLadderRung4Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung4Modal GPins RelCertifier.Oracle

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

theorem sat_regionF (m : ℕ) (x : State (Var 12)) : Formula.sat (regionF m) x ↔
    x (Rv 0) ≤ (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20) := by
  simp [regionF, ceilF, Formula.sat, CompOp.interp, Term.eval, AOp.interp]

noncomputable def gregion (q : ℕ) : Formula (Var 12) :=
  regionG (fun q => hostGuard vsF 12 Side.R (mRF q)) regionF q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (regionF_fv q)

theorem hmvregG : ∀ q, mvF ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aV (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
def vStr (q : ℕ) : String := if q = 0 then "0.3" else if q = 1 then "0.5" else "0.65"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 12) :=
  cutPairsX vsF 12 Side.L (cutAtomsOfX refinement_ladder_rover_rung4_8to12_cutsV2X.L (mLF l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 12) :=
  cutPairsX vsF 12 Side.R (cutAtomsOfX refinement_ladder_rover_rung4_8to12_cutsV2X.R (mRF q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsF 12 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsF,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsF 12 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsF,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]
theorem gR_v (q : ℕ) (hq : q < 3) : hostAtomG vsF 12 Side.R (aV (vStr q)) = thrLe (Rv 0) (ladC q) := by
  interval_cases q <;>
  simp [aV, vStr, ladC, hostAtomG, cutAtomG, Run.lowerE, gp_0_3, gp_0_5, gp_0_65, vsF,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vsF 12 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))] := by
  rw [← gL_s l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsF 12 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q)),
      (hostAtomF vsF 12 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))] := by
  rw [← gR_s q hq, ← gR_v q hq]; interval_cases q <;> rfl

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
  rcases ha with rfl | rfl
  · rw [← gR_s q hq]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gR_v q hq]; exact hostAtom_iff (Or.inl rfl) ν

theorem cutSatL_s (l : ℕ) (hl : l < 3) (ν : State (Var 12)) (h : CutSat (cL l) ν) :
    sK l ≤ ν (Lv 1) := by
  have h1 := hiffL l hl (hostAtomF vsF 12 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))
    (by rw [cL_eq l hl]; simp) ν
  simp only [thrGe, Term.eval, AOp.interp] at h1
  have := h1.mp (h (hostAtomF vsF 12 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))
    (by rw [cL_eq l hl]; simp))
  linarith

/-! ## O1: guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vsF 12 Side.L (mLF l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard refinement_ladder_rover_rung4_8to12_cutsV2X_wf (mLF l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung4_8to12_cutsV2X, mLF,
        refinement_ladder_rover_rung4_8to12_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung4_8to12_cutsV2X, mLF,
        refinement_ladder_rover_rung4_8to12_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsF,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mLF, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
        gp_1_4, gp_0_3, gp_0_5, gp_0_65, gp_899_95, vsF, Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vsF 12 Side.R (mRF q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard refinement_ladder_rover_rung4_8to12_cutsV2X_wf (mRF q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung4_8to12_cutsV2X, mRF,
        refinement_ladder_rover_rung4_8to12_IR] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung4_8to12_cutsV2X, mRF,
        refinement_ladder_rover_rung4_8to12_IR] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsF,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRF, refinement_ladder_rover_rung4_8to12_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
        gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsF, Run.resolveVar, List.findIdx?_cons]

/-! ## The fields and envelopes the atoms' staying needs -/

theorem fLF0_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fLF l 0) x = 3 * (cstF l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLF, hostDyn, mLF, refinement_ladder_rover_rung4_8to12_IR, vsF, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_1, gp_0_15, gp_0_2, gp_0_25, gp_0_3, gp_0_30, gp_0_35, gp_0_4, gp_0_5, gp_0_50, gp_0_6, gp_0_65, gp_0_7, gp_0_75, gp_0_8, gp_0_9, gp_1, gp_1_0, gp_1_1, gp_1_2, gp_1_4, gp_1_5, gp_1_6, gp_2, gp_2_0, gp_3, gp_4, gp_5, gp_10, gp_m0_5, gp_m0_25, gp_m1, gp_m1_0, gp_m2, gp_m0_3, gp_m0_6, gp_m0_4, gp_899_95, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv, cstF]

theorem fLF1_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fLF l 1) x =
      x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 4) * x (Lv 4))) := by
  interval_cases l <;>
    simp [fLF, hostDyn, mLF, refinement_ladder_rover_rung4_8to12_IR, vsF, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_1, gp_0_15, gp_0_2, gp_0_25, gp_0_3, gp_0_30, gp_0_35, gp_0_4, gp_0_5, gp_0_50, gp_0_6, gp_0_65, gp_0_7, gp_0_75, gp_0_8, gp_0_9, gp_1, gp_1_0, gp_1_1, gp_1_2, gp_1_4, gp_1_5, gp_1_6, gp_2, gp_2_0, gp_3, gp_4, gp_5, gp_10, gp_m0_5, gp_m0_25, gp_m1, gp_m1_0, gp_m2, gp_m0_3, gp_m0_6, gp_m0_4, gp_899_95, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]

theorem gp4_1000_0 : Run.parseRat "1000.0" = some (1000:ℚ) := by
  have h : parseQ "1000.0" = some (⟨10000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem domL_bnd (z : State (Var 12)) (hz : Formula.sat domLF z) :
    0 ≤ z (Lv 0) ∧ -(3:ℝ)/5 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 3/5 ∧ -(3:ℝ)/5 ≤ z (Lv 4) ∧
      z (Lv 4) ≤ 3/5 := by
  simp only [domLF, hostEvolve, mLF, refinement_ladder_rover_rung4_8to12_IR, vsF] at hz
  simp [Run.lowerF, Run.lowerE, gp_0, gp_0_0, gp_0_1, gp_0_15, gp_0_2, gp_0_25, gp_0_3, gp_0_30, gp_0_35, gp_0_4, gp_0_5, gp_0_50, gp_0_6, gp_0_65, gp_0_7, gp_0_75, gp_0_8, gp_0_9, gp_1, gp_1_0, gp_1_1, gp_1_2, gp_1_4, gp_1_5, gp_1_6, gp_2, gp_2_0, gp_3, gp_4, gp_5, gp_10, gp_m0_5, gp_m0_25, gp_m1, gp_m1_0, gp_m2, gp_m0_3, gp_m0_6, gp_m0_4, gp_899_95, gp4_1000_0, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]
    at hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 12)) (hz : Formula.sat domLF z) :
    0 ≤ Term.eval (fLF l 1) z := by
  rw [fLF1_eval l hl]
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
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
      (fun z hz _ => sdotR_nonneg q hq z (hD z hz)) hinit
  · exact boxle_thrLe_R 0 (ladC q) _ _ c hc D D (fun x h => h)
      (fun z hz hK => by rw [fRF0_eval q hq, cstF_eq]; linarith) hinit

/-! ## The invariant's components, as the tool lowers them: the statement's own rows -/

theorem atoms_eq : atomsOf invFPF = pAtoms invFPF := by decide

theorem comps_eq : hostComps vsF 12
    (refinement_ladder_rover_rung4_8to12_IRv2.invariants.getD 0 ("", PForm.tt)).2 = gF :: gsF := by
  have hrow : (refinement_ladder_rover_rung4_8to12_IRv2.invariants.getD 0 ("", PForm.tt)).2
      = invFPF := rfl
  have hlist : pAtoms invFPF = [(atomsOf invFPF).getD 0 .tt, (atomsOf invFPF).getD 1 .tt] := by
    decide
  rw [hrow, hostComps_atoms vsF invFPF ?_, hlist]
  · rfl
  · rw [hlist]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hdv : ("L_v".drop 2).copy = "v" ∧ ("R_v".drop 2).copy = "v" := by decide
    have hds : ("L_s".drop 2).copy = "s" ∧ ("R_s".drop 2).copy = "s" := by decide
    have hdp : ("L_psi".drop 2).copy = "psi" ∧ ("R_psi".drop 2).copy = "psi" ∧
        ("L_omega_psi".drop 2).copy = "omega_psi" := by decide
    have hdt : ("L_theta_p".drop 2).copy = "theta_p" ∧ ("R_theta_p".drop 2).copy = "theta_p" ∧
        ("L_omega_theta".drop 2).copy = "omega_theta" := by decide
    rcases ha with rfl | rfl <;>
      exact ⟨⟨_, _, _, rfl⟩, by
        simp [atomsOf, invFPF, refinement_ladder_rover_rung4_8to12_IR, Run.invToG, Run.lowerE,
          vsF, gp_3, gp_0_2, Run.resolveVar, Parse.dr, hdv, hds, hdp, hdt,
          List.findIdx?_cons]⟩

theorem comps_fv : ∀ c ∈ gF :: gsF, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [gF, gsF, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact hgAt _

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 17/10, strata `[0, 1]`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX refinement_ladder_rover_rung4_8to12_IRv2 refinement_ladder_rover_rung4_8to12_cutsV2X 12 0
    [0, 1] (17/10) l q

/-- The pre-joint reposition pack of window `l` at right mode `q` (`dynPreOrder = [0, 1]`). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX refinement_ladder_rover_rung4_8to12_IRv2 refinement_ladder_rover_rung4_8to12_cutsV2X
    12 0 [0, 1] true l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsF 12 Side.L (mLF l) = domLF := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vsF 12 Side.R (mRF q) = domRF := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (gF :: gsF) (fLF l) (fRF q) (17/10)
      (domCutX (Formula.and domLF domRF) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdXCore (([0, 1] : List ℕ).map (fun i => (hostComps vsF 12
      (refinement_ladder_rover_rung4_8to12_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i
        (Term.const 0)))
    (fLF l) (fRF q) ((17/10 : ℝ)) (domCutX (Formula.and (hostEvolve vsF 12 Side.L (mLF l))
      (hostEvolve vsF 12 Side.R (mRF q))) (cL l) (cR q)) at h'
  rw [hc] at h'
  simpa [gsF] using h'

theorem verdD_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : VerdD l q) :
    VerdDynCore true (gF :: gsF) (fRF q)
      (domCutX (Formula.and domLF domRF) (cL l) (cR q)) (hostGuard vsF 12 Side.L (mLF l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdDynCore true (([0, 1] : List ℕ).map (fun i => (hostComps vsF 12
      (refinement_ladder_rover_rung4_8to12_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i
        (Term.const 0)))
    (fRF q) (domCutX (Formula.and (hostEvolve vsF 12 Side.L (mLF l))
      (hostEvolve vsF 12 Side.R (mRF q))) (cL l) (cR q)) (hostGuard vsF 12 Side.L (mLF l)) at h'
  rw [hc] at h'
  simpa [gsF] using h'

/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mRF q = dummyF :=
    List.getD_eq_default _ _ (by simp [refinement_ladder_rover_rung4_8to12_IR]; omega)
  simp only [cR, this]
  rfl

noncomputable def anc (l q : ℕ) : Formula (Var 12) := FM gF (gsF ++ atomTerms (cL l) (cR q))

theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vsF 12 Side.L (mLF l)).fv ⊆ range Lv :=
  hostGuard_fv_L vsF (mLF l) (by interval_cases l <;> decide)

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
    rcases ha with rfl | rfl <;>
    · intro x hx; simp [thrGe, thrLe, Term.fv] at hx; subst hx; simp
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
      Program.sem (Program.ode (jointSys (fLF l) (fRF q) (Term.const (17/10)))
        (Formula.and domLF domRF)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX gF gsF (gF :: gsF) (cL l) (cR q) (fLF l) (fRF q) (17/10) domLF domRF
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl _)
    (stayR_gen q hq (fLF l) (17/10) (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_boxD (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vsF 12 Side.L (mLF l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fRF q) (Term.const 1))
        (Formula.and domLF domRF)) σ ω → Formula.sat (anc l q) ω := by
  intro σ ω h1 h2 h3
  exact couple_box_dyn true gF gsF (gF :: gsF) (cL l) (cR q) (fRF q) domLF domRF
    (hostGuard vsF 12 Side.L (mLF l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fv l hl) (hguardL l hl)
    (stayR_gen q hq _ 1 (by norm_num) _ (fun z hz => by
      simp only [dynBase, if_true] at hz; exact hz.1.2))
    (verdD_core l q hl hq hv) σ ω h1 (fun _ => h2) h3

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vsF 12 Side.R (mRF e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

/-! ## The ladder's switching choreography and the cover's node sets -/

abbrev Cap (q : ℕ) (x : State (Var 12)) : Prop := x (Rv 0) ≤ ladC q

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 12))
    (hg : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) x) (hd : Formula.sat domRF x) :
    ladPre Cap domRF q x := by
  refine ⟨hq, ?_, ?_, hd⟩
  · interval_cases q
    · rw [sat_guardR0] at hg
      exact ⟨fun _ => ⟨hg.1, hg.2.1⟩, fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · rw [sat_guardR1] at hg
      exact ⟨fun h => absurd h (by norm_num), fun _ => ⟨hg.1, hg.2.1⟩, fun h => absurd h (by norm_num)⟩
    · rw [sat_guardR2] at hg
      exact ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ => hg.1⟩
  · interval_cases q
    · rw [sat_guardR0] at hg; simp only [Cap, ladC]; norm_num; exact hg.2.2
    · rw [sat_guardR1] at hg; simp only [Cap, ladC]; norm_num; exact hg.2.2
    · rw [sat_guardR2] at hg; simp only [Cap, ladC]; norm_num; exact hg.2

theorem ladPre_R (q : ℕ) (x y : State (Var 12)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : ladPre Cap domRF q x) : ladPre Cap domRF q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, hc, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · show y (Rv 0) ≤ ladC q; rw [← hxy 0]; exact hc
  · refine (Formula.coincidence domRF (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRF hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 12), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsF 12 Side.R (mRF 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩
theorem leg11 : ∀ x : State (Var 12), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsF 12 Side.R (mRF 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩

def J (l q : ℕ) : Prop := l ≤ q ∧ q < 3
def D (l q : ℕ) : Prop := q + 1 = l

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 12) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domRF q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domRF) E :=
  ladder_hmove LR Cap (ladCap_run LR) ladCap_up (edgeG 0 0) (edgeG 1 1)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc)) leg11
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg22 x hs (by simpa [Cap, ladC] using hc))
    (J l) (fun q hJ hq2 => ⟨by have := hJ.1; omega, by omega⟩) E hE

theorem hexitR (l : ℕ) (hl : l < 3) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domRF) (ladPre Cap domRF) :=
  ladder_hexit LR Cap (ladCap_run LR) ladCap_up
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc)) (J l) (D l)
    (fun q hD hnJ => by
      unfold D at hD; unfold J at hnJ ⊢
      refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩)

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 12)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM gF gsF) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem gAt1_eval (x : State (Var 12)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invFPF, refinement_ladder_rover_rung4_8to12_IR, Run.invToG,
    Run.lowerE, vsF, gp_0_2, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 3) {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FM gF gsF) envF) σ)
    (hg : Formula.sat (hostGuard vsF 12 Side.R (mRF q)) σ) :
    GResp GrG q (gwindowSeg (hostGuard vsF 12 Side.L (mLF l)) (leftBlock (fLF l)) domLF tgF dt
      (1 + 1)) (fun qf => Formula.and (Formula.and (FM gF gsF) envF)
        (regionF qf)) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · unfold D at h; omega
  refine replay_gresp GrG LR.m fRF domRF (fLF l) domLF (hostGuard vsF 12 Side.L (mLF l)) aF
    hgRG (hfLF l hl) hdomLF hdomRF (hguardL l hl) (17/10) (by norm_num) (J l) (D l)
    (fun q h => hfRF q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h.2)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.2 (hJv q h))
    (fun q h => anc_boxD l q hl (by unfold D at h; omega) (hDv q h))
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domRF) (ladPre Cap domRF) (ladPre Cap domRF) ladPre_R ladPre_R
    (hmoveR l _ (fun _ _ _ h => h)) (fun _ _ => hmoveR l _ (fun _ _ hJ h => ⟨hJ, h⟩))
    (hexitR l hl) dt 1 q σ ?_ hσ.2.1 _ ?_
  · intro hgL
    have hpre := pre_of_guard q hq σ hg hσ.2.2
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    by_cases hlq : l ≤ q
    · exact Or.inl ⟨⟨hlq, hq⟩, hpre⟩
    · by_cases hD : q + 1 = l
      · exact Or.inr ⟨hD, fun h => hlq h.1, hpre⟩
      · exfalso
        have hl2 : l = 2 := by omega
        have hq0 : q = 0 := by omega
        subst hl2 hq0
        have hsL := cutSatL_s 2 (by norm_num) σ (hO1L 2 (by norm_num) σ hgL)
        rw [sat_guardR0] at hg
        have hrow := (sat_FM_iff gF gsF σ).mp hσ.1 (gAt 1) (by simp [gsF])
        rw [gAt1_eval] at hrow
        simp [sK] at hsL
        linarith [hg.2.1]
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLF ν :=
      windowSeg_end_domL (leftBlock (fLF l)) domLF tgF dt (1 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FM gF gsF) μ := by
      refine (sat_of_agree (fun x hx => ?_) (fun i => ?_) (fun i => ?_)).mp hA'
      · by_contra hS
        exact notMem_FM_fv (fun g' hg' hxg => hS (comps_fv g' hg' hxg)) hx
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hpre.2.2.2⟩, ?_⟩
    · refine (Formula.coincidence domLF (fun v hv => ?_)).mpr hdomLν
      obtain ⟨i, rfl⟩ := hdomLF hv
      exact hμL i
    · rw [sat_regionF]
      have hc := hpre.2.2.1
      simp only [Cap, ladC] at hc
      exact hc

/-! ## Theorem 3 over the gated windows, by replaying the cover -/

noncomputable def guardsL : List (Formula (Var 12)) :=
  (List.range 3).map (fun l => hostGuard vsF 12 Side.L (mLF l))

noncomputable def leftDataG : List (Formula (Var 12) × (Fin 12 → Term (Var 12)) × Formula (Var 12) × ℕ) :=
  gatedDataGI guardsL leftDataF

theorem leftDataG_eq : leftDataG =
    [(hostGuard vsF 12 Side.L (mLF 0), fLF 0, domLF, 2),
     (hostGuard vsF 12 Side.L (mLF 1), fLF 1, domLF, 2),
     (hostGuard vsF 12 Side.L (mLF 2), fLF 2, domLF, 2)] := rfl

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 12)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tgF dt d.2.2.2)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
    d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  rw [leftDataG_eq] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfLF 0 (by norm_num), hdomLF⟩
  · exact ⟨hguardL 1 (by norm_num), hfLF 1 (by norm_num), hdomLF⟩
  · exact ⟨hguardL 2 (by norm_num), hfLF 2 (by norm_num), hdomLF⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mvF := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tgF dt d.2.2.2 mvF (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-- **`refinement_ladder_rover_rung4_8to12`, Theorem 3 by replaying the emitted cover** (over
the gated two-piece windows; carried to the paper's left automaton by
`theorem3_leftAut_of_choiceR`). The right answers window `l` from band `q` as the cover's
derivation does: a band just below the window's (`dynPre`) repositions alone to the next
floor (`VerdD l q`), then the right keeps time with the window at the cover's λ = 17/10 in the
joint nodes (the bands at or above the window's), switching up at each floor it reaches,
every stretch preserved by its joint pack `Verd l q`; every switch is legal against the
entered band's guard; the `FLAT` window from `STEEP` is inadmissible. -/
theorem rover_ladder_rung4_8to12_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mvF)
      (RFormula.and (RFormula.and (canonInvM gF gsF) (envLR domLF domRF))
        (mvRegionR mvF gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvF (FM gF gsF) domLF domRF gregion
    (leftProgsG dt) (canonInvM gF gsF) (encode_canonInvM gF gsF) ?_ ?_ ?_
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
  · refine hstep_assembled_GR GrG mvF (FM gF gsF) envF gregion
      (leftProgsG dt) hmvFF hmvenvF hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG
      (hframesG dt) ?_
    refine Hmulti_regionG GrG mvF _ regionF GrG_guards (FM gF gsF) envF
      (leftProgsG dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsG, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLG d hd).1
        (hLG d hd).2.1 (hLG d hd).2.2) (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsG, leftDataG_eq, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · refine respondR 0 (by norm_num) dt (fun q h => ?_) (fun q h => ?_) q hq hσ hg
        · obtain ⟨-, h3⟩ := h
          interval_cases q
          · exact h00
          · exact h01
          · exact h02
        · unfold D at h; omega
      · refine respondR 1 (by norm_num) dt (fun q h => ?_) (fun q h => ?_) q hq hσ hg
        · obtain ⟨h1, h3⟩ := h
          interval_cases q
          · exact h11
          · exact h12
        · unfold D at h
          have : q = 0 := by omega
          subst this; exact d10
      · refine respondR 2 (by norm_num) dt (fun q h => ?_) (fun q h => ?_) q hq hσ hg
        · obtain ⟨h1, h3⟩ := h
          interval_cases q
          exact h22
        · unfold D at h
          have : q = 1 := by omega
          subst this; exact d21
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM gF gsF) domLF domRF
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL gF gsF comps_fv)
      (canonInvM_varsR gF gsF) hdomLF hdomRF

end RoverLadderRung4Guarded
end RelCertifier
