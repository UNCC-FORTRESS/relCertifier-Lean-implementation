/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung3_6to8` over the GUARDED right automaton — Theorem 3 by a climb
with a decay budget

`RoverLadderRung3Modal.rover_ladder_rung3_6to8_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT`. This file states it over the GUARDED chain (every edge tests the
lowered guard of the band it enters, `GrG_guards`) at the mode-consistent region (the right in
the guard of its current band and under its cut ceiling `v_R ≤ c_q`).

Rows: `v_L ≤ v_R`, `s_L ≤ s_R + 0.2`, and two attitude rows
`ψ_R² ≤ ψ_L² + 3 (ω_ψL − ψ_L)²` (and `θ` alike). The response is the ladder climb of
`Proofs/Encoding/LadderClimb.lean` with a decay budget (`LadderRun.climbD`): the reference's
`ψ_R`, `θ_R` decay as `e^{−t}` in every band, and the climb holds `FLAT` for at least
`Dmin = (27/4) dt` more. On the deployed side the attitude form
`Q = ψ² + 3 (ω − ψ)²` satisfies `Q' + (9/2) Q ≥ 0` along every left band
(`Q' + (9/2) Q = (9/2) a² − 4 a b + (3/2) b²` with `a = ψ`, `b = ω − ψ`, positive definite), so
over a window of three clocked pieces `Q` keeps at least `e^{−(27/2) dt}` of its start value
(`windowQ`). Together: `ψ_R²` ends at most `e^{−2 Dmin}` times its start, which the row bounds by
`Q_L` at the start, at most `Q_L` at the end. Z3-free; every window length `dt`.
-/
import RelCertifier.Instances.RoverLadderRung3Modal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverLadderRung3Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung3Modal GPins

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := hostGuard vsR 8 Side.R (mRR tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 8) :=
  { modes := [modeR 0, modeR 1, modeR 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range refinement_ladder_rover_rung3_6to8_IR.R.modes.length).flatMap (fun q =>
      (mRR q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung3_6to8_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range refinement_ladder_rover_rung3_6to8_IR.R.modes.length).flatMap (fun q =>
      (mRR q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung3_6to8_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsR 8 Side.R (mRR e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeR q) := by
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
  have hm' : m = modeR q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvR q (modeR q) (GrR_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvR ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsR 8 Side.R (mRR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsR _ dummyR rfl (by
    simp [refinement_ladder_rover_rung3_6to8_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 8)) : Formula.sat (hostGuard vsR 8 Side.R (mRR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRR, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, gp_0_0,
    gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsR, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 8)) : Formula.sat (hostGuard vsR 8 Side.R (mRR 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRR, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, gp_0_0,
    gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsR, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 8)) : Formula.sat (hostGuard vsR 8 Side.R (mRR 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRR, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, gp_0_0,
    gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsR, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The ladder run (explicit: `v` on its exponential law, the odometer integrating
`v · (1 − ψ²/2 − 0.3 θ²)`, `ψ, θ, z, φ` decaying `e^{−t}`, the rates frozen) -/

theorem cstR_eq (q : ℕ) : cstR q = ladC q := rfl

noncomputable def dR : Fin 8 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 1]

noncomputable def φo (ρ : State (Var 8)) (i : Fin 8) (t : ℝ) : ℝ :=
  ρ (Rv i) * Real.exp (-(dR i * t))

/-- The odometer factor along the run, `1 − ψ²/2 − 0.3 θ²`. -/
noncomputable def kapT (ρ : State (Var 8)) (t : ℝ) : ℝ :=
  1 - 1/2 * (φo ρ 2 t * φo ρ 2 t) - 3/10 * (φo ρ 4 t * φo ρ 4 t)

theorem φo_bounds (ρ : State (Var 8)) (hρ : Formula.sat domRR ρ) {t : ℝ} (ht : 0 ≤ t) :
    (-(1/2:ℝ) ≤ φo ρ 2 t ∧ φo ρ 2 t ≤ 3/20) ∧ (-(1/2:ℝ) ≤ φo ρ 4 t ∧ φo ρ 4 t ≤ 3/20) := by
  have hD := (sat_domRR ρ).mp hρ
  obtain ⟨_, _, _, _, _, _, h2l, h2h, _, h4l, h4h, _⟩ := hD
  have b2 := decay_between (ρ (Rv 2)) (dR 2) t (by simp [dR]) ht
  have b4 := decay_between (ρ (Rv 4)) (dR 4) t (by simp [dR]) ht
  simp only [φo]
  refine ⟨⟨le_trans (le_min (by linarith) (by norm_num)) b2.1,
      le_trans b2.2 (max_le h2h (by norm_num))⟩,
    ⟨le_trans (le_min (by linarith) (by norm_num)) b4.1,
      le_trans b4.2 (max_le h4h (by norm_num))⟩⟩

theorem kapT_cont (ρ : State (Var 8)) : Continuous (kapT ρ) := by
  unfold kapT φo; fun_prop

theorem kapT_low (ρ : State (Var 8)) (hρ : Formula.sat domRR ρ) {t : ℝ} (ht : 0 ≤ t) :
    7/10 ≤ kapT ρ t := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h4l, h4h⟩⟩ := φo_bounds ρ hρ ht
  unfold kapT
  nlinarith

theorem hfoR (q : ℕ) (hq : q < 3) (ρ : State (Var 8)) (i : Fin 8) (h0 : i ≠ 0) (h1 : i ≠ 1)
    (t : ℝ) : HasDerivAt (φo ρ i) (Term.eval (fRR q i) (trajR ρ (phiK φo kapT q ρ) t)) t := by
  have hf : φo ρ i = fun u => ρ (Rv i) * Real.exp (-(dR i * u)) := rfl
  have hd := hasDerivAt_decay (ρ (Rv i)) (dR i) t
  rw [hf]
  convert hd using 1
  fin_cases i
  · exact absurd rfl h0
  · exact absurd rfl h1
  all_goals
    simp only [Fin.reduceFinMk, Fin.isValue]
    first
      | (rw [fRR2_eval q hq]) | (rw [fRR3_eval q hq]) | (rw [fRR4_eval q hq])
      | (rw [fRR5_eval q hq]) | (rw [fRR6_eval q hq]) | (rw [fRR7_eval q hq])
    simp [trajR_R, phiK, φo, dR]

noncomputable def LR : LadderRun GrG domRR :=
  LadderRun.ofKappa GrG domRR modeR fRR φo kapT (7/10) (by norm_num) GrG_modeAt
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRR0_eval q hq, cstR_eq])
    (fun ρ i _ _ => by simp [φo])
    (fun q hq ρ _ i h0 h1 t _ => hfoR q hq ρ i h0 h1 t)
    (fun q hq ρ _ t _ => by
      rw [fRR1_eval q hq, trajR_R, trajR_R, trajR_R, phiK_v,
        phiK_other _ _ q ρ 2 (by decide) (by decide), phiK_other _ _ q ρ 4 (by decide) (by decide)]
      simp only [kapT])
    kapT_cont
    (fun ρ hρ t ht => kapT_low ρ hρ ht)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRR ρ).mp hρ
      have hv : min (ρ (Rv 0)) (ladC q) ≤ phiK φo kapT q ρ 0 t ∧
          phiK φo kapT q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
        rw [phiK_v]; exact vLaw_between q ρ ht
      have hc := ladC_bounds q
      have hs : ρ (Rv 1) ≤ phiK φo kapT q ρ 1 t := by
        rw [phiK_s]
        have h := integral_vk_low q ρ (kapT ρ) (kapT_cont ρ) (7/10) (by norm_num) hD.2.2.2.2.2.2.2.2.2.2.2.1 ht
          (fun u hu _ => kapT_low ρ hρ hu)
        linarith [h.2]
      have hk : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) 0 ≤ phiK φo kapT q ρ k t ∧ phiK φo kapT q ρ k t ≤ max (ρ (Rv k)) 0 :=
        fun k h0 h1 => by
          rw [phiK_other φo kapT q ρ k h0 h1]
          exact decay_between _ _ t (by fin_cases k <;> simp [dR]) ht
      obtain ⟨h3l, h3h, h5l, h5h, h7l, h7h, h2l, h2h, h1l, h4l, h4h, h0l, h0h, h6l, h6h⟩ := hD
      rw [sat_domRR]
      simp only [trajR_R]
      exact ⟨le_trans (le_min h3l (by norm_num)) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le h3h (by norm_num)),
        le_trans (le_min h5l (by norm_num)) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le h5h (by norm_num)),
        le_trans (le_min h7l (by norm_num)) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le h7h (by norm_num)),
        le_trans (le_min h2l (by norm_num)) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le h2h (by norm_num)),
        le_trans h1l hs,
        le_trans (le_min h4l (by norm_num)) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le h4h (by norm_num)),
        le_trans (le_min h0l (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le h0h (by linarith [hc.2])),
        le_trans (le_min h6l (by norm_num)) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le h6h (by norm_num))⟩)
    (fun ρ hρ => by have hD := (sat_domRR ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsR 8 Side.R (mRR 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsR 8 Side.R (mRR 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsR 8 Side.R (mRR 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

/-- The reference's attitude coordinates decay as `e^{−t}` along every band. -/
theorem LR_dec : ∀ q < 3, ∀ ρ τ, 0 ≤ τ → ∀ i : Fin 8, (i = 2 ∨ i = 4) →
    |LR.run q ρ τ (Rv i)| ≤ |ρ (Rv i)| * Real.exp (-τ) := by
  intro q _ ρ τ _ i hi
  have hrun : LR.run q ρ τ (Rv i) = ρ (Rv i) * Real.exp (-τ) := by
    show trajR ρ (phiK φo kapT q ρ) τ (Rv i) = _
    rcases hi with rfl | rfl
    · rw [trajR_R, phiK_other φo kapT q ρ 2 (by decide) (by decide)]; simp [φo, dR]
    · rw [trajR_R, phiK_other φo kapT q ρ 4 (by decide) (by decide)]; simp [φo, dR]
  rw [hrun, abs_mul, abs_of_pos (Real.exp_pos _)]

/-! ## The deployed attitude form across a window -/

theorem fLR_eval_att (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLR l 2) x = x (Lv 3) - x (Lv 2) ∧ Term.eval (fLR l 3) x = -1 * x (Lv 3) ∧
    Term.eval (fLR l 4) x = x (Lv 5) - x (Lv 4) ∧ Term.eval (fLR l 5) x = -1 * x (Lv 5) := by
  interval_cases l <;>
    simp [fLR, hostDyn, mLR, refinement_ladder_rover_rung3_6to8_IR, vsR, Run.dynOf,
      Run.lowerE, hr030, hr050, hr065, hr3, hrm1, hr0, hr1, hr05, hr03, hrm05, hr06, hr015, hr00,
      hr08, hrm10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]

theorem fLR0_eval (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLR l 0) x = 3 * (cstR l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLR, hostDyn, mLR, refinement_ladder_rover_rung3_6to8_IR, vsR, Run.dynOf,
      Run.lowerE, hr030, hr050, hr065, hr3, hrm1, hr0, hr1, hr05, hr03, hrm05, hr06, hr015, hr00,
      hr08, hrm10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv, cstR]

/-- The deployed attitude form of the pair `(a, b)` (angle, rate): `ψ² + 3 (ω − ψ)²`. -/
noncomputable def QL (a b : Fin 8) (x : State (Var 8)) : ℝ :=
  x (Lv a) * x (Lv a) + 3 * ((x (Lv b) - x (Lv a)) * (x (Lv b) - x (Lv a)))

theorem QL_nonneg (a b : Fin 8) (x : State (Var 8)) : 0 ≤ QL a b x := by
  unfold QL; nlinarith [mul_self_nonneg (x (Lv a)), mul_self_nonneg (x (Lv b) - x (Lv a))]

/-- **One clocked piece**: `Q` keeps at least `e^{−(9/2) dt}` of its start value
(`Q' + (9/2) Q ≥ 0` along the deployed's `ψ' = ω − ψ`, `ω' = −ω`). -/
theorem QL_piece (l : ℕ) (a b : Fin 8) (dt : ℝ)
    (hfa : ∀ x, Term.eval (fLR l a) x = x (Lv b) - x (Lv a))
    (hfb : ∀ x, Term.eval (fLR l b) x = -1 * x (Lv b))
    {σ ν : State (Var 8)} (h : Program.sem (clockedSeg (leftBlock (fLR l)) domLR tgR dt) σ ν) :
    Real.exp (-(9/2 * dt)) * QL a b σ ≤ QL a b ν := by
  obtain ⟨r, Φ, H, hΦr, hrdt⟩ := clockedSeg_sol h
  have hmem : ∀ j : Fin 8, ((Lv j : Var 8), fLR l j) ∈ clk tgR (leftBlock (fLR l)) := by
    intro j
    simp only [clk, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hA : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt (fun u => Φ u (Lv a))
      (Φ t (Lv b) - Φ t (Lv a)) (Icc 0 r) t := by
    intro t ht
    have := H.hder t ht _ (hmem a)
    rwa [hfa] at this
  have hB : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt (fun u => Φ u (Lv b))
      (-1 * Φ t (Lv b)) (Icc 0 r) t := by
    intro t ht
    have := H.hder t ht _ (hmem b)
    rwa [hfb] at this
  set F : ℝ → ℝ := fun u => QL a b (Φ u) * Real.exp (9/2 * u) with hF
  set F' : ℝ → ℝ := fun t =>
    (2 * Φ t (Lv a) * (Φ t (Lv b) - Φ t (Lv a)) +
      6 * (Φ t (Lv b) - Φ t (Lv a)) * (-1 * Φ t (Lv b) - (Φ t (Lv b) - Φ t (Lv a)))) *
        Real.exp (9/2 * t) + QL a b (Φ t) * (Real.exp (9/2 * t) * (9/2)) with hF'
  have hFd : ∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt F (F' t) (Icc 0 r) t := by
    intro t ht
    have hAt := hA t ht
    have hBt := hB t ht
    have hD := hBt.sub hAt
    have hQ : HasDerivWithinAt (fun u => QL a b (Φ u))
        (2 * Φ t (Lv a) * (Φ t (Lv b) - Φ t (Lv a)) +
          6 * (Φ t (Lv b) - Φ t (Lv a)) * (-1 * Φ t (Lv b) - (Φ t (Lv b) - Φ t (Lv a))))
        (Icc 0 r) t := by
      have h1 := hAt.mul hAt
      have h2 := (hD.mul hD).const_mul 3
      exact (h1.add h2).congr_deriv (by simp only [Pi.sub_apply]; ring)
    have hE : HasDerivWithinAt (fun u => Real.exp (9/2 * u)) (Real.exp (9/2 * t) * (9/2))
        (Icc 0 r) t := by
      have := ((hasDerivAt_id t).const_mul (9/2 : ℝ)).exp
      simpa using this.hasDerivWithinAt
    exact hQ.mul hE
  have hcont : ContinuousOn F (Icc 0 r) := fun t ht => (hFd t ht).continuousWithinAt
  have hmono : MonotoneOn F (Icc 0 r) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hcont
      (fun t ht => (hFd t (interior_subset ht)).mono interior_subset) ?_
    intro t _
    have he := Real.exp_pos (9/2 * t)
    show 0 ≤ F' t
    simp only [hF', QL]
    nlinarith [mul_self_nonneg (9 * Φ t (Lv a) - 4 * (Φ t (Lv b) - Φ t (Lv a))),
      mul_self_nonneg (Φ t (Lv b) - Φ t (Lv a)),
      mul_nonneg he.le (mul_self_nonneg (9 * Φ t (Lv a) - 4 * (Φ t (Lv b) - Φ t (Lv a)))),
      mul_nonneg he.le (mul_self_nonneg (Φ t (Lv b) - Φ t (Lv a)))]
  have hr := H.hr
  have hle := hmono ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩ hr
  simp only [hF, mul_zero, Real.exp_zero, mul_one] at hle
  have h0 : QL a b (Φ 0) = QL a b σ := by
    rw [H.hΦ0]; simp only [QL]
    rw [Function.update_of_ne (by simp [Lv, Prod.ext_iff]),
      Function.update_of_ne (by simp [Lv, Prod.ext_iff])]
  rw [h0, hΦr] at hle
  -- `Q(ν) ≥ e^{−(9/2) r} Q(σ) ≥ e^{−(9/2) dt} Q(σ)`
  have hinv : Real.exp (-(9/2 * r)) * Real.exp (9/2 * r) = 1 := by
    rw [← Real.exp_add]; simp
  have hQr : Real.exp (-(9/2 * r)) * QL a b σ ≤ QL a b ν := by
    have hpos := Real.exp_pos (-(9/2 * r))
    calc Real.exp (-(9/2 * r)) * QL a b σ
        ≤ Real.exp (-(9/2 * r)) * (QL a b ν * Real.exp (9/2 * r)) :=
          mul_le_mul_of_nonneg_left hle hpos.le
      _ = QL a b ν := by rw [mul_comm (QL a b ν), ← mul_assoc, hinv, one_mul]
  have hed : Real.exp (-(9/2 * dt)) ≤ Real.exp (-(9/2 * r)) := Real.exp_le_exp.mpr (by linarith)
  exact le_trans (mul_le_mul_of_nonneg_right hed (QL_nonneg a b σ)) hQr

/-- **The window**: over `k` clocked pieces, `Q` keeps at least `e^{−(9/2) k dt}`. -/
theorem QL_window (l : ℕ) (a b : Fin 8) (dt : ℝ)
    (hfa : ∀ x, Term.eval (fLR l a) x = x (Lv b) - x (Lv a))
    (hfb : ∀ x, Term.eval (fLR l b) x = -1 * x (Lv b)) :
    ∀ (k : ℕ) {σ ν : State (Var 8)},
      Program.sem (windowSeg (leftBlock (fLR l)) domLR tgR dt k) σ ν →
      Real.exp (-(9/2 * dt * k)) * QL a b σ ≤ QL a b ν := by
  intro k
  induction k with
  | zero =>
      intro σ ν h
      simp only [windowSeg, List.replicate_zero, bigSeq, sem_test] at h
      obtain ⟨rfl, -⟩ := h
      simp
  | succ k ih =>
      intro σ ν h
      simp only [windowSeg, List.replicate_succ, bigSeq] at h
      obtain ⟨mid, hseg, hrest⟩ := h
      have h1 := QL_piece l a b dt hfa hfb hseg
      have h2 := ih hrest
      have hsplit : Real.exp (-(9/2 * dt * ((k + 1 : ℕ) : ℝ))) =
          Real.exp (-(9/2 * dt * k)) * Real.exp (-(9/2 * dt)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hsplit, mul_assoc]
      exact le_trans (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) h2

/-! ## The rows, evaluated -/

theorem gAt0_eval (x : State (Var 8)) : Term.eval (gAt 0) x = x (Lv 0) - x (Rv 0) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gAt, atomsOf, invRPF, refinement_ladder_rover_rung3_6to8_IR, Run.invToG,
    Run.lowerE, vsR, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt1_eval (x : State (Var 8)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invRPF, refinement_ladder_rover_rung3_6to8_IR, Run.invToG,
    Run.lowerE, vsR, gp_0_2, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem gAt2_eval (x : State (Var 8)) :
    Term.eval (gAt 2) x = x (Rv 2) * x (Rv 2) - QL 2 3 x := by
  have hdL : ("L_psi".drop 2).copy = "psi" := by decide
  have hdR : ("R_psi".drop 2).copy = "psi" := by decide
  have hdL3 : ("L_omega_psi".drop 2).copy = "omega_psi" := by decide
  simp [gAt, atomsOf, invRPF, refinement_ladder_rover_rung3_6to8_IR, Run.invToG,
    Run.lowerE, vsR, gp_3, hr3, Run.resolveVar, Parse.dr, hdL, hdR, hdL3, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv, QL]
  ring

theorem gAt3_eval (x : State (Var 8)) :
    Term.eval (gAt 3) x = x (Rv 4) * x (Rv 4) - QL 4 5 x := by
  have hdL : ("L_theta_p".drop 2).copy = "theta_p" := by decide
  have hdR : ("R_theta_p".drop 2).copy = "theta_p" := by decide
  have hdL3 : ("L_omega_theta".drop 2).copy = "omega_theta" := by decide
  simp [gAt, atomsOf, invRPF, refinement_ladder_rover_rung3_6to8_IR, Run.invToG,
    Run.lowerE, vsR, gp_3, hr3, Run.resolveVar, Parse.dr, hdL, hdR, hdL3, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv, QL]
  ring

theorem sat_FR (x : State (Var 8)) : Formula.sat (FM gR gsR) x ↔
    (x (Lv 0) - x (Rv 0) ≤ 0 ∧ x (Lv 1) - (x (Rv 1) + 1/5) ≤ 0 ∧
      x (Rv 2) * x (Rv 2) - QL 2 3 x ≤ 0 ∧ x (Rv 4) * x (Rv 4) - QL 4 5 x ≤ 0) := by
  rw [sat_FM_iff]
  simp only [gR, gsR, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    gAt0_eval, gAt1_eval, gAt2_eval, gAt3_eval]


/-! ## The guarded response to a left window -/

theorem window_right (l : ℕ) (hl : l < 3) (dt : ℝ) {σ ν : State (Var 8)}
    (h : Program.sem (windowSeg (leftBlock (fLR l)) domLR tgR dt 3) σ ν) (i : Fin 8) :
    ν (Rv i) = σ (Rv i) := by
  have hP := vars_windowSegL_sub (fLR l) domLR 1 dt 3 (hfLR l hl) hdomLR
  refine (Program.bound_effect _ h (Rv i) ?_).symm
  intro hb
  rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- The attitude row at the response's end: the reference's `x_R` has decayed by `e^{−Dmin}`,
the deployed's form kept `e^{−(27/2) dt}`. -/
theorem att_row {σ ν μ : State (Var 8)} (a b : Fin 8) (i : Fin 8) (dt Dmin : ℝ)
    (hD : 27/2 * dt ≤ 2 * Dmin)
    (hrow : σ (Rv i) * σ (Rv i) ≤ QL a b σ)
    (hQ : Real.exp (-(9/2 * dt * (3:ℕ))) * QL a b σ ≤ QL a b ν)
    (hR : ν (Rv i) = σ (Rv i))
    (hμL : ∀ j, μ (Lv j) = ν (Lv j))
    (hdec : |μ (Rv i)| ≤ |ν (Rv i)| * Real.exp (-Dmin)) :
    μ (Rv i) * μ (Rv i) - QL a b μ ≤ 0 := by
  have hQμ : QL a b μ = QL a b ν := by simp only [QL, hμL]
  rw [hQμ]
  have he := Real.exp_pos (-Dmin)
  have hsq : μ (Rv i) * μ (Rv i) ≤ σ (Rv i) * σ (Rv i) * (Real.exp (-Dmin) * Real.exp (-Dmin)) := by
    rw [hR] at hdec
    have h0 : 0 ≤ |μ (Rv i)| := abs_nonneg _
    have h1 : |μ (Rv i)| * |μ (Rv i)| ≤
        (|σ (Rv i)| * Real.exp (-Dmin)) * (|σ (Rv i)| * Real.exp (-Dmin)) :=
      mul_le_mul hdec hdec h0 (le_trans h0 hdec)
    have e1 : |μ (Rv i)| * |μ (Rv i)| = μ (Rv i) * μ (Rv i) := abs_mul_abs_self _
    have e2 : |σ (Rv i)| * |σ (Rv i)| = σ (Rv i) * σ (Rv i) := abs_mul_abs_self _
    nlinarith
  have hee : Real.exp (-Dmin) * Real.exp (-Dmin) ≤ Real.exp (-(9/2 * dt * (3:ℕ))) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; push_cast; linarith
  have hs0 : 0 ≤ σ (Rv i) * σ (Rv i) := mul_self_nonneg _
  have : σ (Rv i) * σ (Rv i) * (Real.exp (-Dmin) * Real.exp (-Dmin)) ≤
      QL a b σ * Real.exp (-(9/2 * dt * (3:ℕ))) :=
    mul_le_mul hrow hee (by positivity) (QL_nonneg a b σ)
  linarith [mul_comm (QL a b σ) (Real.exp (-(9/2 * dt * (3:ℕ))))]

theorem sat_regionR2 (x : State (Var 8)) (h : x (Rv 0) ≤ 13/20) :
    Formula.sat (regionR 2) x := by
  rw [sat_regionR_iff]; simpa using h

/-- **The guarded response** of left window `l` from right band `q` (in its guard): the
ladder climb with the decay budget `Dmin = max 0 ((27/4) dt)`, then hold `FLAT` until the rows
on `v` and `s` hold; the attitude rows follow from the budget (`att_row`). -/
theorem respondG (l : ℕ) (hl : l < 3) (dt : ℝ) (q : ℕ) (hq : q < 3) {σ : State (Var 8)}
    (hσ : Formula.sat (Formula.and (FM gR gsR) RoverLadderRung3Modal.envR) σ)
    (hguard : Formula.sat (hostGuard vsR 8 Side.R (mRR q)) σ) :
    GResp GrG q (gwindowSeg Formula.tt (leftBlock (fLR l)) domLR tgR dt 3)
      (fun qf => Formula.and (Formula.and (FM gR gsR) RoverLadderRung3Modal.envR) (regionR qf)) σ := by
  refine gresp_of_rresp (fun ν hν => ?_)
  obtain ⟨-, hwin⟩ := gwindowSeg_runs hν
  have hR := window_right l hl dt hwin
  have hvL := windowSeg_coord_le_or_lt (fLR l) domLR tgR dt 0 3 (cstR l) (by norm_num)
    (by simp [Lv, Prod.ext_iff]) (fun s _ => fLR0_eval l hl s) 3 hwin
  have hrow := (sat_FR σ).mp hσ.1
  have hatt := fLR_eval_att l hl
  have hQψ := QL_window l 2 3 dt (fun x => (hatt x).1) (fun x => (hatt x).2.1) 3 hwin
  have hQθ := QL_window l 4 5 dt (fun x => (hatt x).2.2.1) (fun x => (hatt x).2.2.2) 3 hwin
  have hdomLν : Formula.sat domLR ν :=
    windowSeg_end_domL (leftBlock (fLR l)) domLR tgR dt 3 (by norm_num) hwin
  have hdomRν : Formula.sat domRR ν := by
    refine (Formula.coincidence domRR (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomRR hx
    exact (hR i).symm
  have hgν : Formula.sat (hostGuard vsR 8 Side.R (mRR q)) ν :=
    frames_right (vars_windowSegL_sub (fLR l) domLR 1 dt 3 (hfLR l hl) hdomLR)
      (hguardR_all q) hwin hguard
  have hcl := ladC_bounds l
  have hV : ν (Lv 0) < 13/20 ∨ ν (Lv 0) ≤ ν (Rv 0) := by
    rcases hvL with h | h
    · right; rw [hR 0]; linarith [hrow.1]
    · left; rw [cstR_eq] at h; linarith [hcl.2]
  set Dmin : ℝ := max 0 (27/4 * dt) with hDmin
  have hD0 : 0 ≤ Dmin := le_max_left _ _
  have hD1 : 27/2 * dt ≤ 2 * Dmin := by have := le_max_right 0 (27/4 * dt); linarith
  have hfin : ∀ μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat domRR μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ν (Rv 0) ≤ μ (Rv 0) → ν (Lv 0) ≤ μ (Rv 0) →
      ν (Lv 1) - 1/5 ≤ μ (Rv 1) →
      (∀ i : Fin 8, (i = 2 ∨ i = 4) → |μ (Rv i)| ≤ |ν (Rv i)| * Real.exp (-Dmin)) →
      Formula.sat (Formula.and (Formula.and (FM gR gsR) RoverLadderRung3Modal.envR) (regionR 2)) μ := by
    intro μ hμL hμd _ hcap _ hv hs hdec
    refine ⟨⟨(sat_FR μ).mpr ⟨by rw [hμL 0]; linarith, by rw [hμL 1]; linarith,
      att_row 2 3 2 dt Dmin hD1 (by linarith [hrow.2.2.1]) hQψ (hR 2) hμL (hdec 2 (Or.inl rfl)),
      att_row 4 5 4 dt Dmin hD1 (by linarith [hrow.2.2.2]) hQθ (hR 4) hμL (hdec 4 (Or.inr rfl))⟩,
      ?_, hμd⟩, sat_regionR2 μ hcap⟩
    refine (Formula.coincidence domLR (fun x hx => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLR hx
    exact hμL i
  refine LR.climbD (fun i => i = 2 ∨ i = 4) LR_dec Dmin hD0 q hq ν hdomRν ⟨?_, ?_, ?_⟩ _ _ hV hfin
  · rintro rfl; rw [sat_guardR0] at hgν; exact ⟨hgν.2.1, hgν.2.2⟩
  · rintro rfl; rw [sat_guardR1] at hgν; exact hgν
  · rintro rfl; rw [sat_guardR2] at hgν; exact hgν

/-! ## Theorem 3 over the guarded automaton -/

noncomputable def gregion (q : ℕ) : Formula (Var 8) :=
  regionG (fun q => hostGuard vsR 8 Side.R (mRR q)) regionR q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (regionR_fv q)

theorem hmvregG : ∀ q, mvR ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-- **`refinement_ladder_rover_rung3_6to8`, Theorem 3 over the GUARDED right automaton, at the
mode-consistent region.** The left: the file's three windows (three clocked pieces of at most
`dt` each); the right: the 8-DOF chain `STEEP → MODER → FLAT` of the file with every edge
testing the entered band's guard (`GrG_guards`). Loop invariant: the four declared rows, both
envelopes, the right in the guard of its current band and under its cut ceiling (`mvRegionR` at
`gregion`). Response: the ladder climb with a decay budget (`LadderRun.climbD`). Z3-free;
every window length `dt`. -/
theorem rover_ladder_rung3_6to8_guarded (dt : ℝ) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsR dt))
      (rightAutomatonBody GrG mvR)
      (RFormula.and (RFormula.and (canonInvM gR gsR) (envLR domLR domRR))
        (mvRegionR mvR gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvR (FM gR gsR) domLR domRR gregion
    (leftProgsR dt) (canonInvM gR gsR) (encode_canonInvM gR gsR) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgsR, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLR d hd).1
        (hLR d hd).2.1 (hLR d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub GrG _ hgRG hRvG hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · refine hstep_assembled_GR GrG mvR (FM gR gsR) RoverLadderRung3Modal.envR gregion (leftProgsR dt)
      hmvFR hmvenvR hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesR dt) ?_
    refine Hmulti_regionG GrG mvR _ regionR GrG_guards (FM gR gsR) RoverLadderRung3Modal.envR (leftProgsR dt) ?_ ?_
    · intro P hP q _ σ ν hrun
      simp only [leftProgsR, List.mem_map] at hP
      obtain ⟨d, hd, rfl⟩ := hP
      exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hLR d hd).1
        (hLR d hd).2.1 (hLR d hd).2.2) (hguardR_all q) hrun
    · intro P hP q hq σ _ hσ hg _
      rw [GrG_len] at hq
      simp only [leftProgsR, leftDataR, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl
      · exact respondG 0 (by norm_num) dt q hq hσ hg
      · exact respondG 1 (by norm_num) dt q hq hσ hg
      · exact respondG 2 (by norm_num) dt q hq hσ hg
  · exact hddF_multiR_G GrG 0 1 dt leftDataR gregion (canonInvM gR gsR) domLR domRR
      (by decide) hgRG hRvG hLR (fun q _ => gregion_fv q)
      (canonInvM_varsL gR gsR (by
        intro g' hg'
        simp only [gR, gsR, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gR gsR) hdomLR hdomRR


end RoverLadderRung3Guarded
end RelCertifier
