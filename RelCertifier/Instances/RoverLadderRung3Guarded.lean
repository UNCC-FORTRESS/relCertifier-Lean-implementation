/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung3_6to8` over the GUARDED right automaton — Theorem 3 by
replaying the cover

`RoverLadderRung3Modal.rover_ladder_rung3_6to8_modal` states Theorem 3 over the `⊤`-guarded
chain `STEEP → MODER → FLAT`. This file states it over the GUARDED chain (every edge tests the
lowered guard of the band it enters, `GrG_guards`) at the mode-consistent region (the right in
the guard of its current band and under its cut ceiling `v_R ≤ c_q`), against the gated left
windows (three clocked pieces; carried to the paper's left automaton in
`Instances/LeftAutLegacy.lean`), and proves it by REPLAYING THE EMITTED COVER
(`InstancesV2/BenchCovers/refinement_ladder_rover_rung3_6to8.lean`, λ = 9/4 for every window):
a band just below the window's (`dynPre`) repositions alone to the next floor, preserved by
the reposition pack `VerdD l q`; in the joint nodes (the bands at or above the window's,
`jointOK`) the right keeps time with the window at the cover's stretch `9/4`, switching up at
each floor it reaches, every stretch preserved by the joint pack `Verd l q` (the four rows,
attitude rows included, in the cover's strata order); the `FLAT` window from `STEEP` is
inadmissible. Every switch is legal against the entered band's guard; the explicit band runs
(`LR`, the attitude-weighted odometer) supply only the existence of the right's runs.
Hypotheses: six joint packs and two reposition packs (`modalVerdX`, `modalVerdDynX`).
-/
import RelCertifier.Instances.RoverLadderRung3Modal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayBridge
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung3_6to8

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverLadderRung3Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung3Modal GPins RelCertifier.Oracle

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

noncomputable def gregion (q : ℕ) : Formula (Var 8) :=
  regionG (fun q => hostGuard vsR 8 Side.R (mRR q)) regionR q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (regionR_fv q)

theorem hmvregG : ∀ q, mvR ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aV (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
def vStr (q : ℕ) : String := if q = 0 then "0.3" else if q = 1 then "0.5" else "0.65"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 8) :=
  cutPairsX vsR 8 Side.L (cutAtomsOfX refinement_ladder_rover_rung3_6to8_cutsV2X.L (mLR l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 8) :=
  cutPairsX vsR 8 Side.R (cutAtomsOfX refinement_ladder_rover_rung3_6to8_cutsV2X.R (mRR q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsR 8 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsR,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gL_v (l : ℕ) (hl : l < 3) : hostAtomG vsR 8 Side.L (aV (vStr l)) = thrLe (Lv 0) (ladC l) := by
  interval_cases l <;>
  simp [aV, vStr, ladC, hostAtomG, cutAtomG, Run.lowerE, gp_0_3, gp_0_5, gp_0_65, vsR,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsR 8 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsR,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]
theorem gR_v (q : ℕ) (hq : q < 3) : hostAtomG vsR 8 Side.R (aV (vStr q)) = thrLe (Rv 0) (ladC q) := by
  interval_cases q <;>
  simp [aV, vStr, ladC, hostAtomG, cutAtomG, Run.lowerE, gp_0_3, gp_0_5, gp_0_65, vsR,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vsR 8 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l)),
      (hostAtomF vsR 8 Side.L (aV (vStr l)), thrLe (Lv 0) (ladC l))] := by
  rw [← gL_s l hl, ← gL_v l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsR 8 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q)),
      (hostAtomF vsR 8 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))] := by
  rw [← gR_s q hq, ← gR_v q hq]; interval_cases q <;> rfl

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) := by
  rw [cL_eq l hl]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [← gL_s l hl]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gL_v l hl]; exact hostAtom_iff (Or.inl rfl) ν
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) := by
  rw [cR_eq q hq]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [← gR_s q hq]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gR_v q hq]; exact hostAtom_iff (Or.inl rfl) ν

theorem cutSatL_s (l : ℕ) (hl : l < 3) (ν : State (Var 8)) (h : CutSat (cL l) ν) :
    sK l ≤ ν (Lv 1) := by
  have h1 := hiffL l hl (hostAtomF vsR 8 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))
    (by rw [cL_eq l hl]; simp) ν
  simp only [thrGe, Term.eval, AOp.interp] at h1
  have := h1.mp (h (hostAtomF vsR 8 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))
    (by rw [cL_eq l hl]; simp))
  linarith

/-! ## O1: guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vsR 8 Side.L (mLR l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard refinement_ladder_rover_rung3_6to8_cutsV2X_wf (mLR l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung3_6to8_cutsV2X, mLR,
        refinement_ladder_rover_rung3_6to8_IR] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung3_6to8_cutsV2X, mLR,
        refinement_ladder_rover_rung3_6to8_IR] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsR,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mLR, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
        gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsR, Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vsR 8 Side.R (mRR q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard refinement_ladder_rover_rung3_6to8_cutsV2X_wf (mRR q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung3_6to8_cutsV2X, mRR,
        refinement_ladder_rover_rung3_6to8_IR] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung3_6to8_cutsV2X, mRR,
        refinement_ladder_rover_rung3_6to8_IR] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsR,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRR, refinement_ladder_rover_rung3_6to8_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
        gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsR, Run.resolveVar, List.findIdx?_cons]

/-! ## The fields and envelopes the atoms' staying needs -/

theorem fLR0_eval (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLR l 0) x = 3 * (cstR l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fLR, hostDyn, mLR, refinement_ladder_rover_rung3_6to8_IR, vsR, Run.dynOf,
      Run.lowerE, hr030, hr050, hr065, hr3, hrm1, hr0, hr1, hr05, hr03, hrm05, hr06, hr015, hr00,
      hr08, hrm10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv, cstR]

theorem fLR1_eval (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLR l 1) x =
      x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 4) * x (Lv 4))) := by
  interval_cases l <;>
    simp [fLR, hostDyn, mLR, refinement_ladder_rover_rung3_6to8_IR, vsR, Run.dynOf,
      Run.lowerE, hr030, hr050, hr065, hr3, hrm1, hr0, hr1, hr05, hr03, hrm05, hr06, hr015, hr00,
      hr08, hrm10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv]

theorem domL_bnd (z : State (Var 8)) (hz : Formula.sat domLR z) :
    0 ≤ z (Lv 0) ∧ -(3:ℝ)/5 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 3/5 ∧ -(3:ℝ)/5 ≤ z (Lv 4) ∧
      z (Lv 4) ≤ 3/5 := by
  simp only [domLR, hostEvolve, mLR, refinement_ladder_rover_rung3_6to8_IR, vsR] at hz
  simp [Run.lowerF, Run.lowerE, hrm05, hr06, hr015, hr00, hr08, hrm10, gp_m0_6, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]
    at hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 8)) (hz : Formula.sat domLR z) :
    0 ≤ Term.eval (fLR l 1) z := by
  rw [fLR1_eval l hl]
  obtain ⟨h0, h1, h2, h3, h4⟩ := domL_bnd z hz
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Lv 2) * z (Lv 2))) - 3/10 * (z (Lv 4) * z (Lv 4)) := by nlinarith
  exact mul_nonneg h0 this

theorem sdotR_nonneg (q : ℕ) (hq : q < 3) (z : State (Var 8)) (hz : Formula.sat domRR z) :
    0 ≤ Term.eval (fRR q 1) z := by
  rw [fRR1_eval q hq]
  obtain ⟨-, -, -, -, -, -, h2l, h2h, -, h4l, h4h, h0l, -, -, -⟩ := (sat_domRR z).mp hz
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Rv 2) * z (Rv 2))) - 3/10 * (z (Rv 4) * z (Rv 4)) := by nlinarith
  exact mul_nonneg h0l this

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

theorem stayL (l q : ℕ) (hl : l < 3) (c : ℝ) :
    AtomsStayC (cL l) (jointSys (fLR l) (fRR q) (Term.const c)) (Formula.and domLR domRR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domLR domRR) (fun x h => h)
      (fun z hz _ => sdotL_nonneg l hl z hz.1) hinit
  · exact boxle_thrLe_L 0 (ladC l) _ _ _ _ (Formula.and domLR domRR) (fun x h => h)
      (fun z hz hK => by rw [fLR0_eval l hl, cstR_eq]; linarith) hinit

theorem stayR_gen (q : ℕ) (hq : q < 3) (fL : Fin 8 → Term (Var 8)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 8)) (hD : ∀ z, Formula.sat D z → Formula.sat domRR z) :
    AtomsStayC (cR q) (jointSys fL (fRR q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
      (fun z hz _ => sdotR_nonneg q hq z (hD z hz)) hinit
  · exact boxle_thrLe_R 0 (ladC q) _ _ c hc D D (fun x h => h)
      (fun z hz hK => by rw [fRR0_eval q hq, cstR_eq]; linarith) hinit

/-! ## The invariant's components, as the tool lowers them: the statement's own rows -/

theorem atoms_eq : atomsOf invRPF = pAtoms invRPF := by decide

theorem comps_eq : hostComps vsR 8
    (refinement_ladder_rover_rung3_6to8_IRv2.invariants.getD 0 ("", PForm.tt)).2 = gR :: gsR := by
  have hrow : (refinement_ladder_rover_rung3_6to8_IRv2.invariants.getD 0 ("", PForm.tt)).2
      = invRPF := rfl
  have hlist : pAtoms invRPF = [(atomsOf invRPF).getD 0 .tt, (atomsOf invRPF).getD 1 .tt,
      (atomsOf invRPF).getD 2 .tt, (atomsOf invRPF).getD 3 .tt] := by decide
  rw [hrow, hostComps_atoms vsR invRPF ?_, hlist]
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
    rcases ha with rfl | rfl | rfl | rfl <;>
      exact ⟨⟨_, _, _, rfl⟩, by
        simp [atomsOf, invRPF, refinement_ladder_rover_rung3_6to8_IR, Run.invToG, Run.lowerE,
          vsR, gp_3, gp_0_2, Run.resolveVar, Parse.dr, hdv, hds, hdp, hdt,
          List.findIdx?_cons]⟩

theorem comps_fv : ∀ c ∈ gR :: gsR, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [gR, gsR, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact hgAt _

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 9/4, strata `[0, 1, 2, 3]`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX refinement_ladder_rover_rung3_6to8_IRv2 refinement_ladder_rover_rung3_6to8_cutsV2X 8 0
    [0, 1, 2, 3] (9/4) l q

/-- The pre-joint reposition pack of window `l` at right mode `q` (`dynPreOrder = [0, 1, 2, 3]`). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX refinement_ladder_rover_rung3_6to8_IRv2 refinement_ladder_rover_rung3_6to8_cutsV2X
    8 0 [0, 1, 2, 3] true l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsR 8 Side.L (mLR l) = domLR := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vsR 8 Side.R (mRR q) = domRR := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (gR :: gsR) (fLR l) (fRR q) (9/4)
      (domCutX (Formula.and domLR domRR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdXCore (([0, 1, 2, 3] : List ℕ).map (fun i => (hostComps vsR 8
      (refinement_ladder_rover_rung3_6to8_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i
        (Term.const 0)))
    (fLR l) (fRR q) ((9/4 : ℝ)) (domCutX (Formula.and (hostEvolve vsR 8 Side.L (mLR l))
      (hostEvolve vsR 8 Side.R (mRR q))) (cL l) (cR q)) at h'
  rw [hc] at h'
  simpa [gsR] using h'

theorem verdD_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : VerdD l q) :
    VerdDynCore true (gR :: gsR) (fRR q)
      (domCutX (Formula.and domLR domRR) (cL l) (cR q)) (hostGuard vsR 8 Side.L (mLR l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdDynCore true (([0, 1, 2, 3] : List ℕ).map (fun i => (hostComps vsR 8
      (refinement_ladder_rover_rung3_6to8_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i
        (Term.const 0)))
    (fRR q) (domCutX (Formula.and (hostEvolve vsR 8 Side.L (mLR l))
      (hostEvolve vsR 8 Side.R (mRR q))) (cL l) (cR q)) (hostGuard vsR 8 Side.L (mLR l)) at h'
  rw [hc] at h'
  simpa [gsR] using h'

/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mRR q = dummyR :=
    List.getD_eq_default _ _ (by simp [refinement_ladder_rover_rung3_6to8_IR]; omega)
  simp only [cR, this]
  rfl

noncomputable def anc (l q : ℕ) : Formula (Var 8) := FM gR (gsR ++ atomTerms (cL l) (cR q))

theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vsR 8 Side.L (mLR l)).fv ⊆ range Lv :=
  hostGuard_fv_L vsR (mLR l) (by interval_cases l <;> decide)

theorem cL_fv (l : ℕ) (hl : l < 3) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv := by
  intro a ha
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
  · intro x hx; simp [thrGe, thrLe, Term.fv] at hx; subst hx; simp

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
      Program.sem (Program.ode (jointSys (fLR l) (fRR q) (Term.const (9/4)))
        (Formula.and domLR domRR)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX gR gsR (gR :: gsR) (cL l) (cR q) (fLR l) (fRR q) (9/4) domLR domRR
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl _)
    (stayR_gen q hq (fLR l) (9/4) (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_boxD (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vsR 8 Side.L (mLR l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fRR q) (Term.const 1))
        (Formula.and domLR domRR)) σ ω → Formula.sat (anc l q) ω := by
  intro σ ω h1 h2 h3
  exact couple_box_dyn true gR gsR (gR :: gsR) (cL l) (cR q) (fRR q) domLR domRR
    (hostGuard vsR 8 Side.L (mLR l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fv l hl) (hguardL l hl)
    (stayR_gen q hq _ 1 (by norm_num) _ (fun z hz => by
      simp only [dynBase, if_true] at hz; exact hz.1.2))
    (verdD_core l q hl hq hv) σ ω h1 (fun _ => h2) h3

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vsR 8 Side.R (mRR e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

/-! ## The ladder's switching choreography and the cover's node sets -/

abbrev Cap (q : ℕ) (x : State (Var 8)) : Prop := x (Rv 0) ≤ ladC q

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 8))
    (hg : Formula.sat (hostGuard vsR 8 Side.R (mRR q)) x) (hd : Formula.sat domRR x) :
    ladPre Cap domRR q x := by
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

theorem ladPre_R (q : ℕ) (x y : State (Var 8)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : ladPre Cap domRR q x) : ladPre Cap domRR q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, hc, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · show y (Rv 0) ≤ ladC q; rw [← hxy 0]; exact hc
  · refine (Formula.coincidence domRR (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRR hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 8), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsR 8 Side.R (mRR 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩
theorem leg11 : ∀ x : State (Var 8), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsR 8 Side.R (mRR 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩

def J (l q : ℕ) : Prop := l ≤ q ∧ q < 3
def D (l q : ℕ) : Prop := q + 1 = l

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 8) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domRR q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domRR) E :=
  ladder_hmove LR Cap (ladCap_run LR) ladCap_up (edgeG 0 0) (edgeG 1 1)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc)) leg11
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg22 x hs (by simpa [Cap, ladC] using hc))
    (J l) (fun q hJ hq2 => ⟨by have := hJ.1; omega, by omega⟩) E hE

theorem hexitR (l : ℕ) (hl : l < 3) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domRR) (ladPre Cap domRR) :=
  ladder_hexit LR Cap (ladCap_run LR) ladCap_up
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc)) (J l) (D l)
    (fun q hD hnJ => by
      unfold D at hD; unfold J at hnJ ⊢
      refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩)

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 8)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM gR gsR) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem gAt1_eval (x : State (Var 8)) :
    Term.eval (gAt 1) x = x (Lv 1) - (x (Rv 1) + 1/5) := by
  have hdL : ("L_s".drop 2).copy = "s" := by decide
  have hdR : ("R_s".drop 2).copy = "s" := by decide
  simp [gAt, atomsOf, invRPF, refinement_ladder_rover_rung3_6to8_IR, Run.invToG,
    Run.lowerE, vsR, gp_0_2, Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 3) {σ : State (Var 8)}
    (hσ : Formula.sat (Formula.and (FM gR gsR) RoverLadderRung3Modal.envR) σ)
    (hg : Formula.sat (hostGuard vsR 8 Side.R (mRR q)) σ) :
    GResp GrG q (gwindowSeg (hostGuard vsR 8 Side.L (mLR l)) (leftBlock (fLR l)) domLR tgR dt
      (2 + 1)) (fun qf => Formula.and (Formula.and (FM gR gsR) RoverLadderRung3Modal.envR)
        (regionR qf)) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · unfold D at h; omega
  refine replay_gresp GrG LR.m fRR domRR (fLR l) domLR (hostGuard vsR 8 Side.L (mLR l)) aR
    hgRG (hfLR l hl) hdomLR hdomRR (hguardL l hl) (9/4) (by norm_num) (J l) (D l)
    (fun q h => hfRR q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h.2)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.2 (hJv q h))
    (fun q h => anc_boxD l q hl (by unfold D at h; omega) (hDv q h))
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domRR) (ladPre Cap domRR) (ladPre Cap domRR) ladPre_R ladPre_R
    (hmoveR l _ (fun _ _ _ h => h)) (fun _ _ => hmoveR l _ (fun _ _ hJ h => ⟨hJ, h⟩))
    (hexitR l hl) dt 2 q σ ?_ hσ.2.1 _ ?_
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
        have hrow := (sat_FM_iff gR gsR σ).mp hσ.1 (gAt 1) (by simp [gsR])
        rw [gAt1_eval] at hrow
        simp [sK] at hsL
        linarith [hg.2.1]
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLR ν :=
      windowSeg_end_domL (leftBlock (fLR l)) domLR tgR dt (2 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FM gR gsR) μ := by
      refine (sat_of_agree (fun x hx => ?_) (fun i => ?_) (fun i => ?_)).mp hA'
      · by_contra hS
        exact notMem_FM_fv (fun g' hg' hxg => hS (comps_fv g' hg' hxg)) hx
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hpre.2.2.2⟩, ?_⟩
    · refine (Formula.coincidence domLR (fun v hv => ?_)).mpr hdomLν
      obtain ⟨i, rfl⟩ := hdomLR hv
      exact hμL i
    · rw [sat_regionR_iff]
      have hc := hpre.2.2.1
      simp only [Cap, ladC] at hc
      exact hc

/-! ## Theorem 3 over the gated windows, by replaying the cover -/

noncomputable def guardsL : List (Formula (Var 8)) :=
  (List.range 3).map (fun l => hostGuard vsR 8 Side.L (mLR l))

noncomputable def leftDataG : List (Formula (Var 8) × (Fin 8 → Term (Var 8)) × Formula (Var 8) × ℕ) :=
  gatedDataGI guardsL leftDataR

theorem leftDataG_eq : leftDataG =
    [(hostGuard vsR 8 Side.L (mLR 0), fLR 0, domLR, 3),
     (hostGuard vsR 8 Side.L (mLR 1), fLR 1, domLR, 3),
     (hostGuard vsR 8 Side.L (mLR 2), fLR 2, domLR, 3)] := rfl

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 8)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tgR dt d.2.2.2)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
    d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  rw [leftDataG_eq] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfLR 0 (by norm_num), hdomLR⟩
  · exact ⟨hguardL 1 (by norm_num), hfLR 1 (by norm_num), hdomLR⟩
  · exact ⟨hguardL 2 (by norm_num), hfLR 2 (by norm_num), hdomLR⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mvR := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tgR dt d.2.2.2 mvR (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-- **`refinement_ladder_rover_rung3_6to8`, Theorem 3 by replaying the emitted cover** (over
the gated three-piece windows; carried to the paper's left automaton by
`theorem3_leftAut_of_choiceR`). The right answers window `l` from band `q` as the cover's
derivation does: a band just below the window's (`dynPre`) repositions alone to the next
floor (`VerdD l q`), then the right keeps time with the window at the cover's λ = 9/4 in the
joint nodes (the bands at or above the window's), switching up at each floor it reaches,
every stretch preserved by its joint pack `Verd l q`; every switch is legal against the
entered band's guard; the `FLAT` window from `STEEP` is inadmissible. -/
theorem rover_ladder_rung3_6to8_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mvR)
      (RFormula.and (RFormula.and (canonInvM gR gsR) (envLR domLR domRR))
        (mvRegionR mvR gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvR (FM gR gsR) domLR domRR gregion
    (leftProgsG dt) (canonInvM gR gsR) (encode_canonInvM gR gsR) ?_ ?_ ?_
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
  · refine hstep_assembled_GR GrG mvR (FM gR gsR) RoverLadderRung3Modal.envR gregion
      (leftProgsG dt) hmvFR hmvenvR hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG
      (hframesG dt) ?_
    refine Hmulti_regionG GrG mvR _ regionR GrG_guards (FM gR gsR) RoverLadderRung3Modal.envR
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
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM gR gsR) domLR domRR
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL gR gsR comps_fv)
      (canonInvM_varsR gR gsR) hdomLR hdomRR

end RoverLadderRung3Guarded
end RelCertifier
