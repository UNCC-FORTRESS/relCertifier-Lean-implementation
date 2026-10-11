/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2b_6dof` over the GUARDED right automaton — Theorem 3 by
replaying the cover

`RoverRung2b6dofModal` states Theorem 3 over the `⊤`-guarded chain `STEEP → MODER → FLAT`. This
file states it over the GUARDED chain (every edge tests the lowered guard of the band it
enters, `GrG_guards`) at the mode-consistent region (the right in the guard of its current
band), against the gated left windows (two clocked pieces; carried to the paper's left
automaton in `Instances/LeftAutLegacy.lean`), and proves it by REPLAYING THE EMITTED COVER
(`InstancesV2/BenchCovers/refinement_ladder_rover_rung2b_6dof.lean`, λ = 1001/1000 for every
window): a band below the window's (`dynPre`) repositions alone up the chain to the window's
band, every reposition preserved by its pack `VerdD l q`; in the joint nodes (the bands at or
above the window's, `jointOK`) the right keeps time with the window at the cover's stretch,
switching up at each floor it reaches, every stretch preserved by the joint pack `Verd l q`
(the combined row `s_L − s_R − 0.2 + (v_L − v_R)/3 ≤ 0`). Every switch is legal against the
entered band's guard; the explicit band runs (`LR`) supply only the existence of the right's
runs. Hypotheses: six joint packs and three reposition packs (`modalVerdX`, `modalVerdDynX`).
-/
import RelCertifier.Instances.RoverRung2b6dofModal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayBridge
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung2b_6dof

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverRung2b6dofGuarded

open DL DLCalTiming DLRel Parse Set RoverRung2b6dofModal GPins RelCertifier.Oracle

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 6) :=
  { src := st, tgt := tgt, guard := hostGuard vsB2 6 Side.R (mRB2 tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [modeB2 0, modeB2 1, modeB2 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range refinement_ladder_rover_rung2b_6dof_IR.R.modes.length).flatMap (fun q =>
      (mRB2 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2b_6dof_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range refinement_ladder_rover_rung2b_6dof_IR.R.modes.length).flatMap (fun q =>
      (mRB2 q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung2b_6dof_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsB2 6 Side.R (mRB2 e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeB2 q) := by
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
  have hm' : m = modeB2 q := Option.some.inj (hm.symm.trans (GrG_modeAt q hq))
  subst hm'
  exact hRvB2 q (modeB2 q) (GrB2_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvB2 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsB2 6 Side.R (mRB2 q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsB2 _ dummyB2 rfl (by
    simp [refinement_ladder_rover_rung2b_6dof_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 6)) : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5) := by
  simp [hostGuard, mRB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 6)) : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5) := by
  simp [hostGuard, mRB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 6)) : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x ↔
    (7/5 ≤ x (Rv 1)) := by
  simp [hostGuard, mRB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB2, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region (the guard; no kept cut) -/

noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vsB2 6 Side.R (mRB2 q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvB2 ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cB2_eq (q : ℕ) : cB2 q = ladC q := rfl

noncomputable def aR : Fin 6 → ℝ := ![0, 0, 0, 0, 0, 0]
noncomputable def bR : Fin 6 → ℝ := fun _ => 0

theorem aR_nonneg : ∀ k, 0 ≤ aR k := by
  intro k; fin_cases k <;> simp [aR]

noncomputable def LR : LadderRun GrG domRB2 :=
  LadderRun.ofLinear GrG domRB2 modeB2 fRB2 aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRB20_eval q hq, cB2_eq])
    (fun q hq x => fRB21_eval q hq x)
    (fun q hq i h0 h1 x => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB22_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB23_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB24_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRB25_eval q hq]; simp [aR, bR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRB2 ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 4) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 4) hD.2.2.2.2.2.2.2.1 ht).2
      have hc := ladC_bounds q
      have hk : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) (bR k) ≤ phiLin aR bR q ρ k t ∧
            phiLin aR bR q ρ k t ≤ max (ρ (Rv k)) (bR k) :=
        fun k h0 h1 => phiLin_other_between aR bR q ρ k h0 h1 (aR_nonneg k) ht
      rw [sat_domRB2]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num [bR])) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.1 (by norm_num [bR])) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num [bR])),
        le_trans hD.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.1 (by norm_num [bR])) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2 (by norm_num [bR]))⟩)
    (fun ρ hρ => by have hD := (sat_domRB2 ρ).mp hρ; exact hD.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x
      rw [sat_guardR2]; exact le_of_eq hs.symm)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x
      rw [sat_guardR2]; exact hs)

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aV (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
def vStr (q : ℕ) : String := if q = 0 then "0.3" else if q = 1 then "0.5" else "0.65"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 6) :=
  cutPairsX vsB2 6 Side.L (cutAtomsOfX refinement_ladder_rover_rung2b_6dof_cutsV2X.L (mLB2 l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 6) :=
  cutPairsX vsB2 6 Side.R (cutAtomsOfX refinement_ladder_rover_rung2b_6dof_cutsV2X.R (mRB2 q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsB2 6 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsB2,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsB2 6 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsB2,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vsB2 6 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))] := by
  rw [← gL_s l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsB2 6 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))] := by
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

theorem cutSatL_iff (l : ℕ) (hl : l < 3) (ν : State (Var 6)) :
    CutSat (cL l) ν ↔ sK l ≤ ν (Lv 1) := by
  constructor
  · intro h
    have := (hiffL l hl _ (by rw [cL_eq l hl]; exact List.mem_cons_self) ν).mp
      (h _ (by rw [cL_eq l hl]; exact List.mem_cons_self))
    simp [thrGe, Term.eval, AOp.interp] at this; linarith
  · intro h a ha
    rw [cL_eq l hl] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    refine (hiffL l hl _ (by rw [cL_eq l hl]; exact List.mem_cons_self) ν).mpr ?_
    simp [thrGe, Term.eval, AOp.interp]; linarith

/-! ## O1: guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vsB2 6 Side.L (mLB2 l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard refinement_ladder_rover_rung2b_6dof_cutsV2X_wf (mLB2 l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2b_6dof_cutsV2X, mLB2, refinement_ladder_rover_rung2b_6dof_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2b_6dof_cutsV2X, mLB2, refinement_ladder_rover_rung2b_6dof_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsB2, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mLB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
        gp_899_95, vsB2, Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vsB2 6 Side.R (mRB2 q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard refinement_ladder_rover_rung2b_6dof_cutsV2X_wf (mRB2 q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2b_6dof_cutsV2X, mRB2, refinement_ladder_rover_rung2b_6dof_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung2b_6dof_cutsV2X, mRB2, refinement_ladder_rover_rung2b_6dof_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsB2,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRB2, refinement_ladder_rover_rung2b_6dof_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
        gp_0_3, gp_0_5, gp_0_65, vsB2, Run.resolveVar, List.findIdx?_cons]

/-! ## The left field and envelope, evaluated -/

theorem gp_1000_0 : Run.parseRat "1000.0" = some (1000:ℚ) := by
  have h : parseQ "1000.0" = some (⟨10000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fLB21_eval (l : ℕ) (hl : l < 3) (x : State (Var 6)) :
    Term.eval (fLB2 l 1) x =
      x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 3) * x (Lv 3))) := by
  interval_cases l <;>
    simp [fLB2, hostDyn, mLB2, refinement_ladder_rover_rung2b_6dof_IR, vsB2, Run.dynOf,
      Run.lowerE, gp_0, gp_0_0, gp_0_1, gp_0_15, gp_0_2, gp_0_25, gp_0_3, gp_0_30, gp_0_35, gp_0_4, gp_0_5, gp_0_50, gp_0_6, gp_0_65, gp_0_7, gp_0_75, gp_0_8, gp_0_9, gp_1, gp_1_0, gp_1_1, gp_1_2, gp_1_4, gp_1_5, gp_1_6, gp_2, gp_2_0, gp_3, gp_4, gp_5, gp_10, gp_m0_5, gp_m0_25, gp_m1, gp_m1_0, gp_m2, gp_m0_3, gp_m0_6, gp_m0_4, gp_899_95, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv]

/-- The left envelope's bounds the odometer's sign needs. -/
theorem domL_bnd (z : State (Var 6)) (hz : Formula.sat domLB2 z) :
    0 ≤ z (Lv 0) ∧ -(1:ℝ)/2 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 1/2 ∧ -(1:ℝ)/2 ≤ z (Lv 3) ∧
      z (Lv 3) ≤ 1/2 := by
  have h := (sat_domLB2 z).mp hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

/-- The left odometer is non-decreasing on the left envelope (`v ≥ 0`, `|ψ| ≤ 1/2`). -/
theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 6)) (hz : Formula.sat domLB2 z) :
    0 ≤ Term.eval (fLB2 l 1) z := by
  rw [fLB21_eval l hl]
  obtain ⟨h0, h1, h2, h3, h4⟩ := domL_bnd z hz
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Lv 2) * z (Lv 2))) - 3/10 * (z (Lv 3) * z (Lv 3)) := by
    nlinarith
  exact mul_nonneg h0 this

theorem stayL (l q : ℕ) (hl : l < 3) {c : ℝ} :
    AtomsStayC (cL l) (jointSys (fLB2 l) (fRB2 q) (Term.const c)) (Formula.and domLB2 domRB2) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domLB2 domRB2) (fun x h => h)
    (fun z hz _ => sdotL_nonneg l hl z hz.1) hinit

/-- The right atoms stay along every flow of the right mode (joint, or with the left frozen):
`s_R' = v_R ≥ 0`, and `v_R' = 3 (c_q − v_R) ≤ 0` at the cap `v_R = c_q`. -/
theorem stayR_gen (q : ℕ) (hq : q < 3) (fL : Fin 6 → Term (Var 6)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 6)) (hD : ∀ z, Formula.sat D z → Formula.sat domRB2 z) :
    AtomsStayC (cR q) (jointSys fL (fRB2 q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
    (fun z hz _ => by rw [fRB21_eval q hq]; exact LR.v_nonneg z (hD z hz)) hinit

/-! ## The invariant's components, as the tool lowers them -/

theorem comps_eq : hostComps vsB2 6
    (refinement_ladder_rover_rung2b_6dof_IRv2.invariants.getD 0 ("", PForm.tt)).2 = gB2 :: gsB2 := by
  have hrow : (refinement_ladder_rover_rung2b_6dof_IRv2.invariants.getD 0 ("", PForm.tt)).2 = invB2PF := rfl
  have hlist : pAtoms invB2PF = [(atomsOf invB2PF).getD 0 .tt] := by decide
  rw [hrow, hostComps_atoms vsB2 invB2PF ?_, hlist]
  · rfl
  · rw [hlist]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hdrops : ("L_v".drop 2).copy = "v" ∧ ("R_v".drop 2).copy = "v" ∧ ("L_s".drop 2).copy = "s" ∧
        ("R_s".drop 2).copy = "s" := by decide
    rcases ha with rfl <;>
      exact ⟨⟨_, _, _, rfl⟩, by
        simp [atomsOf, invB2PF, refinement_ladder_rover_rung2b_6dof_IR, Run.invToG, Run.lowerE, vsB2, gp_0, gp_0_0, gp_0_1, gp_0_15, gp_0_2, gp_0_25, gp_0_3, gp_0_30, gp_0_35, gp_0_4, gp_0_5, gp_0_50, gp_0_6, gp_0_65, gp_0_7, gp_0_75, gp_0_8, gp_0_9, gp_1, gp_1_0, gp_1_1, gp_1_2, gp_1_4, gp_1_5, gp_1_6, gp_2, gp_2_0, gp_3, gp_4, gp_5, gp_10, gp_m0_5, gp_m0_25, gp_m1, gp_m1_0, gp_m2, gp_m0_3, gp_m0_6, gp_m0_4, gp_899_95,
          Run.resolveVar, Parse.dr, hdrops, List.findIdx?_cons]⟩

theorem comps_fv : ∀ c ∈ gB2 :: gsB2, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [gB2, gsB2, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl <;> exact hgAt _

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 1001/1000, strata `[0]`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX refinement_ladder_rover_rung2b_6dof_IRv2 refinement_ladder_rover_rung2b_6dof_cutsV2X 6 0 [0] (1001/1000) l q

/-- The pre-joint reposition pack of window `l` at right mode `q` (`dynPreOrder = [0]`). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX refinement_ladder_rover_rung2b_6dof_IRv2 refinement_ladder_rover_rung2b_6dof_cutsV2X 6 0 [0] true l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsB2 6 Side.L (mLB2 l) = domLB2 := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vsB2 6 Side.R (mRB2 q) = domRB2 := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (gB2 :: gsB2) (fLB2 l) (fRB2 q) (1001/1000)
      (domCutX (Formula.and domLB2 domRB2) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdXCore (([0] : List ℕ).map (fun i => (hostComps vsB2 6
      (refinement_ladder_rover_rung2b_6dof_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
    (fLB2 l) (fRB2 q) ((1001/1000 : ℝ)) (domCutX (Formula.and (hostEvolve vsB2 6 Side.L (mLB2 l))
      (hostEvolve vsB2 6 Side.R (mRB2 q))) (cL l) (cR q)) at h'
  rw [hc] at h'
  simpa [gsB2] using h'

theorem verdD_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : VerdD l q) :
    VerdDynCore true (gB2 :: gsB2) (fRB2 q)
      (domCutX (Formula.and domLB2 domRB2) (cL l) (cR q)) (hostGuard vsB2 6 Side.L (mLB2 l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdDynCore true (([0] : List ℕ).map (fun i => (hostComps vsB2 6
      (refinement_ladder_rover_rung2b_6dof_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
    (fRB2 q) (domCutX (Formula.and (hostEvolve vsB2 6 Side.L (mLB2 l))
      (hostEvolve vsB2 6 Side.R (mRB2 q))) (cL l) (cR q)) (hostGuard vsB2 6 Side.L (mLB2 l)) at h'
  rw [hc] at h'
  simpa [gsB2] using h'


/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mRB2 q = dummyB2 :=
    List.getD_eq_default _ _ (by simp [refinement_ladder_rover_rung2b_6dof_IR]; omega)
  simp only [cR, this]
  rfl

/-- The anchor of the pair `(l, q)`: the tool's row components and both modes' kept atoms. -/
noncomputable def anc (l q : ℕ) : Formula (Var 6) := FM gB2 (gsB2 ++ atomTerms (cL l) (cR q))

theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vsB2 6 Side.L (mLB2 l)).fv ⊆ range Lv :=
  hostGuard_fv_L vsB2 (mLB2 l) (by interval_cases l <;> decide)

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
      Program.sem (Program.ode (jointSys (fLB2 l) (fRB2 q) (Term.const (1001/1000)))
        (Formula.and domLB2 domRB2)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX gB2 gsB2 (gB2 :: gsB2) (cL l) (cR q) (fLB2 l) (fRB2 q) (1001/1000) domLB2 domRB2
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl)
    (stayR_gen q hq (fLB2 l) (1001/1000) (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_boxD (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vsB2 6 Side.L (mLB2 l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fRB2 q) (Term.const 1))
        (Formula.and domLB2 domRB2)) σ ω → Formula.sat (anc l q) ω := by
  intro σ ω h1 h2 h3
  exact couple_box_dyn true gB2 gsB2 (gB2 :: gsB2) (cL l) (cR q) (fRB2 q) domLB2 domRB2
    (hostGuard vsB2 6 Side.L (mLB2 l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fv l hl) (hguardL l hl)
    (stayR_gen q hq _ 1 (by norm_num) _ (fun z hz => by
      simp only [dynBase, if_true] at hz; exact hz.1.2))
    (verdD_core l q hl hq hv) σ ω h1 (fun _ => h2) h3

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

/-! ## The ladder's switching choreography and the cover's node sets -/

/-- No speed cap: the bands' guards read the odometer only. -/
abbrev Cap (_q : ℕ) (_x : State (Var 6)) : Prop := True

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 6))
    (hg : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 q)) x) (hd : Formula.sat domRB2 x) :
    ladPre Cap domRB2 q x := by
  refine ⟨hq, ?_, trivial, hd⟩
  interval_cases q
  · rw [sat_guardR0] at hg
    exact ⟨fun _ => ⟨hg.1, hg.2⟩, fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
  · rw [sat_guardR1] at hg
    exact ⟨fun h => absurd h (by norm_num), fun _ => ⟨hg.1, hg.2⟩, fun h => absurd h (by norm_num)⟩
  · rw [sat_guardR2] at hg
    exact ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ => hg⟩

theorem ladPre_R (q : ℕ) (x y : State (Var 6)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : ladPre Cap domRB2 q x) : ladPre Cap domRB2 q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, -, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, trivial, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · refine (Formula.coincidence domRB2 (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRB2 hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 6), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2⟩
theorem leg11 : ∀ x : State (Var 6), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 _
  show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2⟩
theorem leg01 : ∀ x : State (Var 6), x (Rv 1) = 3/5 → Cap 0 x → SwitchLegal LR.e01 x := by
  intro x hs _
  show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 1)) x
  rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num⟩
theorem leg12 : ∀ x : State (Var 6), x (Rv 1) = 7/5 → Cap 1 x → SwitchLegal LR.e12 x := by
  intro x hs _
  show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x
  rw [sat_guardR2]; exact le_of_eq hs.symm
theorem leg22 : ∀ x : State (Var 6), 7/5 ≤ x (Rv 1) → Cap 2 x → SwitchLegal LR.e22 x := by
  intro x hs _
  show Formula.sat (hostGuard vsB2 6 Side.R (mRB2 2)) x
  rw [sat_guardR2]; exact hs

/-- The cover's joint nodes of window `l` (`jointOK`: the bands at or above the window's band)
and the reposition nodes its derivation uses from the admissible starts (`dynPre`: the band
just below). -/
def J (l q : ℕ) : Prop := l ≤ q ∧ q < 3
def D (l q : ℕ) : Prop := q < l

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 6) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domRB2 q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domRB2) E :=
  ladder_hmove LR Cap (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (edgeG 0 0)
    (edgeG 1 1) (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    leg01 leg11 leg12 leg22 (J l) (fun q hJ hq2 => ⟨by have := hJ.1; omega, by omega⟩) E hE

theorem hexitR (l : ℕ) (hl : l < 3) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domRB2) (ladPre Cap domRB2) :=
  ladder_hexit LR Cap (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) leg01 leg12 (J l) (D l)
    (fun q hD hnJ => by
      unfold D at hD; unfold J at hnJ ⊢
      refine ⟨by omega, ?_⟩
      by_cases h : l ≤ q + 1
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr ⟨by unfold D; omega, fun h' => h h'.1⟩)

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 6)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM gB2 gsB2) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 3) {σ : State (Var 6)}
    (hσ : Formula.sat (Formula.and (FM gB2 gsB2) envB2) σ)
    (hg : Formula.sat (hostGuard vsB2 6 Side.R (mRB2 q)) σ) :
    GResp GrG q (gwindowSeg (hostGuard vsB2 6 Side.L (mLB2 l)) (leftBlock (fLB2 l)) domLB2 tgB2 dt
      (1 + 1)) (fun _ => Formula.and (Formula.and (FM gB2 gsB2) envB2) Formula.tt) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · unfold D at h; omega
  refine replay_gresp GrG LR.m fRB2 domRB2 (fLB2 l) domLB2 (hostGuard vsB2 6 Side.L (mLB2 l)) aB2
    hgRG (hfLB2 l hl) hdomLB2 hdomRB2 (hguardL l hl) (1001/1000) (by norm_num) (J l) (D l)
    (fun q h => hfRB2 q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h.2)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.2 (hJv q h))
    (fun q h => anc_boxD l q hl (by unfold D at h; omega) (hDv q h))
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domRB2) (ladPre Cap domRB2) (ladPre Cap domRB2) ladPre_R ladPre_R
    (hmoveR l _ (fun _ _ _ h => h)) (fun _ _ => hmoveR l _ (fun _ _ hJ h => ⟨hJ, h⟩))
    (hexitR l hl) dt 1 q σ ?_ hσ.2.1 _ ?_
  · intro hgL
    have hpre := pre_of_guard q hq σ hg hσ.2.2
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    by_cases hlq : l ≤ q
    · exact Or.inl ⟨⟨hlq, hq⟩, hpre⟩
    · exact Or.inr ⟨by unfold D; omega, fun h => hlq h.1, hpre⟩
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLB2 ν :=
      windowSeg_end_domL (leftBlock (fLB2 l)) domLB2 tgB2 dt (1 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FM gB2 gsB2) μ := by
      refine (sat_of_agree (fun x hx => ?_) (fun i => ?_) (fun i => ?_)).mp hA'
      · by_contra hS
        exact notMem_FM_fv (fun g' hg' hxg => hS (comps_fv g' hg' hxg)) hx
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hpre.2.2.2⟩, trivial⟩
    refine (Formula.coincidence domLB2 (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLB2 hv
    exact hμL i

/-! ## Theorem 3 over the gated windows, by replaying the cover -/

/-- The left windows, each behind its lowered IR guard (the left automaton's edge test). -/
noncomputable def guardsL : List (Formula (Var 6)) :=
  (List.range 3).map (fun l => hostGuard vsB2 6 Side.L (mLB2 l))

noncomputable def leftDataG : List (Formula (Var 6) × (Fin 6 → Term (Var 6)) × Formula (Var 6) × ℕ) :=
  gatedData guardsL leftDataB2

theorem leftDataG_eq : leftDataG =
    [(hostGuard vsB2 6 Side.L (mLB2 0), fLB2 0, domLB2, 2),
     (hostGuard vsB2 6 Side.L (mLB2 1), fLB2 1, domLB2, 2),
     (hostGuard vsB2 6 Side.L (mLB2 2), fLB2 2, domLB2, 2)] := rfl

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 6)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tgB2 dt d.2.2.2)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
    d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  rw [leftDataG_eq] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfLB2 0 (by norm_num), hdomLB2⟩
  · exact ⟨hguardL 1 (by norm_num), hfLB2 1 (by norm_num), hdomLB2⟩
  · exact ⟨hguardL 2 (by norm_num), hfLB2 2 (by norm_num), hdomLB2⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mvB2 := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tgB2 dt d.2.2.2 mvB2 (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-- **`refinement_ladder_rover_rung2b_6dof`, Theorem 3 by replaying the emitted cover** (over the gated
windows; carried to the paper's left automaton by `theorem3_leftAut_of_choiceR`). The right
answers window `l` from band `q` as the cover's derivation does: a band below the window's
(`dynPre`) repositions alone to the next floor (the reposition pack `VerdD l q`), then the
right keeps time with the window at the cover's λ = 1 in the joint nodes (`jointOK`: the
bands at or above the window's), switching up at each floor it reaches, the anchor of each
pair preserved by its joint pack `Verd l q`; every switch is legal against the entered
band's guard; the `FLAT` window from `STEEP` is inadmissible. -/
theorem rung2b_6dof_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d20 : VerdD 2 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mvB2)
      (RFormula.and (RFormula.and (canonInvM gB2 gsB2) (envLR domLB2 domRB2))
        (mvRegionR mvB2 gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvB2 (FM gB2 gsB2) domLB2 domRB2 gregion
    (leftProgsG dt) (canonInvM gB2 gsB2) (encode_canonInvM gB2 gsB2) ?_ ?_ ?_
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
  · refine hstep_assembled_GR GrG mvB2 (FM gB2 gsB2) envB2 gregion (leftProgsG dt)
      hmvFB2 hmvenvB2 hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesG dt) ?_
    refine Hmulti_regionG GrG mvB2 _ (fun _ => Formula.tt) GrG_guards (FM gB2 gsB2) envB2
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
          interval_cases q
          · exact d20
          · exact d21
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM gB2 gsB2) domLB2 domRB2
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL gB2 gsB2 (by
        intro g' hg'
        simp only [gB2, gsB2, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gB2 gsB2) hdomLB2 hdomRB2

end RoverRung2b6dofGuarded
end RelCertifier
