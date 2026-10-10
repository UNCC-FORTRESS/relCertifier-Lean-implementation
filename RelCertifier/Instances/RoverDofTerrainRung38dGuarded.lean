/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung3_8d` over the GUARDED right automaton — Theorem 3 by replaying the cover

`RoverDofTerrainRung38dModal` states Theorem 3 over the `⊤`-guarded chain `STEEP → MODER → FLAT`. This file
states it over the GUARDED chain (every edge tests the lowered guard of the band it enters,
`GrG_guards`) at the mode-consistent region (the right in the guard of its current band),
against the gated left windows (carried to the paper's left automaton in
`Instances/LeftAutLegacy.lean`), and proves it by REPLAYING THE EMITTED COVER
(`InstancesV2/BenchCovers/rover_dof_terrain_rung3_8d.lean`, λ = 1 for every window): a band just below the
window's (`dynPre`) repositions alone to the next floor, preserved by the reposition pack
`VerdD l q`; in the joint nodes (the bands at or above the window's, `jointOK`) the right keeps
time with the window, switching up at each floor it reaches, every stretch preserved by the
joint pack `Verd l q` (`ReplayEngine`, `LadderReplay`); the `FLAT` window from `STEEP` is
inadmissible. Every switch is legal against the entered band's guard; the explicit band runs
(`LR`) supply only the existence of the right's runs. Hypotheses: six joint packs and two
reposition packs (`modalVerdX`, `modalVerdDynX`, the tool's own queries, re-sent by
`relcert --run-verdicts-v2`).
-/
import RelCertifier.Instances.RoverDofTerrainRung38dModal
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayBridge
import RelCertifier.InstancesV2.Cuts.rover_dof_terrain_rung3_8d

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace RelCertifier
namespace RoverDofTerrainRung38dGuarded

open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung38dModal GPins RelCertifier.Oracle

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 8) :=
  { src := st, tgt := tgt, guard := hostGuard vsU 8 Side.R (mRU tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 8) :=
  { modes := [modeU 0, modeU 1, modeU 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range rover_dof_terrain_rung3_8d_IR.R.modes.length).flatMap (fun q =>
      (mRU q).next.map (fun nm =>
        (q, rover_dof_terrain_rung3_8d_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range rover_dof_terrain_rung3_8d_IR.R.modes.length).flatMap (fun q =>
      (mRU q).next.map (fun nm =>
        (q, rover_dof_terrain_rung3_8d_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsU 8 Side.R (mRU e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeU q) := by
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
  have hqm : q < 3 ∧ m = modeU q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])
  obtain ⟨hq3, rfl⟩ := hqm
  exact hRvU q (modeU q) (GrU_modeAt q hq3)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvU ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsU 8 Side.R (mRU q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsU _ dummyU rfl (by
    simp [rover_dof_terrain_rung3_8d_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 8)) : Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6,
    gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region (the guard; no kept cut) -/

noncomputable def gregion (q : ℕ) : Formula (Var 8) :=
  regionG (fun q => hostGuard vsU 8 Side.R (mRU q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvU ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The ladder run (explicit: every coordinate on its own linear law, the odometer integrating `v`) -/

theorem cstU_eq (q : ℕ) : cstU q = ladC q := rfl

noncomputable def aR : Fin 8 → ℝ := ![0, 0, 1, 0, 1, 0, 1, 1]
noncomputable def bR : Fin 8 → ℝ := fun _ => 0

theorem aR_nonneg : ∀ k, 0 ≤ aR k := by
  intro k; fin_cases k <;> simp [aR]

noncomputable def LR : LadderRun GrG domRU :=
  LadderRun.ofLinear GrG domRU modeU fRU aR bR GrG_modeAt (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q hq x => by rw [fRU0_eval q hq, cstU_eq])
    (fun q hq x => fRU1_eval q hq x)
    (fun q hq i h0 h1 x => by
      fin_cases i
      · simp at h0
      · simp at h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU2_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU3_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU4_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU5_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU6_eval q hq]; simp [aR, bR]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [fRU7_eval q hq]; simp [aR, bR])
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRU ρ).mp hρ
      have hv := phiLin_v_between aR bR q ρ (n := 6) ht
      have hs := (phiLin_s_low aR bR q ρ (n := 6) hD.2.2.2.2.2.2.2.2.2.2.2.1 ht).2
      have hc := ladC_bounds q
      have hk : ∀ k : Fin 8, k ≠ 0 → k ≠ 1 →
          min (ρ (Rv k)) (bR k) ≤ phiLin aR bR q ρ k t ∧
            phiLin aR bR q ρ k t ≤ max (ρ (Rv k)) (bR k) :=
        fun k h0 h1 => phiLin_other_between aR bR q ρ k h0 h1 (aR_nonneg k) ht
      rw [sat_domRU]
      simp only [trajR_R]
      exact ⟨le_trans (le_min hD.1 (by norm_num [bR])) (hk 3 (by decide) (by decide)).1,
        le_trans (hk 3 (by decide) (by decide)).2 (max_le hD.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.1 (by norm_num [bR])) (hk 5 (by decide) (by decide)).1,
        le_trans (hk 5 (by decide) (by decide)).2 (max_le hD.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.1 (by norm_num [bR])) (hk 7 (by decide) (by decide)).1,
        le_trans (hk 7 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 2 (by decide) (by decide)).1,
        le_trans (hk 2 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans hD.2.2.2.2.2.2.2.2.1 hs,
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 4 (by decide) (by decide)).1,
        le_trans (hk 4 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.1])) hv.1,
        le_trans hv.2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linarith [hc.2])),
        le_trans (le_min hD.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num [bR])) (hk 6 (by decide) (by decide)).1,
        le_trans (hk 6 (by decide) (by decide)).2 (max_le hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by norm_num [bR]))⟩)
    (fun ρ hρ => by have hD := (sat_domRU ρ).mp hρ; exact hD.2.2.2.2.2.2.2.2.2.2.2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsU 8 Side.R (mRU 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aV (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
def vStr (q : ℕ) : String := if q = 0 then "0.3" else if q = 1 then "0.5" else "0.65"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 8) :=
  cutPairsX vsU 8 Side.L (cutAtomsOfX rover_dof_terrain_rung3_8d_cutsV2X.L (mLU l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 8) :=
  cutPairsX vsU 8 Side.R (cutAtomsOfX rover_dof_terrain_rung3_8d_cutsV2X.R (mRU q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsU 8 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsU,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsU 8 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsU,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]
theorem gR_v (q : ℕ) (hq : q < 3) : hostAtomG vsU 8 Side.R (aV (vStr q)) = thrLe (Rv 0) (ladC q) := by
  interval_cases q <;>
  simp [aV, vStr, ladC, hostAtomG, cutAtomG, Run.lowerE, gp_0_3, gp_0_5, gp_0_65, vsU,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vsU 8 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))] := by
  rw [← gL_s l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsU 8 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q)),
      (hostAtomF vsU 8 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))] := by
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

theorem cutSatL_iff (l : ℕ) (hl : l < 3) (ν : State (Var 8)) :
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

theorem cutSatR_iff (q : ℕ) (hq : q < 3) (ν : State (Var 8)) :
    CutSat (cR q) ν ↔ sK q ≤ ν (Rv 1) ∧ ν (Rv 0) ≤ ladC q := by
  have h1 := hiffR q hq (hostAtomF vsU 8 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))
    (by rw [cR_eq q hq]; simp) ν
  have h2 := hiffR q hq (hostAtomF vsU 8 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))
    (by rw [cR_eq q hq]; simp) ν
  simp only [thrGe, thrLe, Term.eval, AOp.interp] at h1 h2
  constructor
  · intro h
    have a1 := h1.mp (h (hostAtomF vsU 8 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))
      (by rw [cR_eq q hq]; simp))
    have a2 := h2.mp (h (hostAtomF vsU 8 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))
      (by rw [cR_eq q hq]; simp))
    constructor <;> linarith
  · rintro ⟨hs, hv⟩ a ha
    rw [cR_eq q hq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h1.mpr (by linarith)
    · exact h2.mpr (by linarith)


/-! ## O1: guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vsU 8 Side.L (mLU l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard rover_dof_terrain_rung3_8d_cutsV2X_wf (mLU l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, rover_dof_terrain_rung3_8d_cutsV2X, mLU, rover_dof_terrain_rung3_8d_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, rover_dof_terrain_rung3_8d_cutsV2X, mLU, rover_dof_terrain_rung3_8d_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsU, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mLU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
        gp_899_95, vsU, Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vsU 8 Side.R (mRU q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard rover_dof_terrain_rung3_8d_cutsV2X_wf (mRU q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, rover_dof_terrain_rung3_8d_cutsV2X, mRU, rover_dof_terrain_rung3_8d_IR] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, rover_dof_terrain_rung3_8d_cutsV2X, mRU, rover_dof_terrain_rung3_8d_IR] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsU,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRU, rover_dof_terrain_rung3_8d_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
        gp_0_3, gp_0_5, gp_0_65, vsU, Run.resolveVar, List.findIdx?_cons]

/-! ## The left field and envelope, evaluated -/

theorem gp_1000_0 : Run.parseRat "1000.0" = some (1000:ℚ) := by
  have h : parseQ "1000.0" = some (⟨10000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fLU1_eval (l : ℕ) (hl : l < 3) (x : State (Var 8)) :
    Term.eval (fLU l 1) x =
      x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 4) * x (Lv 4))) := by
  interval_cases l <;>
    simp [fLU, hostDyn, mLU, rover_dof_terrain_rung3_8d_IR, vsU, Run.dynOf,
      Run.lowerE, gp_3, gp_0_30, gp_0_50, gp_0_65, gp_1, gp_0_5, gp_0_3, gp_m1, gp_m2, gp_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Lv]

/-- The left envelope's bounds the odometer's sign needs. -/
theorem domL_bnd (z : State (Var 8)) (hz : Formula.sat domLU z) :
    0 ≤ z (Lv 0) ∧ -(1:ℝ)/2 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 1/2 ∧ -(1:ℝ)/2 ≤ z (Lv 4) ∧
      z (Lv 4) ≤ 1/2 := by
  simp only [domLU, hostEvolve, mLU, rover_dof_terrain_rung3_8d_IR, vsU] at hz
  simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_8, gp_m0_5, gp_0_15, gp_0_5, gp_1000_0, gp_m1_0,
    gp_1_0, gp_1_1, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv] at hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

/-- The left odometer is non-decreasing on the left envelope (`v ≥ 0`, `|ψ| ≤ 1/2`). -/
theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 8)) (hz : Formula.sat domLU z) :
    0 ≤ Term.eval (fLU l 1) z := by
  rw [fLU1_eval l hl]
  obtain ⟨h0, h1, h2, h3, h4⟩ := domL_bnd z hz
  have : (0:ℝ) ≤ (1 - 1/2 * (z (Lv 2) * z (Lv 2))) - 3/10 * (z (Lv 4) * z (Lv 4)) := by nlinarith
  exact mul_nonneg h0 this

theorem stayL (l q : ℕ) (hl : l < 3) :
    AtomsStayC (cL l) (jointSys (fLU l) (fRU q) (Term.const 1)) (Formula.and domLU domRU) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domLU domRU) (fun x h => h)
    (fun z hz _ => sdotL_nonneg l hl z hz.1) hinit

/-- The right atoms stay along every flow of the right mode (joint, or with the left frozen):
`s_R' = v_R ≥ 0`, and `v_R' = 3 (c_q − v_R) ≤ 0` at the cap `v_R = c_q`. -/
theorem stayR_gen (q : ℕ) (hq : q < 3) (fL : Fin 8 → Term (Var 8)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 8)) (hD : ∀ z, Formula.sat D z → Formula.sat domRU z) :
    AtomsStayC (cR q) (jointSys fL (fRU q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
      (fun z hz _ => by rw [fRU1_eval q hq]; exact LR.v_nonneg z (hD z hz)) hinit
  · exact boxle_thrLe_R 0 (ladC q) _ _ c hc D D (fun x h => h)
      (fun z hz hK => by rw [fRU0_eval q hq, cstU_eq]; linarith) hinit

/-! ## The invariant's components, as the tool lowers them -/

/-- The declared row's components (`invComponents`, the tool's own lowering). -/
noncomputable def gV : Term (Var 8) := Term.binop .sub (Term.var (Lv 0)) (Term.var (Rv 0))
noncomputable def gsV : List (Term (Var 8)) :=
  [Term.binop .sub (Term.var (Lv 1)) (Term.binop .add (Term.var (Rv 1)) (Term.const (1/5)))]

theorem comps_eq : hostComps vsU 8
    (rover_dof_terrain_rung3_8d_IRv2.invariants.getD 0 ("", PForm.tt)).2 = gV :: gsV := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  have hdL' : ("L_s".drop 2).copy = "s" := by decide
  have hdR' : ("R_s".drop 2).copy = "s" := by decide
  simp [hostComps, rover_dof_terrain_rung3_8d_IRv2, Oracle.invComponents, Run.lowerE, vsU,
    Run.resolveVar, Parse.dr, hdL, hdR, hdL', hdR', List.findIdx?_cons, gp_0_2, ITerm.toHost,
    gV, gsV, Lv, Rv]

/-- The tool's components and the statement's rows are the same constraints. -/
theorem sat_FV_iff (x : State (Var 8)) : Formula.sat (FM gV gsV) x ↔ Formula.sat (FM gU gsU) x := by
  rw [sat_FM_iff, sat_FM_iff]
  simp only [gV, gsV, gU, gsU, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, gAt0_eval, gAt1_eval, Term.eval, AOp.interp]

theorem comps_fv : ∀ c ∈ gV :: gsV, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [gV, gsV, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
  · intro x hx
    simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q` (the cover's λ = 1, strata `[0, 1]`). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX rover_dof_terrain_rung3_8d_IRv2 rover_dof_terrain_rung3_8d_cutsV2X 8 0 [0, 1] 1 l q

/-- The pre-joint reposition pack of window `l` at right mode `q` (`dynPreOrder = [0, 1]`). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX rover_dof_terrain_rung3_8d_IRv2 rover_dof_terrain_rung3_8d_cutsV2X 8 0 [0, 1] true l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsU 8 Side.L (mLU l) = domLU := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vsU 8 Side.R (mRU q) = domRU := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (gV :: gsV) (fLU l) (fRU q) 1
      (domCutX (Formula.and domLU domRU) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdXCore (([0, 1] : List ℕ).map (fun i => (hostComps vsU 8
      (rover_dof_terrain_rung3_8d_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
    (fLU l) (fRU q) 1 (domCutX (Formula.and (hostEvolve vsU 8 Side.L (mLU l))
      (hostEvolve vsU 8 Side.R (mRU q))) (cL l) (cR q)) at h'
  rw [hc] at h'
  simpa [gsV] using h'

theorem verdD_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : VerdD l q) :
    VerdDynCore true (gV :: gsV) (fRU q)
      (domCutX (Formula.and domLU domRU) (cL l) (cR q)) (hostGuard vsU 8 Side.L (mLU l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdDynCore true (([0, 1] : List ℕ).map (fun i => (hostComps vsU 8
      (rover_dof_terrain_rung3_8d_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
    (fRU q) (domCutX (Formula.and (hostEvolve vsU 8 Side.L (mLU l))
      (hostEvolve vsU 8 Side.R (mRU q))) (cL l) (cR q)) (hostGuard vsU 8 Side.L (mLU l)) at h'
  rw [hc] at h'
  simpa [gsV] using h'


/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mRU q = dummyU :=
    List.getD_eq_default _ _ (by simp [rover_dof_terrain_rung3_8d_IR]; omega)
  simp only [cR, this]
  rfl

/-- The anchor of the pair `(l, q)`: the tool's row components and both modes' kept atoms. -/
noncomputable def anc (l q : ℕ) : Formula (Var 8) := FM gV (gsV ++ atomTerms (cL l) (cR q))

theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vsU 8 Side.L (mLU l)).fv ⊆ range Lv :=
  hostGuard_fv_L vsU (mLU l) (by interval_cases l <;> decide)

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
      Program.sem (Program.ode (jointSys (fLU l) (fRU q) (Term.const 1))
        (Formula.and domLU domRU)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX gV gsV (gV :: gsV) (cL l) (cR q) (fLU l) (fRU q) 1 domLU domRU
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl)
    (stayR_gen q hq (fLU l) 1 (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_boxD (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vsU 8 Side.L (mLU l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fRU q) (Term.const 1))
        (Formula.and domLU domRU)) σ ω → Formula.sat (anc l q) ω := by
  intro σ ω h1 h2 h3
  exact couple_box_dyn true gV gsV (gV :: gsV) (cL l) (cR q) (fRU q) domLU domRU
    (hostGuard vsU 8 Side.L (mLU l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fv l hl) (hguardL l hl)
    (stayR_gen q hq _ 1 (by norm_num) _ (fun z hz => by
      simp only [dynBase, if_true] at hz; exact hz.1.2))
    (verdD_core l q hl hq hv) σ ω h1 (fun _ => h2) h3

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vsU 8 Side.R (mRU e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

/-! ## The ladder's switching choreography and the cover's node sets -/

/-- The speed cap of each band (`v ≤ c_q`, a conjunct of every right guard). -/
abbrev Cap (q : ℕ) (x : State (Var 8)) : Prop := x (Rv 0) ≤ ladC q

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 8))
    (hg : Formula.sat (hostGuard vsU 8 Side.R (mRU q)) x) (hd : Formula.sat domRU x) :
    ladPre Cap domRU q x := by
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
    (h : ladPre Cap domRU q x) : ladPre Cap domRU q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, hc, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · show y (Rv 0) ≤ ladC q; rw [← hxy 0]; exact hc
  · refine (Formula.coincidence domRU (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRU hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 8), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsU 8 Side.R (mRU 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩
theorem leg11 : ∀ x : State (Var 8), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsU 8 Side.R (mRU 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩

/-- The cover's joint nodes of window `l` (`jointOK`: the bands at or above the window's band)
and the reposition nodes its derivation uses from the admissible starts (`dynPre`: the band
just below). -/
def J (l q : ℕ) : Prop := l ≤ q ∧ q < 3
def D (l q : ℕ) : Prop := q + 1 = l

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 8) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domRU q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domRU) E :=
  ladder_hmove LR Cap (ladCap_run LR) ladCap_up (edgeG 0 0) (edgeG 1 1)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc)) leg11
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg22 x hs (by simpa [Cap, ladC] using hc))
    (J l) (fun q hJ hq2 => ⟨by have := hJ.1; omega, by omega⟩) E hE

theorem hexitR (l : ℕ) (hl : l < 3) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domRU) (ladPre Cap domRU) :=
  ladder_hexit LR Cap (ladCap_run LR) ladCap_up
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc)) (J l) (D l)
    (fun q hD hnJ => by
      unfold D at hD; unfold J at hnJ ⊢
      refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩)

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 8)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM gV gsV) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 3) {σ : State (Var 8)}
    (hσ : Formula.sat (Formula.and (FM gU gsU) envU) σ)
    (hg : Formula.sat (hostGuard vsU 8 Side.R (mRU q)) σ) :
    GResp GrG q (gwindowSeg (hostGuard vsU 8 Side.L (mLU l)) (leftBlock (fLU l)) domLU tgU dt
      (0 + 1)) (fun _ => Formula.and (Formula.and (FM gU gsU) envU) Formula.tt) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · unfold D at h; omega
  refine replay_gresp GrG LR.m fRU domRU (fLU l) domLU (hostGuard vsU 8 Side.L (mLU l)) aU
    hgRG (hfLU l hl) hdomLU hdomRU (hguardL l hl) 1 one_pos (J l) (D l)
    (fun q h => hfRU q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h.2)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.2 (hJv q h))
    (fun q h => anc_boxD l q hl (by unfold D at h; omega) (hDv q h))
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domRU) (ladPre Cap domRU) (ladPre Cap domRU) ladPre_R ladPre_R
    (hmoveR l _ (fun _ _ _ h => h)) (fun _ _ => hmoveR l _ (fun _ _ hJ h => ⟨hJ, h⟩))
    (hexitR l hl) dt 0 q σ ?_ hσ.2.1 _ ?_
  · intro hgL
    have hpre := pre_of_guard q hq σ hg hσ.2.2
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨(sat_FV_iff σ).mpr hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    by_cases hlq : l ≤ q
    · exact Or.inl ⟨⟨hlq, hq⟩, hpre⟩
    · by_cases hD : q + 1 = l
      · exact Or.inr ⟨hD, fun h => hlq h.1, hpre⟩
      · -- the only remaining pair, `FLAT` window from `STEEP`, is inadmissible
        exfalso
        have hl2 : l = 2 := by omega
        have hq0 : q = 0 := by omega
        subst hl2 hq0
        have hsL := (cutSatL_iff 2 (by norm_num) σ).mp (hO1L 2 (by norm_num) σ hgL)
        rw [sat_guardR0] at hg
        have hrow := (sat_FM_iff gU gsU σ).mp hσ.1 (gAt 1) (by simp [gsU])
        rw [gAt1_eval] at hrow
        simp [sK] at hsL
        linarith [hg.2.1]
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLU ν :=
      windowSeg_end_domL (leftBlock (fLU l)) domLU tgU dt (0 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FM gV gsV) μ := by
      refine (sat_of_agree (fun x hx => ?_) (fun i => ?_) (fun i => ?_)).mp hA'
      · by_contra hS
        exact notMem_FM_fv (fun g' hg' hxg => hS (comps_fv g' hg' hxg)) hx
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨(sat_FV_iff μ).mp hF, ?_, hpre.2.2.2⟩, trivial⟩
    refine (Formula.coincidence domLU (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLU hv
    exact hμL i

/-! ## Theorem 3 over the gated windows, by replaying the cover -/

/-- The left windows, each behind its lowered IR guard (the left automaton's edge test). -/
noncomputable def guardsL : List (Formula (Var 8)) :=
  (List.range 3).map (fun l => hostGuard vsU 8 Side.L (mLU l))

noncomputable def leftDataG : List (Formula (Var 8) × (Fin 8 → Term (Var 8)) × Formula (Var 8) × ℕ) :=
  gatedData guardsL leftDataU

theorem leftDataG_eq : leftDataG =
    [(hostGuard vsU 8 Side.L (mLU 0), fLU 0, domLU, 1),
     (hostGuard vsU 8 Side.L (mLU 1), fLU 1, domLU, 1),
     (hostGuard vsU 8 Side.L (mLU 2), fLU 2, domLU, 1)] := rfl

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 8)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tgU dt d.2.2.2)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
    d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  rw [leftDataG_eq] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfLU 0 (by norm_num), hdomLU⟩
  · exact ⟨hguardL 1 (by norm_num), hfLU 1 (by norm_num), hdomLU⟩
  · exact ⟨hguardL 2 (by norm_num), hfLU 2 (by norm_num), hdomLU⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mvU := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tgU dt d.2.2.2 mvU (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-- **`rover_dof_terrain_rung3_8d`, Theorem 3 by replaying the emitted cover** (over the gated
windows; carried to the paper's left automaton by `theorem3_leftAut_of_choiceR`). The right
answers window `l` from band `q` as the cover's derivation does: a band below the window's
(`dynPre`) repositions alone to the next floor (the reposition pack `VerdD l q`), then the
right keeps time with the window at the cover's λ = 1 in the joint nodes (`jointOK`: the
bands at or above the window's), switching up at each floor it reaches, the anchor of each
pair preserved by its joint pack `Verd l q`; every switch is legal against the entered
band's guard; the `FLAT` window from `STEEP` is inadmissible. -/
theorem rover_dof_terrain_rung3_8d_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mvU)
      (RFormula.and (RFormula.and (canonInvM gU gsU) (envLR domLU domRU))
        (mvRegionR mvU gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvU (FM gU gsU) domLU domRU gregion
    (leftProgsG dt) (canonInvM gU gsU) (encode_canonInvM gU gsU) ?_ ?_ ?_
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
  · refine hstep_assembled_GR GrG mvU (FM gU gsU) envU gregion (leftProgsG dt)
      hmvFU hmvenvU hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesG dt) ?_
    refine Hmulti_regionG GrG mvU _ (fun _ => Formula.tt) GrG_guards (FM gU gsU) envU
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
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM gU gsU) domLU domRU
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL gU gsU (by
        intro g' hg'
        simp only [gU, gsU, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gU gsU) hdomLU hdomRU

end RoverDofTerrainRung38dGuarded
end RelCertifier
