/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung1_2to3` over the GUARDED right automaton — Theorem 3 by replaying the cover

`RoverLadderRung1Modal` states Theorem 3 over the `⊤`-guarded chain `STEEP → MODER → FLAT`. This file
states it over the GUARDED chain (every edge tests the lowered guard of the band it enters,
`GrG_guards`) at the mode-consistent region (the right in the guard of its current band),
against the gated left windows (carried to the paper's left automaton in
`Instances/LeftAutLegacy.lean`), and proves it by REPLAYING THE EMITTED COVER
(`InstancesV2/BenchCovers/refinement_ladder_rover_rung1_2to3.lean`, λ = 1 for every window): a band just below the
window's (`dynPre`) repositions alone to the next floor, preserved by the reposition pack
`VerdD l q`; in the joint nodes (the bands at or above the window's, `jointOK`) the right keeps
time with the window, switching up at each floor it reaches, every stretch preserved by the
joint pack `Verd l q` (`ReplayEngine`, `LadderReplay`); the `FLAT` window from `STEEP` is
inadmissible. Every switch is legal against the entered band's guard; the explicit band runs
(`LR`) supply only the existence of the right's runs. Hypotheses: six joint packs and two
reposition packs (`modalVerdX`, `modalVerdDynX`, the tool's own queries, re-sent by
`relcert --run-verdicts-v2`).
-/
import RelCertifier.Instances.RoverLadderRung1Modal
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayBridge
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung1_2to3
import RelCertifier.Instances.GuardedPins
import RelCertifier.Proofs.Encoding.LadderClimb

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace RoverLadderRung1Guarded

open DL DLCalTiming DLRel Parse Set RoverLadderRung1Modal GPins RelCertifier.Oracle

/-! ## The guarded right graph -/

noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsE 3 Side.R (mRE tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeE 0, modeE 1, modeE 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range refinement_ladder_rover_rung1_2to3_IR.R.modes.length).flatMap (fun q =>
      (mRE q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung1_2to3_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range refinement_ladder_rover_rung1_2to3_IR.R.modes.length).flatMap (fun q =>
      (mRE q).next.map (fun nm =>
        (q, refinement_ladder_rover_rung1_2to3_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 2), (1, 1), (2, 2)] := by decide
  rw [this]; rfl

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsE 3 Side.R (mRE e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 3) : GrG.modeAt q = some (modeE q) := by
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
  have hqm : q < 3 ∧ m = modeE q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])
  obtain ⟨hq3, rfl⟩ := hqm
  exact hRvE q (modeE q) (GrE_modeAt q hq3)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mvE ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vsE 3 Side.R (mRE q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsE _ dummyE rfl (by
    simp [refinement_ladder_rover_rung1_2to3_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (st tgt : ℕ) (h : edgeG st tgt ∈ GrG.edges) :
    edgeG st tgt ∈ GrG.edgesFrom st :=
  List.mem_filter.mpr ⟨h, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem he04 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem he14 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem he03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem he05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 3/5 ∧ x (Rv 0) ≤ 3/10) := by
  simp [hostGuard, mRE, refinement_ladder_rover_rung1_2to3_IR, Run.lowerF, Run.lowerE, he00,
    he04, he14, he03, he05, he065, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x ↔
    (3/5 ≤ x (Rv 1) ∧ x (Rv 1) < 7/5 ∧ x (Rv 0) ≤ 1/2) := by
  simp [hostGuard, mRE, refinement_ladder_rover_rung1_2to3_IR, Run.lowerF, Run.lowerE, he00,
    he04, he14, he03, he05, he065, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x ↔
    (7/5 ≤ x (Rv 1) ∧ x (Rv 0) ≤ 13/20) := by
  simp [hostGuard, mRE, refinement_ladder_rover_rung1_2to3_IR, Run.lowerF, Run.lowerE, he00,
    he04, he14, he03, he05, he065, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region (the guard; no kept cut) -/

noncomputable def gregion (q : ℕ) : Formula (Var 3) :=
  regionG (fun q => hostGuard vsE 3 Side.R (mRE q)) (fun _ => Formula.tt) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (by simp [Formula.fv])

theorem hmvregG : ∀ q, mvE ∉ (gregion q).fv := fun q h => aux_notin_range_Rv 0 (gregion_fv q h)

/-! ## The explicit band runs -/

/-- Band `q`'s explicit run from `ρ`: `v → c_q` exponentially at rate 3, `s` its integral,
the unused third coordinate frozen. -/
noncomputable def phiE (q : ℕ) (ρ : State (Var 3)) : Fin 3 → ℝ → ℝ := fun i t =>
  if i = 0 then cstE q + (ρ (Rv 0) - cstE q) * Real.exp (-(3 * t))
  else if i = 1 then
    ρ (Rv 1) + cstE q * t + (ρ (Rv 0) - cstE q) * (1 - Real.exp (-(3 * t))) / 3
  else ρ (Rv i)

noncomputable def runE (q : ℕ) (ρ : State (Var 3)) (t : ℝ) : State (Var 3) :=
  trajR ρ (phiE q ρ) t

theorem runE_v (q : ℕ) (ρ : State (Var 3)) (t : ℝ) :
    runE q ρ t (Rv 0) = cstE q + (ρ (Rv 0) - cstE q) * Real.exp (-(3 * t)) := by
  simp [runE, trajR_R, phiE]
theorem runE_s (q : ℕ) (ρ : State (Var 3)) (t : ℝ) :
    runE q ρ t (Rv 1) =
      ρ (Rv 1) + cstE q * t + (ρ (Rv 0) - cstE q) * (1 - Real.exp (-(3 * t))) / 3 := by
  simp [runE, trajR_R, phiE]
theorem runE_L (q : ℕ) (ρ : State (Var 3)) (t : ℝ) (i : Fin 3) :
    runE q ρ t (Lv i) = ρ (Lv i) := trajR_L _ _ _ _

theorem cstE_bounds (q : ℕ) (hq : q < 3) : 3/10 ≤ cstE q ∧ cstE q ≤ 13/20 := by
  interval_cases q <;> norm_num [cstE]

/-- `s(t) ≥ s₀ + c t − c/3 ≥ s₀` along the run (from `v₀ ≥ 0`). -/
theorem runE_s_low (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hv0 : 0 ≤ ρ (Rv 0)) {t : ℝ}
    (ht : 0 ≤ t) :
    ρ (Rv 1) + cstE q * t - cstE q / 3 ≤ runE q ρ t (Rv 1) ∧ ρ (Rv 1) ≤ runE q ρ t (Rv 1) := by
  rw [runE_s]
  have hc := cstE_bounds q hq
  have he0 : 0 < Real.exp (-(3 * t)) := Real.exp_pos _
  have he1 : Real.exp (-(3 * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have he2 : 1 - 3 * t ≤ Real.exp (-(3 * t)) := by
    have := Real.add_one_le_exp (-(3 * t)); linarith
  constructor
  · nlinarith
  · rcases le_total (ρ (Rv 0)) (cstE q) with h | h
    · nlinarith
    · nlinarith

theorem runE_sem (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hdom : Formula.sat domRE ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Program.sem (Program.ode (modeE q).sys (modeE q).dom) ρ (runE q ρ τ) := by
  have hD := (sat_domRE ρ).mp hdom
  refine explicit_run ρ (phiE q ρ) τ hτ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [phiE]
  · intro i t _ _
    fin_cases i
    · have h := hasDerivAt_expApproach 3 (cstE q) (ρ (Rv 0)) t
      simp only [Fin.zero_eta, Fin.isValue]
      rw [fRE0_eval q hq, trajR_R]
      convert h using 1
      · funext u; simp [phiE]
      · simp [phiE]
    · have h := hasDerivAt_expIntegral 3 (cstE q) (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
      simp only [Fin.mk_one, Fin.isValue]
      rw [fRE1_eval q hq, trajR_R]
      convert h using 1
      · funext u; simp [phiE]
      · simp [phiE]
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [fRE2_eval q hq]
      have hf : phiE q ρ 2 = fun _ => ρ (Rv 2) := by funext u; simp [phiE]
      rw [hf]
      exact hasDerivAt_const t _
  · intro t ht _
    have hb := exp_approach_between 3 (cstE q) (ρ (Rv 0)) t (by norm_num) ht
    have hc := cstE_bounds q hq
    have hs := (runE_s_low q hq ρ hD.2.1 ht).2
    show Formula.sat domRE (runE q ρ t)
    rw [sat_domRE]
    refine ⟨?_, ?_, ?_⟩
    · show 0 ≤ runE q ρ t (Rv 1); linarith [hD.1]
    · show 0 ≤ runE q ρ t (Rv 0)
      rw [runE_v]
      exact le_trans (le_min hD.2.1 (by linarith)) hb.1
    · show runE q ρ t (Rv 0) ≤ 4/5
      rw [runE_v]
      exact le_trans hb.2 (max_le hD.2.2 (by linarith))

/-- **Reaching an odometer level** in band `q` (from `s₀ ≤ L`): the explicit run hits
`s = L` (intermediate values). -/
theorem runE_reach (q : ℕ) (hq : q < 3) (ρ : State (Var 3)) (hv0 : 0 ≤ ρ (Rv 0)) (L : ℝ)
    (hL : ρ (Rv 1) ≤ L) : ∃ τ, 0 ≤ τ ∧ runE q ρ τ (Rv 1) = L := by
  have hc := cstE_bounds q hq
  set T : ℝ := (L - ρ (Rv 1) + cstE q / 3) / cstE q with hT
  have hcpos : 0 < cstE q := by linarith
  have hT0 : 0 ≤ T := div_nonneg (by linarith) hcpos.le
  have hcont : ContinuousOn (fun t => runE q ρ t (Rv 1)) (Icc 0 T) := by
    apply Continuous.continuousOn
    simp only [runE_s]
    fun_prop
  have h0 : runE q ρ 0 (Rv 1) = ρ (Rv 1) := by rw [runE_s]; simp
  have hTv : L ≤ runE q ρ T (Rv 1) := by
    have := (runE_s_low q hq ρ hv0 hT0).1
    have hcT : cstE q * T = L - ρ (Rv 1) + cstE q / 3 := by
      rw [hT]; field_simp
    linarith
  obtain ⟨τ, hτ, hτv⟩ := intermediate_value_Icc hT0 hcont ⟨by rw [h0]; exact hL, hTv⟩
  exact ⟨τ, hτ.1, hτv⟩

/-- Along a band run that starts at or below the band's set point, `v_R` only grows and stays
at or below the set point. -/
theorem runE_v_mono (q : ℕ) (ρ : State (Var 3)) (hv : ρ (Rv 0) ≤ cstE q) {t : ℝ} (ht : 0 ≤ t) :
    ρ (Rv 0) ≤ runE q ρ t (Rv 0) ∧ runE q ρ t (Rv 0) ≤ cstE q := by
  have hb := exp_approach_between 3 (cstE q) (ρ (Rv 0)) t (by norm_num) ht
  rw [runE_v]
  rw [min_eq_left hv] at hb
  rw [max_eq_right hv] at hb
  exact hb

/-! ## The ladder run (explicit; the padded third coordinate frozen) -/

theorem cstE_eq (q : ℕ) : cstE q = ladC q := rfl

noncomputable def LR : LadderRun GrG domRE :=
  LadderRun.ofLinear GrG domRE modeE fRE (fun _ => 0) (fun _ => 0) GrG_modeAt (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun q hq x => by rw [fRE0_eval q hq, cstE_eq])
    (fun q hq x => fRE1_eval q hq x)
    (fun q hq i h0 h1 x => by
      have hi : i = 2 := by fin_cases i <;> simp_all
      subst hi
      rw [fRE2_eval q hq]; simp)
    (fun q _ ρ hρ t ht => by
      have hD := (sat_domRE ρ).mp hρ
      have hv := phiLin_v_between (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) q ρ (n := 1) ht
      have hs := (phiLin_s_low (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) q ρ (n := 1) hD.2.1 ht).2
      have hc := ladC_bounds q
      rw [sat_domRE, trajR_R, trajR_R]
      refine ⟨by linarith [hD.1], ?_, ?_⟩
      · exact le_trans (le_min hD.2.1 (by linarith)) hv.1
      · exact le_trans hv.2 (max_le hD.2.2 (by linarith)))
    (fun ρ hρ => ((sat_domRE ρ).mp hρ).2.1)
    (edgeG 0 1) (edgeG 1 2) (edgeG 2 2)
    (edgeG_mem 0 1 (by simp [GrG])) (edgeG_mem 1 2 (by simp [GrG]))
    (edgeG_mem 2 2 (by simp [GrG])) rfl rfl rfl
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x
      rw [sat_guardR1]; exact ⟨le_of_eq hs.symm, by rw [hs]; norm_num, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x
      rw [sat_guardR2]; exact ⟨le_of_eq hs.symm, by linarith⟩)
    (fun x hs hv => by
      show Formula.sat (hostGuard vsE 3 Side.R (mRE 2)) x
      rw [sat_guardR2]; exact ⟨hs, hv⟩)

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aV (k : String) : PForm := .cmp "<=" (.var "v") (.num k)
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
def vStr (q : ℕ) : String := if q = 0 then "0.3" else if q = 1 then "0.5" else "0.65"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 3) :=
  cutPairsX vsE 3 Side.L (cutAtomsOfX refinement_ladder_rover_rung1_2to3_cutsV2X.L (mLE l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 3) :=
  cutPairsX vsE 3 Side.R (cutAtomsOfX refinement_ladder_rover_rung1_2to3_cutsV2X.R (mRE q).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsE 3 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsE,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsE 3 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsE,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]
theorem gR_v (q : ℕ) (hq : q < 3) : hostAtomG vsE 3 Side.R (aV (vStr q)) = thrLe (Rv 0) (ladC q) := by
  interval_cases q <;>
  simp [aV, vStr, ladC, hostAtomG, cutAtomG, Run.lowerE, gp_0_3, gp_0_5, gp_0_65, vsE,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrLe, Rv]

theorem cL_eq (l : ℕ) (hl : l < 3) :
    cL l = [(hostAtomF vsE 3 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l))] := by
  rw [← gL_s l hl]; interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsE 3 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q)),
      (hostAtomF vsE 3 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))] := by
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

theorem cutSatL_iff (l : ℕ) (hl : l < 3) (ν : State (Var 3)) :
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

theorem cutSatR_iff (q : ℕ) (hq : q < 3) (ν : State (Var 3)) :
    CutSat (cR q) ν ↔ sK q ≤ ν (Rv 1) ∧ ν (Rv 0) ≤ ladC q := by
  have h1 := hiffR q hq (hostAtomF vsE 3 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))
    (by rw [cR_eq q hq]; simp) ν
  have h2 := hiffR q hq (hostAtomF vsE 3 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))
    (by rw [cR_eq q hq]; simp) ν
  simp only [thrGe, thrLe, Term.eval, AOp.interp] at h1 h2
  constructor
  · intro h
    have a1 := h1.mp (h (hostAtomF vsE 3 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))
      (by rw [cR_eq q hq]; simp))
    have a2 := h2.mp (h (hostAtomF vsE 3 Side.R (aV (vStr q)), thrLe (Rv 0) (ladC q))
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
    ∀ ν, Formula.sat (hostGuard vsE 3 Side.L (mLE l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard refinement_ladder_rover_rung1_2to3_cutsV2X_wf (mLE l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung1_2to3_cutsV2X, mLE, refinement_ladder_rover_rung1_2to3_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung1_2to3_cutsV2X, mLE, refinement_ladder_rover_rung1_2to3_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, vsE, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mLE, refinement_ladder_rover_rung1_2to3_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
        gp_899_95, vsE, Run.resolveVar, List.findIdx?_cons]

theorem hO1R (q : ℕ) (hq : q < 3) :
    ∀ ν, Formula.sat (hostGuard vsE 3 Side.R (mRE q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard refinement_ladder_rover_rung1_2to3_cutsV2X_wf (mRE q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung1_2to3_cutsV2X, mRE, refinement_ladder_rover_rung1_2to3_IR] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, refinement_ladder_rover_rung1_2to3_cutsV2X, mRE, refinement_ladder_rover_rung1_2to3_IR] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4, gp_0_3, gp_0_5, gp_0_65, vsE,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRE, refinement_ladder_rover_rung1_2to3_IR, Run.lowerF, Run.lowerE, gp_0_0, gp_0_6, gp_1_4,
        gp_0_3, gp_0_5, gp_0_65, vsE, Run.resolveVar, List.findIdx?_cons]

/-! ## The left field and envelope, evaluated -/

theorem gp_1000_0 : Run.parseRat "1000.0" = some (1000:ℚ) := by
  have h : parseQ "1000.0" = some (⟨10000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fLE1_eval (l : ℕ) (hl : l < 3) (x : State (Var 3)) :
    Term.eval (fLE l 1) x = x (Lv 0) * (1 - 1/2 * (x (Lv 2) * x (Lv 2))) := by
  interval_cases l <;>
    simp [fLE, hostDyn, mLE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
      Run.lowerE, gp_3, gp_0_30, gp_0_50, gp_0_65, gp_1, gp_0_5, gp_m1, gp_0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Lv]

/-- The left envelope's bounds the odometer's sign needs. -/
theorem domL_bnd (z : State (Var 3)) (hz : Formula.sat domLE z) :
    0 ≤ z (Lv 0) ∧ -(1:ℝ)/2 ≤ z (Lv 2) ∧ z (Lv 2) ≤ 1/2 := by
  simp only [domLE, hostEvolve, mLE, refinement_ladder_rover_rung1_2to3_IR, vsE] at hz
  simp [Run.lowerF, Run.lowerE, gp_0_0, gp_0_8, gp_m0_5, gp_0_15, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
    Term.eval, Lv] at hz
  casesm* _ ∧ _
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

/-- The left odometer is non-decreasing on the left envelope (`v ≥ 0`, `|ψ| ≤ 1/2`). -/
theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 3)) (hz : Formula.sat domLE z) :
    0 ≤ Term.eval (fLE l 1) z := by
  rw [fLE1_eval l hl]
  obtain ⟨h0, h1, h2⟩ := domL_bnd z hz
  have : (0:ℝ) ≤ 1 - 1/2 * (z (Lv 2) * z (Lv 2)) := by nlinarith
  exact mul_nonneg h0 this

theorem stayL (l q : ℕ) (hl : l < 3) :
    AtomsStayC (cL l) (jointSys (fLE l) (fRE q) (Term.const 1)) (Formula.and domLE domRE) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  rw [cL_eq l hl] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domLE domRE) (fun x h => h)
    (fun z hz _ => sdotL_nonneg l hl z hz.1) hinit

/-- The right atoms stay along every flow of the right mode (joint, or with the left frozen):
`s_R' = v_R ≥ 0`, and `v_R' = 3 (c_q − v_R) ≤ 0` at the cap `v_R = c_q`. -/
theorem stayR_gen (q : ℕ) (hq : q < 3) (fL : Fin 3 → Term (Var 3)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 3)) (hD : ∀ z, Formula.sat D z → Formula.sat domRE z) :
    AtomsStayC (cR q) (jointSys fL (fRE q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 1 (sK q) _ _ c hc D D (fun x h => h)
      (fun z hz _ => by rw [fRE1_eval q hq]; exact LR.v_nonneg z (hD z hz)) hinit
  · exact boxle_thrLe_R 0 (ladC q) _ _ c hc D D (fun x h => h)
      (fun z hz hK => by rw [fRE0_eval q hq, cstE_eq]; linarith) hinit

/-! ## The invariant's components, as the tool lowers them -/

/-- The declared row's components (`invComponents`, the tool's own lowering). -/
noncomputable def gV : Term (Var 3) := Term.binop .sub (Term.var (Lv 0)) (Term.var (Rv 0))
noncomputable def gsV : List (Term (Var 3)) :=
  [Term.binop .sub (Term.var (Lv 1)) (Term.binop .add (Term.var (Rv 1)) (Term.const (1/5)))]

theorem comps_eq : hostComps vsE 3
    (refinement_ladder_rover_rung1_2to3_IRv2.invariants.getD 0 ("", PForm.tt)).2 = gV :: gsV := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  have hdL' : ("L_s".drop 2).copy = "s" := by decide
  have hdR' : ("R_s".drop 2).copy = "s" := by decide
  simp [hostComps, refinement_ladder_rover_rung1_2to3_IRv2, Oracle.invComponents, Run.lowerE, vsE,
    Run.resolveVar, Parse.dr, hdL, hdR, hdL', hdR', List.findIdx?_cons, gp_0_2, ITerm.toHost,
    gV, gsV, Lv, Rv]

/-- The tool's components and the statement's rows are the same constraints. -/
theorem sat_FV_iff (x : State (Var 3)) : Formula.sat (FM gV gsV) x ↔ Formula.sat (FM gE gsE) x := by
  rw [sat_FM_iff, sat_FM_iff]
  simp only [gV, gsV, gE, gsE, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
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
  modalVerdX refinement_ladder_rover_rung1_2to3_IRv2 refinement_ladder_rover_rung1_2to3_cutsV2X 3 0 [0, 1] 1 l q

/-- The pre-joint reposition pack of window `l` at right mode `q` (`dynPreOrder = [0, 1]`). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX refinement_ladder_rover_rung1_2to3_IRv2 refinement_ladder_rover_rung1_2to3_cutsV2X 3 0 [0, 1] true l q

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsE 3 Side.L (mLE l) = domLE := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vsE 3 Side.R (mRE q) = domRE := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (gV :: gsV) (fLE l) (fRE q) 1
      (domCutX (Formula.and domLE domRE) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdXCore (([0, 1] : List ℕ).map (fun i => (hostComps vsE 3
      (refinement_ladder_rover_rung1_2to3_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
    (fLE l) (fRE q) 1 (domCutX (Formula.and (hostEvolve vsE 3 Side.L (mLE l))
      (hostEvolve vsE 3 Side.R (mRE q))) (cL l) (cR q)) at h'
  rw [hc] at h'
  simpa [gsV] using h'

theorem verdD_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : VerdD l q) :
    VerdDynCore true (gV :: gsV) (fRE q)
      (domCutX (Formula.and domLE domRE) (cL l) (cR q)) (hostGuard vsE 3 Side.L (mLE l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  have hc := comps_eq
  change VerdDynCore true (([0, 1] : List ℕ).map (fun i => (hostComps vsE 3
      (refinement_ladder_rover_rung1_2to3_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
    (fRE q) (domCutX (Formula.and (hostEvolve vsE 3 Side.L (mLE l))
      (hostEvolve vsE 3 Side.R (mRE q))) (cL l) (cR q)) (hostGuard vsE 3 Side.L (mLE l)) at h'
  rw [hc] at h'
  simpa [gsV] using h'


/-! ## The anchors of the cover's pairs -/

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : mRE q = dummyE :=
    List.getD_eq_default _ _ (by simp [refinement_ladder_rover_rung1_2to3_IR]; omega)
  simp only [cR, this]
  rfl

/-- The anchor of the pair `(l, q)`: the tool's row components and both modes' kept atoms. -/
noncomputable def anc (l q : ℕ) : Formula (Var 3) := FM gV (gsV ++ atomTerms (cL l) (cR q))

theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vsE 3 Side.L (mLE l)).fv ⊆ range Lv :=
  hostGuard_fv_L vsE (mLE l) (by interval_cases l <;> decide)

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
      Program.sem (Program.ode (jointSys (fLE l) (fRE q) (Term.const 1))
        (Formula.and domLE domRE)) σ ω → Formula.sat (anc l q) ω :=
  couple_box_cutX gV gsV (gV :: gsV) (cL l) (cR q) (fLE l) (fRE q) 1 domLE domRE
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl)
    (stayR_gen q hq (fLE l) 1 (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl hq hv)

theorem anc_boxD (l q : ℕ) (hl : l < 3) (hq : q < 3) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vsE 3 Side.L (mLE l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fRE q) (Term.const 1))
        (Formula.and domLE domRE)) σ ω → Formula.sat (anc l q) ω := by
  intro σ ω h1 h2 h3
  exact couple_box_dyn true gV gsV (gV :: gsV) (cL l) (cR q) (fRE q) domLE domRE
    (hostGuard vsE 3 Side.L (mLE l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fv l hl) (hguardL l hl)
    (stayR_gen q hq _ 1 (by norm_num) _ (fun z hz => by
      simp only [dynBase, if_true] at hz; exact hz.1.2))
    (verdD_core l q hl hq hv) σ ω h1 (fun _ => h2) h3

theorem anc_hand (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 3 := hltG q e he
  have hg : Formula.sat (hostGuard vsE 3 Side.R (mRE e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

/-! ## The ladder's switching choreography and the cover's node sets -/

/-- The speed cap of each band (`v ≤ c_q`, a conjunct of every right guard). -/
abbrev Cap (q : ℕ) (x : State (Var 3)) : Prop := x (Rv 0) ≤ ladC q

theorem pre_of_guard (q : ℕ) (hq : q < 3) (x : State (Var 3))
    (hg : Formula.sat (hostGuard vsE 3 Side.R (mRE q)) x) (hd : Formula.sat domRE x) :
    ladPre Cap domRE q x := by
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

theorem ladPre_R (q : ℕ) (x y : State (Var 3)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : ladPre Cap domRE q x) : ladPre Cap domRE q y := by
  obtain ⟨hq, ⟨h0, h1, h2⟩, hc, hd⟩ := h
  refine ⟨hq, ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [← hxy 1]; exact h0 h
  · rw [← hxy 1]; exact h1 h
  · rw [← hxy 1]; exact h2 h
  · show y (Rv 0) ≤ ladC q; rw [← hxy 0]; exact hc
  · refine (Formula.coincidence domRE (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRE hv
    exact hxy i

theorem leg00 : ∀ x : State (Var 3), 0 ≤ x (Rv 1) → x (Rv 1) < 3/5 → Cap 0 x →
    SwitchLegal (edgeG 0 0) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsE 3 Side.R (mRE 0)) x
  rw [sat_guardR0]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩
theorem leg11 : ∀ x : State (Var 3), 3/5 ≤ x (Rv 1) → x (Rv 1) < 7/5 → Cap 1 x →
    SwitchLegal (edgeG 1 1) x := by
  intro x h1 h2 h3
  show Formula.sat (hostGuard vsE 3 Side.R (mRE 1)) x
  rw [sat_guardR1]; exact ⟨h1, h2, by simpa [Cap, ladC] using h3⟩

/-- The cover's joint nodes of window `l` (`jointOK`: the bands at or above the window's band)
and the reposition nodes its derivation uses from the admissible starts (`dynPre`: the band
just below). -/
def J (l q : ℕ) : Prop := l ≤ q ∧ q < 3
def D (l q : ℕ) : Prop := q + 1 = l

theorem hmoveR (l : ℕ) (E : ℕ → State (Var 3) → Prop)
    (hE : ∀ q x, J l q → ladPre Cap domRE q x → E q x) :
    HMove GrG LR.m (J l) (fun q => q) (ladPre Cap domRE) E :=
  ladder_hmove LR Cap (ladCap_run LR) ladCap_up (edgeG 0 0) (edgeG 1 1)
    (edgeG_mem 0 0 (by simp [GrG])) (edgeG_mem 1 1 (by simp [GrG])) rfl rfl leg00
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc)) leg11
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg22 x hs (by simpa [Cap, ladC] using hc))
    (J l) (fun q hJ hq2 => ⟨by have := hJ.1; omega, by omega⟩) E hE

theorem hexitR (l : ℕ) (hl : l < 3) :
    HExit GrG LR.m (J l) (D l) (fun q => 2 - q) (ladPre Cap domRE) (ladPre Cap domRE) :=
  ladder_hexit LR Cap (ladCap_run LR) ladCap_up
    (fun x hs hc => LR.leg01 x hs (by simpa [Cap, ladC] using hc))
    (fun x hs hc => LR.leg12 x hs (by simpa [Cap, ladC] using hc)) (J l) (D l)
    (fun q hD hnJ => by
      unfold D at hD; unfold J at hnJ ⊢
      refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩)

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem anc_iff (l q : ℕ) (hl : l < 3) (hq : q < 3) (x : State (Var 3)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FM gV gsV) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem respondR (l : ℕ) (hl : l < 3) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 3) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM gE gsE) envE) σ)
    (hg : Formula.sat (hostGuard vsE 3 Side.R (mRE q)) σ) :
    GResp GrG q (gwindowSeg (hostGuard vsE 3 Side.L (mLE l)) (leftBlock (fLE l)) domLE tgE dt
      (0 + 1)) (fun _ => Formula.and (Formula.and (FM gE gsE) envE) Formula.tt) σ := by
  have hJD3 : ∀ q, J l q ∨ D l q → q < 3 := by
    intro q h; rcases h with h | h
    · exact h.2
    · unfold D at h; omega
  refine replay_gresp GrG LR.m fRE domRE (fLE l) domLE (hostGuard vsE 3 Side.L (mLE l)) aE
    hgRG (hfLE l hl) hdomLE hdomRE (hguardL l hl) 1 one_pos (J l) (D l)
    (fun q h => hfRE q (hJD3 q h)) (fun q => q) (fun q => 2 - q) 3 (fun q h => h.2)
    (fun q h => LR.modeAt q (hJD3 q h)) (fun _ _ => rfl) (fun q h => LR.dom_m q (hJD3 q h))
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.2 (hJv q h))
    (fun q h => anc_boxD l q hl (by unfold D at h; omega) (hDv q h))
    (fun q h => anc_hand l q hl (hJD3 q h))
    (ladPre Cap domRE) (ladPre Cap domRE) (ladPre Cap domRE) ladPre_R ladPre_R
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
        have hrow := (sat_FM_iff gE gsE σ).mp hσ.1 (gAt 1) (by simp [gsE])
        rw [gAt1_eval] at hrow
        simp [sK] at hsL
        linarith [hg.2.1]
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLE ν :=
      windowSeg_end_domL (leftBlock (fLE l)) domLE tgE dt (0 + 1) (by norm_num) hwin
    have hq' : q' < 3 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FM gV gsV) μ := by
      refine (sat_of_agree (fun x hx => ?_) (fun i => ?_) (fun i => ?_)).mp hA'
      · by_contra hS
        exact notMem_FM_fv (fun g' hg' hxg => hS (comps_fv g' hg' hxg)) hx
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨(sat_FV_iff μ).mp hF, ?_, hpre.2.2.2⟩, trivial⟩
    refine (Formula.coincidence domLE (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLE hv
    exact hμL i

/-! ## Theorem 3 over the gated windows, by replaying the cover -/

/-- The left windows, each behind its lowered IR guard (the left automaton's edge test). -/
noncomputable def guardsL : List (Formula (Var 3)) :=
  (List.range 3).map (fun l => hostGuard vsE 3 Side.L (mLE l))

noncomputable def leftDataG : List (Formula (Var 3) × (Fin 3 → Term (Var 3)) × Formula (Var 3) × ℕ) :=
  gatedData guardsL leftDataE

theorem leftDataG_eq : leftDataG =
    [(hostGuard vsE 3 Side.L (mLE 0), fLE 0, domLE, 1),
     (hostGuard vsE 3 Side.L (mLE 1), fLE 1, domLE, 1),
     (hostGuard vsE 3 Side.L (mLE 2), fLE 2, domLE, 1)] := rfl

noncomputable def leftProgsG (dt : ℝ) : List (Program (Var 3)) :=
  leftDataG.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tgE dt d.2.2.2)

theorem hLG : ∀ d ∈ leftDataG, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
    d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  rw [leftDataG_eq] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hguardL 0 (by norm_num), hfLE 0 (by norm_num), hdomLE⟩
  · exact ⟨hguardL 1 (by norm_num), hfLE 1 (by norm_num), hdomLE⟩
  · exact ⟨hguardL 2 (by norm_num), hfLE 2 (by norm_num), hdomLE⟩

theorem hframesG (dt : ℝ) : ∀ P ∈ leftProgsG dt, FramesMv P mvE := by
  intro P hP
  simp only [leftProgsG, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tgE dt d.2.2.2 mvE (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-- **`refinement_ladder_rover_rung1_2to3`, Theorem 3 by replaying the emitted cover** (over the gated
windows; carried to the paper's left automaton by `theorem3_leftAut_of_choiceR`). The right
answers window `l` from band `q` as the cover's derivation does: a band below the window's
(`dynPre`) repositions alone to the next floor (the reposition pack `VerdD l q`), then the
right keeps time with the window at the cover's λ = 1 in the joint nodes (`jointOK`: the
bands at or above the window's), switching up at each floor it reaches, the anchor of each
pair preserved by its joint pack `Verd l q`; every switch is legal against the entered
band's guard; the `FLAT` window from `STEEP` is inadmissible. -/
theorem rover_ladder_rung1_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mvE)
      (RFormula.and (RFormula.and (canonInvM gE gsE) (envLR domLE domRE))
        (mvRegionR mvE gregion GrG.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrG mvE (FM gE gsE) domLE domRE gregion
    (leftProgsG dt) (canonInvM gE gsE) (encode_canonInvM gE gsE) ?_ ?_ ?_
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
  · refine hstep_assembled_GR GrG mvE (FM gE gsE) envE gregion (leftProgsG dt)
      hmvFE hmvenvE hmvregG hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (hframesG dt) ?_
    refine Hmulti_regionG GrG mvE _ (fun _ => Formula.tt) GrG_guards (FM gE gsE) envE
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
  · exact hddF_multiR_G GrG 0 1 dt leftDataG gregion (canonInvM gE gsE) domLE domRE
      (by decide) hgRG hRvG hLG (fun q _ => gregion_fv q)
      (canonInvM_varsL gE gsE (by
        intro g' hg'
        simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gE gsE) hdomLE hdomRE

end RoverLadderRung1Guarded
end RelCertifier
